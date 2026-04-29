import json
import re
import difflib
import time
import uuid
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from pathlib import Path
import ctypes
import ctypes.wintypes as wintypes
import threading
import tkinter as tk
from tkinter import ttk, messagebox
from draft_tools import (
    base64_decode_text,
    base64_encode_text,
    format_json_text,
    url_decode_text,
    url_encode_text,
)


DATE_FMT = "%Y-%m-%d"
TIME_FMT = "%Y-%m-%d %H:%M:%S"
LOG_FLUSH_INTERVAL_MS = 3 * 1000
WM_HOTKEY = 0x0312
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_SHIFT = 0x0004
MOD_WIN = 0x0008
GLOBAL_HOTKEY_ID = 1
ERROR_ALREADY_EXISTS = 183
SINGLE_INSTANCE_MUTEX_NAME = "DailyTaskAssistant.Singleton.Mutex"
_single_instance_mutex_handle = None


def _acquire_single_instance_lock() -> bool:
    global _single_instance_mutex_handle
    if _single_instance_mutex_handle is not None:
        return True
    try:
        handle = ctypes.windll.kernel32.CreateMutexW(None, False, SINGLE_INSTANCE_MUTEX_NAME)
        if not handle:
            return True
        last_error = ctypes.windll.kernel32.GetLastError()
        if last_error == ERROR_ALREADY_EXISTS:
            ctypes.windll.kernel32.CloseHandle(handle)
            return False
        _single_instance_mutex_handle = handle
        return True
    except Exception:
        # 异常时不阻止启动，避免误伤正常使用
        return True

APP_THEME = {
    "bg_root": "#1e222c",
    "bg_main": "#252a36",
    "bg_elevated": "#2c3240",
    "bg_canvas": "#22262f",
    "bg_row": "#2a303c",
    "border": "#3a4254",
    "border_focus": "#6b9fff",
    "fg": "#e8ecf4",
    "fg_muted": "#98a4b8",
    "fg_done": "#7a869c",
    "accent": "#6b9fff",
    "accent_hover": "#82b0ff",
    "title_bar": "#232831",
}

UI_FONT = ("Microsoft YaHei UI", 10)
UI_FONT_SM = ("Microsoft YaHei UI", 9)
MONO_FONT = ("Consolas", 10)

LOG_TAB_AUTO_REFRESH_MS = 45_000

WEEKLY_AI_PROMPT_TEMPLATE = """你是一名熟悉职场写作的助手。以下是我在某一自然周（周一至周日）内，在「每日任务助手」中记录的每日任务完成情况（含已完成与未完成）。

请阅读【任务记录】后，用中文帮我生成一份工作周报，要求：
1) 提炼本周主要完成事项与成果；
2) 简要说明未完成或推迟项的原因（如有）；
3) 给出下周可执行的改进方向或计划建议；
4) 语气专业、简洁，适合粘贴到邮件或 IM。

【任务记录】
{tasks_block}

---
（以上内容由「每日任务助手」按周导出；周区间见任务记录首行。）
"""


@dataclass
class TaskItem:
    id: str
    text: str
    done: bool
    created_at: str
    source_day: str


class DailyTaskAssistant:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("每日任务助手")
        self.base_dir = Path(__file__).resolve().parent
        self.data_dir = self.base_dir / "data"
        self.logs_dir = self.base_dir / "logs"
        self.data_dir.mkdir(exist_ok=True)
        self.logs_dir.mkdir(exist_ok=True)
        self.settings_file = self.data_dir / "settings.json"
        self.settings = self._load_settings()

        self.root.geometry("640x520")
        self._setup_window_appearance()

        self.today = datetime.now().strftime(DATE_FMT)
        self.today_file = self.data_dir / f"tasks_{self.today}.json"
        self.incremental_log_file = self.logs_dir / f"incremental_{self.today}.jsonl"
        self.daily_archive_log_file = self.logs_dir / "daily_archive.jsonl"
        self.draft_file = self.data_dir / "draft.txt"

        self.tasks: list[TaskItem] = []
        self.task_vars: dict[str, tk.BooleanVar] = {}
        self.task_done_canvases: dict[str, tk.Canvas] = {}
        self.task_text_labels: dict[str, tk.Label] = {}
        self.inline_editing_task_id: str | None = None
        self.pending_events: list[dict] = []
        self.last_saved_signature: str | None = None
        self.global_hotkey_registered = False
        self.hotkey_listener_thread: threading.Thread | None = None
        self.hotkey_listener_thread_id: int | None = None

        self._drag_start_x = 0
        self._drag_start_y = 0
        self._win_start_x = 0
        self._win_start_y = 0
        self._drag_from_tabstrip = False
        self._alpha_save_after_id = None
        self._prompt_save_after_id = None
        self._log_refresh_after_id = None
        self._weekly_tasks_plain = ""
        self._log_week_key_by_label: dict[str, str] = {}
        self._draft_search_visible = False
        self._draft_source = ""
        self._draft_refreshing = False
        self._draft_force_raw = False
        self._draft_history: list[str] = []
        self._draft_history_idx: int = -1
        self._draft_history_restoring: bool = False
        self._draft_history_last_change_ts: float = 0.0
        self._draft_history_coalesce_window_s: float = 0.5
        self._draft_last_nav_line: int | None = None
        self._draft_active_raw_line: int | None = None
        self._draft_return_press_col: int | None = None
        self._draft_markdown_return_handled: bool = False
        self._draft_markdown_delete_handled: bool = False
        self._task_scroll_host: tk.Misc | None = None
        self._task_scroll_canvas: tk.Canvas | None = None
        self._settings_scroll_host: tk.Misc | None = None
        self._settings_scroll_canvas: tk.Canvas | None = None
        self._logs_scroll_host: tk.Misc | None = None
        self._logs_scroll_widget: tk.Text | None = None

        self._build_ui()
        self.root.bind_all("<MouseWheel>", self._on_global_mousewheel_for_panels, add="+")
        self._load_tasks_for_today()
        self._refresh_task_list()
        self._schedule_incremental_flush()
        self._setup_shortcuts()
        self._register_global_hotkey()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_ui(self) -> None:
        self._setup_styles()

        th = APP_THEME
        drag_strip = tk.Frame(
            self.root,
            bg=th["title_bar"],
            height=6,
            highlightthickness=0,
            bd=0,
            cursor="fleur",
        )
        drag_strip.pack(side=tk.TOP, fill=tk.X)
        drag_strip.pack_propagate(False)
        drag_strip.bind("<Button-1>", self._start_window_drag)
        drag_strip.bind("<B1-Motion>", self._on_window_drag)

        main_frame = ttk.Frame(self.root, padding=(8, 0, 8, 6), style="Main.TFrame")
        main_frame.pack(fill=tk.BOTH, expand=True)

        self._notebook_shell = tk.Frame(main_frame, bg=th["bg_main"], highlightthickness=0, bd=0)
        self._notebook_shell.pack(fill=tk.BOTH, expand=True)

        self.notebook = ttk.Notebook(self._notebook_shell, style=self._notebook_style_used)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.close_btn = ttk.Button(
            self._notebook_shell,
            text="✕",
            width=2,
            command=self._on_close,
            style="TabClose.TButton",
        )
        self.close_btn.place(relx=1.0, y=5, anchor=tk.NE, x=-4)
        self.root.after_idle(self.close_btn.lift)

        self.notebook.bind("<Button-1>", self._on_notebook_tabstrip_press)
        self.notebook.bind("<B1-Motion>", self._on_notebook_tabstrip_motion)
        self.notebook.bind("<ButtonRelease-1>", self._on_notebook_tabstrip_release)

        self.tasks_tab = ttk.Frame(self.notebook, style="Main.TFrame")
        self.draft_tab = ttk.Frame(self.notebook, style="Main.TFrame")
        self.logs_tab = ttk.Frame(self.notebook, style="Main.TFrame")
        self.settings_tab = ttk.Frame(self.notebook, style="Main.TFrame")

        self.notebook.add(self.tasks_tab, text="任务")
        self.notebook.add(self.draft_tab, text="草稿")
        self.notebook.add(self.logs_tab, text="日志")
        self.notebook.add(self.settings_tab, text="设置")

        self._build_settings_tab(self.settings_tab)

        input_frame = ttk.Frame(self.tasks_tab, style="Main.TFrame")
        input_frame.pack(fill=tk.X, pady=(0, 10))

        self.task_entry = ttk.Entry(input_frame)
        self.task_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.task_entry.bind("<Return>", lambda _event: self._add_task())

        draft_toolbar = ttk.Frame(self.draft_tab, style="Main.TFrame")
        draft_toolbar.pack(fill=tk.X, pady=(0, 6))
        self._draft_tools_popup: tk.Widget | None = None
        self._draft_tools_menu_button = ttk.Button(
            draft_toolbar,
            text="工具 ▼",
            command=self._toggle_draft_tools_popup,
            style="Secondary.TButton",
        )
        self._draft_tools_menu_button.pack(side=tk.LEFT)
        self.root.bind("<Button-1>", self._on_root_click_maybe_hide_draft_tools, add="+")
        ttk.Label(draft_toolbar, text="显示", style="Status.TLabel").pack(side=tk.LEFT, padx=(16, 4))
        self._draft_view_mode_var = tk.StringVar(value="markdown")
        self._draft_md_mode_radio = ttk.Radiobutton(
            draft_toolbar,
            text="Markdown",
            variable=self._draft_view_mode_var,
            value="markdown",
            command=self._apply_draft_view_mode_from_toolbar,
            style="App.TRadiobutton",
        )
        self._draft_md_mode_radio.pack(side=tk.LEFT)
        self._draft_src_mode_radio = ttk.Radiobutton(
            draft_toolbar,
            text="源码",
            variable=self._draft_view_mode_var,
            value="source",
            command=self._apply_draft_view_mode_from_toolbar,
            style="App.TRadiobutton",
        )
        self._draft_src_mode_radio.pack(side=tk.LEFT, padx=(6, 0))

        draft_frame = ttk.Frame(self.draft_tab, style="Main.TFrame")
        draft_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        draft_title_row = ttk.Frame(draft_frame, style="Main.TFrame")
        draft_title_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(draft_title_row, text="草稿区（Markdown：光标所在行为源码，其余行实时渲染）", style="Status.TLabel").pack(
            side=tk.LEFT
        )

        draft_stats_row = ttk.Frame(draft_frame, style="Main.TFrame")
        draft_stats_row.pack(fill=tk.X, side=tk.BOTTOM, pady=(6, 0))
        self.draft_stats_label = ttk.Label(draft_stats_row, text="源码字数：0  选中：0", style="Status.TLabel")
        self.draft_stats_label.pack(side=tk.RIGHT)

        editor_panel = ttk.Frame(draft_frame, style="Main.TFrame")
        editor_panel.pack(fill=tk.BOTH, expand=True)
        self.draft_text = tk.Text(
            editor_panel,
            height=16,
            bg=th["bg_elevated"],
            fg=th["fg"],
            insertbackground=th["fg"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=th["border"],
            highlightcolor=th["border_focus"],
            bd=0,
            font=UI_FONT,
            padx=10,
            pady=10,
            wrap="word",
            undo=False,
            autoseparators=False,
            maxundo=0,
        )
        self.draft_text.pack(fill=tk.BOTH, expand=True)
        self._draft_source = self._load_draft_text()
        self._draft_history = [self._draft_source]
        self._draft_history_idx = 0
        self._draft_history_last_change_ts = 0.0
        self._configure_draft_markdown_tags(self.draft_text)
        self._setup_draft_editor_features(editor_panel)
        self._draft_refresh_view()
        self._update_draft_stats()

        list_container = ttk.Frame(self.tasks_tab, style="Main.TFrame")
        list_container.pack(fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(list_container, highlightthickness=0, bg=th["bg_canvas"], bd=0)
        self.scrollbar = ttk.Scrollbar(list_container, orient="vertical", command=self.canvas.yview)
        self.scroll_frame = ttk.Frame(self.canvas, style="CanvasInner.TFrame")

        self.scroll_frame.bind(
            "<Configure>",
            lambda _event: self.canvas.configure(scrollregion=self.canvas.bbox("all")),
        )
        self._canvas_inner_window = self.canvas.create_window((0, 0), window=self.scroll_frame, anchor="nw")
        self.canvas.bind("<Configure>", self._on_task_canvas_configure)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self._task_scroll_host = list_container
        self._task_scroll_canvas = self.canvas

        log_toolbar = ttk.Frame(self.logs_tab, style="Main.TFrame")
        log_toolbar.pack(fill=tk.X, pady=(0, 8))
        ttk.Label(log_toolbar, text="视图", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_mode_var = tk.StringVar(value="单日")
        self._log_mode_values = ["单日", "周汇总"]
        self.log_mode_dropdown_btn = ttk.Button(
            log_toolbar,
            text=self.log_mode_var.get() + " ▼",
            style="Secondary.TButton",
            command=lambda: self._toggle_log_dropdown("mode"),
        )
        self.log_mode_dropdown_btn.pack(side=tk.LEFT, padx=(4, 12))
        ttk.Frame(log_toolbar, style="Main.TFrame").pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(
            log_toolbar,
            text="一键复制周报提示词",
            command=self._copy_weekly_ai_prompt,
            style="Secondary.TButton",
        ).pack(side=tk.RIGHT)

        self.log_date_frame = ttk.Frame(log_toolbar, style="Main.TFrame")
        ttk.Label(self.log_date_frame, text="日期", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_day_var = tk.StringVar(value=self.today)
        self._log_day_values: list[str] = [self.today]
        self.log_day_dropdown_btn = ttk.Button(
            self.log_date_frame,
            text=self.log_day_var.get() + " ▼",
            style="Secondary.TButton",
            command=lambda: self._toggle_log_dropdown("day"),
        )
        self.log_day_dropdown_btn.pack(side=tk.LEFT, padx=(6, 0))

        self.log_week_frame = ttk.Frame(log_toolbar, style="Main.TFrame")
        ttk.Label(self.log_week_frame, text="自然周", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_week_var = tk.StringVar()
        self._log_week_values: list[str] = []
        self.log_week_dropdown_btn = ttk.Button(
            self.log_week_frame,
            text="请选择自然周 ▼",
            style="Secondary.TButton",
            command=lambda: self._toggle_log_dropdown("week"),
        )
        self.log_week_dropdown_btn.pack(side=tk.LEFT, padx=(6, 0))
        self._active_log_dropdown_popup: tk.Widget | None = None
        self._active_log_dropdown_kind: str | None = None

        log_text_wrap = ttk.Frame(self.logs_tab, style="Main.TFrame")
        log_text_wrap.pack(fill=tk.BOTH, expand=True)
        self.log_text = tk.Text(
            log_text_wrap,
            bg=th["bg_elevated"],
            fg=th["fg"],
            insertbackground=th["fg"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=th["border"],
            highlightcolor=th["border_focus"],
            bd=0,
            font=MONO_FONT,
            padx=10,
            pady=10,
            wrap="word",
        )
        self.log_text_scrollbar = ttk.Scrollbar(log_text_wrap, orient="vertical", command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=self.log_text_scrollbar.set)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.log_text_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(state=tk.DISABLED)
        self._logs_scroll_host = log_text_wrap
        self._logs_scroll_widget = self.log_text

        self._apply_log_mode_layout()
        self._reload_log_comboboxes()
        self._refresh_logs_tab_data()
        self._setup_log_tab_auto_refresh()

        status_frame = ttk.Frame(main_frame)
        status_frame.pack(fill=tk.X, pady=(8, 0))

        self.status_label = ttk.Label(status_frame, text="准备就绪", style="Status.TLabel")
        self.status_label.pack(anchor=tk.W)

    def _on_task_canvas_configure(self, event) -> None:
        if not getattr(self, "_canvas_inner_window", None):
            return
        inner_w = max(1, int(event.width))
        self.canvas.itemconfigure(self._canvas_inner_window, width=inner_w)

    def _on_global_mousewheel_for_panels(self, event=None) -> str | None:
        if event is None:
            return None
        try:
            cursor_widget = self.root.winfo_containing(self.root.winfo_pointerx(), self.root.winfo_pointery())
        except tk.TclError:
            return None
        if cursor_widget is None:
            return None
        canvas: tk.Canvas | None = None
        if self._task_scroll_host is not None and self._widget_is_descendant_of(cursor_widget, self._task_scroll_host):
            canvas = self._task_scroll_canvas
        elif self._settings_scroll_host is not None and self._widget_is_descendant_of(cursor_widget, self._settings_scroll_host):
            canvas = self._settings_scroll_canvas
        elif self._logs_scroll_host is not None and self._widget_is_descendant_of(cursor_widget, self._logs_scroll_host):
            if self._logs_scroll_widget is not None:
                try:
                    delta = int(event.delta / 120)
                except Exception:
                    delta = 0
                if delta == 0:
                    return None
                self._logs_scroll_widget.yview_scroll(-delta, "units")
                return "break"
        if canvas is None:
            return None
        try:
            delta = int(event.delta / 120)
        except Exception:
            delta = 0
        if delta == 0:
            return None
        canvas.yview_scroll(-delta, "units")
        return "break"

    def _build_settings_tab(self, frame: ttk.Frame) -> None:
        wrap = ttk.Frame(frame, style="Main.TFrame")
        wrap.pack(fill=tk.BOTH, expand=True)
        settings_canvas = tk.Canvas(wrap, bg=APP_THEME["bg_main"], highlightthickness=0, bd=0)
        settings_scrollbar = ttk.Scrollbar(wrap, orient="vertical", command=settings_canvas.yview)
        settings_canvas.configure(yscrollcommand=settings_scrollbar.set)
        settings_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        settings_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        inner = ttk.Frame(settings_canvas, padding=8, style="Main.TFrame")
        settings_canvas_window = settings_canvas.create_window((0, 0), window=inner, anchor="nw")

        def _on_settings_inner_configure(_event=None):
            settings_canvas.configure(scrollregion=settings_canvas.bbox("all"))

        def _on_settings_canvas_configure(event):
            settings_canvas.itemconfigure(settings_canvas_window, width=max(1, int(event.width)))

        inner.bind("<Configure>", _on_settings_inner_configure)
        settings_canvas.bind("<Configure>", _on_settings_canvas_configure)
        self._settings_scroll_host = wrap
        self._settings_scroll_canvas = settings_canvas

        ttk.Label(inner, text="基础快捷键", style="Status.TLabel").pack(anchor=tk.W, pady=(0, 6))
        ttk.Label(inner, text="显示/隐藏全局快捷键（例：CTRL+ALT+T）", style="Status.TLabel").pack(anchor=tk.W)
        self.global_hotkey_entry = ttk.Entry(inner)
        self.global_hotkey_entry.pack(fill=tk.X, pady=(4, 10))
        self.global_hotkey_entry.insert(0, self.settings.get("global_toggle_hotkey", "CTRL+ALT+T"))

        ttk.Label(inner, text="聚焦输入框快捷键（例：/ 或 F）", style="Status.TLabel").pack(anchor=tk.W)
        self.focus_key_entry = ttk.Entry(inner)
        self.focus_key_entry.pack(fill=tk.X, pady=(4, 10))
        self.focus_key_entry.insert(0, self.settings.get("focus_input_key", "/"))

        ttk.Label(inner, text="切换标签页快捷键（例：CTRL+TAB）", style="Status.TLabel").pack(anchor=tk.W)
        self.tab_key_entry = ttk.Entry(inner)
        self.tab_key_entry.pack(fill=tk.X, pady=(4, 8))
        self.tab_key_entry.insert(0, self.settings.get("tab_switch_hotkey", "CTRL+TAB"))

        ttk.Label(inner, text="工具快捷键", style="Status.TLabel").pack(anchor=tk.W, pady=(10, 6))
        ttk.Label(inner, text="草稿工具：JSON 格式化（例：CTRL+ALT+J）", style="Status.TLabel").pack(anchor=tk.W)
        self.tool_json_hotkey_entry = ttk.Entry(inner)
        self.tool_json_hotkey_entry.pack(fill=tk.X, pady=(4, 8))
        self.tool_json_hotkey_entry.insert(0, self.settings.get("tool_json_hotkey", "CTRL+ALT+J"))

        ttk.Label(inner, text="草稿工具：Base64 编码（例：CTRL+ALT+E）", style="Status.TLabel").pack(anchor=tk.W)
        self.tool_b64_encode_hotkey_entry = ttk.Entry(inner)
        self.tool_b64_encode_hotkey_entry.pack(fill=tk.X, pady=(4, 8))
        self.tool_b64_encode_hotkey_entry.insert(0, self.settings.get("tool_b64_encode_hotkey", "CTRL+ALT+E"))

        ttk.Label(inner, text="草稿工具：Base64 解码（例：CTRL+ALT+D）", style="Status.TLabel").pack(anchor=tk.W)
        self.tool_b64_decode_hotkey_entry = ttk.Entry(inner)
        self.tool_b64_decode_hotkey_entry.pack(fill=tk.X, pady=(4, 8))
        self.tool_b64_decode_hotkey_entry.insert(0, self.settings.get("tool_b64_decode_hotkey", "CTRL+ALT+D"))

        ttk.Label(inner, text="草稿工具：URL 编码（例：CTRL+ALT+U）", style="Status.TLabel").pack(anchor=tk.W)
        self.tool_url_encode_hotkey_entry = ttk.Entry(inner)
        self.tool_url_encode_hotkey_entry.pack(fill=tk.X, pady=(4, 8))
        self.tool_url_encode_hotkey_entry.insert(0, self.settings.get("tool_url_encode_hotkey", "CTRL+ALT+U"))

        ttk.Label(inner, text="草稿工具：URL 解码（例：CTRL+ALT+I）", style="Status.TLabel").pack(anchor=tk.W)
        self.tool_url_decode_hotkey_entry = ttk.Entry(inner)
        self.tool_url_decode_hotkey_entry.pack(fill=tk.X, pady=(4, 8))
        self.tool_url_decode_hotkey_entry.insert(0, self.settings.get("tool_url_decode_hotkey", "CTRL+ALT+I"))

        self.global_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.global_hotkey_entry, "global"),
        )
        self.focus_key_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.focus_key_entry, "focus"),
        )
        self.tab_key_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tab_key_entry, "tab"),
        )
        self.tool_json_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tool_json_hotkey_entry, "combo"),
        )
        self.tool_b64_encode_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tool_b64_encode_hotkey_entry, "combo"),
        )
        self.tool_b64_decode_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tool_b64_decode_hotkey_entry, "combo"),
        )
        self.tool_url_encode_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tool_url_encode_hotkey_entry, "combo"),
        )
        self.tool_url_decode_hotkey_entry.bind(
            "<FocusIn>",
            lambda _e: self._record_hotkey_into_entry(self.tool_url_decode_hotkey_entry, "combo"),
        )

        for entry in (
            self.global_hotkey_entry,
            self.focus_key_entry,
            self.tab_key_entry,
            self.tool_json_hotkey_entry,
            self.tool_b64_encode_hotkey_entry,
            self.tool_b64_decode_hotkey_entry,
            self.tool_url_encode_hotkey_entry,
            self.tool_url_decode_hotkey_entry,
        ):
            entry.bind("<Return>", lambda _e: self._save_shortcut_settings_from_entries())
            entry.bind("<FocusOut>", lambda _e: self._save_shortcut_settings_from_entries())

        ttk.Label(inner, text="窗口透明度（实时生效）", style="Status.TLabel").pack(anchor=tk.W, pady=(12, 4))
        alpha_row = ttk.Frame(inner, style="Main.TFrame")
        alpha_row.pack(fill=tk.X, pady=(0, 4))
        self.alpha_var = tk.DoubleVar(value=self._clamp_window_alpha(self.settings.get("window_alpha", 0.88)))
        ttk.Label(alpha_row, text="较透", style="Status.TLabel").pack(side=tk.LEFT, padx=(0, 6))
        self.alpha_scale = ttk.Scale(
            alpha_row,
            from_=0.35,
            to=1.0,
            variable=self.alpha_var,
            orient=tk.HORIZONTAL,
            command=lambda _v: self._on_alpha_slider_change(self.alpha_var.get()),
        )
        self.alpha_scale.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        ttk.Label(alpha_row, text="较实", style="Status.TLabel").pack(side=tk.LEFT)
        self.alpha_value_label = ttk.Label(inner, text=self._format_alpha_label(self.alpha_var.get()), style="Status.TLabel")
        self.alpha_value_label.pack(anchor=tk.W, pady=(0, 4))

        th = APP_THEME
        ttk.Label(
            inner,
            text="周报 AI 提示词模板（可编辑；使用占位符 {tasks_block} 插入当周任务正文；留空则恢复内置默认）",
            style="Status.TLabel",
        ).pack(anchor=tk.W, pady=(14, 4))
        self.weekly_prompt_template_text = tk.Text(
            inner,
            height=12,
            bg=th["bg_elevated"],
            fg=th["fg"],
            insertbackground=th["fg"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=th["border"],
            highlightcolor=th["border_focus"],
            bd=0,
            font=UI_FONT_SM,
            padx=8,
            pady=8,
            wrap="word",
        )
        self.weekly_prompt_template_text.pack(fill=tk.BOTH, expand=True, pady=(0, 6))
        self.weekly_prompt_template_text.insert("1.0", self._get_weekly_prompt_template())
        self.weekly_prompt_template_text.bind("<KeyRelease>", self._schedule_weekly_prompt_template_save)
        self.weekly_prompt_template_text.bind("<FocusOut>", lambda _e: self._flush_weekly_prompt_template_save())
        tpl_btn_row = ttk.Frame(inner, style="Main.TFrame")
        tpl_btn_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Button(
            tpl_btn_row,
            text="立即保存模板",
            command=self._flush_weekly_prompt_template_save,
            style="Secondary.TButton",
        ).pack(side=tk.LEFT)
        ttk.Button(
            tpl_btn_row,
            text="恢复默认模板",
            command=self._reset_weekly_prompt_template,
            style="Secondary.TButton",
        ).pack(side=tk.LEFT, padx=(8, 0))

    def _get_weekly_prompt_template(self) -> str:
        t = self.settings.get("weekly_prompt_template")
        if isinstance(t, str) and t.strip():
            return t.strip()
        return WEEKLY_AI_PROMPT_TEMPLATE

    def _schedule_weekly_prompt_template_save(self, _event=None) -> None:
        if self._prompt_save_after_id is not None:
            self.root.after_cancel(self._prompt_save_after_id)
        self._prompt_save_after_id = self.root.after(600, self._flush_weekly_prompt_template_save)

    def _flush_weekly_prompt_template_save(self) -> None:
        if self._prompt_save_after_id is not None:
            try:
                self.root.after_cancel(self._prompt_save_after_id)
            except tk.TclError:
                pass
            self._prompt_save_after_id = None
        if not hasattr(self, "weekly_prompt_template_text"):
            return
        raw = self.weekly_prompt_template_text.get("1.0", tk.END).strip()
        prev = self.settings.get("weekly_prompt_template")
        prev_norm = prev.strip() if isinstance(prev, str) else None
        if not raw:
            if prev_norm is None:
                self._sync_log_weekly_preview_after_template_change()
                return
            self.settings.pop("weekly_prompt_template", None)
        else:
            if prev_norm == raw:
                self._sync_log_weekly_preview_after_template_change()
                return
            self.settings["weekly_prompt_template"] = raw
        self._write_settings_file()
        if "{tasks_block}" not in self._get_weekly_prompt_template():
            self._record_status("模板已保存（建议保留 {tasks_block} 占位符）")
        else:
            self._record_status("周报提示词模板已保存")
        self._sync_log_weekly_preview_after_template_change()

    def _reset_weekly_prompt_template(self) -> None:
        self.settings.pop("weekly_prompt_template", None)
        self._write_settings_file()
        if hasattr(self, "weekly_prompt_template_text"):
            self.weekly_prompt_template_text.delete("1.0", tk.END)
            self.weekly_prompt_template_text.insert("1.0", WEEKLY_AI_PROMPT_TEMPLATE)
        self._record_status("已恢复内置周报提示词模板")
        self._sync_log_weekly_preview_after_template_change()

    def _sync_log_weekly_preview_after_template_change(self) -> None:
        if getattr(self, "log_mode_var", None) and self.log_mode_var.get() == "周汇总" and self._weekly_tasks_plain.strip():
            try:
                body = self._get_weekly_prompt_template().format(tasks_block=self._weekly_tasks_plain.strip())
                self._update_weekly_prompt_preview(body)
            except (KeyError, ValueError):
                self._update_weekly_prompt_preview(
                    self._get_weekly_prompt_template().replace("{tasks_block}", self._weekly_tasks_plain.strip())
                )

    def _clamp_window_alpha(self, value) -> float:
        try:
            a = float(value)
        except (TypeError, ValueError):
            return 0.88
        return max(0.35, min(1.0, a))

    def _format_alpha_label(self, value: float) -> str:
        return f"当前：{int(round(float(value) * 100))}%"

    def _on_alpha_slider_change(self, value) -> None:
        try:
            a = self._clamp_window_alpha(float(value))
        except (TypeError, ValueError):
            return
        self.root.attributes("-alpha", a)
        self.settings["window_alpha"] = a
        if hasattr(self, "alpha_value_label"):
            self.alpha_value_label.configure(text=self._format_alpha_label(a))
        if self._alpha_save_after_id is not None:
            self.root.after_cancel(self._alpha_save_after_id)
        self._alpha_save_after_id = self.root.after(450, self._persist_settings_to_disk)

    def _write_settings_file(self) -> None:
        try:
            self.settings_file.write_text(json.dumps(self.settings, ensure_ascii=False, indent=2), encoding="utf-8")
        except OSError:
            pass

    def _persist_settings_to_disk(self) -> None:
        self._alpha_save_after_id = None
        self._write_settings_file()

    def _draft_format_json(self) -> None:
        selected = self._get_draft_selected_text()
        if selected is None:
            return
        formatted = format_json_text(selected)
        if formatted is None:
            return
        self._draft_apply_transformed_text(formatted, "草稿 JSON 已格式化")

    def _draft_base64_encode(self) -> None:
        selected = self._get_draft_selected_text()
        if selected is None:
            return
        encoded = base64_encode_text(selected)
        if encoded is None:
            return
        self._draft_apply_transformed_text(encoded, "草稿内容已 Base64 编码")

    def _draft_base64_decode(self) -> None:
        selected = self._get_draft_selected_text()
        if selected is None:
            return
        decoded = base64_decode_text(selected)
        if decoded is None:
            self._record_status("Base64 解码失败：请检查内容是否为 UTF-8 Base64")
            return
        self._draft_apply_transformed_text(decoded, "草稿内容已 Base64 解码")

    def _draft_url_encode(self) -> None:
        selected = self._get_draft_selected_text()
        if selected is None:
            return
        encoded = url_encode_text(selected)
        if encoded is None:
            return
        self._draft_apply_transformed_text(encoded, "草稿内容已 URL 编码")

    def _draft_url_decode(self) -> None:
        selected = self._get_draft_selected_text()
        if selected is None:
            return
        decoded = url_decode_text(selected)
        if decoded is None:
            self._record_status("URL 解码失败：请检查输入内容")
            return
        self._draft_apply_transformed_text(decoded, "草稿内容已 URL 解码")

    def _draft_apply_transformed_text(self, transformed: str, success_status: str) -> None:
        try:
            start = self.draft_text.index("sel.first")
            end = self.draft_text.index("sel.last")
        except tk.TclError:
            self._record_status("请先选中要处理的文本")
            return
        try:
            cur_ln = int(self.draft_text.index("insert").split(".")[0])
        except tk.TclError:
            cur_ln = 1
        self._draft_sync_line_at(cur_ln)
        self.draft_text.delete(start, end)
        self.draft_text.insert(start, transformed)
        new_insert = f"{start}+{len(transformed)}c"
        self.draft_text.mark_set("insert", new_insert)
        self.draft_text.see("insert")
        self._draft_set_source(self.draft_text.get("1.0", "end-1c"), coalesce=False)
        try:
            insert_line = int(self.draft_text.index("insert").split(".")[0])
        except tk.TclError:
            insert_line = 1
        self._draft_refresh_view(focus_line=insert_line, focus_col=0)
        self._save_draft_text()
        self._update_draft_stats()
        self._record_status(success_status)

    def _get_draft_selected_text(self) -> str | None:
        try:
            selected = self.draft_text.get("sel.first", "sel.last")
        except tk.TclError:
            self._record_status("未选中文本：工具不会执行")
            return None
        if not selected:
            self._record_status("未选中文本：工具不会执行")
            return None
        return selected

    def _toggle_draft_tools_popup(self) -> None:
        if self._draft_tools_popup is not None and self._draft_tools_popup.winfo_exists():
            self._hide_draft_tools_popup()
            return
        self._show_draft_tools_popup()

    def _show_draft_tools_popup(self) -> None:
        popup = ttk.Frame(self.root, style="Main.TFrame", padding=4)
        popup.configure(borderwidth=1, relief="solid")
        self._draft_tools_popup = popup
        inner = ttk.Frame(popup, style="Main.TFrame")
        inner.pack(fill=tk.BOTH, expand=True)

        ttk.Button(inner, text="JSON 格式化", style="Secondary.TButton", command=lambda: self._run_tool_and_close(self._draft_format_json)).pack(fill=tk.X, pady=1)
        ttk.Button(inner, text="Base64 编码", style="Secondary.TButton", command=lambda: self._run_tool_and_close(self._draft_base64_encode)).pack(fill=tk.X, pady=1)
        ttk.Button(inner, text="Base64 解码", style="Secondary.TButton", command=lambda: self._run_tool_and_close(self._draft_base64_decode)).pack(fill=tk.X, pady=1)
        ttk.Button(inner, text="URL 编码", style="Secondary.TButton", command=lambda: self._run_tool_and_close(self._draft_url_encode)).pack(fill=tk.X, pady=1)
        ttk.Button(inner, text="URL 解码", style="Secondary.TButton", command=lambda: self._run_tool_and_close(self._draft_url_decode)).pack(fill=tk.X, pady=1)

        popup.update_idletasks()
        bx = self._draft_tools_menu_button.winfo_rootx() - self.root.winfo_rootx()
        by = self._draft_tools_menu_button.winfo_rooty() - self.root.winfo_rooty() + self._draft_tools_menu_button.winfo_height() + 2
        popup.place(x=bx, y=by)
        popup.lift()

    def _run_tool_and_close(self, callback) -> None:
        self._hide_draft_tools_popup()
        callback()

    def _hide_draft_tools_popup(self) -> None:
        if self._draft_tools_popup is None:
            return
        try:
            if self._draft_tools_popup.winfo_exists():
                self._draft_tools_popup.destroy()
        except tk.TclError:
            pass
        self._draft_tools_popup = None

    def _on_root_click_maybe_hide_draft_tools(self, event=None) -> None:
        if self._draft_tools_popup is None or not self._draft_tools_popup.winfo_exists():
            self._on_root_click_maybe_hide_log_dropdown(event)
            return
        widget = event.widget if event is not None else None
        if widget is None:
            self._hide_draft_tools_popup()
            self._on_root_click_maybe_hide_log_dropdown(event)
            return
        if widget == self._draft_tools_menu_button or self._widget_is_descendant_of(widget, self._draft_tools_menu_button):
            self._on_root_click_maybe_hide_log_dropdown(event)
            return
        if self._widget_is_descendant_of(widget, self._draft_tools_popup):
            self._on_root_click_maybe_hide_log_dropdown(event)
            return
        self._hide_draft_tools_popup()
        self._on_root_click_maybe_hide_log_dropdown(event)

    def _on_root_click_maybe_hide_log_dropdown(self, event=None) -> None:
        if self._active_log_dropdown_popup is None or not self._active_log_dropdown_popup.winfo_exists():
            return
        widget = event.widget if event is not None else None
        if widget is None:
            self._hide_log_dropdown()
            return
        if widget in (self.log_mode_dropdown_btn, self.log_day_dropdown_btn, self.log_week_dropdown_btn):
            return
        if self._widget_is_descendant_of(widget, self._active_log_dropdown_popup):
            return
        self._hide_log_dropdown()

    def _widget_is_descendant_of(self, widget, ancestor) -> bool:
        cur = widget
        while cur is not None:
            if cur == ancestor:
                return True
            try:
                parent_name = cur.winfo_parent()
            except tk.TclError:
                return False
            if not parent_name:
                return False
            try:
                cur = cur.nametowidget(parent_name)
            except Exception:
                return False
        return False

    def _apply_draft_view_mode_from_toolbar(self) -> None:
        """工具栏「Markdown / 源码」切换，对应 Typora 的视图切换。"""
        if getattr(self, "_draft_search_visible", False):
            return
        mode = self._draft_view_mode_var.get()
        if mode == "source":
            try:
                ln = int(self.draft_text.index("insert").split(".")[0])
                self._draft_sync_line_at(ln)
            except tk.TclError:
                pass
            self._draft_force_raw = True
            self._draft_refresh_view()
        else:
            if self._draft_force_raw:
                self._draft_set_source(self.draft_text.get("1.0", "end-1c"))
            self._draft_force_raw = False
            self._draft_refresh_view()
        self._update_draft_stats()

    def _configure_draft_markdown_tags(self, w: tk.Text) -> None:
        # 标题分级字号；段前段后为 0，减轻与正文编辑行切换时的跳动（仍会比正文略高一行）
        w.tag_configure(
            "md_h1",
            font=("Microsoft YaHei UI", 16, "bold"),
            foreground=APP_THEME["fg"],
            spacing1=0,
            spacing3=0,
        )
        w.tag_configure(
            "md_h2",
            font=("Microsoft YaHei UI", 14, "bold"),
            foreground=APP_THEME["fg"],
            spacing1=0,
            spacing3=0,
        )
        w.tag_configure(
            "md_h3",
            font=("Microsoft YaHei UI", 12, "bold"),
            foreground=APP_THEME["fg_muted"],
            spacing1=0,
            spacing3=0,
        )
        w.tag_configure("md_quote", foreground=APP_THEME["fg_muted"], lmargin1=12, lmargin2=12)
        w.tag_configure("md_list", lmargin1=10, lmargin2=22)
        w.tag_configure("md_code_inline", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_code_block", background=APP_THEME["bg_elevated"], font=MONO_FONT, lmargin1=0, lmargin2=0)
        w.tag_configure("md_code_fence", foreground=APP_THEME["fg_muted"], font=MONO_FONT)
        w.tag_configure("md_code_lineno", foreground=APP_THEME["fg_muted"], font=MONO_FONT, lmargin1=0, lmargin2=0)
        w.tag_configure("md_code_kw", foreground="#82b0ff", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_code_str", foreground="#9adf9f", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_code_comment", foreground="#7f8ba3", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_code_box", background="#232936", lmargin1=0, lmargin2=0, spacing1=2, spacing3=2)
        w.tag_configure("md_math_cmd", foreground="#82b0ff", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_math_num", foreground="#ffd580", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_math_op", foreground="#ff9aa2", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_math_brace", foreground="#caa6ff", background=APP_THEME["bg_elevated"], font=MONO_FONT)
        w.tag_configure("md_math_block", background=APP_THEME["bg_elevated"], foreground=APP_THEME["accent"], font=MONO_FONT, lmargin1=10, lmargin2=10)
        w.tag_configure("md_bold", font=("Microsoft YaHei UI", 10, "bold"))
        w.tag_configure("md_italic", font=("Microsoft YaHei UI", 10, "italic"))
        w.tag_configure("md_strike", overstrike=1)
        w.tag_configure("md_link", foreground=APP_THEME["accent"], underline=1)
        w.tag_configure("md_hr", foreground=APP_THEME["fg_muted"])

    def _insert_markdown_inline(self, widget: tk.Text, text: str, base_tags: tuple[str, ...] = ()) -> None:
        token_re = re.compile(r"(`[^`]+`|\$\$[^$]+\$\$|\$[^$\n]+\$|\*\*[^*]+\*\*|\*[^*]+\*|~~[^~]+~~|\[[^\]]+\]\([^)]+\))")
        pos = 0
        for m in token_re.finditer(text):
            if m.start() > pos:
                widget.insert(tk.END, text[pos:m.start()], base_tags)
            token = m.group(0)
            tags = list(base_tags)
            out = token
            if token.startswith("`") and token.endswith("`"):
                out = token[1:-1]
                tags.append("md_code_inline")
            elif token.startswith("$$") and token.endswith("$$"):
                out = self._render_latex_to_text(token[2:-2])
                tags.append("md_math_block")
            elif token.startswith("$") and token.endswith("$"):
                out = self._render_latex_to_text(token[1:-1])
                tags.append("md_math_block")
            elif token.startswith("**") and token.endswith("**"):
                out = token[2:-2]
                tags.append("md_bold")
            elif token.startswith("*") and token.endswith("*"):
                out = token[1:-1]
                tags.append("md_italic")
            elif token.startswith("~~") and token.endswith("~~"):
                out = token[2:-2]
                tags.append("md_strike")
            elif token.startswith("[") and "](" in token and token.endswith(")"):
                m2 = re.match(r"\[([^\]]+)\]\(([^)]+)\)", token)
                if m2:
                    out = f"{m2.group(1)} ({m2.group(2)})"
                    tags.append("md_link")
            widget.insert(tk.END, out, tuple(tags))
            pos = m.end()
        if pos < len(text):
            widget.insert(tk.END, text[pos:], base_tags)

    def _render_latex_to_text(self, expr: str) -> str:
        s = expr.strip()
        s = s.replace(r"\\", "\n")
        s = s.replace("&", "  ")

        # 常见环境 -> 文本布局
        env_patterns = [
            r"\\begin\{(?:matrix|pmatrix|bmatrix|Bmatrix|vmatrix|Vmatrix|array)\}",
            r"\\end\{(?:matrix|pmatrix|bmatrix|Bmatrix|vmatrix|Vmatrix|array)\}",
            r"\\begin\{(?:align|aligned|cases|gather)\}",
            r"\\end\{(?:align|aligned|cases|gather)\}",
        ]
        for p in env_patterns:
            s = re.sub(p, "", s)

        # \text{...}
        s = re.sub(r"\\text\{([^{}]*)\}", r"\1", s)
        s = re.sub(r"\\mathrm\{([^{}]*)\}", r"\1", s)

        # 分数/根号（多轮以支持简单嵌套）
        frac_re = re.compile(r"\\(?:d?frac|tfrac)\{([^{}]+)\}\{([^{}]+)\}")
        sqrt_re = re.compile(r"\\sqrt(?:\[[^\]]+\])?\{([^{}]+)\}")
        for _ in range(4):
            changed = False
            m = frac_re.search(s)
            if m:
                s = s[: m.start()] + f"({m.group(1)})/({m.group(2)})" + s[m.end() :]
                changed = True
            m = sqrt_re.search(s)
            if m:
                s = s[: m.start()] + f"√({m.group(1)})" + s[m.end() :]
                changed = True
            if not changed:
                break

        # 大型运算符带上下限
        s = re.sub(r"\\sum_\{([^{}]+)\}\^\{([^{}]+)\}", r"∑(\1→\2)", s)
        s = re.sub(r"\\prod_\{([^{}]+)\}\^\{([^{}]+)\}", r"∏(\1→\2)", s)
        s = re.sub(r"\\int_\{([^{}]+)\}\^\{([^{}]+)\}", r"∫[\1,\2]", s)
        s = re.sub(r"\\lim_\{([^{}]+)\}", r"lim(\1)", s)

        cmd_map = {
            # Greek
            r"\alpha": "α", r"\beta": "β", r"\gamma": "γ", r"\delta": "δ", r"\epsilon": "ε", r"\varepsilon": "ε",
            r"\zeta": "ζ", r"\eta": "η", r"\theta": "θ", r"\vartheta": "ϑ", r"\iota": "ι", r"\kappa": "κ",
            r"\lambda": "λ", r"\mu": "μ", r"\nu": "ν", r"\xi": "ξ", r"\pi": "π", r"\varpi": "ϖ",
            r"\rho": "ρ", r"\varrho": "ϱ", r"\sigma": "σ", r"\varsigma": "ς", r"\tau": "τ", r"\upsilon": "υ",
            r"\phi": "φ", r"\varphi": "ϕ", r"\chi": "χ", r"\psi": "ψ", r"\omega": "ω",
            r"\Gamma": "Γ", r"\Delta": "Δ", r"\Theta": "Θ", r"\Lambda": "Λ", r"\Xi": "Ξ", r"\Pi": "Π",
            r"\Sigma": "Σ", r"\Upsilon": "Υ", r"\Phi": "Φ", r"\Psi": "Ψ", r"\Omega": "Ω",
            # Ops/relations
            r"\times": "×", r"\cdot": "·", r"\div": "÷", r"\pm": "±", r"\mp": "∓",
            r"\leq": "≤", r"\geq": "≥", r"\neq": "≠", r"\approx": "≈", r"\equiv": "≡",
            r"\to": "→", r"\rightarrow": "→", r"\leftarrow": "←", r"\leftrightarrow": "↔",
            r"\Rightarrow": "⇒", r"\Leftarrow": "⇐", r"\Leftrightarrow": "⇔",
            r"\infty": "∞", r"\partial": "∂", r"\nabla": "∇", r"\forall": "∀", r"\exists": "∃",
            r"\in": "∈", r"\notin": "∉", r"\subset": "⊂", r"\subseteq": "⊆", r"\supset": "⊃", r"\supseteq": "⊇",
            r"\cup": "∪", r"\cap": "∩", r"\emptyset": "∅",
            r"\land": "∧", r"\lor": "∨", r"\neg": "¬",
            r"\sin": "sin", r"\cos": "cos", r"\tan": "tan", r"\cot": "cot", r"\sec": "sec", r"\csc": "csc",
            r"\ln": "ln", r"\log": "log", r"\exp": "exp",
            r"\sum": "∑", r"\prod": "∏", r"\int": "∫", r"\oint": "∮",
            r"\cdots": "⋯", r"\ldots": "…", r"\vdots": "⋮", r"\ddots": "⋱",
            r"\quad": "  ", r"\qquad": "    ", r"\,": " ", r"\;": " ", r"\:": " ",
        }
        for k, v in cmd_map.items():
            s = s.replace(k, v)

        # 上下标
        s = re.sub(r"\^\{([^{}]+)\}", r"^(\1)", s)
        s = re.sub(r"_\{([^{}]+)\}", r"_(\1)", s)
        s = re.sub(r"\^([A-Za-z0-9+\-])", r"^\1", s)
        s = re.sub(r"_([A-Za-z0-9+\-])", r"_\1", s)

        # 清理包裹命令和分隔符
        s = s.replace(r"\left", "").replace(r"\right", "")
        s = s.replace(r"\!", "").replace(r"\,", " ")
        s = s.replace("{", "(").replace("}", ")")
        s = re.sub(r"\\[A-Za-z]+", "", s)  # 移除残留未识别命令
        s = re.sub(r"[ \t]+", " ", s)
        s = re.sub(r"\n{3,}", "\n\n", s)
        return s.strip()

    def _draft_append_rendered_markdown_line(self, w: tk.Text, line: str) -> None:
        h = re.match(r"^(#{1,6})\s+(.*)$", line)
        if h:
            level = min(len(h.group(1)), 3)
            self._insert_markdown_inline(w, h.group(2), (f"md_h{level}",))
            return
        if re.match(r"^\s*([-*_])\1{2,}\s*$", line):
            w.insert(tk.END, "─" * 18, ("md_hr",))
            return
        quote = re.match(r"^\s*>\s?(.*)$", line)
        if quote:
            w.insert(tk.END, "│ ", ("md_quote",))
            self._insert_markdown_inline(w, quote.group(1), ("md_quote",))
            return
        ul = re.match(r"^\s*[-*+]\s+(.*)$", line)
        if ul:
            w.insert(tk.END, "• ", ("md_list",))
            self._insert_markdown_inline(w, ul.group(1), ("md_list",))
            return
        ol = re.match(r"^\s*(\d+)\.\s+(.*)$", line)
        if ol:
            w.insert(tk.END, f"{ol.group(1)}. ", ("md_list",))
            self._insert_markdown_inline(w, ol.group(2), ("md_list",))
            return
        self._insert_markdown_inline(w, line)

    def _draft_insert_code_line_with_highlight(self, line: str, line_no: int, digits_max: int) -> None:
        # 代码块行号占位宽度固定：digits_max（数字位） + 1（末尾空格），避免多位数时“看起来缩进不齐”
        prefix = f"{line_no:>{digits_max}} "
        self.draft_text.insert("end", prefix, ("md_code_box", "md_code_lineno"))
        text = line if line else " "
        # 注释
        cmt_idx = None
        for token in ("#", "//"):
            i = text.find(token)
            if i != -1 and (cmt_idx is None or i < cmt_idx):
                cmt_idx = i
        code_part = text if cmt_idx is None else text[:cmt_idx]
        cmt_part = "" if cmt_idx is None else text[cmt_idx:]

        token_re = re.compile(r"(\"[^\"]*\"|'[^']*'|\b(?:def|class|return|if|elif|else|for|while|try|except|import|from|as|with|async|await|function|const|let|var|public|private|protected|static|new)\b)")
        pos = 0
        for m in token_re.finditer(code_part):
            if m.start() > pos:
                self.draft_text.insert("end", code_part[pos : m.start()], ("md_code_box", "md_code_block"))
            token = m.group(0)
            if (token.startswith('"') and token.endswith('"')) or (token.startswith("'") and token.endswith("'")):
                self.draft_text.insert("end", token, ("md_code_box", "md_code_str"))
            else:
                self.draft_text.insert("end", token, ("md_code_box", "md_code_kw"))
            pos = m.end()
        if pos < len(code_part):
            self.draft_text.insert("end", code_part[pos:], ("md_code_box", "md_code_block"))
        if cmt_part:
            self.draft_text.insert("end", cmt_part, ("md_code_box", "md_code_comment"))
        self.draft_text.insert("end", "\n", ("md_code_box", "md_code_block"))

    def _draft_insert_math_line_with_highlight(self, line: str) -> None:
        text = line if line else " "
        token_re = re.compile(r"(\\[A-Za-z]+|\\.|[0-9]+(?:\.[0-9]+)?|[\+\-\*/=\^_]|[\(\)\[\]\{\}]|.)")
        for m in token_re.finditer(text):
            token = m.group(0)
            if token.startswith("\\"):
                tags = ("md_math_block", "md_math_cmd")
            elif re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", token):
                tags = ("md_math_block", "md_math_num")
            elif token in "+-*/=^_":
                tags = ("md_math_block", "md_math_op")
            elif token in "()[]{}":
                tags = ("md_math_block", "md_math_brace")
            else:
                tags = ("md_math_block",)
            self.draft_text.insert("end", token, tags)
        self.draft_text.insert("end", "\n", ("md_math_block",))

    def _draft_get_code_block_bounds(self, lines: list[str], focus_line_1based: int) -> tuple[int, int] | None:
        for start, end in self._draft_collect_closed_code_ranges(lines):
            if start <= focus_line_1based <= end:
                return start, end
        return None

    def _draft_collect_closed_code_ranges(self, lines: list[str]) -> list[tuple[int, int]]:
        ranges: list[tuple[int, int]] = []
        start: int | None = None
        for i, line in enumerate(lines, start=1):
            if not line.strip().startswith("```"):
                continue
            if start is None:
                start = i
            else:
                ranges.append((start, i))
                start = None
        return ranges

    def _draft_collect_closed_math_ranges(self, lines: list[str]) -> list[tuple[int, int]]:
        ranges: list[tuple[int, int]] = []
        start: int | None = None
        for i, line in enumerate(lines, start=1):
            if line.strip() != "$$":
                continue
            if start is None:
                start = i
            else:
                ranges.append((start, i))
                start = None
        return ranges

    def _draft_is_inside_code_block_before_line(self, lines: list[str], line_1based: int) -> bool:
        in_code = False
        for i, line in enumerate(lines, start=1):
            if i >= line_1based:
                break
            if line.strip().startswith("```"):
                in_code = not in_code
        return in_code

    def _draft_is_inside_math_block_before_line(self, lines: list[str], line_1based: int) -> bool:
        in_math = False
        for i, line in enumerate(lines, start=1):
            if i >= line_1based:
                break
            if line.strip() == "$$":
                in_math = not in_math
        return in_math

    def _draft_find_closed_code_block_range_by_line(self, parts: list[str], line_1based: int) -> tuple[int, int] | None:
        for s, e in self._draft_collect_closed_code_ranges(parts):
            # 只对代码块内部内容行（不含起止围栏）做补全
            if s < line_1based < e:
                return s, e
        return None

    def _draft_set_insert_in_codeblock_by_source_offset(self, src_offset: int) -> None:
        try:
            src_ln, src_col = self._draft_source_line_col_from_offset(src_offset)
        except Exception:
            return
        parts = self._draft_source.split("\n")
        rng = self._draft_find_closed_code_block_range_by_line(parts, src_ln)
        if rng is None:
            try:
                self.draft_text.mark_set("insert", f"{src_ln}.{max(0, src_col)}")
                self.draft_text.see("insert")
            except tk.TclError:
                pass
            return
        s, e = rng
        # 固定行号占位宽度：digits_max（内容最大行号位数）+ 1（末尾空格）
        content_count = max(1, e - s - 1)
        digits_max = len(str(content_count))
        prefix_len = digits_max + 1
        view_col = prefix_len + max(0, src_col)
        try:
            self.draft_text.mark_set("insert", f"{src_ln}.{view_col}")
            self.draft_text.see("insert")
        except tk.TclError:
            pass

    def _draft_sync_line_at(self, line_1based: int) -> None:
        if self._draft_refreshing:
            return
        if self._draft_force_raw:
            self._draft_set_source(self.draft_text.get("1.0", "end-1c"), coalesce=False)
            return
        # 混合渲染模式下仅允许从“当前源码行”回写，避免把渲染文本覆盖进 Markdown 源码
        if line_1based != getattr(self, "_draft_active_raw_line", None):
            return
        if line_1based < 1:
            return
        parts = self._draft_source.split("\n")
        if line_1based > len(parts):
            parts.extend([""] * (line_1based - len(parts)))
        try:
            raw = self.draft_text.get(f"{line_1based}.0", f"{line_1based}.end")
        except tk.TclError:
            return
        # 代码块渲染会在每行前面加“行号前缀”，回写源码前必须剥离，否则光标移动会把行号写入源码
        try:
            code_rng = self._draft_find_closed_code_block_range_by_line(parts, line_1based)
        except Exception:
            code_rng = None
        if code_rng is not None:
            # 固定剥离渲染层行号前缀宽度（digits_max + 1 空格），
            # 避免用户删掉部分数字时正则失效导致缩进/行号污染源码。
            s, e = code_rng
            content_count = max(1, e - s - 1)
            digits_max = len(str(content_count))
            prefix_len = digits_max + 1
            if len(raw) >= prefix_len:
                raw = raw[prefix_len:]
            else:
                raw = ""
        parts[line_1based - 1] = raw
        self._draft_set_source("\n".join(parts))

    def _draft_set_source(self, new_source: str, *, record_history: bool = True, coalesce: bool = True) -> bool:
        if new_source == self._draft_source:
            return False
        self._draft_source = new_source
        if record_history and not self._draft_history_restoring:
            if self._draft_history_idx < len(self._draft_history) - 1:
                self._draft_history = self._draft_history[: self._draft_history_idx + 1]
            now = time.monotonic()
            can_coalesce = (
                coalesce
                and len(self._draft_history) >= 2
                and self._draft_history_idx == len(self._draft_history) - 1
                and (now - self._draft_history_last_change_ts) <= self._draft_history_coalesce_window_s
            )
            if can_coalesce:
                self._draft_history[self._draft_history_idx] = new_source
            else:
                self._draft_history.append(new_source)
                self._draft_history_idx = len(self._draft_history) - 1
            self._draft_history_last_change_ts = now
        return True

    def _draft_apply_source_line_break(self, line_1based: int, col: int, *, coalesce: bool = True) -> None:
        """在内存 Markdown 源码上按列切分为两行；与 Tk 是否插入 \\n 无关，避免行号对齐启发式错位。"""
        parts = self._draft_source.split("\n")
        i = line_1based - 1
        if i < 0:
            return
        while len(parts) <= i:
            parts.append("")
        s = parts[i]
        c = max(0, min(int(col), len(s)))
        left, right = s[:c], s[c:]
        parts[i : i + 1] = [left, right]
        self._draft_set_source("\n".join(parts), coalesce=coalesce)

    def _draft_ensure_source_line_count_from_widget(self) -> None:
        """Text 逻辑行数多于 _draft_source 时补齐（例如粘贴多行）。回车换行改由 KeyPress 内直接改源码，不经此处。"""
        if self._draft_force_raw:
            return
        try:
            w_lines = int(self.draft_text.index("end-1c").split(".")[0])
        except tk.TclError:
            return
        parts = self._draft_source.split("\n")
        delta = w_lines - len(parts)
        if delta <= 0:
            return
        parts.extend([""] * delta)
        self._draft_set_source("\n".join(parts))

    def _draft_source_offset_from_line_col(self, line_1based: int, col: int) -> int:
        parts = self._draft_source.split("\n")
        if not parts:
            return 0
        ln = max(1, min(int(line_1based), len(parts)))
        offset = 0
        for i in range(ln - 1):
            offset += len(parts[i]) + 1
        c = max(0, min(int(col), len(parts[ln - 1])))
        return offset + c

    def _draft_source_line_col_from_offset(self, offset: int) -> tuple[int, int]:
        parts = self._draft_source.split("\n")
        if not parts:
            return 1, 0
        rem = max(0, min(int(offset), len(self._draft_source)))
        for i, line in enumerate(parts):
            if rem <= len(line):
                return i + 1, rem
            rem -= len(line)
            if i < len(parts) - 1:
                if rem == 0:
                    return i + 2, 0
                rem -= 1
        return len(parts), len(parts[-1])

    def _draft_line_view_to_source_col(self, line_1based: int, view_col: int) -> int:
        parts = self._draft_source.split("\n")
        if not parts:
            return 0
        ln = max(1, min(int(line_1based), len(parts)))
        src = parts[ln - 1]

        # 闭合代码块内容行：视图列 = 行号前缀长度 + 源码列（避免 difflib 因前缀干扰导致偏移）
        try:
            code_rng = self._draft_find_closed_code_block_range_by_line(parts, ln)
        except Exception:
            code_rng = None
        if code_rng is not None:
            s, e = code_rng
            content_count = max(1, e - s - 1)
            digits_max = len(str(content_count))
            prefix_len = digits_max + 1
            if s < ln < e:
                return max(0, min(int(view_col) - prefix_len, len(src)))

        try:
            view = self.draft_text.get(f"{ln}.0", f"{ln}.end")
        except tk.TclError:
            return max(0, min(int(view_col), len(src)))
        if view == src:
            return max(0, min(int(view_col), len(src)))

        char_map = [0] * len(view)
        matcher = difflib.SequenceMatcher(a=view, b=src, autojunk=False)
        for tag, a1, a2, b1, b2 in matcher.get_opcodes():
            if tag == "equal":
                for i in range(a2 - a1):
                    char_map[a1 + i] = b1 + i
            elif tag in ("replace", "insert"):
                span = max(1, b2 - b1)
                for i in range(a2 - a1):
                    char_map[a1 + i] = b1 + min(i, span - 1)
        if not char_map:
            return 0

        boundaries = [0] * (len(view) + 1)
        boundaries[0] = char_map[0]
        for i in range(1, len(view)):
            boundaries[i] = char_map[i]
        boundaries[len(view)] = min(len(src), char_map[-1] + 1)
        for i in range(1, len(boundaries)):
            if boundaries[i] < boundaries[i - 1]:
                boundaries[i] = boundaries[i - 1]
        for i in range(len(boundaries)):
            boundaries[i] = max(0, min(boundaries[i], len(src)))

        vc = max(0, min(int(view_col), len(view)))
        return boundaries[vc]

    def _draft_view_index_to_source_offset(self, index: str) -> int:
        try:
            ln_s, col_s = index.split(".")
            ln = int(ln_s)
            col = int(col_s)
        except Exception:
            return 0
        src_col = self._draft_line_view_to_source_col(ln, col)
        return self._draft_source_offset_from_line_col(ln, src_col)

    def _draft_view_col_to_source_col_for_focus(self, line_1based: int, view_col: int) -> int:
        # 对闭合代码块内容行，视图列 = 行号前缀长度 + 源码列，可直接精确换算，
        # 避免 difflib 在“带行号前缀 + 高亮片段”场景下偏移。
        parts = self._draft_source.split("\n")
        if not self._draft_force_raw:
            rng = self._draft_find_closed_code_block_range_by_line(parts, line_1based)
            if rng is not None:
                s, _e = rng
                e = _e
                content_count = max(1, e - s - 1)
                digits_max = len(str(content_count))
                prefix_len = digits_max + 1
                src_line = parts[line_1based - 1] if 0 <= line_1based - 1 < len(parts) else ""
                src_col = view_col - prefix_len
                return max(0, min(int(src_col), len(src_line)))
        return self._draft_line_view_to_source_col(line_1based, view_col)

    def _draft_refresh_view(self, focus_line: int | None = None, focus_col: int | None = None) -> None:
        if not hasattr(self, "draft_text"):
            return
        self._draft_refreshing = True
        # 整页 delete/insert 若记入撤销栈，会占满栈、截断重做；程序化重绘不加入撤销/重做
        try:
            prev_undo = self.draft_text.cget("undo")
        except tk.TclError:
            prev_undo = True
        try:
            self.draft_text.configure(undo=False)
            lines = self._draft_source.split("\n")
            if not lines:
                lines = [""]

            if focus_line is not None:
                line_no = max(1, min(int(focus_line), len(lines)))
                lt = lines[line_no - 1]
                col = 0 if focus_col is None else max(0, min(int(focus_col), len(lt)))
            else:
                try:
                    idx = self.draft_text.index("insert")
                    line_no = int(idx.split(".")[0])
                    col = int(idx.split(".")[1])
                except tk.TclError:
                    line_no, col = 1, 0

                line_no = max(1, min(line_no, len(lines)))
                line_text = lines[line_no - 1]
                col = max(0, min(col, len(line_text)))

            self.draft_text.delete("1.0", "end")
            code_line_no = 0
            code_ranges = self._draft_collect_closed_code_ranges(lines)
            math_ranges = self._draft_collect_closed_math_ranges(lines)
            code_digits_max_by_line: dict[int, int] = {}
            code_range_by_line: dict[int, tuple[int, int]] = {}
            math_range_by_line: dict[int, tuple[int, int]] = {}
            for s, e in code_ranges:
                for ln in range(s, e + 1):
                    code_range_by_line[ln] = (s, e)
                # code content lines are (s+1) .. (e-1)
                content_count = max(0, e - s - 1)
                digits_max = len(str(max(1, content_count)))
                for ln in range(s + 1, e):
                    code_digits_max_by_line[ln] = digits_max
            for s, e in math_ranges:
                for ln in range(s, e + 1):
                    math_range_by_line[ln] = (s, e)
            for i, line in enumerate(lines):
                lineno = i + 1
                stripped = line.strip()
                is_fence = stripped.startswith("```")
                is_math_fence = stripped == "$$"
                code_bounds = code_range_by_line.get(lineno)
                math_bounds = math_range_by_line.get(lineno)
                in_code = code_bounds is not None
                in_math = math_bounds is not None
                show_raw = self._draft_force_raw or (lineno == line_no)
                # 代码块内容行：无论焦点在哪里，都走“带行号/高亮”的代码渲染，
                # 避免补全时依赖的视图列->源码列映射失效。
                if in_code and not self._draft_force_raw:
                    show_raw = False
                if in_math and not self._draft_force_raw:
                    show_raw = False

                if is_fence:
                    if in_code:
                        code_line_no = 0
                    if show_raw or not in_code:
                        self.draft_text.insert("end", line + "\n")
                    else:
                        self.draft_text.insert("end", line + "\n", ("md_code_fence",))
                    continue
                if is_math_fence:
                    if show_raw or not in_math:
                        self.draft_text.insert("end", line + "\n")
                    else:
                        self.draft_text.insert("end", line + "\n", ("md_code_fence",))
                    continue

                if show_raw:
                    self.draft_text.insert("end", line + "\n")
                    continue

                if in_code:
                    code_line_no += 1
                    digits_max = code_digits_max_by_line.get(lineno, 1)
                    self._draft_insert_code_line_with_highlight(line, code_line_no, digits_max)
                    continue
                if in_math:
                    rendered = self._render_latex_to_text(line if line else " ")
                    self._draft_insert_math_line_with_highlight(rendered)
                    continue

                self._draft_append_rendered_markdown_line(self.draft_text, line)
                self.draft_text.insert("end", "\n")

            view_col = col
            if not self._draft_force_raw:
                rng = self._draft_find_closed_code_block_range_by_line(lines, line_no)
                if rng is not None:
                    s, _e = rng
                    content_count = max(1, _e - s - 1)
                    digits_max = len(str(content_count))
                    prefix_len = digits_max + 1
                    view_col = prefix_len + col
            self.draft_text.mark_set("insert", f"{line_no}.{view_col}")
            self.draft_text.see("insert")
            self._draft_last_nav_line = line_no
            self._draft_active_raw_line = line_no
            try:
                # 渲染层重绘后清除 modified 标记；后续仅在真实输入后才允许回写源码层
                self.draft_text.edit_modified(False)
            except tk.TclError:
                pass
        finally:
            try:
                self.draft_text.configure(undo=prev_undo)
            except tk.TclError:
                pass
            self._draft_refreshing = False

    def _draft_on_editor_key_release(self, event=None) -> None:
        if self._draft_refreshing:
            return
        if self._draft_force_raw:
            self._draft_set_source(self.draft_text.get("1.0", "end-1c"), coalesce=False)
            try:
                self.draft_text.edit_modified(False)
            except tk.TclError:
                pass
            self._update_draft_stats()
            self._schedule_draft_save()
            return
        ks = event.keysym if event is not None else ""
        # Markdown 下 KeyPress-Return 已对源码拆行并重绘，勿再走 ensure/sync，否则会二次改写行结构（表现为吃掉相邻行）
        if (
            not self._draft_force_raw
            and ks in ("Return", "KP_Enter")
            and getattr(self, "_draft_markdown_return_handled", False)
        ):
            self._draft_markdown_return_handled = False
            try:
                cur = int(self.draft_text.index("insert").split(".")[0])
            except tk.TclError:
                return
            self._draft_last_nav_line = cur
            self._update_draft_stats()
            self._schedule_draft_save()
            self._draft_return_press_col = None
            return
        if (
            not self._draft_force_raw
            and ks in ("BackSpace", "Delete")
            and getattr(self, "_draft_markdown_delete_handled", False)
        ):
            self._draft_markdown_delete_handled = False
            try:
                cur = int(self.draft_text.index("insert").split(".")[0])
            except tk.TclError:
                return
            self._draft_last_nav_line = cur
            self._update_draft_stats()
            self._schedule_draft_save()
            return

        try:
            idx = self.draft_text.index("insert")
            cur = int(idx.split(".")[0])
            col = int(idx.split(".")[1])
        except tk.TclError:
            return

        # 只有真实文本修改才回写源码层；点击/选择/移动光标不写源码
        try:
            modified = bool(self.draft_text.edit_modified())
        except tk.TclError:
            modified = False

        if modified:
            self._draft_ensure_source_line_count_from_widget()
            active_line = self._draft_active_raw_line if self._draft_active_raw_line is not None else cur
            self._draft_sync_line_at(active_line)

        # 行切换只做渲染层切换，源码层不参与（除非上面 modified=True 且已写回 active 行）
        active_line = self._draft_active_raw_line if self._draft_active_raw_line is not None else cur
        if cur != active_line:
            src_col = self._draft_view_col_to_source_col_for_focus(cur, col)
            self._draft_refresh_view(focus_line=cur, focus_col=src_col)
        else:
            self._draft_last_nav_line = cur
            self._draft_active_raw_line = cur
            if modified:
                try:
                    self.draft_text.edit_modified(False)
                except tk.TclError:
                    pass
        self._update_draft_stats()
        self._schedule_draft_save()
        if ks in ("Return", "KP_Enter"):
            self._draft_return_press_col = None

    def _draft_on_editor_click(self, _event=None) -> None:
        # 鼠标选择场景延后处理，避免在 ButtonRelease 事件栈内重绘导致选区丢失
        self.root.after_idle(self._draft_after_pointer_release)

    def _draft_after_pointer_release(self) -> None:
        if self._draft_refreshing:
            return
        # 有选区时只更新统计，不触发 sync/refresh；否则会 delete/insert 清空选区
        try:
            has_sel = bool(self.draft_text.tag_ranges(tk.SEL))
        except tk.TclError:
            has_sel = False
        if has_sel:
            self._update_draft_stats()
            return
        self._draft_on_editor_key_release(None)

    def _draft_on_editor_drag_select(self, _event=None) -> None:
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                self._update_draft_stats()
        except tk.TclError:
            pass

    def _draft_on_editor_keypress(self, event=None) -> str | None:
        if self._draft_refreshing or self._draft_force_raw:
            return None
        if event is None:
            return None
        ch = getattr(event, "char", "") or ""
        keysym = (getattr(event, "keysym", "") or "").strip()

        # Tab：在代码块内插入 3 个空格
        if keysym == "Tab" or ch == "\t":
            try:
                if self.draft_text.tag_ranges(tk.SEL):
                    return None
            except tk.TclError:
                pass
            return self._draft_codeblock_insert_spaces(3)

        # 引号补全（代码块内）
        if ch in ("'", '"'):
            return self._draft_codeblock_quote_pair(ch)

        # 括号补全（代码块内）
        if ch != "(":
            return None

        try:
            src_offset = self._draft_view_index_to_source_offset(self.draft_text.index("insert"))
        except Exception:
            return None

        parts = self._draft_source.split("\n")
        src_ln, _src_col = self._draft_source_line_col_from_offset(src_offset)
        rng = self._draft_find_closed_code_block_range_by_line(parts, src_ln)
        if rng is None:
            return None

        try:
            if self.draft_text.tag_ranges(tk.SEL):
                sel_first = self.draft_text.index(tk.SEL_FIRST)
                sel_last = self.draft_text.index(tk.SEL_LAST)
                src_start = self._draft_view_index_to_source_offset(sel_first)
                src_end = self._draft_view_index_to_source_offset(sel_last)
                if src_end < src_start:
                    src_start, src_end = src_end, src_start
            else:
                src_start = src_offset
                src_end = src_offset
        except Exception:
            return None

        selected = self._draft_source[src_start:src_end]
        new_source = self._draft_source[:src_start] + "(" + selected + ")" + self._draft_source[src_end:]
        self._draft_set_source(new_source, coalesce=False)

        cursor_offset = src_start + 1 + len(selected)
        cursor_ln, cursor_col = self._draft_source_line_col_from_offset(cursor_offset)
        self._draft_refresh_view(focus_line=cursor_ln, focus_col=cursor_col)
        self._draft_set_insert_in_codeblock_by_source_offset(cursor_offset)
        self._update_draft_stats()
        self._schedule_draft_save()
        return "break"

    def _draft_codeblock_insert_spaces(self, n: int) -> str | None:
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                return None
        except tk.TclError:
            pass
        try:
            src_offset = self._draft_view_index_to_source_offset(self.draft_text.index("insert"))
        except Exception:
            return None
        parts = self._draft_source.split("\n")
        src_ln, _src_col = self._draft_source_line_col_from_offset(src_offset)
        rng = self._draft_find_closed_code_block_range_by_line(parts, src_ln)
        if rng is None:
            return None
        new_source = self._draft_source[:src_offset] + (" " * n) + self._draft_source[src_offset:]
        self._draft_set_source(new_source, coalesce=False)
        cursor_offset = src_offset + n
        cursor_ln, cursor_col = self._draft_source_line_col_from_offset(cursor_offset)
        self._draft_refresh_view(focus_line=cursor_ln, focus_col=cursor_col)
        self._draft_set_insert_in_codeblock_by_source_offset(cursor_offset)
        self._update_draft_stats()
        self._schedule_draft_save()
        return "break"

    def _draft_codeblock_quote_pair(self, quote_char: str) -> str | None:
        parts = self._draft_source.split("\n")
        try:
            src_offset = self._draft_view_index_to_source_offset(self.draft_text.index("insert"))
        except Exception:
            return None
        src_ln, _src_col = self._draft_source_line_col_from_offset(src_offset)
        rng = self._draft_find_closed_code_block_range_by_line(parts, src_ln)
        if rng is None:
            return None

        try:
            if self.draft_text.tag_ranges(tk.SEL):
                sel_first = self.draft_text.index(tk.SEL_FIRST)
                sel_last = self.draft_text.index(tk.SEL_LAST)
                src_start = self._draft_view_index_to_source_offset(sel_first)
                src_end = self._draft_view_index_to_source_offset(sel_last)
                if src_end < src_start:
                    src_start, src_end = src_end, src_start
            else:
                src_start = src_offset
                src_end = src_offset
        except Exception:
            return None

        selected = self._draft_source[src_start:src_end]
        new_source = self._draft_source[:src_start] + quote_char + selected + quote_char + self._draft_source[src_end:]
        self._draft_set_source(new_source, coalesce=False)

        cursor_offset = src_start + 1 + len(selected)
        cursor_ln, cursor_col = self._draft_source_line_col_from_offset(cursor_offset)
        self._draft_refresh_view(focus_line=cursor_ln, focus_col=cursor_col)
        self._draft_set_insert_in_codeblock_by_source_offset(cursor_offset)
        self._update_draft_stats()
        self._schedule_draft_save()
        return "break"

    def _draft_handle_paste(self, _event=None) -> str:
        try:
            clip_text = self.root.clipboard_get()
        except tk.TclError:
            return "break"
        if clip_text is None:
            return "break"
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                start_index = self.draft_text.index(tk.SEL_FIRST)
                end_index = self.draft_text.index(tk.SEL_LAST)
            else:
                start_index = self.draft_text.index("insert")
                end_index = start_index
        except tk.TclError:
            return "break"

        src_start = self._draft_view_index_to_source_offset(start_index)
        src_end = self._draft_view_index_to_source_offset(end_index)
        if src_end < src_start:
            src_start, src_end = src_end, src_start
        new_source = self._draft_source[:src_start] + clip_text + self._draft_source[src_end:]
        self._draft_set_source(new_source, coalesce=False)
        new_offset = src_start + len(clip_text)
        focus_ln, focus_col = self._draft_source_line_col_from_offset(new_offset)
        self._draft_refresh_view(focus_line=focus_ln, focus_col=focus_col)
        self._update_draft_stats()
        self._schedule_draft_save()
        return "break"

    def _draft_handle_return(self, _event=None) -> str | None:
        if self._draft_force_raw:
            self._draft_return_press_col = None
            return None
        self._draft_markdown_return_handled = False
        try:
            idx = self.draft_text.index("insert")
            sp = idx.split(".")
            col = int(sp[1])
            ln = int(sp[0])
        except tk.TclError:
            self._draft_return_press_col = None
            return None
        self._draft_return_press_col = col
        self._draft_sync_line_at(ln)
        lines = self._draft_source.split("\n")
        i = ln - 1
        if i < 0 or i >= len(lines):
            self._draft_return_press_col = None
            return None
        line = lines[i]

        code_fence_match = re.match(r"^\s*```(?:\s+[^\s`][^`]*)?\s*$", line)
        if code_fence_match:
            # 纯 ``` 且位于现有代码块内时，该行是“闭合围栏”，回车不做自动补全
            if line.strip() == "```" and self._draft_is_inside_code_block_before_line(lines, ln):
                return None
            lines.insert(i + 1, "")
            lines.insert(i + 2, "```")
            self._draft_set_source("\n".join(lines), coalesce=False)
            self._draft_refresh_view(focus_line=ln + 1, focus_col=0)
            self._draft_markdown_return_handled = True
            return "break"

        if re.match(r"^\s*\$\$\s*$", line):
            # 纯 $$ 且位于现有公式块内时，该行是“闭合围栏”，回车不做自动补全
            if line.strip() == "$$" and self._draft_is_inside_math_block_before_line(lines, ln):
                return None
            lines.insert(i + 1, "")
            lines.insert(i + 2, "$$")
            self._draft_set_source("\n".join(lines), coalesce=False)
            self._draft_refresh_view(focus_line=ln + 1, focus_col=0)
            self._draft_markdown_return_handled = True
            return "break"

        # 代码块内：缩进与通用补全
        try:
            src_offset = self._draft_view_index_to_source_offset(self.draft_text.index("insert"))
            src_ln, src_col = self._draft_source_line_col_from_offset(src_offset)
        except Exception:
            src_ln, src_col = ln, col

        code_range = self._draft_find_closed_code_block_range_by_line(lines, src_ln)
        if code_range:
            code_line = lines[src_ln - 1]
            indent_m = re.match(r"^(\s*)", code_line)
            base_indent = indent_m.group(1) if indent_m else ""
            indent_more = base_indent + ("\t" if "\t" in base_indent else "    ")
            left = code_line[:src_col]
            right = code_line[src_col:]

            # "{ + Enter" -> 下一行缩进 + 空行，然后补上对应 "}"（保留右侧内容）
            if left.rstrip().endswith("{"):
                new_parts = (
                    lines[: src_ln - 1]
                    + [left, indent_more, base_indent + "}" + right]
                    + lines[src_ln:]
                )
                self._draft_set_source("\n".join(new_parts), coalesce=False)
                # 光标放到缩进那一行
                cursor_offset = self._draft_source_offset_from_line_col(src_ln + 1, len(indent_more))
                self._draft_refresh_view(focus_line=src_ln + 1, focus_col=0)
                self._draft_set_insert_in_codeblock_by_source_offset(cursor_offset)
                self._update_draft_stats()
                self._schedule_draft_save()
                self._draft_markdown_return_handled = True
                return "break"

            # 常规：回车后自动补齐当前行缩进
            new_right = right.lstrip(" \t")
            new_parts = lines[: src_ln - 1] + [left, base_indent + new_right] + lines[src_ln:]
            self._draft_set_source("\n".join(new_parts), coalesce=False)
            cursor_offset = self._draft_source_offset_from_line_col(src_ln + 1, len(base_indent))
            self._draft_refresh_view(focus_line=src_ln + 1, focus_col=0)
            self._draft_set_insert_in_codeblock_by_source_offset(cursor_offset)
            self._update_draft_stats()
            self._schedule_draft_save()
            self._draft_markdown_return_handled = True
            return "break"

        m_ul = re.match(r"^(\s*)([-*+])\s+(.*)$", line)
        if m_ul:
            indent, marker, rest = m_ul.group(1), m_ul.group(2), m_ul.group(3)
            if rest.strip() == "":
                lines[i] = indent
                self._draft_set_source("\n".join(lines), coalesce=False)
                self._draft_refresh_view(focus_line=ln, focus_col=len(indent))
            else:
                lines.insert(i + 1, f"{indent}{marker} ")
                self._draft_set_source("\n".join(lines), coalesce=False)
                new_ln = ln + 1
                new_text = lines[new_ln - 1]
                self._draft_refresh_view(focus_line=new_ln, focus_col=len(new_text))
            self._draft_markdown_return_handled = True
            return "break"

        m_ol = re.match(r"^(\s*)(\d+)\.\s+(.*)$", line)
        if m_ol:
            indent, num_s, rest = m_ol.group(1), m_ol.group(2), m_ol.group(3)
            if rest.strip() == "":
                lines[i] = indent
                self._draft_set_source("\n".join(lines), coalesce=False)
                self._draft_refresh_view(focus_line=ln, focus_col=len(indent))
            else:
                n = int(num_s) + 1
                lines.insert(i + 1, f"{indent}{n}. ")
                self._draft_set_source("\n".join(lines), coalesce=False)
                new_ln = ln + 1
                new_text = lines[new_ln - 1]
                self._draft_refresh_view(focus_line=new_ln, focus_col=len(new_text))
            self._draft_markdown_return_handled = True
            return "break"

        self._draft_apply_source_line_break(ln, col, coalesce=False)
        self._draft_refresh_view(focus_line=ln + 1, focus_col=0)
        self._draft_markdown_return_handled = True
        return "break"

    def _draft_handle_backspace_delete(self, event=None) -> str | None:
        if self._draft_force_raw:
            return None
        self._draft_markdown_delete_handled = False
        ks = event.keysym if event is not None else ""
        if ks not in ("BackSpace", "Delete"):
            return None
        try:
            idx = self.draft_text.index("insert")
            ln_s, col_s = idx.split(".")
            ln = int(ln_s)
            col = int(col_s)
        except tk.TclError:
            return None
        # 选区删除：先把显示层选区还原到源码层偏移，再在 _draft_source 上做原子删除
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                sel_first = self.draft_text.index(tk.SEL_FIRST)
                sel_last = self.draft_text.index(tk.SEL_LAST)
                if self.draft_text.compare(sel_first, ">", sel_last):
                    sel_first, sel_last = sel_last, sel_first
                src_start = self._draft_view_index_to_source_offset(sel_first)
                src_end = self._draft_view_index_to_source_offset(sel_last)
                if src_start > src_end:
                    src_start, src_end = src_end, src_start
                if src_end > src_start:
                    self._draft_set_source(self._draft_source[:src_start] + self._draft_source[src_end:], coalesce=False)
                    focus_ln, focus_col = self._draft_source_line_col_from_offset(src_start)
                    self._draft_refresh_view(focus_line=focus_ln, focus_col=focus_col)
                    self._draft_markdown_delete_handled = True
                    return "break"
                return "break"
        except tk.TclError:
            pass

        # 代码块内容行：禁止直接删除行号前缀（数字/空格）
        # 若代码行前导缩进被删到空行（仅空白），再按一次 BackSpace 会删除整行
        try:
            parts_now = self._draft_source.split("\n")
            code_rng = self._draft_find_closed_code_block_range_by_line(parts_now, ln)
        except Exception:
            code_rng = None
        if code_rng is not None:
            s, e = code_rng
            content_count = max(1, e - s - 1)
            digits_max = len(str(content_count))
            prefix_len = digits_max + 1

            # 在“行号前缀区域”内操作：不允许，直接把光标挪回到代码内容起点
            if col < prefix_len:
                try:
                    self.draft_text.mark_set("insert", f"{ln}.{prefix_len}")
                    self.draft_text.see("insert")
                except tk.TclError:
                    pass
                return "break"

            if ks == "BackSpace":
                src_col = col - prefix_len
                i = ln - 1
                if i < 0 or i >= len(parts_now):
                    return None
                # 回退到代码内容起点且该行已经“只有空白” => 删除整行
                if src_col == 0 and ln > 1 and parts_now[i].strip() == "":
                    del parts_now[i]
                    self._draft_set_source("\n".join(parts_now), coalesce=False)
                    prev_ln = ln - 1
                    prev_text = parts_now[prev_ln - 1] if 0 <= prev_ln - 1 < len(parts_now) else ""
                    self._draft_refresh_view(focus_line=prev_ln, focus_col=len(prev_text))
                    self._draft_markdown_delete_handled = True
                    return "break"
            # 其它位置：交给默认 Tk 行编辑 + KeyRelease 同步源码
            return None

        self._draft_sync_line_at(ln)
        lines = self._draft_source.split("\n")
        i = ln - 1
        if i < 0 or i >= len(lines):
            return None

        if ks == "BackSpace" and col == 0 and ln > 1:
            prev_text = lines[i - 1]
            lines[i - 1] = prev_text + lines[i]
            del lines[i]
            self._draft_set_source("\n".join(lines), coalesce=False)
            self._draft_refresh_view(focus_line=ln - 1, focus_col=len(prev_text))
            self._draft_markdown_delete_handled = True
            return "break"

        if ks == "Delete" and col == len(lines[i]) and ln < len(lines):
            lines[i] = lines[i] + lines[i + 1]
            del lines[i + 1]
            self._draft_set_source("\n".join(lines), coalesce=False)
            self._draft_refresh_view(focus_line=ln, focus_col=col)
            self._draft_markdown_delete_handled = True
            return "break"
        return None

    def _setup_draft_editor_features(self, draft_frame: ttk.Frame) -> None:
        th = APP_THEME

        self._draft_search_frame = ttk.Frame(draft_frame, style="Main.TFrame")

        self._draft_find_var = tk.StringVar()
        self._draft_replace_var = tk.StringVar()
        self._draft_find_regex_var = tk.BooleanVar(value=False)

        row1 = ttk.Frame(self._draft_search_frame, style="Main.TFrame")
        row1.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(row1, text="查找", style="Status.TLabel").pack(side=tk.LEFT, padx=(0, 6))
        self._draft_find_entry = ttk.Entry(row1, textvariable=self._draft_find_var)
        self._draft_find_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Checkbutton(
            row1,
            text="正则",
            variable=self._draft_find_regex_var,
            style="App.TCheckbutton",
        ).pack(side=tk.LEFT, padx=(8, 0))
        ttk.Button(row1, text="上一个", style="Secondary.TButton", command=lambda: self._draft_find_next(backward=True)).pack(
            side=tk.LEFT, padx=(8, 0)
        )
        ttk.Button(row1, text="下一个", style="Secondary.TButton", command=lambda: self._draft_find_next(backward=False)).pack(
            side=tk.LEFT, padx=(6, 0)
        )
        ttk.Button(row1, text="关闭", style="Secondary.TButton", command=self._hide_draft_search).pack(
            side=tk.LEFT, padx=(6, 0)
        )

        row2 = ttk.Frame(self._draft_search_frame, style="Main.TFrame")
        row2.pack(fill=tk.X)
        ttk.Label(row2, text="替换", style="Status.TLabel").pack(side=tk.LEFT, padx=(0, 6))
        self._draft_replace_entry = ttk.Entry(row2, textvariable=self._draft_replace_var)
        self._draft_replace_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(row2, text="替换", style="Secondary.TButton", command=self._draft_replace_one).pack(
            side=tk.LEFT, padx=(8, 0)
        )
        ttk.Button(row2, text="全部替换", style="Secondary.TButton", command=self._draft_replace_all).pack(
            side=tk.LEFT, padx=(6, 0)
        )

        try:
            self.draft_text.tag_configure(
                "draft_find_match",
                background=th["accent"],
                foreground=th["fg"],
            )
        except tk.TclError:
            pass
        try:
            self.draft_text.tag_configure(
                "draft_find_current",
                background=th["accent_hover"],
                foreground=th["fg"],
            )
        except tk.TclError:
            pass

        self.draft_text.bind("<Control-z>", lambda _e: self._draft_undo())
        self.draft_text.bind("<Control-y>", lambda _e: self._draft_redo())
        self.draft_text.bind("<Control-Shift-Z>", lambda _e: self._draft_redo())

        self.draft_text.bind("<Control-f>", lambda _e: self._show_draft_search(mode="find"))
        self.draft_text.bind("<Control-h>", lambda _e: self._show_draft_search(mode="replace"))
        self.draft_text.bind("<Control-v>", self._draft_handle_paste)
        self.draft_text.bind("<<Paste>>", self._draft_handle_paste)
        self.draft_text.bind("<Escape>", lambda _e: self._draft_escape_handler())

        self._draft_find_entry.bind("<Return>", lambda _e: self._draft_find_next(backward=False))
        self._draft_find_entry.bind("<Shift-Return>", lambda _e: self._draft_find_next(backward=True))
        self._draft_find_entry.bind("<Escape>", lambda _e: self._hide_draft_search())
        self._draft_replace_entry.bind("<Escape>", lambda _e: self._hide_draft_search())

        self._draft_find_var.trace_add("write", lambda *_a: self._draft_highlight_all_matches())
        self._draft_find_regex_var.trace_add("write", lambda *_a: self._draft_highlight_all_matches())

        self.draft_text.bind("<KeyPress-Return>", self._draft_handle_return)
        self.draft_text.bind("<KeyPress-KP_Enter>", self._draft_handle_return)
        self.draft_text.bind("<KeyPress-BackSpace>", self._draft_handle_backspace_delete)
        self.draft_text.bind("<KeyPress-Delete>", self._draft_handle_backspace_delete)

        self.draft_text.bind("<KeyRelease>", self._draft_on_editor_key_release, add=True)
        self.draft_text.bind("<ButtonRelease-1>", lambda _e: self._draft_on_editor_click(), add=True)
        self.draft_text.bind("<B1-Motion>", self._draft_on_editor_drag_select, add=True)
        self.draft_text.bind("<KeyPress>", self._draft_on_editor_keypress, add=True)

    def _draft_escape_handler(self) -> str | None:
        if getattr(self, "_draft_search_visible", False):
            return self._hide_draft_search()
        return None

    def _draft_undo(self) -> str:
        if self._draft_history_idx <= 0:
            return "break"
        self._draft_history_restoring = True
        try:
            self._draft_history_idx -= 1
            self._draft_source = self._draft_history[self._draft_history_idx]
        finally:
            self._draft_history_restoring = False
        self._draft_history_last_change_ts = 0.0
        self._draft_refresh_view()
        self._update_draft_stats()
        return "break"

    def _draft_redo(self) -> str:
        if self._draft_history_idx >= len(self._draft_history) - 1:
            return "break"
        self._draft_history_restoring = True
        try:
            self._draft_history_idx += 1
            self._draft_source = self._draft_history[self._draft_history_idx]
        finally:
            self._draft_history_restoring = False
        self._draft_history_last_change_ts = 0.0
        self._draft_refresh_view()
        self._update_draft_stats()
        return "break"

    def _show_draft_search(self, mode: str = "find") -> str:
        if not hasattr(self, "_draft_search_frame"):
            return "break"
        if hasattr(self, "_draft_view_mode_var"):
            self._draft_view_mode_before_search = self._draft_view_mode_var.get()
        try:
            cur_ln = int(self.draft_text.index("insert").split(".")[0])
        except tk.TclError:
            cur_ln = 1
        self._draft_sync_line_at(cur_ln)
        self._draft_force_raw = True
        self._draft_refresh_view()

        if not self._draft_search_visible:
            self._draft_search_frame.pack(fill=tk.X, pady=(0, 6), before=self.draft_text)
            self._draft_search_visible = True
        if hasattr(self, "_draft_md_mode_radio"):
            self._draft_md_mode_radio.configure(state="disabled")
            self._draft_src_mode_radio.configure(state="disabled")
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                sel = self.draft_text.get(tk.SEL_FIRST, tk.SEL_LAST)
                if sel and sel.strip():
                    self._draft_find_var.set(sel)
        except tk.TclError:
            pass
        if mode == "replace":
            self._draft_replace_entry.focus_set()
            self._draft_replace_entry.icursor(tk.END)
        else:
            self._draft_find_entry.focus_set()
            self._draft_find_entry.icursor(tk.END)
            self._draft_find_entry.select_range(0, tk.END)
        self._draft_highlight_all_matches()
        return "break"

    def _hide_draft_search(self) -> str:
        if getattr(self, "_draft_search_visible", False) and hasattr(self, "_draft_search_frame"):
            self._draft_search_frame.pack_forget()
            self._draft_search_visible = False
        self._draft_set_source(self.draft_text.get("1.0", "end-1c"))
        saved = getattr(self, "_draft_view_mode_before_search", None)
        if saved is None and hasattr(self, "_draft_view_mode_var"):
            saved = self._draft_view_mode_var.get()
        if saved is None:
            saved = "markdown"
        if hasattr(self, "_draft_view_mode_var"):
            self._draft_view_mode_var.set(saved)
        self._draft_force_raw = saved == "source"
        self._draft_refresh_view()
        if hasattr(self, "_draft_md_mode_radio"):
            self._draft_md_mode_radio.configure(state="normal")
            self._draft_src_mode_radio.configure(state="normal")
        self._draft_clear_search_highlight()
        try:
            self.draft_text.focus_set()
        except tk.TclError:
            pass
        return "break"

    def _draft_clear_search_highlight(self) -> None:
        try:
            self.draft_text.tag_remove("draft_find_match", "1.0", tk.END)
            self.draft_text.tag_remove("draft_find_current", "1.0", tk.END)
        except tk.TclError:
            pass

    def _draft_highlight_all_matches(self) -> None:
        needle = (self._draft_find_var.get() if hasattr(self, "_draft_find_var") else "").strip()
        self._draft_clear_search_highlight()
        if not needle:
            return
        if self._draft_find_regex_var.get():
            pattern = self._draft_compile_find_regex(needle)
            if pattern is None:
                return
            content = self.draft_text.get("1.0", "end-1c")
            for m in pattern.finditer(content):
                if m.start() == m.end():
                    continue
                idx = f"1.0+{m.start()}c"
                end = f"1.0+{m.end()}c"
                self.draft_text.tag_add("draft_find_match", idx, end)
            return
        start = "1.0"
        try:
            while True:
                idx = self.draft_text.search(needle, start, stopindex=tk.END, nocase=False)
                if not idx:
                    break
                end = f"{idx}+{len(needle)}c"
                self.draft_text.tag_add("draft_find_match", idx, end)
                start = end
        except tk.TclError:
            return

    def _draft_find_next(self, backward: bool = False) -> str:
        needle = (self._draft_find_var.get() if hasattr(self, "_draft_find_var") else "").strip()
        if not needle:
            return "break"

        try:
            cur = self.draft_text.index(tk.INSERT)
        except tk.TclError:
            cur = "1.0"

        self.draft_text.tag_remove("draft_find_current", "1.0", tk.END)

        try:
            if self._draft_find_regex_var.get():
                pattern = self._draft_compile_find_regex(needle)
                if pattern is None:
                    return "break"
                content = self.draft_text.get("1.0", "end-1c")
                matches = [m for m in pattern.finditer(content) if m.start() != m.end()]
                if not matches:
                    return "break"
                cur_off = len(self.draft_text.get("1.0", cur))
                pick = None
                if backward:
                    for m in reversed(matches):
                        if m.start() < cur_off:
                            pick = m
                            break
                    if pick is None:
                        pick = matches[-1]
                else:
                    for m in matches:
                        if m.start() > cur_off:
                            pick = m
                            break
                    if pick is None:
                        pick = matches[0]
                idx = f"1.0+{pick.start()}c"
                end = f"1.0+{pick.end()}c"
            else:
                if backward:
                    idx = self.draft_text.search(needle, cur, stopindex="1.0", backwards=True, nocase=False)
                    if not idx:
                        idx = self.draft_text.search(needle, tk.END, stopindex="1.0", backwards=True, nocase=False)
                else:
                    idx = self.draft_text.search(needle, f"{cur}+1c", stopindex=tk.END, nocase=False)
                    if not idx:
                        idx = self.draft_text.search(needle, "1.0", stopindex=tk.END, nocase=False)
                if not idx:
                    return "break"
                end = f"{idx}+{len(needle)}c"
            self.draft_text.tag_add("draft_find_current", idx, end)
            self.draft_text.mark_set(tk.INSERT, end)
            self.draft_text.see(idx)
            self.draft_text.tag_remove(tk.SEL, "1.0", tk.END)
            self.draft_text.tag_add(tk.SEL, idx, end)
        except tk.TclError:
            return "break"
        return "break"

    def _draft_replace_one(self) -> str:
        needle = (self._draft_find_var.get() if hasattr(self, "_draft_find_var") else "").strip()
        repl = self._draft_replace_var.get() if hasattr(self, "_draft_replace_var") else ""
        if not needle:
            return "break"
        try:
            if self.draft_text.tag_ranges(tk.SEL):
                sel = self.draft_text.get(tk.SEL_FIRST, tk.SEL_LAST)
                if self._draft_find_regex_var.get():
                    pattern = self._draft_compile_find_regex(needle)
                    if pattern is None:
                        return "break"
                    if pattern.fullmatch(sel):
                        new_sel = pattern.sub(repl, sel, count=1)
                        self.draft_text.delete(tk.SEL_FIRST, tk.SEL_LAST)
                        self.draft_text.insert(tk.INSERT, new_sel)
                elif sel == needle:
                    self.draft_text.delete(tk.SEL_FIRST, tk.SEL_LAST)
                    self.draft_text.insert(tk.INSERT, repl)
            self._draft_find_next(backward=False)
            self._draft_highlight_all_matches()
            self._draft_set_source(self.draft_text.get("1.0", "end-1c"))
            self._update_draft_stats()
            self._schedule_draft_save()
        except tk.TclError:
            pass
        return "break"

    def _draft_replace_all(self) -> str:
        needle = (self._draft_find_var.get() if hasattr(self, "_draft_find_var") else "").strip()
        repl = self._draft_replace_var.get() if hasattr(self, "_draft_replace_var") else ""
        if not needle:
            return "break"
        try:
            content = self.draft_text.get("1.0", tk.END)
            if self._draft_find_regex_var.get():
                pattern = self._draft_compile_find_regex(needle)
                if pattern is None:
                    return "break"
                new_content, _cnt = pattern.subn(repl, content)
            else:
                new_content = content.replace(needle, repl)
            if new_content != content:
                self.draft_text.delete("1.0", tk.END)
                self.draft_text.insert("1.0", new_content)
            self._draft_highlight_all_matches()
            self._draft_set_source(self.draft_text.get("1.0", "end-1c"))
            self._update_draft_stats()
            self._schedule_draft_save()
        except tk.TclError:
            pass
        return "break"

    def _draft_compile_find_regex(self, expr: str):
        try:
            return re.compile(expr)
        except re.error:
            self._record_status("正则表达式无效")
            return None

    def _update_draft_stats(self) -> None:
        if not hasattr(self, "draft_stats_label"):
            return
        if getattr(self, "_draft_force_raw", False):
            try:
                content = self.draft_text.get("1.0", "end-1c")
            except tk.TclError:
                content = self._draft_source
        else:
            content = self._draft_source
        char_count = len(re.sub(r"\s+", "", content))
        selected_count = 0
        try:
            if hasattr(self, "draft_text") and self.draft_text.tag_ranges(tk.SEL):
                selected_count = len(re.sub(r"\s+", "", self.draft_text.get(tk.SEL_FIRST, tk.SEL_LAST)))
        except tk.TclError:
            selected_count = 0
        self.draft_stats_label.configure(text=f"源码字数：{char_count}  选中：{selected_count}")

    def _start_window_drag(self, event) -> None:
        self._drag_start_x = event.x_root
        self._drag_start_y = event.y_root
        self._win_start_x = self.root.winfo_x()
        self._win_start_y = self.root.winfo_y()

    def _on_notebook_tabstrip_press(self, event) -> None:
        strip_h = 36
        reserve_right = 52
        if event.y <= strip_h and event.x < max(20, self.notebook.winfo_width() - reserve_right):
            self._drag_from_tabstrip = True
            self._start_window_drag(event)
        else:
            self._drag_from_tabstrip = False

    def _on_notebook_tabstrip_motion(self, event) -> None:
        if self._drag_from_tabstrip:
            self._on_window_drag(event)

    def _on_notebook_tabstrip_release(self, _event) -> None:
        self._drag_from_tabstrip = False

    def _on_window_drag(self, event) -> None:
        dx = event.x_root - self._drag_start_x
        dy = event.y_root - self._drag_start_y
        self.root.geometry(f"+{self._win_start_x + dx}+{self._win_start_y + dy}")

    def _format_tasks_lines(self, day: str, tasks: list[dict]) -> list[str]:
        lines: list[str] = [f"日期：{day}"]
        if not tasks:
            lines.append("暂无该日任务记录。")
            return lines
        done_tasks = [t for t in tasks if t.get("done")]
        undone_tasks = [t for t in tasks if not t.get("done")]
        lines.append(f"总任务：{len(tasks)}  已完成：{len(done_tasks)}  未完成：{len(undone_tasks)}")
        lines.append("")
        lines.append("【已完成】")
        if done_tasks:
            lines.extend([f"- {t.get('text', '').strip()}" for t in done_tasks])
        else:
            lines.append("- 无")
        lines.append("")
        lines.append("【未完成】")
        if undone_tasks:
            lines.extend([f"- {t.get('text', '').strip()}" for t in undone_tasks])
        else:
            lines.append("- 无")
        return lines

    def _refresh_log_view(self) -> None:
        selected_day = self.log_day_var.get().strip()
        tasks = self._get_tasks_for_day(selected_day)
        lines = self._format_tasks_lines(selected_day, tasks)
        self._set_log_text("\n".join(lines), preserve_view=False)
        self._weekly_tasks_plain = ""

    def _set_log_text(self, content: str, preserve_view: bool = True) -> None:
        # 自动刷新时尽量保留滚动位置，避免“回到第一页”的观感
        y0 = None
        if preserve_view:
            try:
                y0 = self.log_text.yview()[0]
            except tk.TclError:
                y0 = None
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.delete("1.0", tk.END)
        self.log_text.insert("1.0", content)
        if y0 is not None:
            try:
                self.log_text.yview_moveto(y0)
            except tk.TclError:
                pass
        self.log_text.configure(state=tk.DISABLED)

    def _apply_log_mode_layout(self) -> None:
        if self.log_mode_var.get() == "周汇总":
            self.log_date_frame.pack_forget()
            self.log_week_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        else:
            self.log_week_frame.pack_forget()
            self.log_date_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)

    def _on_log_mode_changed(self, _event=None) -> None:
        self._apply_log_mode_layout()
        self._reload_log_comboboxes()
        self._refresh_logs_tab_data()

    def _update_log_dropdown_button_labels(self) -> None:
        mode_text = self.log_mode_var.get().strip() or "单日"
        self.log_mode_dropdown_btn.configure(text=f"{mode_text} ▼")
        day_text = self.log_day_var.get().strip() or "请选择日期"
        self.log_day_dropdown_btn.configure(text=f"{day_text} ▼")
        week_text = self.log_week_var.get().strip() or "请选择自然周"
        self.log_week_dropdown_btn.configure(text=f"{week_text} ▼")

    def _toggle_log_dropdown(self, kind: str) -> None:
        if self._active_log_dropdown_popup is not None and self._active_log_dropdown_popup.winfo_exists():
            if self._active_log_dropdown_kind == kind:
                self._hide_log_dropdown()
                return
            self._hide_log_dropdown()
        self._show_log_dropdown(kind)

    def _show_log_dropdown(self, kind: str) -> None:
        if kind == "mode":
            options = self._log_mode_values
            anchor_widget = self.log_mode_dropdown_btn
        elif kind == "day":
            options = self._log_day_values
            anchor_widget = self.log_day_dropdown_btn
        else:
            options = self._log_week_values
            anchor_widget = self.log_week_dropdown_btn
        if not options:
            return
        popup = ttk.Frame(self.root, style="Main.TFrame", padding=4)
        popup.configure(borderwidth=1, relief="solid")
        self._active_log_dropdown_popup = popup
        self._active_log_dropdown_kind = kind

        for opt in options:
            ttk.Button(
                popup,
                text=opt,
                style="Secondary.TButton",
                command=lambda value=opt, k=kind: self._select_log_dropdown_option(k, value),
            ).pack(fill=tk.X, pady=1)

        popup.update_idletasks()
        bx = anchor_widget.winfo_rootx() - self.root.winfo_rootx()
        by = anchor_widget.winfo_rooty() - self.root.winfo_rooty() + anchor_widget.winfo_height() + 2
        popup.place(x=bx, y=by)
        popup.lift()

    def _select_log_dropdown_option(self, kind: str, value: str) -> None:
        self._hide_log_dropdown()
        if kind == "mode":
            self.log_mode_var.set(value)
            self._update_log_dropdown_button_labels()
            self._on_log_mode_changed()
            return
        if kind == "day":
            self.log_day_var.set(value)
            self._update_log_dropdown_button_labels()
            self._refresh_logs_tab_data()
            return
        self.log_week_var.set(value)
        self._update_log_dropdown_button_labels()
        self._refresh_log_week_view()

    def _hide_log_dropdown(self) -> None:
        if self._active_log_dropdown_popup is None:
            return
        try:
            if self._active_log_dropdown_popup.winfo_exists():
                self._active_log_dropdown_popup.destroy()
        except tk.TclError:
            pass
        self._active_log_dropdown_popup = None
        self._active_log_dropdown_kind = None

    def _reload_log_comboboxes(self) -> None:
        dates = self._collect_log_dates()
        day_values = dates if dates else [self.today]
        self._log_day_values = day_values
        cur_day = self.log_day_var.get().strip()
        if cur_day not in day_values:
            self.log_day_var.set(day_values[0])
        self._update_log_dropdown_button_labels()

        week_opts = self._collect_week_options()
        self._log_week_key_by_label = {lbl: key for key, lbl in week_opts}
        labels = [lbl for _key, lbl in week_opts]
        self._log_week_values = labels
        cur_week = self.log_week_var.get().strip()
        if not labels:
            self.log_week_var.set("")
        elif cur_week not in labels:
            self.log_week_var.set(labels[0])
        self._update_log_dropdown_button_labels()

    def _collect_week_options(self) -> list[tuple[str, str]]:
        today = datetime.now().date()
        monday = today - timedelta(days=today.weekday())
        out: list[tuple[str, str]] = []
        for i in range(26):
            m = monday - timedelta(weeks=i)
            s = m + timedelta(days=6)
            key = f"{m.strftime(DATE_FMT)}|{s.strftime(DATE_FMT)}"
            tag = "（本周）" if i == 0 else ""
            label = f"{m.strftime(DATE_FMT)} ~ {s.strftime(DATE_FMT)}{tag}"
            out.append((key, label))
        return out

    def _refresh_logs_tab_data(self) -> None:
        self._reload_log_comboboxes()
        if self.log_mode_var.get() == "周汇总":
            self._refresh_log_week_view()
        else:
            self._refresh_log_view()

    def _refresh_log_week_view(self) -> None:
        label = self.log_week_var.get().strip()
        key = self._log_week_key_by_label.get(label)
        if not key:
            self._weekly_tasks_plain = ""
            self._set_log_text("暂无周数据，请先选择自然周。", preserve_view=False)
            return
        mon_str, sun_str = key.split("|", 1)
        start = datetime.strptime(mon_str, DATE_FMT).date()
        end = datetime.strptime(sun_str, DATE_FMT).date()
        all_lines: list[str] = [f"自然周：{mon_str} 至 {sun_str}（按日汇总）", ""]
        plain_parts: list[str] = [all_lines[0], ""]
        cur = start
        while cur <= end:
            day = cur.strftime(DATE_FMT)
            tasks = self._get_tasks_for_day(day)
            block = self._format_tasks_lines(day, tasks)
            all_lines.extend(block)
            all_lines.append("")
            plain_parts.extend(block)
            plain_parts.append("")
            cur += timedelta(days=1)
        self._weekly_tasks_plain = "\n".join(plain_parts).strip()
        self._set_log_text("\n".join(all_lines).rstrip(), preserve_view=False)
        try:
            full_prompt = self._get_weekly_prompt_template().format(tasks_block=self._weekly_tasks_plain)
        except (KeyError, ValueError):
            full_prompt = self._get_weekly_prompt_template().replace("{tasks_block}", self._weekly_tasks_plain)
        _ = full_prompt

    def _update_weekly_prompt_preview(self, text: str) -> None:
        _ = text

    def _copy_weekly_ai_prompt(self) -> None:
        if self.log_mode_var.get() != "周汇总" or not self._weekly_tasks_plain.strip():
            self._record_status("请先在「周汇总」下选择一周并加载任务")
            return
        try:
            body = self._get_weekly_prompt_template().format(tasks_block=self._weekly_tasks_plain.strip())
        except (KeyError, ValueError):
            body = self._get_weekly_prompt_template().replace("{tasks_block}", self._weekly_tasks_plain.strip())
        self.root.clipboard_clear()
        self.root.clipboard_append(body)
        self._record_status("提示词已复制到剪贴板")

    def _setup_log_tab_auto_refresh(self) -> None:
        self.notebook.bind("<<NotebookTabChanged>>", self._on_notebook_tab_changed_logs)

    def _on_notebook_tab_changed_logs(self, _event=None) -> None:
        self._cancel_log_periodic_refresh()
        try:
            if self.notebook.select() == str(self.logs_tab):
                self._refresh_logs_tab_data()
                self._schedule_log_tab_periodic_refresh()
        except tk.TclError:
            pass

    def _schedule_log_tab_periodic_refresh(self) -> None:
        self._cancel_log_periodic_refresh()

        def tick() -> None:
            try:
                if self.notebook.select() == str(self.logs_tab):
                    self._refresh_logs_tab_data()
            except tk.TclError:
                return
            self._log_refresh_after_id = self.root.after(LOG_TAB_AUTO_REFRESH_MS, tick)

        self._log_refresh_after_id = self.root.after(LOG_TAB_AUTO_REFRESH_MS, tick)

    def _cancel_log_periodic_refresh(self) -> None:
        if self._log_refresh_after_id is not None:
            self.root.after_cancel(self._log_refresh_after_id)
            self._log_refresh_after_id = None

    def _maybe_refresh_logs_tab(self) -> None:
        try:
            if self.notebook.select() == str(self.logs_tab):
                self._refresh_logs_tab_data()
        except tk.TclError:
            pass

    def _collect_log_dates(self) -> list[str]:
        dates: set[str] = set()
        for path in self.data_dir.glob("tasks_*.json"):
            name = path.stem.replace("tasks_", "", 1)
            if len(name) == 10:
                dates.add(name)
        if self.daily_archive_log_file.exists():
            for line in self.daily_archive_log_file.read_text(encoding="utf-8").splitlines():
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                day = obj.get("day")
                if isinstance(day, str) and len(day) == 10:
                    dates.add(day)
        return sorted(dates, reverse=True)

    def _is_day_archived(self, day: str) -> bool:
        if not self.daily_archive_log_file.exists():
            return False
        try:
            # 从后往前找，通常更快命中最近日期
            for line in reversed(self.daily_archive_log_file.read_text(encoding="utf-8").splitlines()):
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("type") == "daily_archive" and obj.get("day") == day:
                    return True
        except Exception:
            return False
        return False

    def _find_latest_task_day_before(self, day: str) -> str | None:
        """找到 day 之前最近一个存在 tasks_YYYY-MM-DD.json 的日期。"""
        try:
            target = datetime.strptime(day, DATE_FMT).date()
        except (TypeError, ValueError):
            return None
        candidates: list[str] = []
        for path in self.data_dir.glob("tasks_*.json"):
            name = path.stem.replace("tasks_", "", 1)
            if len(name) != 10:
                continue
            try:
                d = datetime.strptime(name, DATE_FMT).date()
            except (TypeError, ValueError):
                continue
            if d < target:
                candidates.append(name)
        return max(candidates) if candidates else None

    def _get_tasks_for_day(self, day: str) -> list[dict]:
        day_file = self.data_dir / f"tasks_{day}.json"
        if day_file.exists():
            try:
                payload = json.loads(day_file.read_text(encoding="utf-8"))
                tasks = payload.get("tasks", [])
                if isinstance(tasks, list):
                    return tasks
            except Exception:
                return []
        if self.daily_archive_log_file.exists():
            for line in reversed(self.daily_archive_log_file.read_text(encoding="utf-8").splitlines()):
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("day") == day and isinstance(obj.get("tasks"), list):
                    return obj["tasks"]
        return []

    def _load_tasks_for_today(self) -> None:
        if self.today_file.exists():
            self.tasks = self._read_tasks_file(self.today_file)
            self._sort_tasks()
            self._record_status("已加载今日任务文件")
            return

        self.tasks = []
        yesterday_date = (datetime.now() - timedelta(days=1)).strftime(DATE_FMT)
        last_day = None
        last_file = self.data_dir / f"tasks_{yesterday_date}.json"
        if last_file.exists():
            last_day = yesterday_date
        else:
            # 周末/节假日可能没打开应用 → 没有生成文件；回溯到最近一次有记录的日期
            last_day = self._find_latest_task_day_before(self.today)
            last_file = self.data_dir / f"tasks_{last_day}.json" if last_day else None

        if last_day and last_file and last_file.exists():
            last_tasks = self._read_tasks_file(last_file)
            # 避免重复归档同一天（例如反复启动应用但未生成新一天文件时）
            if not self._is_day_archived(last_day):
                self._archive_yesterday(last_day, last_tasks)

            carry_over = [
                TaskItem(
                    id=str(uuid.uuid4()),
                    text=item.text,
                    done=False,
                    created_at=datetime.now().strftime(TIME_FMT),
                    source_day=last_day,
                )
                for item in last_tasks
                if not item.done
            ]
            self.tasks.extend(carry_over)
            self._sort_tasks()

            if carry_over:
                self._append_event(
                    "carry_over_from_previous_day",
                    {
                        "from_day": last_day,
                        "carried_count": len(carry_over),
                        "task_texts": [item.text for item in carry_over],
                    },
                )
            if last_day != yesterday_date:
                self._record_status(f"已从最近记录日 {last_day} 继承未完成任务 {len(carry_over)} 项")
            else:
                self._record_status(f"已继承昨天未完成任务 {len(carry_over)} 项")
        else:
            self._record_status("未找到历史任务文件，已创建新的一天")

        self._sort_tasks()
        self._save_today_tasks()

    def _rollover_day_if_needed(self) -> None:
        current_day = datetime.now().strftime(DATE_FMT)
        if current_day == self.today:
            return

        previous_day = self.today
        previous_tasks = list(self.tasks)
        self._flush_incremental_log(force=True)
        if previous_tasks and not self._is_day_archived(previous_day):
            self._archive_yesterday(previous_day, previous_tasks)

        carry_over = [
            TaskItem(
                id=str(uuid.uuid4()),
                text=item.text,
                done=False,
                created_at=datetime.now().strftime(TIME_FMT),
                source_day=previous_day,
            )
            for item in previous_tasks
            if not item.done
        ]

        self.today = current_day
        self.today_file = self.data_dir / f"tasks_{self.today}.json"
        self.incremental_log_file = self.logs_dir / f"incremental_{self.today}.jsonl"
        self.tasks = carry_over
        self._sort_tasks()
        self._save_today_tasks()
        self.pending_events.clear()
        self._append_event(
            "rollover_to_new_day",
            {
                "from_day": previous_day,
                "to_day": current_day,
                "carried_count": len(carry_over),
            },
        )
        if hasattr(self, "log_day_var"):
            self.log_day_var.set(self.today)
        self._record_status(f"检测到跨日：已归档 {previous_day}，并迁移未完成任务 {len(carry_over)} 项")

    def _archive_yesterday(self, day: str, tasks: list[TaskItem]) -> None:
        archive_event = {
            "ts": datetime.now().strftime(TIME_FMT),
            "type": "daily_archive",
            "day": day,
            "total": len(tasks),
            "done": len([t for t in tasks if t.done]),
            "undone": len([t for t in tasks if not t.done]),
            "tasks": [asdict(t) for t in tasks],
        }
        self._append_jsonl(self.daily_archive_log_file, archive_event)

    def _add_task(self) -> None:
        self._rollover_day_if_needed()
        text = self.task_entry.get().strip()
        if not text:
            messagebox.showwarning("提示", "请输入任务内容")
            return

        new_task = TaskItem(
            id=str(uuid.uuid4()),
            text=text,
            done=False,
            created_at=datetime.now().strftime(TIME_FMT),
            source_day=self.today,
        )
        self.tasks.append(new_task)
        self._sort_tasks()
        self.task_entry.delete(0, tk.END)
        self._save_today_tasks()
        self._append_event("task_added", {"task": asdict(new_task)})
        self._refresh_task_list()
        self._record_status("已新增任务")

    def _setup_shortcuts(self) -> None:
        self.root.unbind_all("<KeyPress>")
        self.root.bind_all("<KeyPress>", self._focus_input_from_shortcut)
        tab_hotkey = str(self.settings.get("tab_switch_hotkey", "CTRL+TAB")).strip().upper()
        tab_seq = self._hotkey_to_tk_sequence(tab_hotkey)
        old_seq = getattr(self, "_tab_switch_seq", None)
        if old_seq and (old_seq != tab_seq or not tab_seq):
            try:
                self.root.unbind_all(old_seq)
            except tk.TclError:
                pass
            for cls in ("TEntry", "Entry", "Text", "TCombobox"):
                try:
                    self.root.unbind_class(cls, old_seq)
                except tk.TclError:
                    pass
        self._tab_switch_seq = tab_seq
        if tab_seq:
            self.root.bind_all(tab_seq, self._switch_tab_by_shortcut)
            for cls in ("TEntry", "Entry", "Text", "TCombobox"):
                self.root.bind_class(cls, tab_seq, self._switch_tab_by_shortcut)
        self._setup_draft_tool_shortcuts()

    def _setup_draft_tool_shortcuts(self) -> None:
        for seq in getattr(self, "_draft_tool_shortcut_seqs", {}).values():
            if not seq:
                continue
            try:
                self.root.unbind_all(seq)
            except tk.TclError:
                pass
            for cls in ("TEntry", "Entry", "Text", "TCombobox"):
                try:
                    self.root.unbind_class(cls, seq)
                except tk.TclError:
                    pass

        tool_config = {
            "json": ("tool_json_hotkey", self._draft_format_json),
            "b64_encode": ("tool_b64_encode_hotkey", self._draft_base64_encode),
            "b64_decode": ("tool_b64_decode_hotkey", self._draft_base64_decode),
            "url_encode": ("tool_url_encode_hotkey", self._draft_url_encode),
            "url_decode": ("tool_url_decode_hotkey", self._draft_url_decode),
        }
        self._draft_tool_shortcut_seqs = {}
        for key, (setting_name, callback) in tool_config.items():
            hotkey = str(self.settings.get(setting_name, "")).strip().upper()
            seq = self._hotkey_to_tk_sequence(hotkey) if hotkey else None
            self._draft_tool_shortcut_seqs[key] = seq
            if not seq:
                continue
            handler = self._make_local_shortcut_handler(callback)
            self.root.bind_all(seq, handler)
            for cls in ("TEntry", "Entry", "Text", "TCombobox"):
                self.root.bind_class(cls, seq, handler)

    def _make_local_shortcut_handler(self, callback):
        def handler(_event=None):
            if not self._is_app_focused():
                return None
            if self.notebook.select() != str(self.draft_tab):
                return None
            callback()
            return "break"

        return handler

    def _switch_tab_by_shortcut(self, _event=None) -> str | None:
        if not self._is_app_focused():
            return None
        tabs = self.notebook.tabs()
        if not tabs:
            return "break"
        current = self.notebook.select()
        idx = tabs.index(current) if current in tabs else 0
        next_idx = (idx + 1) % len(tabs)
        self.notebook.select(tabs[next_idx])
        return "break"

    def _hotkey_to_tk_sequence(self, hotkey: str) -> str | None:
        parts = [p.strip().upper() for p in hotkey.split("+") if p.strip()]
        if not parts:
            return None
        key = parts[-1]
        mods = parts[:-1]
        mod_map = {
            "CTRL": "Control",
            "ALT": "Alt",
            "SHIFT": "Shift",
        }
        tk_mods: list[str] = []
        for mod in mods:
            if mod not in mod_map:
                return None
            tk_mods.append(mod_map[mod])

        key_map = {
            "TAB": "Tab",
            "RETURN": "Return",
            "ESCAPE": "Escape",
            "SPACE": "space",
            "LEFT": "Left",
            "RIGHT": "Right",
            "UP": "Up",
            "DOWN": "Down",
            "/": "slash",
        }
        if key in key_map:
            tk_key = key_map[key]
        elif len(key) == 1 and key.isalnum():
            tk_key = key.lower()
        elif key.startswith("F") and key[1:].isdigit():
            tk_key = key.upper()
        else:
            return None

        if tk_mods:
            return f"<{'-'.join(tk_mods)}-{tk_key}>"
        return f"<{tk_key}>"

    def _focus_input_from_shortcut(self, event=None) -> str | None:
        if event is None:
            return None
        if not self._is_app_focused():
            return None
        # 在任何可编辑输入控件中输入字符时，不触发“聚焦任务输入框”，避免草稿等页面输入 '/' 被打断
        try:
            w = event.widget
            if isinstance(w, (tk.Text, tk.Entry, ttk.Entry, ttk.Combobox)):
                return None
        except Exception:
            pass
        if self.inline_editing_task_id is not None:
            return "break"
        expected = str(self.settings.get("focus_input_key", "/")).strip().lower()
        pressed = self._normalize_focus_key(event)
        if pressed != expected:
            return None
        self.notebook.select(self.tasks_tab)
        self.task_entry.focus_set()
        self.task_entry.icursor(tk.END)
        return "break"

    def _normalize_focus_key(self, event) -> str:
        if event.keysym == "slash":
            return "/"
        if event.char and event.char.strip():
            return event.char.lower()
        return event.keysym.lower()

    def _is_app_focused(self) -> bool:
        if not self.root.winfo_viewable():
            return False
        try:
            return self.root.focus_displayof() is not None
        except tk.TclError:
            return False

    def _on_toggle_task(self, task_id: str) -> None:
        self._rollover_day_if_needed()
        task = next((t for t in self.tasks if t.id == task_id), None)
        if task is None:
            return
        is_done = self.task_vars[task_id].get()
        task.done = is_done
        self._sort_tasks()
        self._save_today_tasks()
        self._append_event(
            "task_toggled",
            {
                "task_id": task.id,
                "text": task.text,
                "done": task.done,
            },
        )
        self._refresh_task_list()
        self._record_status("任务状态已更新")

    def _paint_task_done_toggle_canvas(self, c: tk.Canvas, done: bool) -> None:
        th = APP_THEME
        c.delete("all")
        w = int(c.cget("width"))
        h = int(c.cget("height"))
        pad = 5
        box = min(w, h) - pad * 2
        x0, y0 = pad, pad
        x1, y1 = x0 + box, y0 + box
        if done:
            c.create_rectangle(x0, y0, x1, y1, outline=th["accent"], fill=th["accent"], width=1)
            c.create_text(
                (x0 + x1) / 2,
                (y0 + y1) / 2,
                text="\u2713",
                fill=th["fg"],
                font=("Segoe UI Symbol", 10, "bold"),
            )
        else:
            c.create_rectangle(x0, y0, x1, y1, outline=th["border"], fill=th["bg_elevated"], width=1)

    def _create_task_done_toggle(self, row: tk.Misc, task_id: str, var: tk.BooleanVar) -> tk.Canvas:
        th = APP_THEME
        total = 28
        c = tk.Canvas(
            row,
            width=total,
            height=total,
            bg=th["bg_row"],
            highlightthickness=0,
            bd=0,
            cursor="hand2",
        )

        def on_click(_e):
            var.set(not var.get())
            self._on_toggle_task(task_id)

        c.bind("<Button-1>", on_click)
        self._paint_task_done_toggle_canvas(c, var.get())
        return c

    def _refresh_task_list(self) -> None:
        for widget in self.scroll_frame.winfo_children():
            widget.destroy()
        self.task_vars.clear()
        self.task_done_canvases.clear()
        self.task_text_labels.clear()

        if not self.tasks:
            empty_label = ttk.Label(
                self.scroll_frame,
                text="今天还没有任务，先新增一条吧。",
                style="CanvasHint.TLabel",
            )
            empty_label.pack(anchor=tk.W, padx=8, pady=12)
            return

        th = APP_THEME
        for task in self.tasks:
            row = tk.Frame(self.scroll_frame, bg=th["bg_row"], highlightthickness=0, bd=0)
            row.pack(fill=tk.X, pady=(0, 4), padx=0)

            var = tk.BooleanVar(value=task.done)
            self.task_vars[task.id] = var

            done_toggle = self._create_task_done_toggle(row, task.id, var)
            self.task_done_canvases[task.id] = done_toggle
            done_toggle.pack(side=tk.LEFT, padx=(6, 2), pady=4)

            source_text = ""
            if task.source_day != self.today:
                source_text = f"（来自 {task.source_day} 未完成）"
            if self.inline_editing_task_id == task.id:
                edit_entry = tk.Entry(
                    row,
                    bg=th["bg_elevated"],
                    fg=th["fg"],
                    insertbackground=th["fg"],
                    relief="flat",
                    highlightthickness=1,
                    highlightbackground=th["border"],
                    highlightcolor=th["border_focus"],
                    bd=0,
                    font=UI_FONT,
                )
                edit_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 36), pady=6, ipady=6)
                edit_entry.insert(0, task.text)
                edit_entry.select_range(0, tk.END)
                edit_entry.focus_set()
                edit_entry.bind("<Return>", lambda _event, tid=task.id, e=edit_entry: self._save_inline_edit(tid, e.get()))
                edit_entry.bind("<Escape>", lambda _event: self._cancel_inline_edit())
                edit_entry.bind("<FocusOut>", lambda _event, tid=task.id, e=edit_entry: self._save_inline_edit(tid, e.get()))
            else:
                text_label = tk.Label(
                    row,
                    text=f"{task.text} {source_text}".strip(),
                    bg=th["bg_row"],
                    fg=th["fg"],
                    anchor="w",
                    font=UI_FONT,
                )
                text_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 36), pady=8)
                text_label.bind("<Double-1>", lambda _event, tid=task.id: self._start_inline_edit(tid))
                self.task_text_labels[task.id] = text_label
                self._refresh_task_style(task)

            del_btn = ttk.Button(
                row,
                text="✕",
                width=2,
                command=lambda tid=task.id: self._delete_task(tid),
                style="Mini.TButton",
            )
            self._bind_delete_button_hover(row, del_btn)

    def _refresh_task_style(self, task: TaskItem) -> None:
        label = self.task_text_labels.get(task.id)
        if not label:
            return
        if task.done:
            label.configure(foreground=APP_THEME["fg_done"])
        else:
            label.configure(foreground=APP_THEME["fg"])

    def _save_today_tasks(self) -> None:
        payload = {
            "date": self.today,
            "updated_at": datetime.now().strftime(TIME_FMT),
            "tasks": [asdict(task) for task in self.tasks],
        }
        self.today_file.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        self.last_saved_signature = self._current_signature()
        self._maybe_refresh_logs_tab()

    def _start_inline_edit(self, task_id: str) -> None:
        self.inline_editing_task_id = task_id
        self._refresh_task_list()

    def _cancel_inline_edit(self) -> None:
        self.inline_editing_task_id = None
        self._refresh_task_list()

    def _save_inline_edit(self, task_id: str, new_text_raw: str) -> None:
        self._rollover_day_if_needed()
        task = next((t for t in self.tasks if t.id == task_id), None)
        if task is None:
            self.inline_editing_task_id = None
            return

        new_text = new_text_raw.strip()
        if not new_text:
            messagebox.showwarning("提示", "任务内容不能为空")
            return
        if new_text == task.text:
            self.inline_editing_task_id = None
            self._refresh_task_list()
            return

        old_text = task.text
        task.text = new_text
        self._sort_tasks()
        self._save_today_tasks()
        self._append_event(
            "task_edited",
            {
                "task_id": task.id,
                "old_text": old_text,
                "new_text": new_text,
            },
        )
        self.inline_editing_task_id = None
        self._refresh_task_list()
        self._record_status("任务内容已修改")

    def _delete_task(self, task_id: str) -> None:
        self._rollover_day_if_needed()
        task = next((t for t in self.tasks if t.id == task_id), None)
        if task is None:
            return
        self.tasks = [t for t in self.tasks if t.id != task_id]
        self._sort_tasks()
        self._save_today_tasks()
        self._append_event(
            "task_deleted",
            {
                "task_id": task.id,
                "text": task.text,
                "done": task.done,
            },
        )
        if self.inline_editing_task_id == task_id:
            self.inline_editing_task_id = None
        self._refresh_task_list()
        self._record_status("任务已删除")

    def _bind_delete_button_hover(self, row: tk.Frame, del_btn: ttk.Button) -> None:
        def show_btn(_event=None) -> None:
            self._set_task_row_hover(row, is_hover=True)
            if del_btn.winfo_manager() != "place":
                del_btn.place(relx=1.0, rely=0.5, anchor="e", x=-8)
            del_btn.lift()

        def hide_btn(_event=None) -> None:
            pointer_widget = row.winfo_containing(self.root.winfo_pointerx(), self.root.winfo_pointery())
            if pointer_widget is not None and self._is_descendant_of(pointer_widget, row):
                return
            self._set_task_row_hover(row, is_hover=False)
            if del_btn.winfo_manager() == "place":
                del_btn.place_forget()

        row.bind("<Enter>", show_btn)
        row.bind("<Leave>", hide_btn)
        for child in row.winfo_children():
            child.bind("<Enter>", show_btn)
            child.bind("<Leave>", hide_btn)
        self._set_task_row_hover(row, is_hover=False)

    def _set_task_row_hover(self, row: tk.Frame, is_hover: bool) -> None:
        bg = APP_THEME["bg_elevated"] if is_hover else APP_THEME["bg_row"]
        row.configure(bg=bg)
        for child in row.winfo_children():
            try:
                child.configure(bg=bg)
            except tk.TclError:
                continue

    def _is_descendant_of(self, widget: tk.Widget, parent: tk.Widget) -> bool:
        current = widget
        while current is not None:
            if current == parent:
                return True
            current_name = current.winfo_parent()
            if not current_name:
                return False
            try:
                current = current._nametowidget(current_name)
            except Exception:
                return False
        return False

    def _read_tasks_file(self, path: Path) -> list[TaskItem]:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
            tasks = payload.get("tasks", [])
            result = []
            for item in tasks:
                result.append(
                    TaskItem(
                        id=item.get("id", str(uuid.uuid4())),
                        text=item.get("text", "").strip(),
                        done=bool(item.get("done", False)),
                        created_at=item.get("created_at", datetime.now().strftime(TIME_FMT)),
                        source_day=item.get("source_day", payload.get("date", self.today)),
                    )
                )
            return [t for t in result if t.text]
        except Exception as exc:
            messagebox.showerror("读取失败", f"任务文件读取失败：{exc}")
            return []

    def _task_created_ts(self, task: TaskItem) -> float:
        try:
            return datetime.strptime(task.created_at, TIME_FMT).timestamp()
        except (TypeError, ValueError):
            return 0.0

    def _sort_tasks(self) -> None:
        self.tasks.sort(key=lambda task: (1 if task.done else 0, -self._task_created_ts(task)))

    def _append_event(self, event_type: str, data: dict) -> None:
        event = {
            "ts": datetime.now().strftime(TIME_FMT),
            "type": event_type,
            "data": data,
        }
        self.pending_events.append(event)

    def _append_jsonl(self, path: Path, obj: dict) -> None:
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(obj, ensure_ascii=False) + "\n")

    def _load_draft_text(self) -> str:
        if not self.draft_file.exists():
            return ""
        try:
            return self.draft_file.read_text(encoding="utf-8")
        except Exception:
            return ""

    def _save_draft_text(self) -> None:
        if hasattr(self, "draft_text") and not getattr(self, "_draft_force_raw", False):
            try:
                ln = int(self.draft_text.index("insert").split(".")[0])
                self._draft_sync_line_at(ln)
            except tk.TclError:
                pass
        try:
            self.draft_file.write_text(self._draft_source.rstrip("\n"), encoding="utf-8")
        except OSError:
            pass

    def _schedule_draft_save(self, _event=None) -> None:
        self._update_draft_stats()
        if hasattr(self, "_draft_save_after_id") and self._draft_save_after_id is not None:
            self.root.after_cancel(self._draft_save_after_id)
        self._draft_save_after_id = self.root.after(800, self._save_draft_text)

    def _current_signature(self) -> str:
        return json.dumps([asdict(task) for task in self.tasks], ensure_ascii=False, sort_keys=True)

    def _flush_incremental_log(self, force: bool = False) -> None:
        has_events = len(self.pending_events) > 0
        changed_since_last_save = self._current_signature() != self.last_saved_signature
        if not force and not has_events and not changed_since_last_save:
            return

        batch = {
            "ts": datetime.now().strftime(TIME_FMT),
            "type": "incremental_batch",
            "events": self.pending_events.copy(),
            "task_snapshot_count": len(self.tasks),
        }
        self._append_jsonl(self.incremental_log_file, batch)
        self.pending_events.clear()
        self.last_saved_signature = self._current_signature()
        self._record_status("已写入增量日志")

    def _manual_flush_incremental_log(self) -> None:
        self._flush_incremental_log(force=True)
        messagebox.showinfo("完成", f"已写入：{self.incremental_log_file}")

    def _copy_log_paths(self) -> None:
        text = (
            f"今日增量日志：{self.incremental_log_file}\n"
            f"每日归档日志：{self.daily_archive_log_file}"
        )
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self._record_status("日志路径已复制到剪贴板")
        messagebox.showinfo("已复制", "日志路径已复制到剪贴板")

    def _schedule_incremental_flush(self) -> None:
        self._rollover_day_if_needed()
        self._flush_incremental_log(force=False)
        self.root.after(LOG_FLUSH_INTERVAL_MS, self._schedule_incremental_flush)

    def _record_status(self, text: str) -> None:
        now = datetime.now().strftime("%H:%M:%S")
        self.status_label.configure(text=f"[{now}] {text}")

    def _on_close(self) -> None:
        self._rollover_day_if_needed()
        self._hide_draft_tools_popup()
        self._hide_log_dropdown()
        if self._alpha_save_after_id is not None:
            self.root.after_cancel(self._alpha_save_after_id)
            self._alpha_save_after_id = None
        if self._prompt_save_after_id is not None:
            self.root.after_cancel(self._prompt_save_after_id)
            self._prompt_save_after_id = None
        if hasattr(self, "weekly_prompt_template_text"):
            raw = self.weekly_prompt_template_text.get("1.0", tk.END).strip()
            if not raw:
                self.settings.pop("weekly_prompt_template", None)
            else:
                self.settings["weekly_prompt_template"] = raw
        self._persist_settings_to_disk()
        self._save_draft_text()
        self._flush_incremental_log(force=True)
        self._unregister_global_hotkey()
        self._cancel_log_periodic_refresh()
        self.root.destroy()

    def _load_settings(self) -> dict:
        default = {
            "global_toggle_hotkey": "CTRL+ALT+T",
            "focus_input_key": "/",
            "tab_switch_hotkey": "CTRL+TAB",
            "tool_json_hotkey": "CTRL+ALT+J",
            "tool_b64_encode_hotkey": "CTRL+ALT+E",
            "tool_b64_decode_hotkey": "CTRL+ALT+D",
            "tool_url_encode_hotkey": "CTRL+ALT+U",
            "tool_url_decode_hotkey": "CTRL+ALT+I",
            "window_alpha": 0.88,
        }
        if not self.settings_file.exists():
            self.settings_file.write_text(json.dumps(default, ensure_ascii=False, indent=2), encoding="utf-8")
            return default
        try:
            data = json.loads(self.settings_file.read_text(encoding="utf-8"))
            if not isinstance(data, dict):
                return default
            merged = default.copy()
            merged.update(data)
            merged["window_alpha"] = self._clamp_window_alpha(merged.get("window_alpha", default["window_alpha"]))
            return merged
        except Exception:
            return default

    def _parse_hotkey(self, hotkey: str) -> tuple[int, int] | None:
        token_to_mod = {
            "CTRL": MOD_CONTROL,
            "ALT": MOD_ALT,
            "SHIFT": MOD_SHIFT,
            "WIN": MOD_WIN,
        }
        vk_map = {
            "/": 0xBF,
            "SPACE": 0x20,
            "TAB": 0x09,
            "RETURN": 0x0D,
            "ESCAPE": 0x1B,
            "UP": 0x26,
            "DOWN": 0x28,
            "LEFT": 0x25,
            "RIGHT": 0x27,
        }
        parts = [p.strip().upper() for p in hotkey.split("+") if p.strip()]
        if not parts:
            return None
        mods = 0
        key_part = parts[-1]
        for item in parts[:-1]:
            if item not in token_to_mod:
                return None
            mods |= token_to_mod[item]
        if len(key_part) == 1 and "A" <= key_part <= "Z":
            vk = ord(key_part)
        elif len(key_part) == 1 and "0" <= key_part <= "9":
            vk = ord(key_part)
        elif key_part.startswith("F") and key_part[1:].isdigit():
            fn = int(key_part[1:])
            if 1 <= fn <= 24:
                vk = 0x6F + fn
            else:
                return None
        elif key_part in vk_map:
            vk = vk_map[key_part]
        else:
            return None
        return mods, vk

    def _register_global_hotkey(self) -> None:
        self._unregister_global_hotkey()
        parsed = self._parse_hotkey(self.settings.get("global_toggle_hotkey", "CTRL+ALT+T"))
        if parsed is None:
            self._record_status("全局快捷键配置无效，已跳过注册")
            return
        mods, vk = parsed
        self.hotkey_listener_thread = threading.Thread(
            target=self._hotkey_listener_loop,
            args=(mods, vk),
            daemon=True,
        )
        self.hotkey_listener_thread.start()
        self._record_status(f"全局快捷键已启用：{self.settings.get('global_toggle_hotkey')}")

    def _hotkey_listener_loop(self, mods: int, vk: int) -> None:
        self.hotkey_listener_thread_id = ctypes.windll.kernel32.GetCurrentThreadId()
        if not ctypes.windll.user32.RegisterHotKey(None, GLOBAL_HOTKEY_ID, mods, vk):
            self.root.after(0, lambda: self._record_status("全局快捷键注册失败，可能被占用"))
            return
        self.global_hotkey_registered = True
        msg = wintypes.MSG()
        while ctypes.windll.user32.GetMessageW(ctypes.byref(msg), None, 0, 0) != 0:
            if msg.message == WM_HOTKEY and msg.wParam == GLOBAL_HOTKEY_ID:
                self.root.after(0, self._toggle_window_visibility)
            ctypes.windll.user32.TranslateMessage(ctypes.byref(msg))
            ctypes.windll.user32.DispatchMessageW(ctypes.byref(msg))
        ctypes.windll.user32.UnregisterHotKey(None, GLOBAL_HOTKEY_ID)
        self.global_hotkey_registered = False
        self.hotkey_listener_thread_id = None

    def _toggle_window_visibility(self) -> None:
        st = self.root.state()
        if st in ("withdrawn", "iconic"):
            self._activate_window_front()
            return
        self.root.withdraw()

    def _activate_window_front(self) -> None:
        if self.root.state() == "withdrawn":
            self.root.deiconify()
        if self.root.state() == "iconic":
            self.root.deiconify()
            self.root.state("normal")
        self.root.lift()
        try:
            self.root.attributes("-topmost", True)
        except tk.TclError:
            pass
        self.root.focus_force()
        self.notebook.select(self.tasks_tab)
        self.task_entry.focus_set()

    def _unregister_global_hotkey(self) -> None:
        if self.hotkey_listener_thread_id is not None:
            WM_QUIT = 0x0012
            ctypes.windll.user32.PostThreadMessageW(self.hotkey_listener_thread_id, WM_QUIT, 0, 0)
            self.hotkey_listener_thread_id = None
        self.global_hotkey_registered = False

    def _bind_auto_save_for_settings_entry(
        self,
        target_entry: ttk.Entry,
        paired_entry_a: ttk.Entry,
        paired_entry_b: ttk.Entry,
        mode: str,
    ) -> None:
        def on_commit(_event=None):
            if mode == "global":
                new_global = target_entry.get().strip().upper()
                new_focus = paired_entry_a.get().strip()
                new_tab = paired_entry_b.get().strip().upper()
            elif mode == "focus":
                new_global = paired_entry_a.get().strip().upper()
                new_focus = target_entry.get().strip()
                new_tab = paired_entry_b.get().strip().upper()
            else:
                new_global = paired_entry_a.get().strip().upper()
                new_focus = paired_entry_b.get().strip()
                new_tab = target_entry.get().strip().upper()
            self._apply_settings_changes(new_global, new_focus, new_tab)
            return None

        target_entry.bind("<Return>", on_commit)
        target_entry.bind("<FocusOut>", on_commit)

    def _apply_settings_changes(
        self,
        new_global: str,
        new_focus: str,
        new_tab: str,
        new_tool_json: str | None = None,
        new_tool_b64_encode: str | None = None,
        new_tool_b64_decode: str | None = None,
        new_tool_url_encode: str | None = None,
        new_tool_url_decode: str | None = None,
    ) -> None:
        if not new_global or not new_focus or not new_tab:
            return
        if new_tool_json is None:
            new_tool_json = str(self.settings.get("tool_json_hotkey", "CTRL+ALT+J")).strip().upper()
        if new_tool_b64_encode is None:
            new_tool_b64_encode = str(self.settings.get("tool_b64_encode_hotkey", "CTRL+ALT+E")).strip().upper()
        if new_tool_b64_decode is None:
            new_tool_b64_decode = str(self.settings.get("tool_b64_decode_hotkey", "CTRL+ALT+D")).strip().upper()
        if new_tool_url_encode is None:
            new_tool_url_encode = str(self.settings.get("tool_url_encode_hotkey", "CTRL+ALT+U")).strip().upper()
        if new_tool_url_decode is None:
            new_tool_url_decode = str(self.settings.get("tool_url_decode_hotkey", "CTRL+ALT+I")).strip().upper()
        if not (new_tool_json and new_tool_b64_encode and new_tool_b64_decode and new_tool_url_encode and new_tool_url_decode):
            return
        if (
            new_global == self.settings.get("global_toggle_hotkey", "")
            and new_focus == self.settings.get("focus_input_key", "")
            and new_tab == self.settings.get("tab_switch_hotkey", "")
            and new_tool_json == self.settings.get("tool_json_hotkey", "")
            and new_tool_b64_encode == self.settings.get("tool_b64_encode_hotkey", "")
            and new_tool_b64_decode == self.settings.get("tool_b64_decode_hotkey", "")
            and new_tool_url_encode == self.settings.get("tool_url_encode_hotkey", "")
            and new_tool_url_decode == self.settings.get("tool_url_decode_hotkey", "")
        ):
            return
        if self._parse_hotkey(new_global) is None:
            messagebox.showwarning("提示", "全局快捷键格式无效", parent=self.root)
            return
        if self._hotkey_to_tk_sequence(new_tab) is None:
            messagebox.showwarning("提示", "Tab 切换快捷键格式无效", parent=self.root)
            return
        for label, hotkey in (
            ("JSON 格式化", new_tool_json),
            ("Base64 编码", new_tool_b64_encode),
            ("Base64 解码", new_tool_b64_decode),
            ("URL 编码", new_tool_url_encode),
            ("URL 解码", new_tool_url_decode),
        ):
            if self._hotkey_to_tk_sequence(hotkey) is None:
                messagebox.showwarning("提示", f"{label} 快捷键格式无效", parent=self.root)
                return
        self.settings["global_toggle_hotkey"] = new_global
        self.settings["focus_input_key"] = new_focus
        self.settings["tab_switch_hotkey"] = new_tab
        self.settings["tool_json_hotkey"] = new_tool_json
        self.settings["tool_b64_encode_hotkey"] = new_tool_b64_encode
        self.settings["tool_b64_decode_hotkey"] = new_tool_b64_decode
        self.settings["tool_url_encode_hotkey"] = new_tool_url_encode
        self.settings["tool_url_decode_hotkey"] = new_tool_url_decode
        self.settings_file.write_text(json.dumps(self.settings, ensure_ascii=False, indent=2), encoding="utf-8")
        self._setup_shortcuts()
        self._register_global_hotkey()
        self._record_status("快捷键设置已自动保存")

    def _record_hotkey_into_entry(self, entry: ttk.Entry, mode: str) -> None:
        all_entries = [
            self.global_hotkey_entry,
            self.focus_key_entry,
            self.tab_key_entry,
            getattr(self, "tool_json_hotkey_entry", None),
            getattr(self, "tool_b64_encode_hotkey_entry", None),
            getattr(self, "tool_b64_decode_hotkey_entry", None),
            getattr(self, "tool_url_encode_hotkey_entry", None),
            getattr(self, "tool_url_decode_hotkey_entry", None),
        ]
        for e in all_entries:
            if e is None:
                continue
            e.unbind("<KeyPress>")
        tip = "请按一个组合键..." if mode in {"global", "tab", "combo"} else "请按一个按键..."
        self._record_status(tip)
        entry.focus_set()
        entry.icursor(tk.END)

        def on_key(event) -> str:
            if mode in {"global", "tab", "combo"}:
                hotkey = self._build_global_hotkey_text_from_event(event)
                if not hotkey:
                    return "break"
                entry.delete(0, tk.END)
                entry.insert(0, hotkey)
            else:
                key_text = self._build_focus_key_text_from_event(event)
                if not key_text:
                    return "break"
                entry.delete(0, tk.END)
                entry.insert(0, key_text)
            entry.unbind("<KeyPress>")
            self._save_shortcut_settings_from_entries()
            self._record_status("按键录制完成")
            return "break"

        entry.bind("<KeyPress>", on_key)

    def _save_shortcut_settings_from_entries(self) -> None:
        new_global = self.global_hotkey_entry.get().strip().upper()
        new_focus = self.focus_key_entry.get().strip()
        new_tab = self.tab_key_entry.get().strip().upper()
        new_tool_json = self.tool_json_hotkey_entry.get().strip().upper()
        new_tool_b64_encode = self.tool_b64_encode_hotkey_entry.get().strip().upper()
        new_tool_b64_decode = self.tool_b64_decode_hotkey_entry.get().strip().upper()
        new_tool_url_encode = self.tool_url_encode_hotkey_entry.get().strip().upper()
        new_tool_url_decode = self.tool_url_decode_hotkey_entry.get().strip().upper()
        self._apply_settings_changes(
            new_global,
            new_focus,
            new_tab,
            new_tool_json,
            new_tool_b64_encode,
            new_tool_b64_decode,
            new_tool_url_encode,
            new_tool_url_decode,
        )

    def _build_global_hotkey_text_from_event(self, event) -> str | None:
        mods = []
        # Tk 的 state 位：Shift=0x0001, Control=0x0004, Alt(Mod1)=0x0008
        if event.state & 0x0004:
            mods.append("CTRL")
        if event.state & 0x0008:
            mods.append("ALT")
        if event.state & 0x0001:
            mods.append("SHIFT")

        key = self._event_to_hotkey_key(event)
        if not key:
            return None
        if key in {"SHIFT", "CTRL", "ALT", "WIN"}:
            return None
        return "+".join(mods + [key]) if mods else key

    def _build_focus_key_text_from_event(self, event) -> str | None:
        key = self._event_to_hotkey_key(event)
        if not key:
            return None
        if key == "OEM_2":
            return "/"
        return key.lower() if len(key) == 1 else key

    def _event_to_hotkey_key(self, event) -> str | None:
        keysym = (event.keysym or "").upper()
        if keysym == "SLASH":
            return "/"
        if len(keysym) == 1 and ("A" <= keysym <= "Z" or "0" <= keysym <= "9"):
            return keysym
        if keysym.startswith("F") and keysym[1:].isdigit():
            return keysym
        if keysym in {"SPACE", "TAB", "RETURN", "ESCAPE", "UP", "DOWN", "LEFT", "RIGHT"}:
            return keysym
        return None

    def _setup_window_appearance(self) -> None:
        self.root.configure(bg=APP_THEME["bg_root"])
        self.root.attributes("-alpha", self._clamp_window_alpha(self.settings.get("window_alpha", 0.88)))
        self.root.attributes("-topmost", True)
        self.root.overrideredirect(True)
        self.root.after(10, self._try_enable_windows_blur)

    def _setup_styles(self) -> None:
        style = ttk.Style()
        if "clam" in style.theme_names():
            style.theme_use("clam")

        t = APP_THEME
        bg_main = t["bg_main"]
        bg_elev = t["bg_elevated"]
        bg_canvas = t["bg_canvas"]
        bg_row = t["bg_row"]
        border = t["border"]
        accent = t["accent"]
        accent_h = t["accent_hover"]
        fg = t["fg"]
        fg_muted = t["fg_muted"]

        style.configure("Main.TFrame", background=bg_main)
        style.configure("TFrame", background=bg_main)
        style.configure("CanvasInner.TFrame", background=bg_canvas)
        style.configure("CanvasHint.TLabel", background=bg_canvas, foreground=fg_muted, font=UI_FONT_SM)
        style.configure("TLabel", background=bg_main, foreground=fg)
        style.configure("Title.TLabel", background=bg_main, foreground=fg)
        style.configure("Status.TLabel", background=bg_main, foreground=fg_muted, font=UI_FONT_SM)
        style.configure(
            "App.TRadiobutton",
            background=bg_main,
            foreground=fg,
            font=UI_FONT_SM,
            focuscolor=accent,
        )
        style.map(
            "App.TRadiobutton",
            background=[("active", bg_main), ("selected", bg_main)],
            foreground=[("active", accent_h), ("selected", fg)],
        )
        style.configure(
            "App.TCheckbutton",
            background=bg_main,
            foreground=fg_muted,
            font=UI_FONT_SM,
            focuscolor=accent,
        )
        style.map(
            "App.TCheckbutton",
            background=[("active", bg_main), ("selected", bg_main)],
            foreground=[("active", fg), ("selected", fg)],
        )

        style.configure(
            "TButton",
            background=bg_elev,
            foreground=fg,
            bordercolor=border,
            lightcolor=bg_elev,
            darkcolor=bg_elev,
            focuscolor=accent,
            padding=(10, 6),
            font=UI_FONT,
        )
        style.map(
            "TButton",
            background=[("active", "#363d50"), ("pressed", "#1f232c")],
            foreground=[("disabled", "#6d7688")],
        )

        style.configure(
            "Secondary.TButton",
            background=bg_main,
            foreground=fg_muted,
            bordercolor=border,
            lightcolor=bg_main,
            darkcolor=bg_main,
            focuscolor=accent,
            padding=(8, 5),
            font=UI_FONT_SM,
        )
        style.map(
            "Secondary.TButton",
            background=[("active", bg_elev), ("pressed", "#22262f")],
            foreground=[("active", fg)],
        )

        style.configure(
            "Mini.TButton",
            background=bg_main,
            foreground=fg_muted,
            bordercolor=border,
            lightcolor=bg_main,
            darkcolor=bg_main,
            focuscolor=accent,
            padding=(6, 4),
            font=("Microsoft YaHei UI", 11),
        )
        style.map(
            "Mini.TButton",
            background=[("active", "#363d50"), ("pressed", "#2a303c")],
            foreground=[("active", accent_h)],
        )

        style.configure(
            "TEntry",
            fieldbackground=bg_elev,
            foreground=fg,
            insertcolor=fg,
            bordercolor=border,
            lightcolor=bg_elev,
            darkcolor=bg_elev,
            padding=(8, 6),
            font=UI_FONT,
        )
        style.map(
            "TEntry",
            fieldbackground=[("focus", "#343b4d")],
            bordercolor=[("focus", accent)],
            lightcolor=[("focus", accent_h)],
            darkcolor=[("focus", accent)],
        )

        style.configure(
            "App.TCombobox",
            fieldbackground=bg_elev,
            background=bg_elev,
            foreground=fg,
            bordercolor=border,
            lightcolor=bg_elev,
            darkcolor=bg_elev,
            arrowcolor=fg_muted,
            padding=(6, 4),
            font=UI_FONT,
        )
        style.map(
            "App.TCombobox",
            fieldbackground=[("readonly", bg_elev), ("focus", "#343b4d")],
            bordercolor=[("focus", accent)],
            arrowcolor=[("focus", accent)],
        )

        style.configure(
            "Vertical.TScrollbar",
            background=bg_elev,
            troughcolor=bg_canvas,
            bordercolor=border,
            arrowcolor=fg_muted,
            troughrelief="flat",
            relief="flat",
        )
        style.map(
            "Vertical.TScrollbar",
            background=[("active", "#363d50"), ("pressed", "#2a303c")],
            arrowcolor=[("active", accent)],
        )

        style.configure(
            "Horizontal.TScale",
            background=bg_main,
            troughcolor=bg_canvas,
            bordercolor=border,
            lightcolor=accent,
            darkcolor=bg_elev,
        )
        style.map(
            "Horizontal.TScale",
            background=[("active", bg_elev)],
            lightcolor=[("pressed", accent_h)],
        )

        self._notebook_style_used = "TNotebook"
        try:
            style.configure(
                "App.TNotebook",
                parent="TNotebook",
                background=bg_main,
                borderwidth=0,
                relief="flat",
                tabmargins=[0, 0, 0, 0],
                lightcolor=bg_main,
                darkcolor=bg_main,
                bordercolor=bg_main,
            )
            self._notebook_style_used = "App.TNotebook"
        except tk.TclError:
            style.configure(
                "TNotebook",
                background=bg_main,
                borderwidth=0,
                relief="flat",
                tabmargins=[0, 0, 0, 0],
                lightcolor=bg_main,
                darkcolor=bg_main,
                bordercolor=bg_main,
            )

        style.configure(
            "TNotebook.Tab",
            background=bg_elev,
            foreground=fg_muted,
            padding=[12, 6],
            borderwidth=0,
            font=UI_FONT_SM,
            lightcolor=bg_elev,
            darkcolor=bg_elev,
            bordercolor=bg_elev,
        )
        style.map(
            "TNotebook.Tab",
            background=[("selected", bg_canvas), ("active", "#323848")],
            foreground=[("selected", fg), ("active", fg)],
            lightcolor=[("selected", bg_canvas), ("active", "#323848")],
            darkcolor=[("selected", bg_canvas), ("active", "#323848")],
            bordercolor=[("selected", bg_canvas), ("active", "#323848")],
        )

        style.configure(
            "TabClose.TButton",
            background=bg_elev,
            foreground=fg_muted,
            bordercolor=bg_elev,
            lightcolor=bg_elev,
            darkcolor=bg_elev,
            focuscolor=accent,
            padding=(2, 0),
            font=("Microsoft YaHei UI", 10),
        )
        style.map(
            "TabClose.TButton",
            background=[("active", "#363d50"), ("pressed", "#2a303c")],
            foreground=[("active", accent_h)],
        )

    def _try_enable_windows_blur(self) -> None:
        # 尝试在 Windows 上开启 DWM 模糊；失败时保持半透明降级效果
        try:
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())

            class DWM_BLURBEHIND(ctypes.Structure):
                _fields_ = [
                    ("dwFlags", ctypes.c_uint32),
                    ("fEnable", ctypes.c_int),
                    ("hRgnBlur", ctypes.c_void_p),
                    ("fTransitionOnMaximized", ctypes.c_int),
                ]

            DWM_BB_ENABLE = 0x00000001
            bb = DWM_BLURBEHIND(DWM_BB_ENABLE, 1, None, 0)
            ctypes.windll.dwmapi.DwmEnableBlurBehindWindow(hwnd, ctypes.byref(bb))
        except Exception:
            pass


def main() -> None:
    if not _acquire_single_instance_lock():
        ctypes.windll.user32.MessageBoxW(
            0,
            "每日任务助手已在运行，无需重复启动。",
            "启动提示",
            0x00000040,
        )
        return
    root = tk.Tk()
    DailyTaskAssistant(root)
    root.mainloop()


if __name__ == "__main__":
    main()
