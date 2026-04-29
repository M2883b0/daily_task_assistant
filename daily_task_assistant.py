import json
import re
import difflib
import uuid
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from pathlib import Path
import ctypes
import ctypes.wintypes as wintypes
import threading
import tkinter as tk
from tkinter import ttk, messagebox


DATE_FMT = "%Y-%m-%d"
TIME_FMT = "%Y-%m-%d %H:%M:%S"
LOG_FLUSH_INTERVAL_MS = 3 * 1000
WM_HOTKEY = 0x0312
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_SHIFT = 0x0004
MOD_WIN = 0x0008
GLOBAL_HOTKEY_ID = 1

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
        self._draft_last_nav_line: int | None = None
        self._draft_active_raw_line: int | None = None
        self._draft_return_press_col: int | None = None
        self._draft_markdown_return_handled: bool = False
        self._draft_markdown_delete_handled: bool = False

        self._build_ui()
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
        ttk.Label(draft_toolbar, text="工具", style="Status.TLabel").pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(
            draft_toolbar,
            text="JSON 格式化",
            command=self._draft_format_json,
            style="Secondary.TButton",
        ).pack(side=tk.LEFT)
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
            undo=True,
            autoseparators=True,
            maxundo=-1,
        )
        self.draft_text.pack(fill=tk.BOTH, expand=True)
        self._draft_source = self._load_draft_text()
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

        log_toolbar = ttk.Frame(self.logs_tab, style="Main.TFrame")
        log_toolbar.pack(fill=tk.X, pady=(0, 8))
        ttk.Label(log_toolbar, text="视图", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_mode_var = tk.StringVar(value="单日")
        self.log_mode_combo = ttk.Combobox(
            log_toolbar,
            textvariable=self.log_mode_var,
            values=("单日", "周汇总"),
            state="readonly",
            width=8,
            style="App.TCombobox",
        )
        self.log_mode_combo.pack(side=tk.LEFT, padx=(4, 12))
        self.log_mode_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_log_mode_changed())

        self.log_date_frame = ttk.Frame(log_toolbar, style="Main.TFrame")
        ttk.Label(self.log_date_frame, text="日期", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_day_var = tk.StringVar(value=self.today)
        self.log_day_combo = ttk.Combobox(
            self.log_date_frame,
            textvariable=self.log_day_var,
            state="readonly",
            width=14,
            style="App.TCombobox",
        )
        self.log_day_combo.pack(side=tk.LEFT, padx=(6, 0))
        self.log_day_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_logs_tab_data())

        self.log_week_frame = ttk.Frame(log_toolbar, style="Main.TFrame")
        ttk.Label(self.log_week_frame, text="自然周", style="Status.TLabel").pack(side=tk.LEFT)
        self.log_week_var = tk.StringVar()
        self.log_week_combo = ttk.Combobox(
            self.log_week_frame,
            textvariable=self.log_week_var,
            state="readonly",
            width=32,
            style="App.TCombobox",
        )
        self.log_week_combo.pack(side=tk.LEFT, padx=(6, 0))
        self.log_week_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_log_week_view())

        self.log_text = tk.Text(
            self.logs_tab,
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
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self.log_text.configure(state=tk.DISABLED)

        self.weekly_prompt_frame = ttk.Frame(self.logs_tab, style="Main.TFrame")
        ttk.Label(
            self.weekly_prompt_frame,
            text="周报：周汇总模式下预览完整提示词，点「一键复制提示词」粘贴给 AI。",
            style="Status.TLabel",
        ).pack(anchor=tk.W, pady=(0, 4))
        self.weekly_prompt_preview = tk.Text(
            self.weekly_prompt_frame,
            height=6,
            bg=th["bg_elevated"],
            fg=th["fg_muted"],
            insertbackground=th["fg"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=th["border"],
            bd=0,
            font=UI_FONT_SM,
            padx=8,
            pady=6,
            wrap="word",
        )
        self.weekly_prompt_preview.pack(fill=tk.X, pady=(0, 6))
        self.weekly_prompt_preview.configure(state=tk.DISABLED)
        prompt_btn_row = ttk.Frame(self.weekly_prompt_frame, style="Main.TFrame")
        prompt_btn_row.pack(anchor=tk.W, fill=tk.X)
        ttk.Button(
            prompt_btn_row,
            text="一键复制提示词",
            command=self._copy_weekly_ai_prompt,
            style="Secondary.TButton",
        ).pack(side=tk.LEFT)
        ttk.Label(
            prompt_btn_row,
            text="（模板可在「设置」中修改）",
            style="Status.TLabel",
        ).pack(side=tk.LEFT, padx=(8, 0))

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

    def _build_settings_tab(self, frame: ttk.Frame) -> None:
        inner = ttk.Frame(frame, padding=8, style="Main.TFrame")
        inner.pack(fill=tk.BOTH, expand=True)

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

        self._bind_auto_save_for_settings_entry(
            self.global_hotkey_entry, self.focus_key_entry, self.tab_key_entry, mode="global"
        )
        self._bind_auto_save_for_settings_entry(
            self.focus_key_entry, self.global_hotkey_entry, self.tab_key_entry, mode="focus"
        )
        self._bind_auto_save_for_settings_entry(
            self.tab_key_entry, self.global_hotkey_entry, self.focus_key_entry, mode="tab"
        )

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
        try:
            cur_ln = int(self.draft_text.index("insert").split(".")[0])
        except tk.TclError:
            cur_ln = 1
        self._draft_sync_line_at(cur_ln)
        raw = self._draft_source.strip()
        if not raw:
            return
        try:
            obj = json.loads(raw)
            for _ in range(2):
                if not isinstance(obj, str):
                    break
                s = obj.strip()
                if not s:
                    break
                try:
                    obj2 = json.loads(s)
                except json.JSONDecodeError:
                    break
                obj = obj2
            formatted = json.dumps(obj, ensure_ascii=False, indent=2)
        except json.JSONDecodeError:
            return
        self._draft_source = formatted
        self._draft_force_raw = True
        if hasattr(self, "_draft_view_mode_var"):
            self._draft_view_mode_var.set("source")
        self._draft_refresh_view()
        self._save_draft_text()
        self._update_draft_stats()
        self._record_status("草稿 JSON 已格式化")

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
                self._draft_source = self.draft_text.get("1.0", "end-1c")
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
        w.tag_configure("md_code_block", background=APP_THEME["bg_elevated"], font=MONO_FONT, lmargin1=10, lmargin2=10)
        w.tag_configure("md_code_fence", foreground=APP_THEME["fg_muted"], font=MONO_FONT)
        w.tag_configure("md_bold", font=("Microsoft YaHei UI", 10, "bold"))
        w.tag_configure("md_italic", font=("Microsoft YaHei UI", 10, "italic"))
        w.tag_configure("md_strike", overstrike=1)
        w.tag_configure("md_link", foreground=APP_THEME["accent"], underline=1)
        w.tag_configure("md_hr", foreground=APP_THEME["fg_muted"])

    def _insert_markdown_inline(self, widget: tk.Text, text: str, base_tags: tuple[str, ...] = ()) -> None:
        token_re = re.compile(r"(`[^`]+`|\*\*[^*]+\*\*|\*[^*]+\*|~~[^~]+~~|\[[^\]]+\]\([^)]+\))")
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

    def _draft_sync_line_at(self, line_1based: int) -> None:
        if self._draft_refreshing:
            return
        if self._draft_force_raw:
            self._draft_source = self.draft_text.get("1.0", "end-1c")
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
        parts[line_1based - 1] = raw
        self._draft_source = "\n".join(parts)

    def _draft_apply_source_line_break(self, line_1based: int, col: int) -> None:
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
        self._draft_source = "\n".join(parts)

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
        self._draft_source = "\n".join(parts)

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
            in_code = False

            for i, line in enumerate(lines):
                lineno = i + 1
                stripped = line.strip()
                is_fence = stripped.startswith("```")
                show_raw = self._draft_force_raw or (lineno == line_no)

                if is_fence:
                    in_code = not in_code
                    if show_raw:
                        self.draft_text.insert("end", line + "\n")
                    else:
                        self.draft_text.insert("end", line + "\n", ("md_code_fence",))
                    continue

                if show_raw:
                    self.draft_text.insert("end", line + "\n")
                    continue

                if in_code:
                    self.draft_text.insert("end", (line if line else " ") + "\n", ("md_code_block",))
                    continue

                self._draft_append_rendered_markdown_line(self.draft_text, line)
                self.draft_text.insert("end", "\n")

            self.draft_text.mark_set("insert", f"{line_no}.{col}")
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
            self._draft_source = self.draft_text.get("1.0", "end-1c")
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
            self._draft_refresh_view(focus_line=cur, focus_col=col)
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

        m_ul = re.match(r"^(\s*)([-*+])\s+(.*)$", line)
        if m_ul:
            indent, marker, rest = m_ul.group(1), m_ul.group(2), m_ul.group(3)
            if rest.strip() == "":
                lines[i] = indent
                self._draft_source = "\n".join(lines)
                self._draft_refresh_view(focus_line=ln, focus_col=len(indent))
            else:
                lines.insert(i + 1, f"{indent}{marker} ")
                self._draft_source = "\n".join(lines)
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
                self._draft_source = "\n".join(lines)
                self._draft_refresh_view(focus_line=ln, focus_col=len(indent))
            else:
                n = int(num_s) + 1
                lines.insert(i + 1, f"{indent}{n}. ")
                self._draft_source = "\n".join(lines)
                new_ln = ln + 1
                new_text = lines[new_ln - 1]
                self._draft_refresh_view(focus_line=new_ln, focus_col=len(new_text))
            self._draft_markdown_return_handled = True
            return "break"

        self._draft_apply_source_line_break(ln, col)
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
                    self._draft_source = self._draft_source[:src_start] + self._draft_source[src_end:]
                    focus_ln, focus_col = self._draft_source_line_col_from_offset(src_start)
                    self._draft_refresh_view(focus_line=focus_ln, focus_col=focus_col)
                    self._draft_markdown_delete_handled = True
                    return "break"
                return "break"
        except tk.TclError:
            pass

        self._draft_sync_line_at(ln)
        lines = self._draft_source.split("\n")
        i = ln - 1
        if i < 0 or i >= len(lines):
            return None

        if ks == "BackSpace" and col == 0 and ln > 1:
            prev_text = lines[i - 1]
            lines[i - 1] = prev_text + lines[i]
            del lines[i]
            self._draft_source = "\n".join(lines)
            self._draft_refresh_view(focus_line=ln - 1, focus_col=len(prev_text))
            self._draft_markdown_delete_handled = True
            return "break"

        if ks == "Delete" and col == len(lines[i]) and ln < len(lines):
            lines[i] = lines[i] + lines[i + 1]
            del lines[i + 1]
            self._draft_source = "\n".join(lines)
            self._draft_refresh_view(focus_line=ln, focus_col=col)
            self._draft_markdown_delete_handled = True
            return "break"
        return None

    def _setup_draft_editor_features(self, draft_frame: ttk.Frame) -> None:
        th = APP_THEME

        self._draft_search_frame = ttk.Frame(draft_frame, style="Main.TFrame")

        self._draft_find_var = tk.StringVar()
        self._draft_replace_var = tk.StringVar()

        row1 = ttk.Frame(self._draft_search_frame, style="Main.TFrame")
        row1.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(row1, text="查找", style="Status.TLabel").pack(side=tk.LEFT, padx=(0, 6))
        self._draft_find_entry = ttk.Entry(row1, textvariable=self._draft_find_var)
        self._draft_find_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
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
        self.draft_text.bind("<Escape>", lambda _e: self._draft_escape_handler())

        self._draft_find_entry.bind("<Return>", lambda _e: self._draft_find_next(backward=False))
        self._draft_find_entry.bind("<Shift-Return>", lambda _e: self._draft_find_next(backward=True))
        self._draft_find_entry.bind("<Escape>", lambda _e: self._hide_draft_search())
        self._draft_replace_entry.bind("<Escape>", lambda _e: self._hide_draft_search())

        self._draft_find_var.trace_add("write", lambda *_a: self._draft_highlight_all_matches())

        self.draft_text.bind("<KeyPress-Return>", self._draft_handle_return)
        self.draft_text.bind("<KeyPress-KP_Enter>", self._draft_handle_return)
        self.draft_text.bind("<KeyPress-BackSpace>", self._draft_handle_backspace_delete)
        self.draft_text.bind("<KeyPress-Delete>", self._draft_handle_backspace_delete)

        self.draft_text.bind("<KeyRelease>", self._draft_on_editor_key_release, add=True)
        self.draft_text.bind("<ButtonRelease-1>", lambda _e: self._draft_on_editor_click(), add=True)
        self.draft_text.bind("<B1-Motion>", self._draft_on_editor_drag_select, add=True)

    def _draft_escape_handler(self) -> str | None:
        if getattr(self, "_draft_search_visible", False):
            return self._hide_draft_search()
        return None

    def _draft_undo(self) -> str:
        try:
            self.draft_text.edit_undo()
        except tk.TclError:
            pass
        if self._draft_force_raw:
            self._draft_source = self.draft_text.get("1.0", "end-1c")
        else:
            try:
                self._draft_sync_line_at(int(self.draft_text.index("insert").split(".")[0]))
            except tk.TclError:
                pass
            self._draft_refresh_view()
        self._update_draft_stats()
        return "break"

    def _draft_redo(self) -> str:
        try:
            self.draft_text.edit_redo()
        except tk.TclError:
            pass
        if self._draft_force_raw:
            self._draft_source = self.draft_text.get("1.0", "end-1c")
        else:
            try:
                self._draft_sync_line_at(int(self.draft_text.index("insert").split(".")[0]))
            except tk.TclError:
                pass
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
        self._draft_source = self.draft_text.get("1.0", "end-1c")
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
                if sel == needle:
                    self.draft_text.delete(tk.SEL_FIRST, tk.SEL_LAST)
                    self.draft_text.insert(tk.INSERT, repl)
            self._draft_find_next(backward=False)
            self._draft_highlight_all_matches()
            self._draft_source = self.draft_text.get("1.0", "end-1c")
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
            new_content = content.replace(needle, repl)
            if new_content != content:
                self.draft_text.delete("1.0", tk.END)
                self.draft_text.insert("1.0", new_content)
            self._draft_highlight_all_matches()
            self._draft_source = self.draft_text.get("1.0", "end-1c")
            self._update_draft_stats()
            self._schedule_draft_save()
        except tk.TclError:
            pass
        return "break"

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
        self._update_weekly_prompt_preview("")

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
            self.weekly_prompt_frame.pack(fill=tk.X, pady=(8, 0), after=self.log_text)
        else:
            self.log_week_frame.pack_forget()
            self.log_date_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self.weekly_prompt_frame.pack_forget()

    def _on_log_mode_changed(self, _event=None) -> None:
        self._apply_log_mode_layout()
        self._reload_log_comboboxes()
        self._refresh_logs_tab_data()

    def _reload_log_comboboxes(self) -> None:
        dates = self._collect_log_dates()
        day_values = dates if dates else [self.today]
        self.log_day_combo["values"] = day_values
        cur_day = self.log_day_var.get().strip()
        if cur_day not in day_values:
            self.log_day_var.set(day_values[0])

        week_opts = self._collect_week_options()
        self._log_week_key_by_label = {lbl: key for key, lbl in week_opts}
        labels = [lbl for _key, lbl in week_opts]
        self.log_week_combo["values"] = labels
        cur_week = self.log_week_var.get().strip()
        if not labels:
            self.log_week_var.set("")
        elif cur_week not in labels:
            self.log_week_var.set(labels[0])

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
            self._update_weekly_prompt_preview("")
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
        self._update_weekly_prompt_preview(full_prompt)

    def _update_weekly_prompt_preview(self, text: str) -> None:
        self.weekly_prompt_preview.configure(state=tk.NORMAL)
        self.weekly_prompt_preview.delete("1.0", tk.END)
        self.weekly_prompt_preview.insert("1.0", text or "（切换到「周汇总」并选择周后，此处显示可复制提示词预览）")
        self.weekly_prompt_preview.configure(state=tk.DISABLED)

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

    def _switch_tab_by_shortcut(self, _event=None) -> str:
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
        if not self.root.winfo_viewable():
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

    def _on_toggle_task(self, task_id: str) -> None:
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
        self._flush_incremental_log(force=False)
        self.root.after(LOG_FLUSH_INTERVAL_MS, self._schedule_incremental_flush)

    def _record_status(self, text: str) -> None:
        now = datetime.now().strftime("%H:%M:%S")
        self.status_label.configure(text=f"[{now}] {text}")

    def _on_close(self) -> None:
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
    ) -> None:
        if not new_global or not new_focus or not new_tab:
            return
        if (
            new_global == self.settings.get("global_toggle_hotkey", "")
            and new_focus == self.settings.get("focus_input_key", "")
            and new_tab == self.settings.get("tab_switch_hotkey", "")
        ):
            return
        if self._parse_hotkey(new_global) is None:
            messagebox.showwarning("提示", "全局快捷键格式无效", parent=self.root)
            return
        if self._hotkey_to_tk_sequence(new_tab) is None:
            messagebox.showwarning("提示", "Tab 切换快捷键格式无效", parent=self.root)
            return
        self.settings["global_toggle_hotkey"] = new_global
        self.settings["focus_input_key"] = new_focus
        self.settings["tab_switch_hotkey"] = new_tab
        self.settings_file.write_text(json.dumps(self.settings, ensure_ascii=False, indent=2), encoding="utf-8")
        self._setup_shortcuts()
        self._register_global_hotkey()
        self._record_status("快捷键设置已自动保存")

    def _record_hotkey_into_entry(self, entry: ttk.Entry, mode: str) -> None:
        for e in (self.global_hotkey_entry, self.focus_key_entry, self.tab_key_entry):
            e.unbind("<KeyPress>")
        tip = "请按一个组合键..." if mode in {"global", "tab"} else "请按一个按键..."
        self._record_status(tip)
        entry.focus_set()
        entry.icursor(tk.END)

        def on_key(event) -> str:
            if mode in {"global", "tab"}:
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
            current_global = self.settings.get("global_toggle_hotkey", "CTRL+ALT+T")
            current_focus = self.settings.get("focus_input_key", "/")
            current_tab = self.settings.get("tab_switch_hotkey", "CTRL+TAB")
            if mode == "global":
                new_global = entry.get().strip().upper()
                new_focus = current_focus
                new_tab = current_tab
            elif mode == "tab":
                new_global = current_global
                new_focus = current_focus
                new_tab = entry.get().strip().upper()
            else:
                new_global = current_global
                new_focus = entry.get().strip()
                new_tab = current_tab
            self._apply_settings_changes(new_global, new_focus, new_tab)
            self._record_status("按键录制完成")
            return "break"

        entry.bind("<KeyPress>", on_key)

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
    root = tk.Tk()
    DailyTaskAssistant(root)
    root.mainloop()


if __name__ == "__main__":
    main()
