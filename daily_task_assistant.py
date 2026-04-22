import json
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

        draft_frame = ttk.Frame(self.draft_tab, style="Main.TFrame")
        draft_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        ttk.Label(draft_frame, text="草稿区（不记录日志）", style="Status.TLabel").pack(anchor=tk.W, pady=(0, 4))
        self.draft_text = tk.Text(
            draft_frame,
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
        )
        self.draft_text.pack(fill=tk.BOTH, expand=True)
        self.draft_text.insert("1.0", self._load_draft_text())
        self.draft_text.bind("<KeyRelease>", self._schedule_draft_save)

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
        raw = self.draft_text.get("1.0", tk.END).strip()
        if not raw:
            return
        try:
            obj = json.loads(raw)
            formatted = json.dumps(obj, ensure_ascii=False, indent=2)
        except json.JSONDecodeError:
            return
        self.draft_text.delete("1.0", tk.END)
        self.draft_text.insert("1.0", formatted)
        self._save_draft_text()
        self._record_status("草稿 JSON 已格式化")

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
        self._set_log_text("\n".join(lines))
        self._weekly_tasks_plain = ""
        self._update_weekly_prompt_preview("")

    def _set_log_text(self, content: str) -> None:
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.delete("1.0", tk.END)
        self.log_text.insert("1.0", content)
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
            self._set_log_text("暂无周数据，请先选择自然周。")
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
        self._set_log_text("\n".join(all_lines).rstrip())
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
        yesterday_file = self.data_dir / f"tasks_{yesterday_date}.json"

        if yesterday_file.exists():
            yesterday_tasks = self._read_tasks_file(yesterday_file)
            self._archive_yesterday(yesterday_date, yesterday_tasks)

            carry_over = [
                TaskItem(
                    id=str(uuid.uuid4()),
                    text=item.text,
                    done=False,
                    created_at=datetime.now().strftime(TIME_FMT),
                    source_day=yesterday_date,
                )
                for item in yesterday_tasks
                if not item.done
            ]
            self.tasks.extend(carry_over)
            self._sort_tasks()

            if carry_over:
                self._append_event(
                    "carry_over_from_yesterday",
                    {
                        "from_day": yesterday_date,
                        "carried_count": len(carry_over),
                        "task_texts": [item.text for item in carry_over],
                    },
                )
            self._record_status(f"已继承昨天未完成任务 {len(carry_over)} 项")
        else:
            self._record_status("未找到昨天任务文件，已创建新的一天")

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
        try:
            content = self.draft_text.get("1.0", tk.END).rstrip("\n")
            self.draft_file.write_text(content, encoding="utf-8")
        except Exception:
            pass

    def _schedule_draft_save(self, _event=None) -> None:
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
        try:
            focused = self.root.focus_get()
            in_app = focused is not None and focused.winfo_toplevel() == self.root
        except tk.TclError:
            in_app = False
        if in_app:
            self.root.withdraw()
        else:
            self._activate_window_front()

    def _activate_window_front(self) -> None:
        if self.root.state() == "withdrawn":
            self.root.deiconify()
        if self.root.state() == "iconic":
            self.root.deiconify()
            self.root.state("normal")
        self.root.lift()
        try:
            self.root.attributes("-topmost", True)
            self.root.after(80, lambda: self._clear_topmost_if_alive())
        except tk.TclError:
            pass
        self.root.focus_force()
        self.notebook.select(self.tasks_tab)
        self.task_entry.focus_set()

    def _clear_topmost_if_alive(self) -> None:
        if not self.root.winfo_exists():
            return
        try:
            self.root.attributes("-topmost", False)
        except tk.TclError:
            pass

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
