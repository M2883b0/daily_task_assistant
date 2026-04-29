# 每日任务助手（Daily Task Assistant）

一个基于 `tkinter` 的 Windows 桌面小工具，用于记录每日任务、快速勾选进度，并按周导出可直接给 AI 使用的周报提示词。

## 功能简介

- 每日任务新增、勾选完成、删除、双击行内编辑
- 草稿页支持 Markdown 实时渲染（当前光标行保持源码编辑）
- 草稿页支持 Markdown/源码双视图切换
- 草稿页支持 JSON 格式化
- 草稿页支持字数统计与选中字符统计
- 草稿页支持查找替换（Ctrl+F / Ctrl+H）与匹配高亮
- 日志页支持单日查看与周汇总
- 周汇总可一键复制 AI 周报提示词
- 支持自定义周报提示词模板（含 `{tasks_block}` 占位符）
- 支持全局热键唤起窗口、切换标签快捷键、窗口透明度设置

## 最近更新（自上次提交以来）

- 草稿编辑器升级为“所见即所得 + 当前行源码编辑”模式，提升 Markdown 编写体验
- 新增草稿区视图切换：可在工具栏手动切换 `Markdown` 与 `源码` 模式
- 新增草稿统计信息：显示源码字数与当前选中字符数
- 优化草稿搜索替换流程：搜索时自动进入源码视图，关闭后恢复原视图模式
- 完善草稿编辑交互：改进回车、撤销/重做、Esc 行为与内容保存一致性

## 运行环境

- Windows 10/11
- Python 3.10+（建议）
- 仅使用标准库，无第三方依赖

## 快速启动

```bash
python daily_task_assistant.py
```

或使用无控制台入口：

```bash
pythonw daily_task_assistant.pyw
```

## 数据与配置说明

- 运行后会自动创建：
  - `data/tasks_YYYY-MM-DD.json`（每日任务）
  - `data/draft.txt`（草稿内容）
  - `data/settings.json`（当前本机配置）
  - `logs/incremental_YYYY-MM-DD.jsonl`（增量日志）
  - `logs/daily_archive.jsonl`（归档日志）
- 仓库内提供默认配置模板：`data/settings.default.json`
- Git 已忽略运行时数据与日志，避免上传个人记录

## 默认快捷键

- 显示/隐藏窗口：`CTRL + ALT + T`
- 聚焦输入框：`/`
- 切换标签页：`CTRL + TAB`

> 可在应用「设置」页内修改。

## 项目结构

```text
daily_task_assistant.py      # 主程序
daily_task_assistant.pyw     # 无控制台启动入口
data/settings.default.json   # 默认配置模板
.gitignore
```

