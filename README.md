# 逻辑验证漫游指南 2026 版

本仓库包含《逻辑验证漫游指南》（2026 版）的中文译本及其配套 Lean 文件。
英文原书为 _The Hitchhiker's Guide to Logical Verification_。

根目录中的 `逻辑验证漫游指南-2026-桌面版.pdf` 与
`逻辑验证漫游指南-2026-Pad版.pdf` 分别为桌面版和 Pad 版中文 PDF。

## 目录

* `lean/LoVe`：英文版配套 Lean 4 项目，可用 Lake 构建。
* `lean/LoVe-zh`：中文译文对应的 Lean 文件，正文保留在块注释中，Lean 代码保持原样以便对照阅读。
* `scripts/build_docs.py`：从 `lean/LoVe-zh` 自动生成静态中文网页。
* `book_zh/_out/html-multi`：本地生成的网页输出目录，不纳入版本控制；GitHub Actions 会把它发布到 `gh-pages` 分支。

## 构建

要检查 Lean 文件，请将 `lean` 文件夹作为 Lean 4 项目打开，或运行：

```powershell
cd lean
lake build
```

要生成中文网页，请在仓库根目录运行：

```powershell
python scripts/build_docs.py
```

生成结果位于 `book_zh/_out/html-multi`。推送到 `main` 后，GitHub Actions 会构建 Lean 项目、生成中文网页，并将网页发布到 `gh-pages` 分支，便于配置 GitHub Pages。
