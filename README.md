# 逻辑验证漫游指南 2026 版

本仓库用于维护 _The Hitchhiker's Guide to Logical Verification_
（2026 版）的独立中文译本及其配套 Lean 文件。

中文译稿以英文原书和仓库中的英文 Lean 注释为内容依据；第三方中文译本不作为译文内容来源。

## 目录

* `lean/LoVe`：英文版配套 Lean 4 项目，可用 Lake 构建。
* `book_zh/src`：独立中文译稿。Lean 代码保持原样，说明文字位于块注释中。
* `scripts/build_docs.py`：从 `book_zh/src` 自动生成静态中文网页。
* `book_zh/_out/html-multi`：本地生成的网页输出目录，不纳入版本控制；GitHub Actions 会把它发布到 `gh-pages` 分支。

根目录中的 `hitchhikers_guide_2026_desktop.pdf` 与
`hitchhikers_guide_2026_tablet.pdf` 是英文原书 PDF。中文 PDF 将在独立译稿完成后再由本仓库内容生成。

## 构建

要检查 Lean 文件，请将 `lean` 文件夹作为 Lean 4 项目打开，或运行：

```powershell
cd lean
lake build
```

`lake build` 检查讲义示例与习题解答。`ExerciseSheet` 与 `HomeworkSheet`
文件是留给读者填写的材料，含有未定义的占位符，因此不纳入默认 Lake 构建目标。

要生成中文网页，请在仓库根目录运行：

```powershell
python scripts/build_docs.py
```

生成结果位于 `book_zh/_out/html-multi`。推送到 `main` 后，GitHub Actions 会构建 Lean 项目、生成中文网页，并将网页发布到 `gh-pages` 分支，便于配置 GitHub Pages。
