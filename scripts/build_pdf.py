from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "book_zh" / "src"
BUILD_DIR = ROOT / "book_zh" / "_out" / "pdf"
MARKDOWN_PATH = BUILD_DIR / "logical-verification-2026-zh.md"
HEADER_PATH = BUILD_DIR / "pdf-header.tex"
PDF_PATH = ROOT / "logical-verification-2026-zh.pdf"


def main() -> None:
    if shutil.which("pandoc") is None:
        raise SystemExit("pandoc is required to build the Chinese PDF")
    if shutil.which("xelatex") is None:
        raise SystemExit("xelatex is required to build the Chinese PDF")

    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    MARKDOWN_PATH.write_text(render_markdown(), encoding="utf-8")
    HEADER_PATH.write_text(
        "\n".join(
            [
                r"\setmainfont{DejaVuSans.ttf}[Path=C:/Windows/Fonts/]",
                r"\setsansfont{DejaVuSans.ttf}[Path=C:/Windows/Fonts/]",
                r"\setCJKmainfont{NotoSerifSC-VF.ttf}[Path=C:/Windows/Fonts/]",
                r"\setCJKsansfont{NotoSansSC-VF.ttf}[Path=C:/Windows/Fonts/]",
                r"\setCJKmonofont{NotoSansSC-VF.ttf}[Path=C:/Windows/Fonts/]",
                r"\setmonofont{DejaVuSans.ttf}[Path=C:/Windows/Fonts/]",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    subprocess.run(
        [
            "pandoc",
            str(MARKDOWN_PATH),
            "-o",
            str(PDF_PATH),
            "--pdf-engine=xelatex",
            "-V",
            "documentclass=ctexbook",
            "-V",
            "classoption=oneside",
            "-V",
            "classoption=fontset=none",
            "-V",
            "geometry:margin=1in",
            "-H",
            str(HEADER_PATH),
            "--toc",
            "--toc-depth=2",
            "--number-sections",
        ],
        cwd=ROOT,
        check=True,
    )


def render_markdown() -> str:
    parts = [
        "---",
        "title: 逻辑验证漫游指南",
        "subtitle: The Hitchhiker's Guide to Logical Verification 2026",
        "lang: zh-Hans",
        "---",
        "",
        "\\frontmatter",
        "",
        "# 前言",
        "",
        "本 PDF 由仓库中的独立中文译稿自动生成。译稿以英文原书和英文 Lean "
        "注释为依据；Lean 代码保持原样，以便与形式化文件对应阅读。",
        "",
        "\\mainmatter",
        "",
    ]
    for path in sorted(SOURCE_DIR.glob("LoVe*_Demo.lean")):
        parts.append(render_lean_file(path))
    return "\n".join(parts).rstrip() + "\n"


def render_lean_file(path: Path) -> str:
    blocks = parse_lean_file(path)
    rendered: list[str] = []
    for kind, content in blocks:
        if kind == "markdown":
            rendered.append(normalize_pdf_text(content))
        else:
            rendered.extend(["```lean", content, "```"])
    return "\n\n".join(part for part in rendered if part.strip())


def normalize_pdf_text(text: str) -> str:
    return text.replace("⬝", "·")


def parse_lean_file(path: Path) -> list[tuple[str, str]]:
    text = path.read_text(encoding="utf-8-sig")
    blocks: list[tuple[str, str]] = []
    pos = 0
    for match in re.finditer(r"/-([\s\S]*?)-/", text):
        append_code(blocks, text[pos : match.start()])
        comment = clean_comment(match.group(1))
        if comment:
            blocks.append(("markdown", comment))
        pos = match.end()
    append_code(blocks, text[pos:])
    return blocks


def append_code(blocks: list[tuple[str, str]], code: str) -> None:
    code = strip_boilerplate(code)
    if code.strip():
        blocks.append(("code", code.strip("\n")))


def strip_boilerplate(code: str) -> str:
    lines = []
    for line in code.splitlines():
        stripped = line.strip()
        if not stripped:
            lines.append(line)
            continue
        if stripped.startswith("import "):
            continue
        if stripped.startswith("set_option "):
            continue
        if stripped.startswith("namespace ") or stripped.startswith("end "):
            continue
        lines.append(line)
    return "\n".join(lines)


def clean_comment(comment: str) -> str:
    lines = comment.splitlines()
    if lines and lines[0].strip().startswith("Copyright"):
        return ""
    return "\n".join(line.rstrip() for line in lines).strip()


if __name__ == "__main__":
    main()
