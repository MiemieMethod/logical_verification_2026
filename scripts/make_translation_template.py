from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ENGLISH_DIR = ROOT / "lean" / "LoVe"
TRANSLATION_DIR = ROOT / "book_zh" / "src"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Create independent Chinese translation templates from the English LoVe sources."
    )
    parser.add_argument(
        "files",
        nargs="*",
        help="Specific Lean source file names to template. Defaults to all LoVe demo files.",
    )
    parser.add_argument(
        "--all-materials",
        action="store_true",
        help="Template demos, exercise sheets, homework sheets, and exercise solutions.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite existing files in book_zh/src.",
    )
    args = parser.parse_args()

    if args.files:
        sources = [ENGLISH_DIR / name for name in args.files]
    elif args.all_materials:
        sources = sorted(ENGLISH_DIR.glob("LoVe*.lean"))
    else:
        sources = sorted(ENGLISH_DIR.glob("LoVe*_Demo.lean"))

    if not sources:
        raise SystemExit("no source files selected")

    TRANSLATION_DIR.mkdir(parents=True, exist_ok=True)
    for source in sources:
        if not source.is_file():
            raise SystemExit(f"missing source file: {source}")
        target = TRANSLATION_DIR / source.name
        if target.exists() and not args.force:
            print(f"skip existing {target}")
            continue
        target.write_text(template_text(source), encoding="utf-8")
        print(f"wrote {target}")


def template_text(source: Path) -> str:
    text = source.read_text(encoding="utf-8-sig")

    def replace_comment(match: re.Match[str]) -> str:
        body = match.group(1)
        if "Copyright ©" in body:
            return match.group(0)
        title = first_heading(body)
        lines = ["/-"]
        if title:
            lines.append(title)
            lines.append("")
        lines.append("译稿待补：请根据英文原文独立翻译本注释块。")
        lines.append("-/")
        return "\n".join(lines)

    return re.sub(r"/-([\s\S]*?)-/", replace_comment, text)


def first_heading(body: str) -> str | None:
    for line in body.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            return stripped
    return None


if __name__ == "__main__":
    main()
