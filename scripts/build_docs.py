from __future__ import annotations

import html
import re
import shutil
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "lean" / "LoVe-zh"
OUT_DIR = ROOT / "book_zh" / "_out" / "html-multi"


KIND_ORDER = {
    "Demo": 0,
    "ExerciseSheet": 1,
    "HomeworkSheet": 2,
}

KIND_LABEL = {
    "Demo": "讲义",
    "ExerciseSheet": "习题",
    "HomeworkSheet": "作业",
}

PUNCT_TRANSLATIONS = str.maketrans(
    {
        "，": ",",
        "。": ".",
        "：": ":",
        "；": ";",
        "（": "(",
        "）": ")",
        "【": "[",
        "】": "]",
        "《": "",
        "》": "",
        "“": "",
        "”": "",
        "‘": "",
        "’": "",
        "、": "-",
        "—": "-",
        "–": "-",
        " ": "-",
    }
)


@dataclass(frozen=True)
class DocFile:
    path: Path
    chapter: int
    title: str
    kind: str
    slug: str


def main() -> None:
    docs = discover_docs()
    if not docs:
        raise SystemExit(f"no Chinese Lean files found in {SOURCE_DIR}")

    if OUT_DIR.exists():
        shutil.rmtree(OUT_DIR)
    OUT_DIR.mkdir(parents=True)

    write_css(OUT_DIR / "style.css")
    copy_pdfs()
    for doc in docs:
        write_doc(doc, docs)
    write_index(docs)
    (OUT_DIR / ".nojekyll").write_text("", encoding="utf-8")


def discover_docs() -> list[DocFile]:
    docs: list[DocFile] = []
    pattern = re.compile(r"LoVe(\d{2})_(.+)_(Demo|ExerciseSheet|HomeworkSheet)\.lean$")
    for path in SOURCE_DIR.glob("LoVe*.lean"):
        match = pattern.fullmatch(path.name)
        if not match:
            continue
        chapter = int(match.group(1))
        kind = match.group(3)
        title = first_title(path) or path.stem
        slug = f"{chapter:02d}-{kind.lower()}.html"
        docs.append(DocFile(path, chapter, title, kind, slug))
    return sorted(docs, key=lambda d: (d.chapter, KIND_ORDER[d.kind], d.path.name))


def first_title(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8-sig")
    for comment in iter_comments(text):
        for line in comment.splitlines():
            stripped = line.strip()
            if stripped.startswith("# "):
                return stripped[2:].strip()
    return None


def write_doc(doc: DocFile, docs: list[DocFile]) -> None:
    blocks = parse_lean_file(doc.path)
    prev_doc, next_doc = adjacent_docs(doc, docs)
    body = "\n".join(render_block(kind, content) for kind, content in blocks)
    page = render_page(
        title=doc.title,
        nav=render_nav(doc, docs),
        body=body,
        prev_doc=prev_doc,
        next_doc=next_doc,
    )
    (OUT_DIR / doc.slug).write_text(page, encoding="utf-8")


def write_index(docs: list[DocFile]) -> None:
    grouped: dict[int, list[DocFile]] = {}
    for doc in docs:
        grouped.setdefault(doc.chapter, []).append(doc)

    chapters = []
    for chapter, chapter_docs in grouped.items():
        primary = next((d for d in chapter_docs if d.kind == "Demo"), chapter_docs[0])
        entries = "\n".join(
            f'<li><a href="{html.escape(d.slug)}">{html.escape(KIND_LABEL[d.kind])}</a></li>'
            for d in chapter_docs
        )
        chapters.append(
            f"""
            <section class="chapter-card">
              <h2><a href="{html.escape(primary.slug)}">{html.escape(primary.title)}</a></h2>
              <ul>{entries}</ul>
            </section>
            """
        )

    pdfs = "\n".join(
        f'<li><a href="{html.escape(p.name)}">{html.escape(p.name)}</a></li>'
        for p in sorted(OUT_DIR.glob("逻辑验证漫游指南-2026-*.pdf"))
    )
    pdf_section = f"<h2>PDF</h2><ul>{pdfs}</ul>" if pdfs else ""

    body = f"""
    <header class="hero">
      <p class="eyebrow">Logical Verification 2026</p>
      <h1>逻辑验证漫游指南</h1>
      <p>本页由仓库中的中文 Lean 讲义注释自动生成，代码块保持原样，便于与 Lean 项目配合阅读。</p>
    </header>
    <section class="toc-grid">
      {''.join(chapters)}
    </section>
    <section class="pdf-list">
      {pdf_section}
    </section>
    """
    page = render_page(title="逻辑验证漫游指南", nav=render_nav(None, docs), body=body)
    (OUT_DIR / "index.html").write_text(page, encoding="utf-8")


def copy_pdfs() -> None:
    for pdf in ROOT.glob("逻辑验证漫游指南-2026-*.pdf"):
        shutil.copy2(pdf, OUT_DIR / pdf.name)


def render_page(
    *,
    title: str,
    nav: str,
    body: str,
    prev_doc: DocFile | None = None,
    next_doc: DocFile | None = None,
) -> str:
    footer_links = []
    if prev_doc:
        footer_links.append(f'<a href="{html.escape(prev_doc.slug)}">上一节：{html.escape(prev_doc.title)}</a>')
    if next_doc:
        footer_links.append(f'<a href="{html.escape(next_doc.slug)}">下一节：{html.escape(next_doc.title)}</a>')
    footer = ""
    if footer_links:
        footer = f'<nav class="page-nav">{"".join(footer_links)}</nav>'

    return f"""<!doctype html>
<html lang="zh-Hans">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(title)}</title>
  <link rel="stylesheet" href="style.css">
</head>
<body>
  <aside class="sidebar">
    {nav}
  </aside>
  <main class="content">
    {body}
    {footer}
  </main>
</body>
</html>
"""


def render_nav(current: DocFile | None, docs: list[DocFile]) -> str:
    items = ['<h1><a href="index.html">逻辑验证漫游指南</a></h1>']
    chapter = None
    for doc in docs:
        if doc.chapter != chapter:
            if chapter is not None:
                items.append("</ul>")
            chapter = doc.chapter
            items.append(f'<h2>第 {chapter} 章</h2><ul>')
        active = " active" if current == doc else ""
        label = f"{KIND_LABEL[doc.kind]}：{doc.title.removeprefix('LoVe ')}"
        items.append(f'<li class="{active}"><a href="{html.escape(doc.slug)}">{html.escape(label)}</a></li>')
    if chapter is not None:
        items.append("</ul>")
    return "\n".join(items)


def adjacent_docs(doc: DocFile, docs: list[DocFile]) -> tuple[DocFile | None, DocFile | None]:
    index = docs.index(doc)
    prev_doc = docs[index - 1] if index > 0 else None
    next_doc = docs[index + 1] if index + 1 < len(docs) else None
    return prev_doc, next_doc


def parse_lean_file(path: Path) -> list[tuple[str, str]]:
    text = path.read_text(encoding="utf-8-sig")
    blocks: list[tuple[str, str]] = []
    pos = 0
    for match in re.finditer(r"/-([\s\S]*?)-/", text):
        code = text[pos : match.start()]
        append_code(blocks, code)
        comment = clean_comment(match.group(1))
        if comment:
            blocks.append(("markdown", comment))
        pos = match.end()
    append_code(blocks, text[pos:])
    return blocks


def iter_comments(text: str):
    for match in re.finditer(r"/-([\s\S]*?)-/", text):
        yield clean_comment(match.group(1))


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


def render_block(kind: str, content: str) -> str:
    if kind == "code":
        return f'<pre class="lean"><code>{html.escape(content)}</code></pre>'
    return render_markdown(content)


def render_markdown(markdown: str) -> str:
    result: list[str] = []
    paragraph: list[str] = []
    list_open = False
    code_open = False
    code_lines: list[str] = []

    def flush_paragraph() -> None:
        nonlocal paragraph
        if paragraph:
            text = " ".join(part.strip() for part in paragraph)
            result.append(f"<p>{render_inline(text)}</p>")
            paragraph = []

    def flush_list() -> None:
        nonlocal list_open
        if list_open:
            result.append("</ul>")
            list_open = False

    def flush_code() -> None:
        nonlocal code_open, code_lines
        if code_open:
            result.append(f'<pre><code>{html.escape(chr(10).join(code_lines).rstrip())}</code></pre>')
            code_open = False
            code_lines = []

    for raw in markdown.splitlines():
        line = raw.rstrip()
        stripped = line.strip()
        if stripped.startswith("```"):
            if code_open:
                flush_code()
            else:
                flush_paragraph()
                flush_list()
                code_open = True
                code_lines = []
            continue
        if code_open:
            code_lines.append(line)
            continue
        if not stripped:
            flush_paragraph()
            flush_list()
            continue
        if re.match(r"^#{1,6}\s+", stripped):
            flush_paragraph()
            flush_list()
            level = min(len(stripped) - len(stripped.lstrip("#")), 4)
            text = stripped[level:].strip()
            result.append(f'<h{level} id="{slugify(text)}">{render_inline(text)}</h{level}>')
            continue
        bullet_match = re.match(r"^\*\s+(.*)$", stripped)
        if bullet_match:
            flush_paragraph()
            if not list_open:
                result.append("<ul>")
                list_open = True
            result.append(f"<li>{render_inline(bullet_match.group(1))}</li>")
            continue
        ordered_match = re.match(r"^\d+\.\s+(.*)$", stripped)
        if ordered_match:
            flush_paragraph()
            if not list_open:
                result.append("<ul>")
                list_open = True
            result.append(f"<li>{render_inline(ordered_match.group(1))}</li>")
            continue
        if line.startswith("    "):
            flush_paragraph()
            flush_list()
            result.append(f'<pre><code>{html.escape(line[4:])}</code></pre>')
            continue
        paragraph.append(line)

    flush_paragraph()
    flush_list()
    flush_code()
    return "\n".join(result)


def render_inline(text: str) -> str:
    escaped = html.escape(text)
    escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
    escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"__([^_]+)__", r"<strong>\1</strong>", escaped)
    return escaped


def slugify(text: str) -> str:
    text = text.strip().translate(PUNCT_TRANSLATIONS)
    text = re.sub(r"[^0-9A-Za-z\u4e00-\u9fff_-]+", "-", text)
    text = re.sub(r"-+", "-", text).strip("-")
    return text or "section"


def write_css(path: Path) -> None:
    path.write_text(
        """* {
  box-sizing: border-box;
}

:root {
  color-scheme: light;
  --ink: #18202f;
  --muted: #526071;
  --line: #d8dde6;
  --paper: #fbfaf7;
  --panel: #ffffff;
  --accent: #0f766e;
  --accent-soft: #e5f3f0;
  --code: #111827;
  --code-bg: #f0f4f8;
}

body {
  margin: 0;
  display: grid;
  grid-template-columns: minmax(260px, 320px) minmax(0, 1fr);
  min-height: 100vh;
  background: var(--paper);
  color: var(--ink);
  font-family: "Noto Serif SC", "Source Han Serif SC", "Songti SC", "SimSun", serif;
  line-height: 1.72;
}

a {
  color: var(--accent);
  text-decoration-thickness: 1px;
  text-underline-offset: 0.18em;
}

.sidebar {
  position: sticky;
  top: 0;
  height: 100vh;
  overflow: auto;
  border-right: 1px solid var(--line);
  background: #f4f2ed;
  padding: 1.4rem 1.1rem 2rem;
}

.sidebar h1 {
  margin: 0 0 1.1rem;
  font-size: 1.08rem;
  line-height: 1.3;
}

.sidebar h2 {
  margin: 1.1rem 0 0.35rem;
  font-size: 0.88rem;
  color: var(--muted);
  font-family: "Noto Sans SC", "Microsoft YaHei UI", sans-serif;
}

.sidebar ul {
  list-style: none;
  margin: 0;
  padding: 0;
}

.sidebar li a {
  display: block;
  padding: 0.22rem 0.25rem;
  border-radius: 4px;
  color: var(--ink);
  font-size: 0.92rem;
  line-height: 1.42;
  text-decoration: none;
}

.sidebar li.active a,
.sidebar li a:hover {
  background: var(--accent-soft);
  color: #075e57;
}

.content {
  width: min(100%, 980px);
  padding: 3rem clamp(1.2rem, 4vw, 4rem) 5rem;
}

.hero {
  padding-bottom: 2.2rem;
  border-bottom: 1px solid var(--line);
  margin-bottom: 2rem;
}

.eyebrow {
  margin: 0 0 0.3rem;
  color: var(--muted);
  font-family: "Noto Sans SC", "Microsoft YaHei UI", sans-serif;
  letter-spacing: 0;
}

h1,
h2,
h3,
h4 {
  line-height: 1.3;
  margin: 2rem 0 0.85rem;
  font-weight: 700;
}

h1 {
  margin-top: 0;
  font-size: clamp(2rem, 4vw, 3.2rem);
}

h2 {
  border-top: 1px solid var(--line);
  padding-top: 1.4rem;
  font-size: 1.65rem;
}

h3 {
  font-size: 1.28rem;
}

h4 {
  font-size: 1.08rem;
}

p {
  margin: 0.85rem 0;
}

ul {
  padding-left: 1.4rem;
}

li {
  margin: 0.25rem 0;
}

code,
pre {
  font-family: "Noto Sans Mono", "Cascadia Code", "Consolas", monospace;
}

code {
  background: var(--code-bg);
  padding: 0.05rem 0.25rem;
  border-radius: 4px;
}

pre {
  overflow: auto;
  padding: 1rem;
  background: var(--code-bg);
  border: 1px solid var(--line);
  border-radius: 6px;
  line-height: 1.55;
  color: var(--code);
  font-size: 0.92rem;
}

pre code {
  padding: 0;
  background: transparent;
}

.toc-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
  gap: 1rem;
}

.chapter-card {
  background: var(--panel);
  border: 1px solid var(--line);
  border-radius: 6px;
  padding: 1rem;
}

.chapter-card h2 {
  border: 0;
  padding: 0;
  margin: 0 0 0.6rem;
  font-size: 1.05rem;
}

.chapter-card ul {
  margin: 0;
}

.pdf-list {
  margin-top: 2rem;
}

.page-nav {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  gap: 1rem;
  border-top: 1px solid var(--line);
  margin-top: 3rem;
  padding-top: 1.2rem;
}

@media (max-width: 860px) {
  body {
    display: block;
  }

  .sidebar {
    position: static;
    height: auto;
    max-height: 50vh;
    border-right: 0;
    border-bottom: 1px solid var(--line);
  }

  .content {
    padding-top: 2rem;
  }
}
""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
