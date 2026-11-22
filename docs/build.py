"""Assemble docs/index.html from docs/src and the Lean sources."""
import json
from pathlib import Path

DOCS = Path(__file__).resolve().parent
ROOT = DOCS.parent
SRC = DOCS / "src"
LIB = ROOT / "DirichletPoincare"


def read(p: Path) -> str:
    return p.read_text(encoding="utf-8")


sources = {"DirichletPoincare.lean": read(ROOT / "DirichletPoincare.lean")}
for f in sorted(LIB.rglob("*.lean")):
    sources[f.relative_to(LIB).as_posix()] = read(f).replace("\r\n", "\n")

js = "\n".join(read(SRC / n) for n in ("a_core.js", "b_viz.js", "c_sim.js"))
page = read(SRC / "index.template.html")
for key, val in {
    "/*CSS*/": read(SRC / "style.css"),
    "<!--BODY-->": read(SRC / "body.html"),
    "/*SOURCES*/": json.dumps(sources, ensure_ascii=False).replace("</", "<\\/"),
    "/*DATA*/": read(SRC / "data.js"),
    "/*JS*/": js,
}.items():
    page = page.replace(key, val.replace("</script", "<\\/script") if key in ("/*DATA*/", "/*JS*/") else val)

(DOCS / "index.html").write_text(page, encoding="utf-8")
print(f"docs/index.html: {len(page) // 1024} KiB, {len(sources)} Lean files")
