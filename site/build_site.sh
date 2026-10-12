#!/bin/sh
# Assemble the website of the repository (GitHub Pages; see .github/workflows/pages.yml):
#   OUT/index.html        landing page
#   OUT/paper.pdf         paper/core.pdf
#   OUT/blueprint/        blueprint/web (build it first: scripts/build_blueprint.sh)
#   OUT/explainers/       the explainer pages, each given a document skeleton, plus netcore.js and an index
# usage: site/build_site.sh [OUT=_site]        (POSIX sh; no network access, no build tools)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:-_site}
rm -rf "$OUT"
mkdir -p "$OUT/explainers"
cp "$ROOT/paper/core.pdf" "$OUT/paper.pdf"
if [ -d "$ROOT/blueprint/web" ]; then
  cp -R "$ROOT/blueprint/web" "$OUT/blueprint"
else
  echo "build_site.sh: blueprint/web not found (run scripts/build_blueprint.sh first); the site has no blueprint" >&2
fi
cp "$ROOT/explainers/netcore.js" "$OUT/explainers/netcore.js"
# The pages are written without <!doctype>/<html>/<head>/<body> (README of explainers/); the parser puts their leading
# <title>/<style> into the head and opens the body at the first content element.
for f in "$ROOT"/explainers/*.html; do
  n=$(basename "$f")
  {
    printf '<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
    printf '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
    cat "$f"
    printf '\n</html>\n'
  } > "$OUT/explainers/$n"
done
PAGE_HEAD='<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
:root { --bg: #ffffff; --ink: #15191f; --muted: #586271; --accent: #2b6cb0; }
@media (prefers-color-scheme: dark) { :root { --bg: #15191f; --ink: #e8ebef; --muted: #a3acb8; --accent: #7fb0e6; } }
body { background: var(--bg); color: var(--ink); font: 17px/1.55 Georgia, "Times New Roman", serif;
       max-width: 44rem; margin: 2.5rem auto; padding: 0 16px; }
a { color: var(--accent); }
.muted { color: var(--muted); font-size: 0.95em; }
li { margin: 0.35em 0; }
</style>'
cat > "$OUT/explainers/index.html" <<HTML
$PAGE_HEAD
<title>Explainers</title>
</head>
<body>
<h1>Interactive explainers</h1>
<p>Companions to the paper <em>Low-discrepancy quasi-uniform digital nets in every dimension</em>. Each page computes
the nets in the browser, with exact integer arithmetic, from the paper's generator matrices or graph forms, and cites
the paper by its LaTeX labels.</p>
<ul>
<li><a href="anatomy.html">Digits, Cubes, Lattices</a>: how the nets are built (frames, scrambles, the turned layer,
a worked example, the column nets and their holonomy).</li>
<li><a href="shifts.html">Shifted Digits</a>: digital shifts and the question of Dick, Goda and Suzuki.</li>
<li><a href="beyond.html">Beyond the Cube</a>: the column ceiling, the nets above the cubic value at m = 3, and the
half-integer layer in dimension five.</li>
</ul>
<p class="muted"><a href="../">Home</a> · <a href="../paper.pdf">Paper (PDF)</a> · <a href="../blueprint/">Blueprint</a></p>
</body>
</html>
HTML
cat > "$OUT/index.html" <<HTML
$PAGE_HEAD
<title>Quasi-uniform digital nets</title>
</head>
<body>
<h1>Low-discrepancy quasi-uniform digital nets in every dimension</h1>
<p>Leonhard Gruenschloss · version 1</p>
<p>Explicit digital (0, sk, s)-nets in every dimension s &ge; 3 whose minimum distance and covering radius are both of
the optimal order N<sup>&minus;1/s</sup>, answering a question of Dick, Goda and Suzuki. The results are formalized in
Lean&nbsp;4 (616 theorems, checked by Comparator with two kernels).</p>
<ul>
<li><a href="paper.pdf">Paper (PDF)</a></li>
<li><a href="blueprint/">Blueprint</a>: the results of the paper with their Lean declarations and the dependency graph</li>
<li><a href="explainers/">Interactive explainers</a></li>
<li><a href="https://github.com/lgruen/separated-nets-lean">Source repository</a> (paper, Lean project, scripts)</li>
</ul>
</body>
</html>
HTML
echo "site: $OUT ($(find "$OUT" -type f | wc -l | tr -d ' ') files)"
