#!/bin/sh
# V14 stage S1: build the web blueprint (blueprint/web/) with plasTeX directly.
# The `leanblueprint` CLI is not used: it expects the Lake package at the git root
# (the research notes, section C). Python via uv (pinned versions, ephemeral environment).
#
#   scripts/build_blueprint.sh            regenerate blueprint/src from core.tex, then build
#   scripts/build_blueprint.sh --no-gen   build the committed blueprint/src as is
#
# Then: uv run --no-project python scripts/check_blueprint_decls.py  (every \lean{} name
# resolves in the Solution environment). The PDF (print.tex, latexmk + xelatex) needs TeX Live
# and is not built here.
set -eu
cd "$(dirname "$0")/.."
LEAN_DIR=$(pwd)
if [ "${1:-}" != "--no-gen" ]; then
  uv run --no-project python scripts/gen_blueprint.py
fi
if ! command -v kpsewhich >/dev/null 2>&1; then
  echo "build_blueprint.sh: no kpsewhich on PATH, using scripts/kpsewhich-shim"
  PATH="$LEAN_DIR/scripts/kpsewhich-shim:$PATH"
  export PATH
fi
rm -rf blueprint/web
cd blueprint/src
TEXINPUTS=".:./macros:${TEXINPUTS:-}" \
  uv run --no-project --python 3.12 \
    --with leanblueprint==0.0.20 --with plastex==3.1 --with plastexdepgraph==0.0.5 \
    plastex -c plastex.cfg web.tex
cd "$LEAN_DIR"
echo "blueprint/web: $(find blueprint/web -name '*.html' | wc -l | tr -d ' ') HTML pages;" \
  "lean_decls: $(grep -c . blueprint/lean_decls) names"
