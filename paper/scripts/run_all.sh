#!/usr/bin/env bash
# run_all.sh -- build the C++ programs and rerun every computation of scripts/ (see README.md).
# Run from anywhere:  bash scripts/run_all.sh        (~4 min on a laptop; needs uv, g++, and for the figure
# comparison pdftoppm from poppler). base23_certs.py also needs certificates/ (base23_audit, base23_everyshift, witnesses/r1;
# or $BASE23_DIR, $EVERYSHIFT_DIR, $WITNESS_DIR) and uses OpenMP if the compiler has it (about 40 s on 10 cores, about 4 min on one).  Exit status 0 iff every asserted value agrees with core.tex and every
# regenerated figure agrees with figs/ (bytes, or pixels after rasterization).
# Figures are regenerated into $FIGOUT (default: a fresh temporary directory), never over figs/.
# MPL=matplotlib==3.11.0 reproduces the committed PDFs byte for byte (default: the current matplotlib).
set -u
cd "$(dirname "$0")/.."                      # the paper directory: core.tex, figs/, scripts/
MPL="${MPL:-matplotlib}"
FIGOUT="${FIGOUT:-$(mktemp -d)}"
PY="uv run -q --with numpy --with $MPL --with mpmath --with python-flint python"
FAIL=()
T0=$(date +%s)

step() {   # step NAME COMMAND...
  local name="$1"; shift
  local t=$(date +%s)
  echo "=== $name: $*"
  if "$@"; then echo "--- $name: ok ($(( $(date +%s) - t )) s)"
  else echo "--- $name: FAILED ($(( $(date +%s) - t )) s)"; FAIL+=("$name"); fi
}

mkdir -p scripts/bin
step build-netmind     g++ -O3 -std=c++17 -o scripts/bin/netmind     scripts/netmind.cpp
step build-cellmin     g++ -O3 -std=c++17 -o scripts/bin/cellmin     scripts/cellmin.cpp
step build-whylat_cube g++ -O3 -std=c++17 -o scripts/bin/whylat_cube scripts/whylat_cube.cpp
step build-colmind     g++ -O3 -std=c++17 -o scripts/bin/colmind     scripts/colmind.cpp
step build-half5_mind  g++ -O3 -std=c++17 -pthread -o scripts/bin/half5_mind  scripts/half5_mind.cpp
step build-half5_thmD  g++ -O3 -std=c++17 -o scripts/bin/half5_thmD  scripts/half5_thmD.cpp
step build-shiftmin    g++ -O3 -std=c++17 -o scripts/bin/shiftmin    scripts/shiftmin.cpp
step build-gk2d_rescr  g++ -O3 -std=c++17 -o scripts/bin/gk2d_rescr  scripts/gk2d_rescr.cpp

step gk09_decay      $PY scripts/gk09_decay.py
step gk2d_affine     $PY scripts/gk2d_affine.py
step gk2d_rescramble $PY scripts/gk2d_rescramble.py
step cubecost        $PY scripts/cubecost.py
step tab_c           $PY scripts/tab_c.py
step as_table        $PY scripts/as_table.py
step deficit_tables  $PY scripts/deficit_tables.py
step skel_table      $PY scripts/skel_table.py
step twocoset        $PY scripts/twocoset.py
step colnets         $PY scripts/colnets.py
step half5_qstar     $PY scripts/half5_qstar.py
step half5_exact     $PY scripts/half5_exact.py
step wnet            $PY scripts/wnet.py
step wfamily         $PY scripts/wfamily.py
step truncate_bounds $PY scripts/truncate_bounds.py
step printed_data    $PY scripts/printed_data.py
step base23_certs    $PY scripts/base23_certs.py
step figs_arc        $PY scripts/figs_arc.py --out "$FIGOUT"
step figs_part1      $PY scripts/figs_part1.py --out "$FIGOUT"
step figs_net        $PY scripts/figs_net.py --out "$FIGOUT"
step figs_col        $PY scripts/figs_col.py --out "$FIGOUT"
step figs_wnet       $PY scripts/figs_wnet.py --out "$FIGOUT"
step figcmp          $PY scripts/figcmp.py "$FIGOUT"

echo "==================================================================="
echo "total $(( $(date +%s) - T0 )) s; regenerated figures in $FIGOUT"
if [ ${#FAIL[@]} -eq 0 ]; then echo "run_all: ALL OK"; exit 0
else echo "run_all: FAILED: ${FAIL[*]}"; exit 1; fi
