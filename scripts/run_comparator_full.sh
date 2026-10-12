#!/bin/bash
# Full Comparator run of one configuration, meant to be launched DETACHED (it takes most of an hour):
#   nohup scripts/run_comparator_full.sh <tools dir> [config] [tag] > /dev/null 2>&1 &
# <tools dir> holds comparator/, lean4export-rc3/, nanoda_lib/ (built as in COMPARATOR_RESULTS.md);
# `landrun` is replaced by scripts/fake-landrun.sh (macOS has no Landlock; no sandbox).
# Writes, in this directory (the Lean project (repository root)):
#   comparator_<tag>.log     the full Comparator output, then `/usr/bin/time -l`
#   comparator_<tag>.result  one summary block: config, theorem count, start/end, EXIT, elapsed, max RSS,
#                            peak summed RSS of the Comparator/Lean/NanoDa processes (5-s sampler)
# The result file is written only at the end; while it is missing the run is in progress (pid in the log).
set -u
T=${1:?tools dir}
CFG=${2:-comparator.json}
TAG=${3:-full}
L=$(cd "$(dirname "$0")/.." && pwd)
cd "$L"
LOG="$L/comparator_$TAG.log"
RES="$L/comparator_$TAG.result"
PEAK="$L/.lake/comparator_$TAG.peak"
rm -f "$RES"
mkdir -p "$L/.lake/landrunbin"
ln -sf "$L/scripts/fake-landrun.sh" "$L/.lake/landrunbin/landrun"
echo 0 > "$PEAK"
N=$(python3 -c "import json,sys; print(len(json.load(open(sys.argv[1]))['theorem_names']))" "$CFG")
START=$(date +%s)
{
  echo "config $CFG ($N theorems), tag $TAG, start $(date '+%Y-%m-%d %H:%M:%S'), pid $$"
  echo "git $(git rev-parse --short HEAD)"
} > "$LOG"
( while true; do
    s=$(ps -axo rss=,comm= | awk '/comparator|lean|nanoda|lean4export/ {t+=$1} END {print t+0}')
    p=$(cat "$PEAK"); [ "$s" -gt "$p" ] && echo "$s" > "$PEAK"
    sleep 5
  done ) &
SAMPLER=$!
PATH="$L/.lake/landrunbin:$T/nanoda_lib/target/release:$PATH" \
COMPARATOR_LEAN4EXPORT="$T/lean4export-rc3/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$T/nanoda_lib/target/release/nanoda_bin" \
  /usr/bin/time -l lake env "$T/comparator/.lake/build/bin/comparator" "$CFG" >> "$LOG" 2>&1
EXIT=$?
kill $SAMPLER 2>/dev/null
END=$(date +%s)
{
  echo "config: $CFG ($N theorems), tag: $TAG"
  echo "git: $(git rev-parse --short HEAD)"
  echo "start: $(date -r "$START" '+%Y-%m-%d %H:%M:%S'), end: $(date -r "$END" '+%Y-%m-%d %H:%M:%S')"
  echo "EXIT $EXIT  elapsed $((END - START)) s"
  grep -E 'maximum resident set size|real' "$LOG" | tail -2
  echo "peak summed RSS (5-s sampler): $(cat "$PEAK") KB"
  grep -E 'accepts the solution|Your solution is okay|rejects|error|Error' "$LOG" | tail -6
} > "$RES"
