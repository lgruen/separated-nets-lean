#!/bin/bash
# Stand-in for `landrun` on macOS (no Landlock), in the spirit of the Comparator repository's
# scripts/fake-landrun.sh: NO SANDBOX. Comparator calls `landrun <options> -- <command> <args>`;
# this drops everything up to the first `--` and execs the command. Used by
# scripts/run_comparator_full.sh only for local runs.
args=("$@")
for i in "${!args[@]}"; do
  if [ "${args[$i]}" = "--" ]; then
    cmd=("${args[@]:$((i + 1))}")
    echo "WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING exec ${cmd[*]}" >&2
    exec "${cmd[@]}"
  fi
done
echo "fake-landrun: no '--' separator in: $*" >&2
exit 2
