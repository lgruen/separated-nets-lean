#!/usr/bin/env python3
"""Constant-identity check of the Palomar headline entry (comparatorHeadline.json), `thm:A`.

Stage 13d wrote it for `thm:U`; V14 stage S6 re-targeted the entry to `thm:A` (`Z3NetA.theoremA`); stage S6b added
`Z3NetA.ustarCols_spec`, `gamma_spec`, `net_wellDefined` (the theorem list is read from comparatorHeadline.json).
The headline Challenge (`Headline/Challenge.lean`) imports only Mathlib and holds verbatim copies
of the definitions of `Z3Net/FDefs.lean` (namespace `Z3NetF`) and `Z3Net/ThmADefs.lean` (namespace
`Z3NetA`) that the compared theorem reaches. Comparator compares every constant reachable from the
compared statements by name and structure, auxiliary constants (`X._proof_N`, `X.match_N`, `X._f`)
included. This script dumps, with `lake env lean` (a `run_cmd` over the environment), in the
environment of the Challenge and in that of the Solution (`Headline/Solution.lean`): the compared
theorems and every *project* constant (prefix in PREFIXES) reachable from their types
(transitively through types and, for definitions, values), each with its kind and the structural
hash of its type and (definitions only) value (`Expr.hash`). The two dumps must be identical.
Re-run whenever `Z3Net/FDefs.lean`, `Z3Net/ThmADefs.lean` or the Challenge changes.

A hash check, not Comparator; Comparator on `comparatorHeadline.json` remains the authority.
Usage (from the Lean project (repository root), after `lake build Headline`):
    uv run --no-project python scripts/check_headline_identity.py <work dir>
"""
import json
import os
import subprocess
import sys

L = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CFG = json.load(open(os.path.join(L, 'comparatorHeadline.json')))
PREFIXES = ['Z3NetF', 'Z3NetA']

DUMP = r'''import {root}

open Lean in
run_cmd do
  let env ← getEnv
  let roots : List Name := [{roots}]
  let mut seen : NameSet := {{}}
  let mut todo : List Name := roots
  let mut out : Array String := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | out := out.push s!"{{n}} MISSING"; continue
    let isRoot := roots.contains n
    let mut cs := ci.type.getUsedConstants
    if !ci.isThm then
      if let some v := ci.value? then cs := cs ++ v.getUsedConstants
    if {prefix_test} then
      let kind := if ci.isThm then "thm" else if ci.isDefinition then "def" else "other"
      let vh := if ci.isThm then 0 else (ci.value?.map hash).getD 0
      out := out.push s!"{{n}} {{kind}} {{hash ci.type}} {{vh}} root={{isRoot}}"
      for c in cs do todo := c :: todo
    else if isRoot then
      for c in cs do todo := c :: todo
  IO.FS.writeFile "{out}" ("\n".intercalate (out.qsort (· < ·)).toList)
'''


def dump(work, side, module):
    src = os.path.join(work, f'HeadDump_{side}.lean')
    out = os.path.join(work, f'head_dump_{side}.txt')
    roots = ', '.join('`' + t for t in CFG['theorem_names'])
    test = ' || '.join(f'(`{p}).isPrefixOf n' for p in PREFIXES)
    open(src, 'w').write(DUMP.format(root=module, roots=roots, prefix_test=test, out=out))
    r = subprocess.run(['lake', 'env', 'lean', src], cwd=L, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'{side}: lean failed\n{r.stdout}\n{r.stderr}')
    return open(out).read().splitlines()


def main():
    work = sys.argv[1] if len(sys.argv) > 1 else '/tmp'
    os.makedirs(work, exist_ok=True)
    a = dump(work, 'challenge', CFG['challenge_module'])
    b = dump(work, 'solution', CFG['solution_module'])
    nthm = sum(1 for x in a if 'root=true' in x)
    bad = sorted(set(a) ^ set(b)) + [x for x in a + b if 'MISSING' in x]
    print(f'{len(a)} constants in the Challenge dump ({nthm} compared theorems), {len(b)} in the '
          f'Solution dump')
    if bad or len(a) != len(b) or nthm != len(CFG['theorem_names']):
        print('DIFFERENCES:')
        for x in bad:
            print('  ', x)
        sys.exit(1)
    print('ALL IDENTICAL')


if __name__ == '__main__':
    main()
