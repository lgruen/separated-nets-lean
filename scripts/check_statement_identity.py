#!/usr/bin/env python3
"""Constant-identity check of the statement library (stage 13c; re-based in V14 stage S0).

A `run_cmd` over the environment (`lake env lean`) dumps a list of compared theorems and every
constant reachable from their types (transitively through the types of reachable constants and the
values of reachable *project* definitions, i.e. not from Mathlib/core; for library constants only the
name and the type hash are recorded), each with its kind, the structural hash of its type and
(definitions only) value (`Expr.hash`), and, for the compared theorems, the full printed type
(`toString`, which includes binder names; the module part of hygienic binder names is erased).
Values of theorems (proofs; `sorry` in the Challenge) are not compared.

Modes (from the repository root):
  * `baseline <root> <names.json>`: dump the theorems listed in `<names.json>` (a JSON list) in the
    environment of `<root>` and write the baseline file. Stage S0 ran it once on the stage-13c root
    `ChallengeAll` (before the re-sectioning) for the 420 kept and held theorems
    (`scripts/identity_baseline_v14s0.txt`, kept as a record; that root no longer exists). Stage S1
    first ran `check` against that file (ALL IDENTICAL), then, before retiring the four Half
    statements about s = 6, 8 only, re-ran `baseline Challenge` on the same S0 environment for the
    416 remaining theorems: `scripts/identity_baseline_v14s1.txt`, the current reference.
  * `check [<root>]` (default root `Challenge`): dump the theorems of the baseline in the
    environment of `<root>` and compare line by line with the baseline. Every theorem of the
    baseline must still be compared (`comparator.json`).
  * `check-unchanged <baseline file> [<root>] [<stage>]` (V14 stage S2): the same against an older
    baseline, leaving out the theorems whose statement changed (`scripts/v14_delta.py` CHANGED; with
    `<stage>`, only those changed in that stage, e.g. `S9′`). The dump
    of the remaining theorems must be a line subset of the old baseline (constants reachable only from
    the changed theorems drop out), with every remaining theorem's TYPE line present and identical.
    Stage S2 ran it against `identity_baseline_v14s1.txt` (413 unchanged theorems), then
    `baseline Challenge <427 names>` wrote `scripts/identity_baseline_v14s2.txt` (it includes the 3
    changed and 11 new theorems of S2). Stage S3 ran `check` against that file (430 theorems, ALL
    IDENTICAL; no statement changed in S3), then `baseline Challenge <451 names>` wrote
    `scripts/identity_baseline_v14s3.txt` (it adds the 21 new theorems of S3). Stage S4 ran `check`
    against that file (451 theorems, ALL IDENTICAL; no statement changed in S4), then
    `baseline Challenge <467 names>` wrote `scripts/identity_baseline_v14s4.txt` (it adds the 16 new
    theorems of S4). Stage S5 ran `check` against that file (467 theorems, ALL IDENTICAL; no statement
    changed in S5), then `baseline Challenge <477 names>` wrote `scripts/identity_baseline_v14s5.txt`
    (it adds the 10 new theorems of S5). Stage S6b ran `check` against that file (477 theorems, ALL
    IDENTICAL; no statement changed in S6b), then `baseline Challenge <480 names>` wrote
    `scripts/identity_baseline_v14s6b.txt` (it adds the 3 new theorems of S6b:
    `Z3NetF.PGen_indep`, `Z3NetA.Apoint_indep`, `Z3NetA.gamS_unique`). Stage S7 ran `check` against that
    file (480 theorems, ALL IDENTICAL; no statement changed in S7), then `baseline Challenge <488 names>`
    wrote `scripts/identity_baseline_v14s7.txt` (it adds the 8 new theorems of S7: `lem:O`, `prop:E`,
    `lem:C`, `thm:Lstar`). Stage S8 ran `check` against that file (488 theorems, ALL IDENTICAL; no
    statement changed in S8), then `baseline Challenge <502 names>` wrote
    `scripts/identity_baseline_v14s8.txt` (it adds the 14 new theorems of S8: `prop:4D2`, `prop:k1`(3)).
    Stage S9′ ran `check-unchanged` against that file (since S9′ this mode also leaves out the theorems
    retired since, `gen_v14_statements.RETIRE`: the 71 of the former holding section), then
    `baseline Challenge <461 names>` wrote `scripts/identity_baseline_v14s9.txt` (the 30 new theorems of S9′,
    the 3 changed `cor:allm` statements). Stage S10′ ran `check` against that file (461 theorems, ALL IDENTICAL
    in `Challenge` and `Solution`; no statement changed in S10′), then `baseline Challenge <520 names>` wrote
    `scripts/identity_baseline_v14s10.txt` (it adds the 59 new theorems of S10′). Stage S11′ ran `check-unchanged`
    against that file (514 unchanged theorems, ALL IDENTICAL in `Challenge` and `Solution`; the 6 Half statements of the
    layer M₅ retired), then `baseline Challenge <524 names>` wrote `scripts/identity_baseline_v14s11.txt` (it adds the
    10 new theorems of S11′: `thm:D`, `lem:R2`, `prop:half5`). Stage S12′ ran `check` against that file (524 theorems,
    ALL IDENTICAL in `Challenge` and `Solution`; no statement changed or retired in S12′), then
    `baseline Challenge <552 names>` wrote `scripts/identity_baseline_v14s12.txt` (it adds the
    28 new theorems of S12′: `prop:wnet`, `lem:wwrap`, `prop:wfamily`, `rem:wstar`, `rem:shiftshared` for `𝒲_p`).
    Stage S13′ ran `check` against that file (552 theorems, ALL IDENTICAL in `Challenge` and `Solution`; no statement
    changed or retired in S13′), then `baseline Challenge <576 names>` wrote `scripts/identity_baseline_v14s13.txt` (it adds the
    24 new theorems of S13′: `rem:projlines`, `rem:accounting`, the `digitalPtS` link). Stage S14′ ran `check` against
    it (576, ALL IDENTICAL in `Challenge` and `Solution`; no statement changed or retired in S14′), then
    `baseline Challenge <591 names>` wrote `scripts/identity_baseline_v14s14.txt` (it adds the 15 new theorems of S14′:
    `lem:lift`, `lem:liftsep`, `lem:shiftcert`, `thm:base23`). Stage S15′ ran `check` against it (591, ALL IDENTICAL in
    `Challenge` and `Solution`; no statement changed or retired in S15′), then `baseline Challenge <602 names>` wrote
    `scripts/identity_baseline_v14s15.txt`, the current reference (it adds the 11 new theorems of S15′: `rem:ppshift`,
    `rem:dgsfinite` in every prime base, `prop:k1designs`).

Stage 13c compared the 13 stage-9 entries with `ChallengeAll` (458/458 identical; the 13c version
of this script is in git history before stage S0).

A hash check, not Comparator; Comparator on `comparator.json` remains the authority.
"""
import json
import re
import os
import subprocess
import sys

L = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(L, 'scripts', 'identity_baseline_v14s16r.txt')

DUMP = r'''import {root}

open Lean in
run_cmd do
  let env ← getEnv
  let libs : List Name := [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible,
    `ProofWidgets, `ImportGraph, `LeanSearchClient]
  let isLib (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        libs.any (fun p => p.isPrefixOf m)
    | none => false
  let roots : Array Name := #[{names}]
  -- V14 stage S16′ (`check-renamed`): map the current names back to the old ones (prefix map) before printing and
  -- hashing, so that a dump of the renamed library is comparable with a baseline of the old one
  let inv : List (Name × Name) := [{inv}]
  let back (n : Name) : Name := Id.run do
    for (newP, oldP) in inv do
      if newP.isPrefixOf n then return n.replacePrefix newP oldP
    return n
  let backE (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => some (.const (back n) ls)
    | _ => none
  let mut seen : NameSet := {{}}
  let mut todo : Array Name := roots
  let mut out : Array String := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => out := out.push s!"{{n}} MISSING"
    | some ci =>
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      let lib := isLib n
      let bn := back n
      if roots.contains n then
        out := out.push s!"{{bn}} TYPE {{toString (backE ci.type)}}"
      if lib then
        out := out.push s!"{{bn}} {{kind}} lib {{hash (backE ci.type)}}"
      else
        let v := ci.value? (allowOpaque := true)
        -- values of theorems (proofs; `sorry` in the Challenge) are not compared
        let vh := if ci.isThm then 0 else ((v.map backE).map hash).getD 0
        out := out.push s!"{{bn}} {{kind}} prj {{hash (backE ci.type)}} {{vh}} {{ci.levelParams}}"
        for c in ci.type.getUsedConstants do todo := todo.push c
        if let some e := v then
          if !ci.isThm then
            for c in e.getUsedConstants do todo := todo.push c
        match ci with
        | .inductInfo i => for c in i.ctors do todo := todo.push c
        | .ctorInfo c => todo := todo.push c.induct
        | _ => pure ()
  IO.FS.writeFile "{out}" ("\n".intercalate (out.qsort (· < ·)).toList ++ "\n")
'''


def run(root, names, out, work, inv=()):
    """`inv`: pairs (new prefix, old prefix) of the rename map; the dump then reports old names (mode `check-renamed`)."""
    src = os.path.join(work, f'dump_{os.path.basename(out)}.lean')
    open(src, 'w').write(DUMP.format(root=root, names=', '.join('`' + n for n in names), out=out,
                                     inv=', '.join(f'(`{a}, `{b})' for a, b in inv)))
    r = subprocess.run(['lake', 'env', 'lean', src], cwd=L, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f'lean failed on {src}:\n{r.stdout}\n{r.stderr}')
    # hygienic binder names carry the module name (`x._@.<Module>.<hash>._hygCtx._hyg.<n>`);
    # binder names are irrelevant to Comparator (and to `Expr.hash`), so erase the module part
    txt = re.sub(r'_@\.[A-Za-z0-9_.]+?\.(\d+\._hygCtx)', r'_@.M.\1', open(out).read())
    return txt.split('\n')


def main():
    work = os.path.join(L, '.lake', 'identity_check')
    os.makedirs(work, exist_ok=True)
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if mode == 'baseline':
        root, names = sys.argv[2], json.load(open(sys.argv[3]))
        lines = run(root, names, os.path.join(work, 'baseline.txt'), work)
        open(BASELINE, 'w').write('\n'.join(lines))
        nthm = sum(1 for ln in lines if ' TYPE ' in ln)
        miss = [ln for ln in lines if ln.endswith('MISSING')]
        print(f'baseline in {root}: {nthm} theorems, {len(lines)} dump lines, missing {len(miss)}')
        return 1 if miss or nthm != len(names) else 0
    if mode == 'check-unchanged':
        sys.path.insert(0, os.path.join(L, 'scripts'))
        import v14_delta as D
        bfile = sys.argv[2]
        root = sys.argv[3] if len(sys.argv) > 3 else 'Challenge'
        stage = sys.argv[4] if len(sys.argv) > 4 else None  # leave out only the theorems changed in this stage
        import gen_v14_statements as V
        old = open(bfile).read().split('\n')
        names = [ln.split(' TYPE ')[0] for ln in old if ' TYPE ' in ln]
        drop = [n for n in names if n in D.CHANGED and (stage is None or D.STAGE.get(n) == stage)]
        retired = [n for n in names if n in V.RETIRE]
        names = [n for n in names if n not in drop and n not in V.RETIRE]
        cfg = json.load(open(os.path.join(L, 'comparator.json')))['theorem_names']
        not_cmp = [n for n in names if n not in cfg]
        new = run(root, names, os.path.join(work, 'new_unchanged.txt'), work)
        so = set(old)
        extra = [ln for ln in new if ln not in so]
        types_old = {ln for ln in old if ' TYPE ' in ln and ln.split(' TYPE ')[0] in set(names)}
        types_new = {ln for ln in new if ' TYPE ' in ln}
        miss = [ln for ln in new if ln.endswith('MISSING')]
        print(f'{len(names)} unchanged theorems of {os.path.basename(bfile)} (left out, changed: '
              f'{", ".join(drop)}; retired since: {len(retired)}); {len(new)} dump lines in {root}, '
              f'all in the old baseline: '
              f'{not extra}; TYPE lines identical: {types_old == types_new}; missing: {len(miss)}; '
              f'not in comparator.json: {len(not_cmp)}')
        for ln in extra[:20]:
            print('   not in the old baseline:', ln[:300])
        ok = not extra and types_old == types_new and not miss and not not_cmp
        print('ALL IDENTICAL (unchanged theorems)' if ok else 'DIFFERENCES FOUND')
        return 0 if ok else 1
    if mode == 'check-renamed':
        # V14 stage S16′: the legacy-name rename (`scripts/v16_rename.py`, recorded in the research notes). Query the
        # renamed theorems, map every constant name back with the inverse prefix map before printing and hashing, and
        # require the dump to equal the old baseline line by line: the statement bodies (types; values of
        # definitions) are then identical modulo the rename.
        sys.path.insert(0, os.path.join(L, 'scripts'))
        import v16_rename as R
        bfile = sys.argv[2]
        root = sys.argv[3] if len(sys.argv) > 3 else 'Challenge'
        old = open(bfile).read().split('\n')
        names = [R.new_name(ln.split(' TYPE ')[0]) for ln in old if ' TYPE ' in ln]
        cfg = json.load(open(os.path.join(L, 'comparator.json')))['theorem_names']
        not_cmp = [n for n in names if n not in cfg]
        inv = [(b, a) for a, b in R.NS_PREFIX.items()]
        new = run(root, names, os.path.join(work, 'new_renamed.txt'), work, inv)
        miss = [ln for ln in new if ln.endswith('MISSING')]
        same = old == new
        nren = sum(1 for ln in old if ' TYPE ' in ln and R.new_name(ln.split(' TYPE ')[0]) != ln.split(' TYPE ')[0])
        print(f'{len(names)} theorems of {os.path.basename(bfile)} ({nren} renamed), {len(old)} dump lines; in {root} '
              f'with the inverse rename map {inv}: identical: {same}, missing: {len(miss)}, '
              f'not in comparator.json: {len(not_cmp)}')
        if not same:
            so, sn = set(old), set(new)
            for ln in sorted(so - sn)[:20]:
                print('   baseline only:', ln[:300])
            for ln in sorted(sn - so)[:20]:
                print('   new only:', ln[:300])
        ok = same and not miss and not not_cmp
        print('ALL IDENTICAL (modulo the rename)' if ok else 'DIFFERENCES FOUND')
        return 0 if ok else 1
    root = sys.argv[2] if len(sys.argv) > 2 else 'Challenge'
    old = open(BASELINE).read().split('\n')
    names = [ln.split(' TYPE ')[0] for ln in old if ' TYPE ' in ln]
    cfg = json.load(open(os.path.join(L, 'comparator.json')))['theorem_names']
    not_cmp = [n for n in names if n not in cfg]
    new = run(root, names, os.path.join(work, 'new.txt'), work)
    miss = [ln for ln in new if ln.endswith('MISSING')]
    same = old == new
    print(f'{len(names)} baseline theorems, {len(old)} dump lines; in {root}: identical: {same}, '
          f'missing: {len(miss)}, not in comparator.json: {len(not_cmp)}')
    if not same:
        so, sn = set(old), set(new)
        for ln in sorted(so - sn)[:20]:
            print('   baseline only:', ln[:300])
        for ln in sorted(sn - so)[:20]:
            print('   new only:', ln[:300])
    for n in not_cmp[:20]:
        print('   not compared:', n)
    ok = same and not miss and not not_cmp
    print('ALL IDENTICAL' if ok else 'DIFFERENCES FOUND')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
