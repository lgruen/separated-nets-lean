#!/usr/bin/env python3
"""V14 stage S1: every `\\lean{...}` name of the blueprint resolves in the `Solution` environment.

Replaces `lake exe checkdecls` (the research notes, section C, item 2: `checkdecls` imports every
library root together, and `Challenge` / `Solution` / the headline Challenge declare the same names,
so a joint import fails; it would also need a `checkdecls` release for the pinned toolchain).

The names are read from `blueprint/src/content.tex` (so the check does not need the web build); if
the web build has written `blueprint/lean_decls`, its set of names must be the same. A generated
Lean file `import Solution` looks every name up with `Environment.contains` (`lake env lean`;
`Solution` must be built: `lake build Solution`).

It also reports which compared theorems (`comparator.json`) are not in any `\\lean{}`; they must be
exactly the held ones (`QUNets/Statements/Hold.lean`, until V14 stage S9′), which the blueprint lists as text.

Usage (from the repository root): uv run --no-project python scripts/check_blueprint_decls.py
"""
import json
import os
import re
import subprocess
import sys

L = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

LEAN = r'''import Solution

open Lean in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[{names}]
  let mut missing : Array Name := #[]
  for n in names do
    unless env.contains n do
      missing := missing.push n
  IO.println s!"checked {{names.size}} names, missing {{missing.size}}"
  for n in missing do
    IO.println s!"MISSING {{n}}"
'''


def main():
    content = open(os.path.join(L, 'blueprint', 'src', 'content.tex')).read()
    names = []
    for grp in re.findall(r'\\lean\{([^}]*)\}', content):
        for n in grp.split(','):
            n = n.strip()
            if n and n not in names:
                names.append(n)
    ok = True
    decls = os.path.join(L, 'blueprint', 'lean_decls')
    if os.path.exists(decls):
        web = {ln.strip() for ln in open(decls) if ln.strip()}
        if web != set(names):
            ok = False
            print('lean_decls differs from content.tex: only in lean_decls %s, only in content.tex %s'
                  % (sorted(web - set(names))[:10], sorted(set(names) - web)[:10]))
        else:
            print('blueprint/lean_decls: same %d names as content.tex' % len(web))
    work = os.path.join(L, '.lake', 'blueprint_check')
    os.makedirs(work, exist_ok=True)
    src = os.path.join(work, 'CheckBlueprintDecls.lean')
    open(src, 'w').write(LEAN.format(names=', '.join('`' + n for n in names)))
    r = subprocess.run(['lake', 'env', 'lean', src], cwd=L, capture_output=True, text=True)
    print(r.stdout.strip())
    if r.returncode != 0:
        print(r.stderr.strip())
        return 1
    miss = re.findall(r'^MISSING (\S+)', r.stdout, re.M)
    if miss or not re.search(r'checked %d names, missing 0' % len(names), r.stdout):
        ok = False
    cmp_names = json.load(open(os.path.join(L, 'comparator.json')))['theorem_names']
    hold_path = os.path.join(L, 'QUNets', 'Statements', 'Hold.lean')  # retired in V14 stage S9′
    hold = (set(re.findall(r'^theorem (\S+)', open(hold_path).read(), re.M))
            if os.path.exists(hold_path) else set())
    unref = [n for n in cmp_names if n not in names]
    not_held = [n for n in unref if n.split('.')[-1] not in hold]
    print('compared theorems: %d; in \\lean{}: %d; not in \\lean{}: %d (held: %d, other: %d)'
          % (len(cmp_names), len(set(cmp_names) & set(names)), len(unref),
             len(unref) - len(not_held), len(not_held)))
    if not_held:
        ok = False
        print('compared, not held, not in the blueprint:', not_held[:20])
    print('ALL RESOLVE' if ok else 'PROBLEMS FOUND')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
