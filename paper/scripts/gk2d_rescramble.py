#!/usr/bin/env python3
"""rem:gk2d(iii) (rev 15.5): the phases of the two-dimensional Gruenschloss-Keller nets and the re-scramble.

Runs bin/gk2d_rescr (built from gk2d_rescr.cpp by run_all.sh; built here if missing) and checks the sentences of
rem:gk2d(iii) against core.tex:
  (a) on the lines of rem:gk2d (shear 1/4, the offset R/4 of GK09) the phase maps that keep t = 0 are exactly the
      2^(R-1) nested scramblings of the van der Corput phases, for m = 4, 6, 8 (DFS over all permutations, box counts);
  (b) all of them have the same distance J = 1/4 - 1/(2R) from lattice phases (all nested scramblings, m = 4, 6, 8);
  (c) the re-scramble (third phase digit flipped on the lines u = 2, 3 mod 4) is a nested scrambling with
      0 bad elementary boxes for every even m = 8..20; in the tiling metric <(N,0),(N/4,N)> (the only metric printed;
      rev 15.5) its exact d^2 is 229 against GK's 241 at m = 8 (worse) and 977 * 2^(m-10) against GK's
      964 * 2^(m-10) = 241 * 2^(m-8) for every even m = 10..20 (the standard-torus values are not printed or checked);
  (d) GK09 itself: 241 * 2^(m-8) in the tiling metric for every even m = 8..20 (Rud26, Thm 4.1), as a cross-check;
  (e) the printed decimals sqrt(977)/32 = 0.9767... and sqrt(241)/16 = 0.9702... are truncations (also checked by
      truncate_bounds.py).
Run: uv run python scripts/gk2d_rescramble.py      (~8 s; exit status 1 on any discrepancy)
"""
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
BIN = os.path.join(HERE, 'bin', 'gk2d_rescr')
if not os.path.exists(BIN):
    os.makedirs(os.path.dirname(BIN), exist_ok=True)
    subprocess.run(['g++', '-O3', '-std=c++17', '-o', BIN, os.path.join(HERE, 'gk2d_rescr.cpp')], check=True)
core = open(os.path.join(PAPER, 'core.tex')).read()

ok = True


def check(name, cond, msg):
    global ok
    print(('OK   ' if cond else 'FAIL ') + name + ': ' + msg)
    ok &= bool(cond)


def run(*args):
    return subprocess.run([BIN] + [str(a) for a in args], capture_output=True, text=True, check=True).stdout


def kv(line):
    return dict(t.split('=', 1) for t in line.split() if '=' in t)


# (a), (b)
for r in (2, 3, 4):
    R = 1 << r
    c = kv(run('census', r))
    check(f'census m={2 * r}', int(c['solutions']) == 2 ** (R - 1) and c['nested'] == c['solutions'],
          f"{c['solutions']} phase maps keep t=0, {c['nested']} of them nested (2^(R-1) = {2 ** (R - 1)})")
    j = kv(run('jitter', r))
    vals = [int(v) for v in j['values2RJ'].strip(',').split(',')]
    check(f'jitter m={2 * r}', vals == [R // 2 - 1] and int(j['scramblings']) == 2 ** (R - 1),
          f"2R*J over all {j['scramblings']} nested scramblings: {vals} (expected [{R // 2 - 1}], J = 1/4 - 1/(2R))")

# (c), (d)
for r in range(4, 11):
    m = 2 * r
    rows = {}
    for line in run('mind', r).splitlines():
        rows[line.split()[0]] = {k: int(v) for k, v in kv(line).items()}
    gk, rs = rows['GK'], rows['rescramble']
    check(f'GK m={m}', gk['bad'] == 0 and gk['tiling'] == 241 * 2 ** (m - 8),
          f"bad boxes {gk['bad']}, tiling d^2 = {gk['tiling']} = 241*2^(m-8)")
    if m == 8:    # tiling metric: worse, 229/256 against 241/256
        til_ok = rs['tiling'] == 229 and gk['tiling'] == 241
    else:         # tiling metric, m = 10..20: 977/1024 against 241/256 = 964/1024
        til_ok = rs['tiling'] == 977 * 2 ** (m - 10) and gk['tiling'] == 964 * 2 ** (m - 10)
    check(f'rescramble m={m}', rs['bad'] == 0 and rs['nested'] == 1 and til_ok,
          f"bad boxes {rs['bad']}, nested {rs['nested']}, tiling d^2 = {rs['tiling']} (GK {gk['tiling']}); "
          f"d^2 N/N^2 = {rs['tiling'] / 2 ** m:.6f} against {gk['tiling'] / 2 ** m:.6f}")


# (e) the printed text; no standard-torus comparison is printed in rem:gk2d any more
check('no standard torus in rem:gk2d', 'standard torus' not in core[core.index(r'\label{rem:gk2d}'):core.index(r'\label{fig:arcgk}')].split('The net is not digital')[0], 'rem:gk2d (i)-(iv) name only the tiling metric')
def trunc(x, d):
    return math.floor(x * 10 ** d) / 10 ** d


snips = [
    r'the slides that keep $t=0$ are exactly the nested scramblings of the van der Corput slides, and all of them are '
    r'equally far from lattice slides (both computed for $m\le8$)',
    r'Flipping the third binary digit of the slide on the lines $u\equiv2,3\pmod4$ is again a nested scrambling',
    r'In the tiling metric it is worse at $m=8$ ($\delta^2N=229/256$ against $241/256$), and for every even $m$ with '
    r'$10\le m\le20$ it has $\delta^2N=977/1024$ against $241/256=964/1024$, i.e.\ $\delta\sqrt N=0.9767\ldots$ '
    r'against $0.9702\ldots$ (computed)',
    r'distances are taken modulo the lattice $\langle(N,0),(N/4,N)\rangle$ of the row-shifted tiling for which they '
    r'were designed \cite{GK09,Rud26} (the tiling metric)',
    r'$\delta^2N=241/256$ in the tiling metric for every even $m\ge8$ \cite{Rud26}',
]
for s in snips:
    check('core.tex snippet', s in core, s[:70] + '...')
# 0.9767 / 0.9702 are truncations (exact integer square roots)
check('sqrt(977)/32 truncated', math.isqrt(977 * 10 ** 8 // 1024) == 9767, f'{math.sqrt(977) / 32:.8f}')
check('sqrt(241)/16 truncated', math.isqrt(241 * 10 ** 8 // 256) == 9702, f'{math.sqrt(241) / 16:.8f}')

print('OK' if ok else 'FAIL')
sys.exit(0 if ok else 1)
