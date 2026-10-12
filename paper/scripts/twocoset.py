#!/usr/bin/env python3
"""twocoset.py -- the computed values after Proposition prop:twocoset and Figure fig:arctwocoset(c).

Exact toroidal minimum distances, by the cell scan cellmin.cpp, of
  T_p  (Proposition prop:twocoset; rows  C_x: e_x, (0,h,h), (0,1,2);  C_y: e_y, (r,-1,1), (3,0,1);
        C_z: e_z, (r,-1,1), (1,5,0);  h = (p-1)/2, r = nearest integer to p/8)  at p = 101, 151, 211, 251, 307, 401,
        503, 1009, and
  (until rev 14.3 also E_p, the m = 3 net of the former thm:E1; its stored values stay in the json, and the paper's
  comparison nets at m = 3 are now recomputed by colnets.py.)
Asserted: every recomputed d2 equals the stored value in twocoset_exact.json (which figs_arc.py plots); for T_p it
equals the pair value d_*^2 of Proposition prop:twocoset(3); and the values printed in the paper (".9949..." etc.,
truncated; rev 14.1 prints T_p at p = 101, 1009 and E_p at p = 101, 307) are the truncations of sqrt(d2)/p^2.

    g++ -O3 -o scripts/bin/cellmin scripts/cellmin.cpp
    uv run python scripts/twocoset.py            (~2.5 min; p = 1009 alone ~85 s)
    uv run python scripts/twocoset.py --quick    (skips p = 1009, whose stored value is still checked; ~40 s)
"""
import json
import os
import subprocess
import sys
import time
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
CELLMIN = os.path.join(HERE, 'bin', 'cellmin')

PAPER_T = {101: '0.9949', 1009: '1.0132'}      # rev 14.1 prints only the two ends of the range (all eight are computed)
PAPER_E = {}                                   # rev 15.0: E_p values no longer printed (kept in the json)


def graph_form(p, kind):
    """cellmin input: p, then the 3x3 second-digit rows B and the 3x3 third-digit rows R (row c = coordinate c)"""
    if kind == 'T':
        h, r = (p - 1) // 2, round(p / 8)
        B = [[0, h, h], [r, -1, 1], [r, -1, 1]]
        R = [[0, 1, 2], [3, 0, 1], [1, 5, 0]]
    else:
        a = p // 3
        B = [[a, a, a]] * 3
        R = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
    rows = [' '.join(str(x % p) for x in row) for row in B + R]
    return f'{p}\n' + '\n'.join(rows) + '\n'


def cellmin(p, kind, *args):
    out = subprocess.run([CELLMIN, *map(str, args)], input=graph_form(p, kind), capture_output=True, text=True,
                         check=True).stdout
    return int(out.split()[0]), out.strip()


def dstar2(p):  # Proposition prop:twocoset(3): the pair of cells 0 and (p-1)1, integer scale p^3
    r = (p + 4) // 8
    return (p * p - 2 * p + 3) ** 2 + ((r - 1) * p + 4) ** 2 + ((r - 1) * p + 6) ** 2


def trunc4(d2, p):  # floor(sqrt(d2)/p^2 * 10^4), formatted like the paper
    f = isqrt(d2 * 10 ** 8 // p ** 4)
    return f'{f // 10000}.{f % 10000:04d}'


def main():
    if not os.path.exists(CELLMIN):
        sys.exit(f'build first: g++ -O3 -o {CELLMIN} {os.path.join(HERE, "cellmin.cpp")}')
    quick = '--quick' in sys.argv
    W = json.load(open(os.path.join(HERE, 'twocoset_exact.json')))
    bad = 0
    t0 = time.time()
    for kind, key in (('T', 'twocoset'),):   # rev 15.0: the net E_p (former thm:E1) is no longer printed
        for ps, rec in W[key].items():
            p = int(ps)
            t = time.time()
            if kind == 'T' and p == 1009:
                if quick:
                    d2, raw = rec['d2'], 'not recomputed (--quick)'
                else:   # two parts with a preset bound d_*^2 + 1: nothing below it, so the minimum is d_*^2
                    pre = dstar2(p) + 1
                    d2a, rawa = cellmin(p, kind, 0, 6, pre)
                    d2b, rawb = cellmin(p, kind, 6, 1000, pre)
                    d2, raw = min(d2a, d2b), rawa + ' | ' + rawb
            else:
                d2, raw = cellmin(p, kind)
            ok = d2 == rec['d2'] and (kind == 'E' or d2 == dstar2(p))
            paper = (PAPER_T if kind == 'T' else PAPER_E).get(p)
            if paper is not None:
                ok &= trunc4(d2, p) == paper
            bad += not ok
            print(f'  {kind}_{p:<5d} d2={d2:<14d} c={trunc4(d2, p)}...  paper {paper or "(figure only)":>13s}  '
                  f'{"ok" if ok else "MISMATCH"}  ({time.time() - t:.1f} s)  [{raw}]', flush=True)
    print(f'twocoset: {"all values agree" if not bad else f"{bad} MISMATCH(ES)"} ({time.time() - t0:.1f} s)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
