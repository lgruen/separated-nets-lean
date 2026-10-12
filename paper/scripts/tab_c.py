#!/usr/bin/env python3
"""tab_c.py -- Table tab:c of core.tex (dimension three, m = 6).

Exact values: the normalized toroidal minimum distance c = delta N^{1/3} of P_{2,q} (Definition def:net; q = 4..13,
16), by the exact neighbour-cell scan of netmind.cpp over all N = q^6 points (nets rebuilt from the paper's formulas
by netdefs.py); printed truncated, 4 digits (rev 15.2; rounded to nearest before).  Formula row, in exact integer arithmetic: c(q) of Theorem
thm:main (truncated).  Both rows are read from core.tex at run time and every printed value is asserted.
(Until rev 14.0 this script was tab_c_two.py and also checked Table tab:two, the nets Q_{2,p}; that table is no longer
in the paper.)

    g++ -O3 -std=c++17 -o scripts/bin/netmind scripts/netmind.cpp
    uv run python scripts/tab_c.py            (~3 s)
"""
import os
import subprocess
import sys
import time
from fractions import Fraction as Fr
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import netdefs  # noqa: E402

NETMIND = os.path.join(HERE, 'bin', 'netmind')

CORE = os.path.join(os.path.dirname(HERE), 'core.tex')


def printed_tab_c():
    """the rows q, c(q), P_{2,q} exact of Table tab:c, read from core.tex."""
    L = open(CORE).read().split('\n')
    i = next(i for i, l in enumerate(L) if '\\label{tab:c}' in l)
    j = max(j for j in range(i) if '\\begin{table}' in L[j])
    rows = {}
    for l in L[j:i]:
        cells = [c.strip() for c in l.strip().rstrip('\\').split('&')]
        for key, tag in (('q', '$q$'), ('cq', 'certified $c(q)$'), ('P2', 'exact $c$ of $\\mathcal P_{2,q}$')):
            if cells[0].startswith(tag):
                rows[key] = cells[1:]
    assert set(rows) == {'q', 'cq', 'P2'}, rows
    qs = [int(x) for x in rows['q']]
    return dict(zip(qs, rows['cq'])), dict(zip(qs, rows['P2']))


def fmt(n, d=4):
    return '.' + str(n).zfill(d) if n < 10 ** d else '1.' + str(n - 10 ** d).zfill(d)


def sqrt_trunc(r, d=4):          # floor(sqrt(r) 10^d), r a nonnegative Fraction
    y = r * 10 ** (2 * d)
    return isqrt(y.numerator // y.denominator)


def sqrt_trunc_d2(d2, W, d=4):   # floor(sqrt(d2)/W 10^d), exactly (floor of floor is floor)
    return isqrt(d2 * 10 ** (2 * d) // (W * W))


def c_main(q):                   # Theorem thm:main
    q = Fr(q)
    return min((1 - 1 / q) ** 2, (1 - 2 / q) ** 2 + (1 - 4 / q) ** 2, 3 * (1 - 3 / q) ** 2)


def exact_min(C, q):
    m = len(C[0])
    inp = f'{q} {m} 3\n' + ''.join(' '.join(str(x % q) for r in Cc for x in r) + '\n' for Cc in C)
    out = subprocess.run([NETMIND], input=inp, capture_output=True, text=True, check=True).stdout
    kv = dict(t.split('=', 1) for t in out.split())
    return int(kv['d2']), int(kv['W']), out.strip()


def main():
    if not os.path.exists(NETMIND):
        sys.exit(f'build first: g++ -O3 -std=c++17 -o {NETMIND} {os.path.join(HERE, "netmind.cpp")}')
    bad = 0

    def row(label, got, want):
        nonlocal bad
        ok = got == want
        bad += not ok
        print(f'  {label:34s} {got:>7s}  paper {want:>7s}  {"ok" if ok else "MISMATCH"}')

    t0 = time.time()
    TAB_C_CQ, TAB_C_P2 = printed_tab_c()
    print('Table tab:c  (m = 6; printed values read from core.tex)')
    for q in TAB_C_P2:
        row(f'c({q})  (thm:main, truncated)', fmt(sqrt_trunc(c_main(q))), TAB_C_CQ[q])
        d2, W, raw = exact_min(netdefs.P_mats(2)['C'], q)
        row(f'P_(2,{q}) exact (truncated)', fmt(sqrt_trunc_d2(d2, W)), TAB_C_P2[q])
        print(f'      netmind: {raw}')
    print(f'tab_c: {"all values agree with the paper" if not bad else f"{bad} MISMATCH(ES)"} '
          f'({time.time() - t0:.1f} s)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
