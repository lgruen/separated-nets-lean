#!/usr/bin/env python3
"""cubecost.py -- Remark rem:cubecost of core.tex (computed values).

(1) whylat_cube.cpp enumerates, for every e = 1..11, all lattices of covolume 1 contained in (1/e)Z^3; the number of
    lattices is asserted to equal the number of sublattices of index e^3 of Z^3 (sum over a*b*c = e^3 of a^2 b), so
    the enumeration is complete.  Asserted: the largest minimum of a one-per-cube lattice over e <= 11 is
    sqrt(29/25) = 1.0770..., attained at e = 10 (and only there); it lies below 2^(1/6) = 1.1224....
(2) whylat_check.py re-checks the printed maximizers for e = 4, 6, 8, 9, 10 independently (one point per cube, exact
    minimum = the maximum found in (1)) and asserts that their offsets are not affine modulo 1 in the cell.

    g++ -O3 -std=c++17 -o scripts/bin/whylat_cube scripts/whylat_cube.cpp
    uv run python scripts/cubecost.py            (~25 s; e = 10, 11 take ~10 s each)
"""
import os
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import whylat_check  # noqa: E402

EXE = os.path.join(HERE, 'bin', 'whylat_cube')


def n_sublattices3(n):
    return sum(a * a * b for a in range(1, n + 1) if n % a == 0 for b in range(1, n // a + 1) if (n // a) % b == 0)


def main():
    if not os.path.exists(EXE):
        sys.exit(f'build first: g++ -O3 -std=c++17 -o {EXE} {os.path.join(HERE, "whylat_cube.cpp")}')
    t0 = time.time()
    best = {}
    for e in range(1, 12):
        out = subprocess.run([EXE, 'lat', '3', str(e)], capture_output=True, text=True, check=True).stdout
        nlat = int(re.search(r'lattices=(\d+)', out).group(1))
        a, b = map(int, re.search(r'one-per-cube lattices: [\d.]+ \(lambda\^2 = (\d+)/(\d+)\)', out).groups())
        best[e] = Fr(a, b)
        assert nlat == n_sublattices3(e ** 3), (e, nlat, n_sublattices3(e ** 3))
        print(f'  e={e:2d}: {nlat:8d} lattices (= # sublattices of index e^3), max one-per-cube lambda^2 = '
              f'{best[e]} = {float(best[e]) ** .5:.6f}', flush=True)
    top = max(best.values())
    assert top == Fr(29, 25) and [e for e in best if best[e] == top] == [10], best
    assert top ** 3 < 2, 'below 2^(1/6)'
    print(f'  largest minimum for e <= 11: sqrt(29/25) = {float(top) ** .5:.6f}..., at e = 10 only; '
          f'2^(1/6) = {2 ** (1 / 6):.6f}')
    for H, e in whylat_check.CASES:
        r = whylat_check.check(H, e)
        lam2 = Fr(*map(int, r['lam2'].split('/')))
        assert r['one_per_cube'] and lam2 == best[e] and r['offsets_linear_mod1'] is False, (H, e, r)
        print(f'  e={e:2d} maximizer H={H}: one per cube, lambda^2 = {lam2}, offsets affine mod 1: '
              f'{r["offsets_linear_mod1"]}')
    print(f'cubecost: all asserted values OK ({time.time() - t0:.1f} s)')


if __name__ == '__main__':
    main()
