#!/usr/bin/env python3
"""Certificates of Proposition prop:S1E (Euclidean form of Theorem thm:S1) and Table tab:S1E.

For each (p, kappa) of the witness files e1_random_search.txt and e1_rootlattice_rounding.txt, recompute EXACTLY (exact-rational LLL + complete enumeration of
all lattice vectors with ||a|| <= lam_jit + sqrt(s), each re-checked in integers; code of the audit,
codesaudit_e1.py) the integer
    J2 = min_{0 != a in Lambda_h} ||(|a|-1)_+||_2^2,   Lambda_h = {a : a_z == sum_d kappa_d a_{x_d} (mod p)},
so that the certified bound is c_jit = sqrt(J2) * p^(-1/s) (a lower bound on delta N^{1/s}).
Run: uv run python scripts/s1e_certs.py   (< 5 s).  Imported by truncate_bounds.py (function certs()).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from codesaudit_e1 import analyse  # noqa: E402

FILES = {'search': os.path.join(HERE, 'e1_random_search.txt'),
         'round': os.path.join(HERE, 'e1_rootlattice_rounding.txt')}


def rows():
    out = []
    for line in open(FILES['search']):
        m = re.match(r'(\d+) (\d+) .*kappa=([\d,]+),', line)
        if m:
            out.append(('search', int(m.group(1)), int(m.group(2)), [int(x) for x in m.group(3).split(',')]))
    for line in open(FILES['round']):
        m = re.match(r'(\w+) (1e\d+) mode3 s=(\d+) .* p=(\d+) c_jit=\S+ kappa=([\d,]+),', line)
        if m:
            out.append(('round:' + m.group(1) + ':' + m.group(2), int(m.group(3)), int(m.group(4)),
                        [int(x) for x in m.group(5).split(',')]))
    return out


def certs():
    """list of dicts: src, s, p, kappa, J2 (exact integer), rho_bound_num (rho-1, for comparison)."""
    res = []
    for src, s, p, kap in rows():
        r = analyse(p, kap)
        assert r['s'] == s
        res.append(dict(src=src, s=s, p=p, kappa=kap, J2=r['lamjit2']))
    return res


if __name__ == '__main__':
    for r in certs():
        c = r['J2'] ** 0.5 * r['p'] ** (-1 / r['s'])
        print('%-16s s=%d p=%-12d J2=%-5d c_jit~%.6f kappa=%s' % (r['src'], r['s'], r['p'], r['J2'], c,
                                                                  ','.join(map(str, r['kappa']))))
