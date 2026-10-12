#!/usr/bin/env python3
"""as_table.py -- Table tab:astar (Theorem A) and the values derived from it elsewhere in core.tex.

Recomputed here, and compared with the cells of tab:astar as printed in core.tex (read at run time):
  * a*_s and the largest entry max|M^(j)| of the design U*_s, s = 3..10, by ustar_det.py (Definition def:Ustar,
    exact integer / rational arithmetic, python-flint for the Hermite normal forms; it also checks the column
    polynomials of Proposition prop:F and the dominance of the diagonal);
  * 5a*_s + 4 (exact);
  * the bound 2(s-1)^{3/2}(3/2)^{s-2}(s-2)! of Theorem A (truncated at the printed precision, exact
    rational comparison; rev 15.2, rounded to nearest before) and a*_s <= bound for s >= 4;
  * a_s of the monomial design U_s (Remark rem:Us), from its definition: places {inf,0,...,s-2},
    L_s = lcm(1..s-2)^(s-1), F_n[c][d] = L_s/(c-d)^(n+1), F_n[inf][d] = [n=0], F_n[c][inf] = L_s binom(c,n),
    M^(j) = F_0+...+F_j, alpha_c = sum_{d!=c} max_j |M^(j)[c][d]|, a_s = max_c alpha_c (exact; printed exactly
    below 10^5, else truncated to three significant digits; rev 15.2), and a_s <= L_s (s^2 + 2^(s-2)).
Also: the display of U*_3 before tab:astar (F_0, F_1), the list a*_s = 2,...,13640 and the thresholds q = 14, 29, 84
of the introduction, a_5 = 17407 (introduction, rem:Us), and the rows a*_s and floor lcm(1,...,s-3) of tab:Kdesigns.

    uv run --with python-flint python scripts/as_table.py        (~1 s)
"""
import os
import re
import sys
from fractions import Fraction as Fr
from math import comb, lcm, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ustar_det  # noqa: E402  (needs python-flint)

CORE = os.path.join(os.path.dirname(HERE), 'core.tex')
TEX = open(CORE).read()
LINES = TEX.split('\n')
BAD = []


def ok(label, cond, detail=''):
    print(f'  {"ok      " if cond else "MISMATCH"} {label}' + (f'   [{detail}]' if detail else ''))
    if not cond:
        BAD.append(label)


def table_rows(label):
    i = next(i for i, l in enumerate(LINES) if '\\label{%s}' % label in l)
    j = max(j for j in range(i) if '\\begin{table}' in LINES[j])
    out = []
    for l in LINES[j:i]:
        if '&' in l and '\\begin{tabular}' not in l:
            t = l.strip()
            if t.endswith('\\\\'):
                t = t[:-2]
            out.append([c.strip() for c in t.split('&')])
    return out


def row(rows, head):
    r = [r for r in rows if r[0].startswith(head)]
    assert len(r) == 1, (head, r)
    return r[0][1:]


def parse_num(cell):
    """printed number -> (value as Fraction, unit of the last printed digit).  '46.8', '324', '$2.68\\cdot10^4$'."""
    c = cell.replace('$', '').replace('{', '').replace('}', '').strip()
    m = re.fullmatch(r'([0-9.]+)(?:\\cdot10\^(\d+))?', c)
    assert m, cell
    mant, e = m.group(1), int(m.group(2) or 0)
    d = len(mant.split('.')[1]) if '.' in mant else 0
    return Fr(mant) * 10 ** e, Fr(10 ** e, 10 ** d)


def trunc_ok(x2, cell):
    """the printed cell is the truncation of sqrt(x2) (x2 >= 0 rational) at its last printed digit."""
    v, u = parse_num(cell)
    return v ** 2 <= x2 < (v + u) ** 2


def a_U(s):
    """a_s of the monomial design U_s (Remark rem:Us), exact."""
    n = s - 2
    L = lcm(*range(1, n + 1)) ** (s - 1)
    places = ['inf'] + list(range(n + 1))

    def F(j, c, d):
        if c == 'inf':
            return Fr(1 if j == 0 else 0)
        if d == 'inf':
            return Fr(L * comb(c, j))
        return Fr(L, (c - d) ** (j + 1))

    alpha = []
    for c in places:
        tot = Fr(0)
        for d in places:
            if d == c:
                continue
            ps, best = Fr(0), Fr(0)
            for j in range(s - 1):
                ps += F(j, c, d)
                best = max(best, abs(ps))
            tot += best
        assert tot.denominator == 1
        alpha.append(int(tot))
    a = max(alpha)
    assert a <= L * (s * s + 2 ** (s - 2))
    return a


def bound2(s):
    """square of 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!"""
    return 4 * Fr(s - 1) ** 3 * Fr(9, 4) ** (s - 2) * factorial(s - 2) ** 2


def main():
    rows = table_rows('tab:astar')
    S = [int(x) for x in row(rows, '$s$')]
    assert S == list(range(3, 11)), S
    pa, pmx = row(rows, '$a^*_s$'), row(rows, 'largest entry')
    p5a, pbd, paU = row(rows, '$5a^*_s+4$'), row(rows, 'bound of Theorem'), row(rows, '$a_s$ of $U_s$')
    A = {}
    print('Table tab:astar (printed cells read from core.tex)')
    for i, s in enumerate(S):
        F, Mp, alpha, ties, ratio = ustar_det.construct(s)
        assert ustar_det.check(s, F, Mp, alpha)
        a = max(alpha)
        mx = max(abs(Mp[j][c][d]) for j in range(s - 1) for c in range(s) for d in range(s) if c != d)
        A[s] = (a, F)
        ok(f's={s:2d} a*_s = {a}', str(a) == pa[i], f'printed {pa[i]}')
        ok(f's={s:2d} largest entry of U*_s = {mx}', str(mx) == pmx[i], f'printed {pmx[i]}')
        ok(f's={s:2d} 5a*_s+4 = {5 * a + 4}', str(5 * a + 4) == p5a[i], f'printed {p5a[i]}')
        if s == 3:
            ok('s= 3 bound of Theorem A printed "--" (s >= 4 only)', pbd[i] == '--')
        else:
            b2 = bound2(s)
            ok(f's={s:2d} bound 2(s-1)^(3/2)(3/2)^(s-2)(s-2)! = {float(b2) ** .5:.6g} truncates to {pbd[i]}',
               trunc_ok(b2, pbd[i]))
            ok(f's={s:2d} a*_s <= bound', a * a <= b2)
        aU = a_U(s)
        v, u = parse_num(paU[i])
        ok(f's={s:2d} a_s(U_s) = {aU:.6g} truncates to {paU[i]}', v <= aU < v + u and (u == 1) == (aU < 10 ** 5),
           'exact below 1e5, three significant digits above')
    # the display of U*_3 before the table (coordinate order inf, 0, 1)
    mats = re.findall(r'F_(\d)=\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}', TEX[:TEX.index('\\label{tab:astar}')])
    disp = {int(k): [[int(x) for x in r.split('&')] for r in body.split('\\\\')] for k, body in mats[-2:]}
    ok('display of U*_3 (F_0, F_1) before tab:astar = U*_3 of ustar_det.py', [disp[0], disp[1]] == A[3][1])
    print('Introduction and remarks')
    lst = ','.join(str(A[s][0]) for s in S)
    ok(f'intro "a^*_s={lst}"', f'$a^*_s={lst}$' in TEX)
    ok('intro "from q=14, 29 and 84" = 5a*_s+4 (s=3,4,5)',
       f'from $q={5 * A[3][0] + 4}$, ${5 * A[4][0] + 4}$ and ${5 * A[5][0] + 4}$ on' in TEX)
    a5 = a_U(5)
    ok(f'a_5 = {a5} (intro, rem:Us)', TEX.count(f'$a_5={a5}$') == 2, f'occurrences {TEX.count(f"$a_5={a5}$")}')
    ok('Theorem A: "a^*_3=2"', '$a^*_3=2$' in TEX and A[3][0] == 2)
    print('Table tab:Kdesigns (rows a*_s and lower bound on K(F))')
    rk = table_rows('tab:Kdesigns')
    SK = [int(x) for x in row(rk, '$s$')]
    for s, cell in zip(SK, row(rk, '$a^*_s$')):
        ok(f's={s} a*_s = {A[s][0]}', cell == str(A[s][0]), f'printed {cell}')
    for s, cell in zip(SK, row(rk, 'lower bound on $K(F)$')):   # rev 15.7 pass 3: was 'floor'
        fl = lcm(*range(1, s - 2))
        ok(f's={s} floor lcm(1,...,s-3) = {fl}', cell == str(fl), f'printed {cell}')
    print('as_table:', 'all values agree with core.tex' if not BAD else f'{len(BAD)} MISMATCH(ES): {BAD}')
    sys.exit(1 if BAD else 0)


if __name__ == '__main__':
    main()
