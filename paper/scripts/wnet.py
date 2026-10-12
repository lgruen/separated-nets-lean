#!/usr/bin/env python3
"""wnet.py -- rev 15.1: the rank-one nets W_p of Proposition prop:wnet (Section sec:wnet) and the remarks around it.

W_p over F_p (p >= 5 prime, h = (p-1)/2, r = floor(p/48), rho = 2r+1): generator rows
    C_x: e_x, rho(-1,-1,2), (0,1,2);   C_y: e_y, rho(-1,-1,2), (1,0,1);   C_z: e_z, (h-r,h-r,rho), (0,1,0).
z reads zeta(n) = u.n mod p, u = (h-r,h-r,rho); x and y read 2 zeta mod p.

Checked here, in exact arithmetic (Fractions / integers) unless stated:
  (1) t = 0: the 10 box determinants built from the generator matrices are units mod p, every prime 5 <= p <= 3000;
      the printed minors -rho, 2rho, h-r (boxes (2,1,0)) and -4rho, -3rho, h-r (boxes (3,0,0)).
  (2) Lemma lem:wwrap (the exact wrap set) by enumerating all cells, p = 5..23 (--full: ..31).
  (3) the realizability rule of the proof (table of (M, kappa)) against Lemma lem:wwrap at every prime 53..1500
      (--full ..5000), and the identity u.E = (pS - Q rho)/2.
  (4) Table tab:wcontacts: every realizable option with |A|^2 <= 9/4 (up to the symmetries) is a printed row; A lies in
      the lattice of the proof; the values q(1/48), the slopes, the monotone check at p = 53 for rows (c)-(g); the
      uniform bound for |A|^2 >= 3.
  (5) rev 15.3: the tangent-line step of the proof of (2) (Table tab:wclasses was removed); and, as an independent
      check of (2) of the proposition, the full quadratic |V0 + V1/p|^2 - (281/256 - 345/(128p)) >= 0 for every option, every class and
      every real p >= 53 (the audit's form).
  (6) the direct relaxation (min over the options of Lemma lem:wwrap at the prime itself) >= 281/256 - 345/(128p) at
      every prime 53..3000 (--full ..20000).
  (7) the pair of part (3): d*^2 against points generated from the matrices, every prime 53..2000; d*/p^2 <
      sqrt(281)/16 + 5/(2p) there; d*/p^2 > c at every computed prime >= 53 (the pair is not the closest pair).
  (8) the constants of (2), (4): the bound at p = 61, 67, 89, 97.
  (9) exact minimum distances (cellmin.cpp, the cell scan of twocoset.py): W_p at every prime 5..199 (c > 1 exactly for
      17 <= p, c < 1 for p <= 13; c > sqrt66/8 for 53..199), at 307 and 353; T_p (colnets_exact.json) behind W_p at
      every prime 17..47 other than 23; the net T15 of the remark (t = 0 and c at p = 307).
 (10) digital shifts of W_101 (shiftmin.cpp): shifts of the second digits that keep or break g_x = g_y = 2 g_z; rev 15.3:
      a = 2b + 1 keeps it too ((1,1,0), (3,3,1), (5,5,2)), every (c,c,0) with 2 <= c <= 100 breaks it (< 0.1356).
 (11) the limit model of the text (phases in a subtorus Y): 33/32 for T_p, 281/256 for W_p, 233/225 for the T15 layer.
 (12) every value printed in core.tex for these items (quoted snippets).

    g++ -O3 -std=c++17 -o scripts/bin/cellmin scripts/cellmin.cpp
    g++ -O3 -std=c++17 -o scripts/bin/shiftmin scripts/shiftmin.cpp
    uv run python scripts/wnet.py            (~25 s)
    uv run python scripts/wnet.py --full     (longer ranges; ~2 min)
    uv run python scripts/wnet.py --write    (regenerate w_exact.json, the data of figs_wnet.py)
"""
import itertools
import json
import math
import os
import re
import subprocess
import sys
from fractions import Fraction as Fr
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
CORE = os.path.join(PAPER, 'core.tex')
CELLMIN = os.path.join(HERE, 'bin', 'cellmin')
SHIFTMIN = os.path.join(HERE, 'bin', 'shiftmin')
FULL = '--full' in sys.argv
FAIL = []
NCHK = [0]
WV = (2, 2, 1)                         # the vector w = (2,2,1) of the layer w u^T
STEPS = [E for E in itertools.product(range(-2, 3), repeat=3) if any(E)]
MU2 = Fr(281, 256)
K = Fr(345, 128)


def check(ok, what):
    NCHK[0] += 1
    if not ok:
        FAIL.append(what)
        print('  FAIL:', what)


def isprime(n):
    return n > 1 and all(n % k for k in range(2, isqrt(n) + 1))


def primes(a, b):
    return [p for p in range(a, b + 1) if isprime(p)]


def W(p):
    h, r = (p - 1) // 2, p // 48
    rho = 2 * r + 1
    return [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]


def T(p):   # prop:twocoset
    h, r = (p - 1) // 2, round(p / 8)
    return [[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]


def T15(p):  # the rank-two layer of the remark after prop:wnet (third rows of T_p)
    a, r = round(2 * p / 5), round(p / 15)
    return [[0, a, a], [2 * r, -r, -r], [2 * r, -r, -r]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]


def detmod(M, p):
    M = [[x % p for x in row] for row in M]
    n, d = len(M), 1
    for i in range(n):
        piv = next((k for k in range(i, n) if M[k][i]), None)
        if piv is None:
            return 0
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            d = -d
        d = d * M[i][i] % p
        inv = pow(M[i][i], p - 2, p)
        for k in range(i + 1, n):
            f = M[k][i] * inv % p
            for j in range(n):
                M[k][j] = (M[k][j] - f * M[i][j]) % p
    return d % p


def is_net(B, R, p):
    """t = 0 of the graph form with rows e_c, B_c, R_c: all 10 box determinants are units mod p"""
    for d in itertools.product(range(4), repeat=3):
        if sum(d) != 3:
            continue
        rows = []
        for c in range(3):
            rows += [[int(j == c) for j in range(3)], B[c], R[c]][:d[c]]
        if detmod(rows, p) == 0:
            return False
    return True


def tex_num(x):
    x = x.strip().strip('$').strip()
    sg = 1
    if x.startswith('-'):
        sg, x = -1, x[1:]
    m = re.fullmatch(r'\\frac(\{\d+\}|\d)(\{\d+\}|\d)', x)
    if m:
        return sg * Fr(int(m.group(1).strip('{}')), int(m.group(2).strip('{}')))
    return sg * Fr(int(x))


def tex_tuple(x):
    x = x.strip().strip('$').strip()
    assert x[0] == '(' and x[-1] == ')', x
    return tuple(tex_num(t) for t in x[1:-1].split(','))


def tex_poly(x):
    x = x.strip().strip('$').replace(' ', '')
    c = [Fr(0)] * 3
    for sg, num, var, sq in re.findall(r'([+-]?)(\\frac\{\d+\}\{\d+\}|\d+)(\\varepsilon(\^2)?)?', x):
        v = tex_num(num) * (-1 if sg == '-' else 1)
        c[0 if not var else (2 if sq else 1)] += v
    return tuple(c)


# ------------------------------------------------------------------------------------------- the options of the proof
def options():
    """all (E, M, kappa) admitted by the realizability rule of the proof (valid for every prime p >= 53), with
    A = E + (2M-kappa)(1,1,0) + M e_z and Q = E_x + E_y - 2E_z; then V = A - Q eps w, eps = rho/(2p)."""
    out = []
    for E in STEPS:
        S = E[0] + E[1]
        Q = S - 2 * E[2]
        for twoM in range(-3, 4):
            if (twoM - S) % 2:
                continue
            M = Fr(twoM, 2)
            if Q == 0:
                ks = [0] if M == 0 else []
            elif M == 0:
                ks = [0, -1 if Q > 0 else 1]
            elif abs(M) == Fr(1, 2):
                s = 1 if M > 0 else -1
                ks = [s] + ([0] if s * Q >= 1 else [])
            elif abs(M) == 1:
                s = 1 if M > 0 else -1
                ks = [s] if s * Q >= 1 else []
            else:
                ks = []
            for k in ks:
                A = (E[0] + 2 * M - k, E[1] + 2 * M - k, E[2] + M)
                out.append((E, M, k, A, Q))
    return out


def lemma_set(p, E):
    """Lemma lem:wwrap: the realized (dzeta, kappa) for the step E at the prime p (from the lemma's statement)"""
    B, R = W(p)
    u = B[2]
    h = (p - 1) // 2
    sig = sum(a * b for a, b in zip(u, E)) % p
    out = set()
    for dz in ([0] if sig == 0 else [sig, sig - p]):
        s = (dz > 0) - (dz < 0)
        out.add((dz, s))
        if dz != 0 and abs(dz) <= h:
            out.add((dz, 0))
    return out


def lemma_by_cells(p):
    B, R = W(p)
    u = B[2]
    ok = True
    for E in STEPS:
        real = set()
        for n in itertools.product(range(p), repeat=3):
            z = sum(a * b for a, b in zip(u, n)) % p
            m = [(n[i] + E[i]) % p for i in range(3)]
            z2 = sum(a * b for a, b in zip(u, m)) % p
            g = [sum(B[c][j] * n[j] for j in range(3)) % p for c in range(3)]
            g2 = [sum(B[c][j] * m[j] for j in range(3)) % p for c in range(3)]
            k = (2 * z2 >= p) - (2 * z >= p)
            if not (g[2] == z and g[0] == g[1] == 2 * z % p and g2[2] == z2):
                ok = False
            if [g2[c] - g[c] for c in range(3)] != [2 * (z2 - z) - p * k] * 2 + [z2 - z]:
                ok = False
            real.add((z2 - z, k))
        ok &= real == lemma_set(p, E)
    return ok


def nrm(v):
    return sum(x * x for x in v)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def quad(A, Q):
    """|A - Q eps w|^2 = c0 + c1 eps + c2 eps^2"""
    return nrm(A), -2 * Q * dot(A, WV), 9 * Q * Q


def ev(c, x):
    return c[0] + c[1] * x + c[2] * x * x


# rows of tab:wcontacts: (|A|^2, Q A.w, Q^2) -> printed name
ROWS = {(Fr(5, 4), Fr(9, 2), 9): 'a', (Fr(1), Fr(-2), 4): 'b', (Fr(5, 4), Fr(5, 2), 1): 'c',
        (Fr(5, 4), Fr(3, 2), 1): 'd', (Fr(5, 4), Fr(-5, 2), 1): 'e', (Fr(2), Fr(8), 4): 'f', (Fr(2), Fr(0), 0): 'g'}


def contact_rows():
    rows = {}
    for E, M, k, A, Q in options():
        n = nrm(A)
        if n <= Fr(9, 4):
            key = (n, Q * dot(A, WV), Q * Q)
            rows.setdefault(key, []).append((E, M, k, A, Q))
    return rows


def model_value(Amat, Y):
    """the limit model: min |E + beta - kappa|^2 over E in {-2..2}^3 \\ 0 and the wrap patterns kappa realized by an open
    box that meets the phase set Y ('free', ('rank1', w), ('pair', c1, c2) for psi_c1 = psi_c2); beta = {A E}."""
    best = None
    for E in STEPS:
        beta = [sum(Amat[c][d] * E[d] for d in range(3)) % 1 for c in range(3)]
        for kap in itertools.product((0, 1), repeat=3):
            if any(kap[c] and beta[c] == 0 for c in range(3)):
                continue
            iv = [(1 - beta[c], Fr(1)) if kap[c] else (Fr(0), 1 - beta[c]) for c in range(3)]
            if not realizable(iv, Y):
                continue
            v = nrm([E[c] + beta[c] - kap[c] for c in range(3)])
            if best is None or v < best:
                best = v
    return best


def realizable(iv, Y):
    if Y == 'free':
        return all(lo < hi for lo, hi in iv)
    if Y[0] == 'pair':
        c1, c2 = Y[1], Y[2]
        lo, hi = max(iv[c1][0], iv[c2][0]), min(iv[c1][1], iv[c2][1])
        return lo < hi and all(iv[c][0] < iv[c][1] for c in range(3) if c not in (c1, c2))
    w = Y[1]                                 # theta in [0,1), coordinate c at {theta w_c}
    bps = {Fr(0), Fr(1)}
    for c in range(3):
        for j in range(abs(w[c]) + 1):
            for b in (iv[c][0], iv[c][1]):
                t = (j + b) / abs(w[c])
                if 0 <= t <= 1:
                    bps.add(t)
    bps = sorted(bps)
    for a, b in zip(bps, bps[1:]):
        th = (a + b) / 2
        if all(iv[c][0] < (th * w[c]) % 1 < iv[c][1] for c in range(3)):
            return True
    return False


def cellmin(B, R, p, prog=CELLMIN, shift=None):
    inp = f'{p}\n' + '\n'.join(' '.join(str(x % p) for x in row) for row in B + R) + '\n'
    if shift is not None:
        inp += ' '.join(str(x % p) for x in shift) + '\n'
    out = subprocess.run([prog], input=inp, capture_output=True, text=True, check=True).stdout
    return int(out.split()[0])


def dstar2(p):
    h, r = (p - 1) // 2, p // 48
    return (p * p - (6 * r + 2) * p - 2) ** 2 + ((6 * r + 3) * p) ** 2 + ((h + 3 * r + 2) * p) ** 2


def point(B, R, p, n):
    return [p * p * n[c] + p * (sum(B[c][j] * n[j] for j in range(3)) % p) + sum(R[c][j] * n[j] for j in range(3)) % p
            for c in range(3)]


def tor2(a, b, p):
    P3 = p ** 3
    s = 0
    for x, y in zip(a, b):
        d = (y - x) % P3
        d = min(d, P3 - d)
        s += d * d
    return s


def bound(p):   # (2): sqrt(281/256 - 345/(128p)) - sqrt3/p
    return math.sqrt(281 / 256 - 345 / (128 * p)) - math.sqrt(3) / p


def lb_trunc(x, nd=4):
    return math.floor(x * 10 ** nd) / 10 ** nd


def main():
    TEX = open(CORE, encoding='utf-8').read()
    i0 = TEX.index('\\label{sec:wnet}')
    SEC = TEX[i0:TEX.index('\\subsection', i0 + 20)]

    print('(1) t = 0 of W_p from its generator matrices')
    bad = [p for p in primes(5, 3000) if not is_net(*W(p), p)]
    check(not bad, f'W_p is a (0,3,3)-net for every prime 5 <= p <= 3000 (exceptions: {bad})')
    for p in primes(5, 3000):
        B, R = W(p)
        h, r = (p - 1) // 2, p // 48
        rho = 2 * r + 1
        offd = [B[0][1], B[0][2], B[1][0], B[1][2], B[2][0], B[2][1]]
        m300 = [B[0][1] * R[0][2] - B[0][2] * R[0][1], B[1][0] * R[1][2] - B[1][2] * R[1][0],
                B[2][0] * R[2][1] - B[2][1] * R[2][0]]
        if offd != [-rho, 2 * rho, -rho, 2 * rho, h - r, h - r] or m300 != [-4 * rho, -3 * rho, h - r] \
                or not (1 <= rho < p and 1 <= h - r < p) or any((2 * u - v) % p for u, v in zip(B[2], B[0])):
            check(False, f'printed minors / 2u = B_x at p = {p}')
    print('    10 box determinants units at all', len(primes(5, 3000)), 'primes; minors -rho, 2rho, h-r, -4rho, -3rho')

    print('(2) Lemma lem:wwrap by enumeration of all cells')
    ps = primes(5, 31 if FULL else 23)
    check(all(lemma_by_cells(p) for p in ps), f'lem:wwrap at p = {ps}')
    print('    realized (dzeta, kappa) = the lemma\'s set for every step, p =', ps)

    print('(3) the realizability rule of the proof against Lemma lem:wwrap')
    OPT = options()
    nbad = 0
    for p in primes(53, 5000 if FULL else 1500):
        B, R = W(p)
        rho = 2 * (p // 48) + 1
        for E in STEPS:
            S, Q = E[0] + E[1], E[0] + E[1] - 2 * E[2]
            if 2 * dot(B[2], E) != p * S - Q * rho:
                nbad += 1
            got = {(Fr(2 * dz + Q * rho, 2 * p), k) for dz, k in lemma_set(p, E)}
            rule = {(M, k) for (E2, M, k, A, Q2) in OPT if E2 == E}
            nbad += got != rule
    check(nbad == 0, f'realizability rule = Lemma lem:wwrap at every prime 53..{5000 if FULL else 1500} ({nbad} bad)')
    print(f'    {len(OPT)} options; rule and identity u.E = (pS - Q rho)/2 agree with the lemma at every prime in range')

    print('(4) Table tab:wcontacts')
    rows = contact_rows()
    check(set(rows) == set(ROWS), f'short options give exactly the rows a-g ({sorted(rows)})')
    for key, lst in rows.items():
        for E, M, k, A, Q in lst:
            check((A[0] + A[1] - 2 * A[2]) % 2 == 0 and A[0].denominator == 1 and A[1].denominator == 1,
                  f'A = {A} in the lattice (a+b even... a+b = 2c mod 2)')
    for E, M, k, A, Q in OPT:
        check(all(2 * x == int(2 * x) for x in A) and (A[0] + A[1] - 2 * A[2]) % 2 == 0 and nrm(A) > 0,
              f'A in Lambda, A != 0 ({E},{M},{k})')
        check(abs(Q - (A[0] + A[1] - 2 * A[2]) + 2 * M - 2 * k) == 0 and abs(2 * k - 2 * M) <= 2, 'Q identity')
        if nrm(A) >= 3:
            # |V| >= |A| - 3|Q| eps with eps <= 3/100: |V| >= (1 - 9 sqrt6/100)|A| - 9/50 >= 1.05 for |A|^2 >= 3
            check(math.sqrt(nrm(A)) - Fr(9, 100) * abs(Q) > 1.05, f'uniform bound for |A|^2 >= 3 at {E}')
    e0 = Fr(1, 48)
    tab = {}
    for key, name in ROWS.items():
        c = (key[0], -2 * key[1], 9 * key[2])
        val = ev(c, e0)
        slope = c[1] + 2 * c[2] * e0
        tab[name] = (key, c, val, slope)
        if name not in 'ab':
            # p (LHS - RHS) = p (q(1/48) - 281/256) - (23/48)|q'| is nondecreasing in p; positive at p = 53
            check(val > MU2 and 53 * (val - MU2) - Fr(23, 48) * abs(slope) > 0, f'row {name}: > 281/256 for p >= 53')
    check(tab['a'][2] == MU2 and tab['a'][3] == Fr(-45, 8), 'row a: 281/256, slope -45/8')
    check(tab['b'][2] == Fr(211, 192) and tab['b'][3] == Fr(11, 2), 'row b: 211/192, slope 11/2')
    check(Fr(45, 8) * Fr(23, 48) == K and Fr(11, 2) * Fr(23, 48) < K, '345/128 = (45/8)(23/48); (11/2)(23/48) < 345/128')
    check(19 * 50 < 3 * 636 and Fr(1, 48) + Fr(23, 48 * 53) == Fr(19, 636), 'eps <= 19/636 < 3/100 for p >= 53')
    check(Fr(105, 100) ** 2 > MU2 and (1 - 9 * math.sqrt(6) / 100) * math.sqrt(3) - 0.18 > 1.05, 'uniform constant 1.05')
    # the printed table
    m = re.search(r'\\label\{tab:wcontacts\}', TEX)
    tb = TEX[TEX.rfind('\\begin{tabular}', 0, m.start()):m.start()]
    body = tb[tb.index('\\midrule'):tb.index('\\bottomrule')]
    lines = [ln.strip() for ln in body.split('\\\\') if '&' in ln]
    printed, cur = {}, None
    for ln in lines:
        cells = [x.strip() for x in ln.replace('\\midrule', '').split('&')]
        if cells[0]:
            cur = cells[0].strip('()')
            printed[cur] = dict(A=tex_tuple(cells[1]), Q=tex_num(cells[4]), poly=tex_poly(cells[5]),
                                val=tex_num(cells[6]), slope=tex_num(cells[7]), steps=[])
        printed[cur]['steps'].append((tuple(int(x) for x in tex_tuple(cells[2])), tex_tuple(cells[3])))
    check(sorted(printed) == sorted(ROWS.values()), f'rows printed: {sorted(printed)}')
    def orbit(E, M, k):
        out = set()
        for sg in (1, -1):
            for sw in (False, True):
                e = tuple(sg * x for x in E)
                if sw:
                    e = (e[1], e[0], e[2])
                out.add((e, sg * M, sg * k))
        return out
    covered = set()
    for name, pr in printed.items():
        key = [kk for kk, v in ROWS.items() if v == name][0]
        _, c, val, slope = tab[name]
        A, Q = pr['A'], pr['Q']
        check(quad(A, Q) == c == pr['poly'] and (nrm(A), Q * dot(A, WV), Q * Q) == key,
              f'row ({name}): printed A, Q and |V|^2 = {pr["poly"]}')
        check(pr['val'] == val and pr['slope'] == slope, f'row ({name}): value {val} and slope {slope} at 1/48')
        for E, (M, k) in pr['steps']:
            o = [x for x in OPT if x[0] == E and x[1] == M and x[2] == k]
            check(len(o) == 1 and o[0][3] == A and o[0][4] == Q, f'row ({name}): step {E}, (M,kappa)=({M},{k}) is an '
                                                                  f'option of the rules with this A, Q')
            covered |= orbit(E, M, k)
    short = {(E, M, k) for (E, M, k, A, Q) in OPT if nrm(A) <= Fr(9, 4)}
    check(short == covered, f'the printed steps cover all {len(short)} short options up to reversal and x<->y')
    print('    rows a-g:', {n: (str(v[2]), str(v[3])) for n, v in tab.items()})

    print('(5) tangent lines of the proof of (2), and the full check of (2) in every class mod 48')
    thetas = list(range(-47, 0, 2))
    worst = None
    for th in thetas:
        phi = th + 24
        for E, M, k, A, Q in OPT:
            V0 = [A[c] - Fr(Q, 48) * WV[c] for c in range(3)]
            V1 = [-Fr(Q * phi, 48) * WV[c] for c in range(3)]
            a0, a1, a2 = nrm(V0) - MU2, 2 * dot(V0, V1) + K, nrm(V1)     # f(x) = a0 + a1 x + a2 x^2, x = 1/p
            xs = [Fr(0), Fr(1, 53)]
            if a2 > 0 and 0 < -a1 / (2 * a2) < Fr(1, 53):
                xs.append(-a1 / (2 * a2))
            lo = min(a0 + a1 * x + a2 * x * x for x in xs)
            if worst is None or lo < worst[0]:
                worst = (lo, th, E)
            check(lo >= 0, f'class theta={th}, step {E}: |V|^2 >= 281/256 - 345/(128p) for p >= 53')
    print(f'    24 classes x {len(OPT)} options: min of the margin {worst[0]} (class {worst[1]}, step {worst[2]})')
    # rev 15.3: tab:wclasses was replaced by the tangent-line step of the proof (the class table is gone)
    check('tab:wclasses' not in TEX, 'rev 15.3: Table tab:wclasses removed (tangent lines at 1/48 instead)')
    check(Fr(11, 2) * Fr(23, 48) == Fr(253, 96) and Fr(253, 96) < K and Fr(211, 192) > MU2,
          'tangent line of row (b): 211/192 - 253/(96p) > 281/256 - 345/(128p)')
    for snip in ('$T(p)=\\frac{281}{256}-\\frac{345}{128p}$, as $\\frac{45}8\\cdot\\frac{23}{48}=\\frac{345}{128}$',
                 '$T(p)=\\frac{211}{192}-\\frac{253}{96p}$',   # rev 15.7 pass 3: L(p) -> T(p)
                 '|V_{\\mathrm a}|^2=\\frac{281}{256}-\\frac{45}8\\,x+81x^2'):
        check(snip in SEC, f'printed tangent-line step: {snip}')
    # the exact row (a) in x = eps - 1/48, and the bound used in (3): 281/256 + 345/(128p) + 4761/(256p^2)
    check(tab['a'][1] == (Fr(5, 4), Fr(-9), Fr(81)) and ev(tab['a'][1], e0) == MU2
          and 81 * Fr(23, 48) ** 2 == Fr(4761, 256), 'row (a) = 281/256 - (45/8)x + 81x^2; 81(23/48)^2 = 4761/256')
    # exact (a), (b) quadratics in 1/p from the rows
    for phi in range(-23, 24, 2):
        y = Fr(phi, 48)                                     # eps - 1/48 = phi/(48p): coefficient of 1/p
        qa = (MU2, tab['a'][3] * y, 81 * y * y)
        qb = (Fr(211, 192), tab['b'][3] * y, 36 * y * y)
        check(qa == (MU2, -Fr(15 * phi, 128), Fr(9 * phi * phi, 256)) and qb == (Fr(211, 192), Fr(11 * phi, 96), Fr(phi * phi, 64)),
              f'phi={phi}: quadratics of (a), (b)')

    print('(6) direct relaxation at the primes')
    nfail, least = 0, None
    PR = 20000 if FULL else 3000
    for p in primes(53, PR):
        B, R = W(p)
        best = None
        for E in STEPS:
            for dz, k in lemma_set(p, E):
                v = [p * E[0] + 2 * dz - p * k, p * E[1] + 2 * dz - p * k, p * E[2] + dz]
                n2 = nrm(v)
                best = n2 if best is None or n2 < best else best
        if 256 * best < 281 * p * p - 690 * p:
            nfail += 1
        mg = Fr(best, p * p) - (MU2 - K / p)
        least = mg if least is None or mg < least else least
    check(nfail == 0, f'relaxation >= 281/256 - 345/(128p) at every prime 53..{PR}')
    print(f'    every prime 53..{PR}: no failure; least margin {float(least):.2e}')

    print('(7) the pair of part (3)')
    nb = 0
    for p in primes(53, 2000):
        B, R = W(p)
        d2 = tor2(point(B, R, p, (1, 0, 0)), point(B, R, p, (2, 0, p - 1)), p)
        nb += d2 != dstar2(p)
        nb += not (math.sqrt(d2) / p ** 2 < math.sqrt(281) / 16 + 2.5 / p)
    check(nb == 0, 'd*^2 formula and d*/p^2 < sqrt281/16 + 5/(2p) at every prime 53..2000')
    # the hand bound: q_a <= 281/256 + (345/128 + 4761/(256*53))/p, sqrt step, + 1/p
    c3 = K + Fr(4761, 256 * 53)
    check(float(c3) < 3.047 and 8 * 3.047 / math.sqrt(281) + 1 < 2.5, 'pair: 3.047, 8*3.047/sqrt281 + 1 < 5/2')

    print('(8) constants of (2) and (4)')
    check(bound(67) > 1 > bound(61), f'bound > 1 from 67 ({bound(67):.6f}), < 1 at 61 ({bound(61):.6f})')
    s66 = math.sqrt(66) / 8
    check(bound(97) > s66 > bound(89), f'bound > sqrt66/8 from 97 ({bound(97):.6f}), < at 89 ({bound(89):.6f})')
    check(all(bound(p) < bound(p + 1) for p in range(53, 3000)), 'bound increasing in p')

    print('(9) exact minimum distances (cellmin)')
    exact = {}
    for p in primes(5, 199) + [307, 353]:
        exact[p] = cellmin(*W(p), p)
    JS = os.path.join(HERE, 'w_exact.json')
    if '--write' in sys.argv:
        json.dump({'note': 'Exact toroidal d^2 (integer scale p^3) of W_p (prop:wnet), by cellmin.cpp; written by '
                           'wnet.py --write, read by figs_wnet.py', 'W': {str(p): exact[p] for p in exact}},
                  open(JS, 'w'), indent=1)
    stored = {int(k): v for k, v in json.load(open(JS))['W'].items()}
    check(stored == exact, 'recomputed d^2 == w_exact.json')
    c = {p: math.sqrt(d) / p ** 2 for p, d in exact.items()}
    check(all(c[p] > 1 for p in c if p >= 17) and all(c[p] < 1 for p in c if p <= 13), 'c(W_p) > 1 iff p >= 17 (5..199)')
    check(all(c[p] > s66 for p in c if p >= 53), 'c(W_p) > sqrt66/8 for p >= 53 (computed range)')
    check(min(c[p] for p in primes(17, 61)) == c[47], 'least c over 17..61 at p = 47')
    check(min(c[p] for p in primes(53, 89)) == c[89], 'least c over 53..89 at p = 89')
    check(all(dstar2(p) > exact[p] for p in exact if p >= 53), 'the pair is not the closest pair at any computed p >= 53')
    colx = json.load(open(os.path.join(HERE, 'colnets_exact.json')))
    Tp = {int(k): v['d2'] for k, v in colx['T'].items()} if 'T' in colx else {}
    if Tp:
        check(all(exact[p] > Tp[p] for p in primes(17, 47) if p != 23 and p in Tp), 'W_p ahead of T_p, 17..47 (not 23)')
        check(all(exact[p] > Tp[p] for p in primes(17, 199) if p != 23 and p in Tp), 'W_p ahead of T_p, 17..199')
    else:
        check(False, 'colnets_exact.json: T_p values')
    B15, R15 = T15(307)
    check(is_net(B15, R15, 307), 'T15 at p = 307 is a (0,3,3)-net')
    c15 = math.sqrt(cellmin(B15, R15, 307)) / 307 ** 2
    print('    c(W_p):', {p: round(v, 6) for p, v in c.items() if p in (13, 17, 47, 53, 61, 89, 101, 199, 307, 353)},
          ' c(T15_307) =', round(c15, 6))

    print('(10) digital shifts of W_101 (second digits)')
    B, R = W(101)
    sh, sh_tr = {}, {}
    for g2 in [(2, 2, 1), (14, 14, 7), (0, 0, 0), (1, 0, 0), (0, 0, 1), (5, 5, 0), (7, 7, 7), (10, 20, 30)]:
        d2_ = cellmin(B, R, 101, SHIFTMIN, list(g2) + [0, 0, 0])
        sh[g2] = math.sqrt(d2_) / 101 ** 2
        sh_tr[g2] = '%d.%04d' % divmod(math.isqrt(d2_ * 10 ** 8 // 101 ** 4), 10 ** 4)   # truncated, exactly
    sh3 = math.sqrt(cellmin(B, R, 101, SHIFTMIN, [0, 0, 0, 3, 5, 7])) / 101 ** 2
    check(abs(sh[(0, 0, 0)] - c[101]) < 1e-12 and abs(sh[(2, 2, 1)] - c[101]) < 1e-12 and abs(sh[(14, 14, 7)] - c[101]) < 1e-12
          and abs(sh3 - c[101]) < 1e-12, 'shifts keeping g_x = g_y = 2 g_z (and third-digit shifts): value unchanged')
    check(all(sh_tr[g] == '0.1355' for g in [(0, 0, 1), (5, 5, 0), (7, 7, 7), (10, 20, 30)]),
          'shifts (0,0,1), (5,5,0), (7,7,7), (10,20,30): c = .1355... (exact, truncated; rev 15.2: was the rounded .1356)')
    print('    ', {k: round(v, 4) for k, v in sh.items()})
    # rev 15.3 (rem:shiftshared corrected): a - 2b = 1 keeps the lock too; every (c,c,0), 2 <= c <= 100, breaks it
    keep1 = {g: cellmin(B, R, 101, SHIFTMIN, list(g) + [0, 0, 0]) for g in [(1, 1, 0), (3, 3, 1), (5, 5, 2)]}
    check(all(d == exact[101] for d in keep1.values()), 'shifts (1,1,0), (3,3,1), (5,5,2) (a = 2b+1): exact value of W_101')
    brk = {c_: cellmin(B, R, 101, SHIFTMIN, [c_, c_, 0, 0, 0, 0]) for c_ in range(2, 101)}
    check(all(10 ** 8 * d < 1356 ** 2 * 101 ** 4 for d in brk.values()), 'every shift (c,c,0), 2 <= c <= 100: c < 0.1356')
    check(max(brk.values()) == max(cellmin(B, R, 101, SHIFTMIN, g) for g in ([0, 0, 1, 0, 0, 0], [7, 7, 7, 0, 0, 0])),
          'the largest of them equals the value .1355... of (0,0,1) and (7,7,7)')
    for snip in ('$(1,1,0)$, $(3,3,1)$ and $(5,5,2)$ keep $1.0362\\ldots$', 'with $2\\le t\\le100$ gives $\\delta N^{1/3}<0.1356$',
                 'whenever $t\\equiv2t\'$ or $t\\equiv2t\'+1$'):   # rev 15.7 pass 3: moved to rem:wshift, letters t, t'
        check(snip in TEX, f'rem:wshift printed: {snip}')

    print('(11) limit model')
    h2 = Fr(1, 2)
    mT = model_value([[0, h2, h2], [Fr(1, 8), 0, 0], [Fr(1, 8), 0, 0]], ('pair', 1, 2))
    tau = (Fr(23, 48), Fr(23, 48), Fr(1, 24))
    mW = model_value([[w * t for t in tau] for w in WV], ('rank1', WV))
    m15 = model_value([[Fr(x, 15) for x in r] for r in ([0, 6, 6], [2, -1, -1], [2, -1, -1])], ('pair', 1, 2))
    check(mT == Fr(33, 32) and mW == MU2 and m15 == Fr(233, 225), f'model values {mT}, {mW}, {m15}')
    print(f'    T: {mT}, W: {mW}, T15 layer: {m15}')

    print('(12) values printed in core.tex')
    tr = lambda x, nd=4: f'{lb_trunc(x, nd):.{nd}f}'
    snips = [
        (f'$\\sqrt{{281}}/16={tr(math.sqrt(281) / 16)}\\ldots$', TEX),
        (f'{tr(bound(67))}\\ldots', SEC), (f'{tr(bound(97))}\\ldots', SEC),
        (f'{tr(c[17])}\\ldots', SEC), (f'{tr(c[47])}\\ldots', SEC), (f'{tr(c[53])}\\ldots', SEC),
        (f'{tr(c[101])}\\ldots', SEC), (f'{tr(c[353])}\\ldots', SEC), (f'{tr(c[89])}\\ldots', SEC),
        (f'{tr(c15)}\\ldots', SEC), (f'{tr(math.sqrt(233) / 15)}\\ldots', SEC),
        ('=.' + sh_tr[(0, 0, 1)][2:] + '\\ldots$', TEX),
    ]
    for s, where in snips:
        check(s in where, f'printed: {s}')
    eps = (13 - 2 * math.sqrt(31)) / 90
    check(abs((72 - 8 * math.sqrt(31)) / 25 - (1 + 4 * eps + 36 * eps * eps)) < 1e-12
          and abs(5 / 4 - 9 * eps + 81 * eps * eps - (1 + 4 * eps + 36 * eps * eps)) < 1e-12, 'balance point eps*')
    check(f'{tr(math.sqrt((72 - 8 * math.sqrt(31)) / 25))}' in SEC, 'printed sqrt((72-8sqrt31)/25)')

    print(f'wnet: {NCHK[0]} checks, {len(FAIL)} failures')
    sys.exit(1 if FAIL else 0)


if __name__ == '__main__':
    main()
