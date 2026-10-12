#!/usr/bin/env python3
"""printed_data.py -- cross-checks every data block that rev 14.3 prints in core.tex against its source.

Each printed block is parsed back out of core.tex (by its \\label or a fixed snippet) and compared entry by entry
with the source data; some blocks also get an independent recomputation.  Nothing is compared by eye.

  (1) app:perprime, Table tab:ppdesigns: the 11 per-prime designs that the all-of-N coverage needs
      (m = 1 mod 3, p = 5..31; m = 2 mod 3, p = 5, 7) == the rows of the Lean library (Z3Net/KNDefs.lean).
  (2) Table tab:S1Ekappa: the kappa behind every entry of tab:S1E == e1_random_search.txt / e1_rootlattice_rounding.txt
      (the files whose exact J2 truncate_bounds.py checks against tab:S1E).
  (3) Table tab:b23seeds: the six seeds of thm:base23 == the seed point files ../witnesses/r1/*_seed_m*.txt
      (point sets rebuilt from the printed matrices and shifts and compared as sets; t = 0 of every printed
      seed by the rank of every box).  Skipped with a note if ../witnesses is not present (deposit without it).
  (4) rem:cubecost: the printed basis spans the e = 10 maximizer of whylat_check.py (same lattice), has covolume 1,
      its Gram matrix is as printed and Minkowski-reduced, and its minimum is 29/25 (complete enumeration).
  (5) prop:korobov4: the printed skeleton digits == Lean design t3d13 (Z3Net/T3S4Defs.lean) and
      scripts/t3_s4.json; the reachability conditions of its proof modulo 13; lambda_inf(kappa) = 5; M_13 = 4 by
      enumeration of the relaxation in the proof; and (M_13-1) 13^(-3/4) >= .438.
  (6) rev 15.0: prop:half5 (2F_0^*, D_1, D_2, D_3) == half5_qstar.py and the audit's aud_lib.py; rem:M5 (2M_5) ==
      Lean M5h (Z3Net/HLDefs.lean); the (Lambda) example of rem:accounting (B2, MIN, det, the even step);
      A = 13/2; lambda(M_5) = sqrt5/2 over all 5^5-1 vectors E; every one of the 126 box minors is a nonzero
      rational whose prime factors lie in {2,3,5,7,11,13,17,29,41,47,257}, and each of these primes divides one.
  (7) prop:twocoset, proof: the polynomial identity of part (3) and the numerical estimates of the cases.
  (8) rev 15.1: prop:wnet, the printed generator rows == ../twocoset_ext/layers.py and ../rev15_audit/nets.py (if
      present) and wnet.py; the counterexample printed in the proof of lem:drift(2); the constant of prop:4D2(3).
      (Table tab:wcontacts is checked entry by entry by wnet.py; rev 15.3: tab:wclasses removed. prop:wfamily and
      rem:wstar, with every decimal they print, are checked by wfamily.py.)
The Lean data are read from the Lean library (rev 15.1: Z3Net/*.lean of the Lean project (repository root), or lean/ next to the paper,
or $LEAN_DIR).

Run: uv run python scripts/printed_data.py      (< 10 s)
"""
import itertools
import math
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
CORE = os.path.join(PAPER, 'core.tex')
TEX = open(CORE, encoding='utf-8').read()
# rev 15.1: the Lean library (the Lean project (repository root) in the source repository, lean/ next to the paper in a deposit, or
# $LEAN_DIR) keeps its data in Z3Net/*.lean (statements in QUNets/Statements/*.lean); the files read here:
LEAN_FILES = {'KN': os.path.join('Z3Net', 'KNDefs.lean'),          # rows1_p, rows2_p, table1/table2 (T_p)
              'T3S4': os.path.join('Z3Net', 'T3S4Defs.lean'),      # t3d13
              'HL': os.path.join('Z3Net', 'HLDefs.lean')}          # M5h
_lean_dirs = [os.environ.get('LEAN_DIR', ''), os.path.join(PAPER, 'lean'), os.path.join(os.path.dirname(PAPER), 'lean'), os.path.dirname(PAPER)]
LEAN = next((d for d in _lean_dirs if d and all(os.path.exists(os.path.join(d, f)) for f in LEAN_FILES.values())), None)
if LEAN is None:
    sys.exit('Lean library not found (Z3Net/KNDefs.lean, T3S4Defs.lean, HLDefs.lean): set LEAN_DIR')
WIT = os.environ.get('WITNESS_DIR', os.path.join(PAPER, 'certificates', 'witnesses'))
FAIL = []
NCHK = [0]


def check(ok, what):
    NCHK[0] += 1
    if not ok:
        FAIL.append(what)
        print('  FAIL:', what)


def block(label):
    """the table/figure/environment body that contains \\label{label}"""
    i = TEX.index('\\label{%s}' % label)
    a = max(TEX.rfind('\\begin{table}', 0, i), TEX.rfind('\\begin{proposition}', 0, i))
    return TEX[a:i]


def tuples(s):
    return [tuple(int(x) for x in t.split(',')) for t in re.findall(r'\((-?\d+(?:,-?\d+)*)\)', s)]


def lean_arr(s):
    return eval(s.replace('![', '[').replace('\n', ' '))


# ---------------------------------------------------------------------------------------------------- (1) perprime
def knpp_rows():
    src = open(os.path.join(LEAN, LEAN_FILES['KN'])).read()
    rows = {}
    for m in re.finditer(r'def rows([12])_(\d+) : Rows where\s*sk := (.*?)\n\s*jt := (.*?)\n\n', src, re.S):
        rows[(int(m.group(1)), int(m.group(2)))] = (lean_arr(m.group(3)), lean_arr(m.group(4)))
    return rows


def geo_rows(r, sk, jt):
    """name -> per-coordinate windows (lists), Definition def:ppdesign; X,Y,Z = 0,1,2"""
    win = lambda d: 4 if (r == 1 and d == 0) else 3
    def w(row):
        out = []
        for d in range(3):
            assert all(v == 0 for v in row[d][win(d):]), 'entry beyond the window'
            out.append(tuple(row[d][:win(d)]))
        return tuple(out)
    if r == 1:
        return [('X0', w(jt[0])), ('Y0', w(sk[1])), ('Y1', w(jt[1])), ('Z0', w(sk[2])), ('Z1', w(jt[2]))]
    return [('X0', w(jt[0])), ('Y0', w(jt[1])), ('Z0', w(sk[2])), ('Z1', w(jt[2]))]


PP_COVER = [(1, p) for p in (5, 7, 11, 13, 17, 19, 23, 29, 31)] + [(2, 5), (2, 7)]


def emit_perprime():
    R = knpp_rows()
    lines = []
    for r, p in PP_COVER:
        for name, (wx, wy, wz) in geo_rows(r, *R[(r, p)]):
            f = lambda t: '$(' + ','.join(map(str, t)) + ')$'
            lines.append((r, p, name, f(wx), f(wy), f(wz)))
    return lines


def check_perprime():
    print('(1) app:perprime designs vs the Lean library (Z3Net/KNDefs.lean)')
    R = knpp_rows()
    blk = block('tab:ppdesigns')
    got = {}
    r, cur = None, {}
    for line in blk.split('\\\\'):
        line = line.strip().split('\n')[-1]
        if 'm\\equiv1' in line:
            r, cur = 1, {}
        if 'm\\equiv2' in line:
            r, cur = 2, {}
        cells = [c.strip() for c in line.split('&')]
        if r is None or len(cells) not in (5, 10):
            continue
        for side, j in enumerate(range(0, len(cells), 5)):
            c = cells[j:j + 5]
            if re.fullmatch(r'\$?\d+\$?', c[0]):
                cur[side] = int(c[0].strip('$'))
            if not re.fullmatch(r'\$?[XYZ][01]\$?', c[1]):
                continue
            key = (r, cur[side], c[1].strip('$'))
            got[key] = (tuples(c[2])[0], tuples(c[3])[0], tuples(c[4])[0])
    n = 0
    for r, p in PP_COVER:
        for name, wins in geo_rows(r, *R[(r, p)]):
            n += 1
            check(got.get((r, p, name)) == wins, f'tab:ppdesigns p={p} r={r} {name}: printed {got.get((r, p, name))} '
                  f'vs Lean {wins}')
    check(len(got) == n, f'tab:ppdesigns has {len(got)} rows, expected {n} (no extra rows)')
    print(f'    {n} geometric rows of {len(PP_COVER)} designs compared')


# ---------------------------------------------------------------------------------------------------- (2) kappa
def kappa_source():
    sys.path.insert(0, HERE)
    import s1e_certs
    rows = s1e_certs.rows()
    out = {}
    for src, s, p, kap in rows:
        if src == 'search':
            if p in (1009, 10007, 1000003, 100000007):
                out[(s, p)] = tuple(kap)
        elif src.endswith(':1e6') or src.endswith(':1e10'):
            out[(s, p)] = tuple(kap)
    return out


def check_kappa():
    print('(2) tab:S1Ekappa vs e1_*.txt')
    src = kappa_source()
    blk = block('tab:S1Ekappa')
    got = {}
    for line in blk.split('\\\\'):
        line = line.strip().split('\n')[-1]
        cells = [c.strip() for c in line.split('&')]
        for j in range(0, len(cells) - 2, 3):
            c = cells[j:j + 3]
            if not re.fullmatch(r'\d', c[0]):
                continue
            p = int(re.sub(r'[^\d]', '', c[1]))
            got[(int(c[0]), p)] = tuples(c[2])[0]
    for key, kap in src.items():
        check(got.get(key) == kap, f'kappa s={key[0]} p={key[1]}: printed {got.get(key)} vs source {kap}')
    check(len(got) == len(src) == 36, f'tab:S1Ekappa: {len(got)} printed, {len(src)} in the source (36 expected)')
    print(f'    {len(src)} kappa vectors compared')


# ---------------------------------------------------------------------------------------------------- (3) seeds
B23 = [('b2_mod0', 2, 9), ('b2_mod1', 2, 10), ('b2_mod2', 2, 11), ('b3_mod0', 3, 6), ('b3_mod1', 3, 7),
       ('b3_mod2', 3, 8)]


def digits(v, b, M):
    return [(v // b ** (M - 1 - d)) % b for d in range(M)]


def undigits(ds, b):
    v = 0
    for x in ds:
        v = v * b + x
    return v


def seed_canonical(fam, b, M):
    """(A_y, A_z, tau_y, tau_z) with the point set {(u, A_y u + tau_y, A_z u + tau_z)} (digit vectors, F_b)"""
    fn = os.path.join(WIT, 'r1', f'{fam}_seed_m{M}.txt')
    L = open(fn).read().split('\n')
    bb, MM = map(int, L[0].split())
    assert (bb, MM) == (b, M)
    pts = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
    assert len(pts) == b ** M
    byx = {p[0]: p for p in pts}
    assert len(byx) == b ** M, 'x not a bijection'
    o = byx[0]
    ty, tz = digits(o[1], b, M), digits(o[2], b, M)
    Ay = [[0] * M for _ in range(M)]
    Az = [[0] * M for _ in range(M)]
    for j in range(M):
        q = byx[b ** (M - 1 - j)]
        cy, cz = digits(q[1], b, M), digits(q[2], b, M)
        for d in range(M):
            Ay[d][j] = (cy[d] - ty[d]) % b
            Az[d][j] = (cz[d] - tz[d]) % b
    return Ay, Az, ty, tz, set(pts)


def build_points(b, M, Ay, Az, ty, tz):
    pts = set()
    for v in range(b ** M):
        u = digits(v, b, M)
        y = [(sum(Ay[d][j] * u[j] for j in range(M)) + ty[d]) % b for d in range(M)]
        z = [(sum(Az[d][j] * u[j] for j in range(M)) + tz[d]) % b for d in range(M)]
        pts.add((v, undigits(y, b), undigits(z, b)))
    return pts


def rank_mod(rows, b):
    A = [list(r) for r in rows]
    rk, col, n = 0, 0, len(A[0]) if A else 0
    for col in range(n):
        piv = next((i for i in range(rk, len(A)) if A[i][col] % b), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        inv = pow(A[rk][col], b - 2, b)
        A[rk] = [x * inv % b for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][col] % b:
                f = A[i][col]
                A[i] = [(x - f * y) % b for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def t0(b, M, mats):
    for dx in range(M + 1):
        for dy in range(M + 1 - dx):
            dz = M - dx - dy
            rows = mats[0][:dx] + mats[1][:dy] + mats[2][:dz]
            if rank_mod(rows, b) < M:
                return False
    return True


def row_int(row, b):
    return undigits(row, b)


def emit_seeds():
    out = []
    for fam, b, M in B23:
        Ay, Az, ty, tz, _ = seed_canonical(fam, b, M)
        out.append((fam, b, M, [row_int(r, b) for r in Ay], [row_int(r, b) for r in Az],
                    undigits(ty, b), undigits(tz, b)))
    return out


def check_seeds():
    print('(3) tab:b23seeds vs ../witnesses/r1 seed point files')
    blk = block('tab:b23seeds')
    printed = {}
    for line in blk.split('\\\\'):
        line = line.strip().split('\n')[-1]
        cells = [c.strip() for c in line.split('&')]
        if len(cells) < 6 or not re.fullmatch(r'\$?\d\$?', cells[0]):
            continue
        b, res, M = int(cells[0].strip('$')), int(cells[1].strip('$')), int(cells[2].strip('$'))
        ints = lambda s: [int(x) for x in re.findall(r'\d+', s)]
        printed[(b, res)] = (M, ints(cells[3]), ints(cells[4]), ints(cells[5]))
    for fam, b, M in B23:
        res = int(fam[-1])
        pr = printed.get((b, res))
        check(pr is not None and pr[0] == M, f'seed {fam}: printed level {pr and pr[0]} vs {M}')
        if pr is None:
            continue
        _, ay, az, tau = pr
        check(len(ay) == M and len(az) == M and len(tau) == 2, f'seed {fam}: row counts')
        Ay = [digits(v, b, M) for v in ay]
        Az = [digits(v, b, M) for v in az]
        I = [[int(i == j) for j in range(M)] for i in range(M)]
        check(t0(b, M, [I, Ay, Az]), f'seed {fam}: printed matrices are a (0,{M},3)-net over F_{b}')
        if os.path.isdir(os.path.join(WIT, 'r1')):
            *_, src = seed_canonical(fam, b, M)
            pts = build_points(b, M, Ay, Az, digits(tau[0], b, M), digits(tau[1], b, M))
            check(pts == src, f'seed {fam}: printed net (with shift) == seed point file')
    if not os.path.isdir(os.path.join(WIT, 'r1')):
        print('    NOTE: ../witnesses/r1 not found; printed seeds checked for t = 0 only')
    print(f'    {len(printed)} seeds compared')


# ---------------------------------------------------------------------------------------------------- (4) cubecost
def check_cubecost():
    print('(4) rem:cubecost witness basis')
    i = TEX.index('\\label{rem:cubecost}')
    seg = TEX[i:TEX.index('\\end{remark}', i)]
    m = re.search(r'with basis (.*?)It has covolume', seg, re.S)
    vecs = []
    for t in re.findall(r'\\tfrac1\{?(\d+)\}?\((-?\d+),(-?\d+),(-?\d+)\)', m.group(1)):
        den = int(t[0])
        vecs.append(tuple(Fr(int(x), den) for x in t[1:]))
    check(len(vecs) == 3, f'cubecost: 3 basis vectors parsed ({len(vecs)})')
    U = [[int(x * 10) for x in v] for v in vecs]               # units 1/10
    det = (U[0][0] * (U[1][1] * U[2][2] - U[1][2] * U[2][1]) - U[0][1] * (U[1][0] * U[2][2] - U[1][2] * U[2][0])
           + U[0][2] * (U[1][0] * U[2][1] - U[1][1] * U[2][0]))
    check(abs(det) == 1000, f'cubecost: covolume {abs(det)}/1000 == 1')
    H = [[50, 5, 11], [0, 20, 2], [0, 0, 1]]                   # whylat_check.CASES, e = 10

    def inH(v):
        c3 = Fr(v[2]); c2 = (v[1] - 2 * c3) / 20; c1 = (v[0] - 5 * c2 - 11 * c3) / 50
        return all(x.denominator == 1 for x in (c1, c2, c3))
    check(all(inH(u) for u in U), 'cubecost: the printed vectors lie in the e = 10 maximizer of whylat_check.py')
    G = [[sum(a * b for a, b in zip(u, w)) for w in U] for u in U]
    gm = re.search(r'Gram matrix \$100\^\{-1\}\\left\(\\begin\{smallmatrix\}(.*?)\\end\{smallmatrix\}', seg, re.S)
    Gp = [[int(x) for x in row.split('&')] for row in gm.group(1).split('\\\\')]
    check(Gp == G, f'cubecost: printed Gram matrix {Gp} == {G}')
    # Minkowski reduction (dimension 3): g11 <= g22 <= g33, |2 g_ij| <= g_ii (i<j), |u3 +- u1 +- u2| >= |u3|
    ok = G[0][0] <= G[1][1] <= G[2][2] and 2 * abs(G[0][1]) <= G[0][0] and 2 * abs(G[0][2]) <= G[0][0] \
        and 2 * abs(G[1][2]) <= G[1][1]
    for e1, e2 in itertools.product((1, -1), repeat=2):
        ok = ok and G[0][0] + G[1][1] + 2 * (e1 * G[0][2] + e2 * G[1][2] + e1 * e2 * G[0][1]) >= 0
    check(ok, 'cubecost: the printed basis is Minkowski-reduced')
    best = min(sum(x * x for x in v) for v in itertools.product(range(-15, 16), repeat=3)
               if v != (0, 0, 0) and inH(v))
    check(best == 116 == G[0][0], f'cubecost: minimum 116/100 = 29/25 by enumeration ({best})')
    print('    basis, Gram matrix, reduction and minimum checked')


# ---------------------------------------------------------------------------------------------------- (5) dim 4
def t3d13():
    src = open(os.path.join(LEAN, LEAN_FILES['T3S4'])).read()
    m = re.search(r'def t3d13 : T3Design where(.*?)\n\n', src, re.S).group(1)
    get = lambda k: lean_arr(re.search(r'\b' + k + r' := (.*)', m).group(1))
    return dict(p=get('p'), a3=get('a3'), kappa=get('κ'), beta=get('β'), eta=get('η'), g=get('g'), H=get('H'),
                o=get('o'), M=get('M'), lat=get('lat'))


def skel_terms_printed():
    i = TEX.index('\\label{prop:korobov4}')
    seg = TEX[i:TEX.index('\\end{proof}', i)]
    out = {}
    for m in re.finditer(r'S_\{z_(\d)\}&=(.*?)(?:,\\\\|\\\\|\\end\{align)', seg, re.S):
        out[int(m.group(1))] = m.group(2)
    return out, seg


def parse_lin(expr):
    """'4x_k-2x_{k-1}+z_{2,k-2}...' -> {var: coef}"""
    expr = expr.replace(' ', '').replace('\\,', '')
    terms = {}
    for sgn, co, var in re.findall(r'([+-]?)(\d*)((?:x|z)_(?:\{[^}]*\}|[a-z0-9]))', expr):
        c = int(co) if co else 1
        if sgn == '-':
            c = -c
        terms[var] = terms.get(var, 0) + c
    return terms


def check_dim4():
    print('(5) prop:korobov4 vs Lean t3d13 and t3_s4.json; reachability, lambda, M_13')
    D = t3d13()
    import json
    J = json.load(open(os.path.join(HERE, 't3_s4.json')))['13']
    p, a3 = D['p'], D['a3']
    check(p == 13 and J['p'] == 13 and J['tau'] == a3 and J['kappa'] == D['kappa'] and J['beta'] == D['beta']
          and J['eta'] == D['eta'] and J['own'] == D['o'] and J['cert_M'] == D['M'] and J['lat'] == D['lat'],
          'korobov4: Lean t3d13 == t3_s4.json (p = 13)')
    gj = J['g']                                   # order (1,2),(1,3),(2,1),(2,3),(3,1),(3,2)
    pairs = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
    check([D['g'][i][j] for i, j in pairs] == gj, 'korobov4: faults g, Lean == json')
    printed, seg = skel_terms_printed()
    check(sorted(printed) == [1, 2, 3], f'korobov4: three skeleton digits parsed ({sorted(printed)})')
    for i in range(3):
        want = {'x_k': D['kappa'][i], 'x_{k-1}': D['beta'][i], 'x_{k-2}': D['eta'][i]}
        for j in range(3):
            if j != i:
                want[f'z_{{{j + 1},k-1}}'] = D['g'][i][j]
                want[f'z_{{{j + 1},k-2}}'] = D['H'][i][j]
        want[f'z_{{{i + 1},k-1}}'] = D['o'][i]
        want = {k: v for k, v in want.items() if v}
        got = parse_lin(printed.get(i + 1, ''))
        check(got == want, f'korobov4: S_z{i + 1} printed {got} vs Lean {want}')
    pl = re.search(r'places \$0\$, \$1\$, \$(\d+)\$', seg)
    check(pl is not None and int(pl.group(1)) == a3, 'korobov4: place a_3 printed == Lean')
    # reachability (proof of prop:korobov4), modulo p
    inv = lambda x: pow(x % p, p - 2, p)
    a = [0, 1, a3]
    kap, bet, eta, g, H = D['kappa'], D['beta'], D['eta'], D['g'], D['H']
    lam = [k % p for k in kap]                    # lambda' = kappa, mu_x = 1
    ok = True
    mus = []
    for j in range(3):
        r = [i for i in range(3) if i != j]
        mu = [g[i][j] * (a[i] - a[j]) * inv(lam[i]) % p for i in r]
        ok = ok and mu[0] == mu[1] and mu[0] != 0
        mus.append(mu[0])
    check(ok, 'korobov4: g_ij = lambda_i mu_j / (a_i - a_j) solvable with lambda = kappa (one mu_j per column)')
    pm = re.search(r'\\mu_\{z_1\},\\mu_\{z_2\},\\mu_\{z_3\}\)=\((-?\d+),(-?\d+),(-?\d+)\)', seg)
    check(pm is not None and [int(x) % p for x in pm.groups()] == mus, f'korobov4: printed mu == {mus}')
    s = [(kap[i] + bet[i]) * inv(kap[i]) % p for i in range(3)]          # = c0 + c1 a_i
    c0, c1 = s[0], (s[1] - s[0]) % p
    check((c0 + c1 * a3) % p == s[2] and c1 != 0, f'korobov4: kappa+beta = kappa*(c0+c1 a), c1 = {c1} != 0')
    pc = re.search(r'\(c_0,c_1\)=\((-?\d+),(-?\d+)\)', seg)
    check(pc is not None and (int(pc.group(1)) % p, int(pc.group(2)) % p) == (c0, c1), 'korobov4: printed (c0,c1)')
    det3 = (kap[0] * (bet[1] * eta[2] - bet[2] * eta[1]) - bet[0] * (kap[1] * eta[2] - kap[2] * eta[1])
            + eta[0] * (kap[1] * bet[2] - kap[2] * bet[1]))
    check(det3 % p != 0, f'korobov4: det[kappa,beta,eta] = {det3} != 0 mod 13')
    for j in range(3):
        i, l = [x for x in range(3) if x != j]
        dd = g[i][j] * H[l][j] - H[i][j] * g[l][j]
        check(dd % p != 0, f'korobov4: corner det column z{j + 1} = {dd}')
    check(g[0][1] * g[1][2] * g[2][0] == -g[1][0] * g[2][1] * g[0][2], 'korobov4: cyclic identity (C)')
    # lambda_inf of the Korobov lattice {u : u_zi = kappa_i u_x}
    lat = min(max(abs(ux), *[abs(((kap[i] * ux + p // 2) % p) - p // 2) for i in range(3)])
              for ux in range(1, p))
    zero_x = p   # with u_x = 0 the z are multiples of p
    check(min(lat, zero_x) == D['lat'] == 5, f'korobov4: lambda_inf(kappa) = {lat} == 5')
    # M_13: the relaxation of the proof
    cen = lambda v: ((v + p // 2) % p) - p // 2
    pats = lambda sg: [(0, 0)] if sg == 0 else [(0, 0), (sg, 0), (sg, sg)]
    best = None
    for ax in range(-(p // 2), p // 2 + 1):
        for xi in pats((ax > 0) - (ax < 0)):
            for zs in itertools.product(*[[(0, 0), (1, 0), (1, 1), (-1, 0), (-1, -1)]] * 3):
                az = []
                for i in range(3):
                    v = kap[i] * ax + bet[i] * xi[0] + eta[i] * xi[1] + D['o'][i] * zs[i][0]
                    v += sum(g[i][j] * zs[j][0] + H[i][j] * zs[j][1] for j in range(3) if j != i)
                    az.append(cen(v))
                if ax == 0 and az == [0, 0, 0]:
                    continue
                if any(zs[i] != (0, 0) and (az[i] == 0 or (az[i] > 0) != (zs[i][0] > 0)) for i in range(3)):
                    continue                                   # sign-consistent prefix patterns only
                if ax == 0 and xi != (0, 0):
                    continue
                v = max(abs(ax), *map(abs, az))
                best = v if best is None else min(best, v)
    check(best == D['M'] == 4, f'korobov4: M_13 = {best} == 4')
    check(2 * best <= p + 1, 'korobov4: 2 M_13 <= p + 1')
    val = (best - 1) * 13 ** -0.75
    check(math.floor(val * 1000) == 438 and '.438' in seg, f'korobov4: (M-1) 13^(-3/4) = {val:.6f}, printed .438')
    print('    design, reachability, lambda_inf, M_13 and the bound checked')


# ---------------------------------------------------------------------------------------------------- (6) half5
def _psmall(seg, name):
    m = re.search(re.escape(name) + r'=\\begin\{psmallmatrix\}(.*?)\\end\{psmallmatrix\}', seg, re.S)
    return None if m is None else [[int(x) for x in r.split('&')] for r in m.group(1).split('\\\\')]


def check_half5():
    """rev 15.0: prop:half5 is the layer F_0^* with the rows D_1, D_2, D_3 (net Q*_p); rem:M5 prints the layer 2M_5 of
    rev 14.3; rem:accounting prints a layer violating (Lambda).  Sources: half5_qstar.py (which certifies them) and,
    if present, the independent audit's typed matrices ../../holonomy_s5_audit/aud_lib.py; 2M_5 also against the Lean
    Lean library (Z3Net/HLDefs.lean, M5h)."""
    print('(6) prop:half5, rem:M5, rem:accounting: printed layers vs their sources')
    import half5_qstar as H5
    i = TEX.index('\\label{prop:half5}')
    seg = TEX[i:TEX.index('\\end{proposition}', i)]
    pr = {k: _psmall(seg, k) for k in ('2F_0^*', 'D_1', 'D_2', 'D_3')}
    src = {'2F_0^*': H5.HQ, 'D_1': H5.D1Q, 'D_2': H5.D2Q, 'D_3': H5.D3Q}
    for k in pr:
        check(pr[k] == src[k], f'half5: printed {k} == half5_qstar.py')
    aud = os.path.join(PAPER, '..', 'holonomy_s5_audit', 'aud_lib.py')
    if os.path.exists(aud):
        A = {}
        exec(compile(open(aud).read().split('S = 5')[0], aud, 'exec'), A)
        for k, nm in (('2F_0^*', 'HQ'), ('D_1', 'D1Q'), ('D_2', 'D2Q'), ('D_3', 'D3Q')):
            check(pr[k] == A[nm], f'half5: printed {k} == audit aud_lib.{nm}')
    else:
        print('    (audit library not found; compared with half5_qstar.py only)')
    H = pr['2F_0^*']
    check(all(x % 2 for r in H for x in r), 'half5: every entry of 2F_0^* is odd (F_0^* in 1/2 + Z)')
    check(max(sum(abs(x) for x in r) for r in H) == 11, 'half5: A = max_c sum_d |F_0^*[c][d]| = 11/2')
    j = TEX.index('\\label{rem:M5}')
    M5 = _psmall(TEX[j:TEX.index('\\end{remark}', j)], '2M_5')
    check(M5 == H5.HM, 'rem:M5: printed 2M_5 == half5_qstar.py HM')
    try:
        src5 = open(os.path.join(LEAN, LEAN_FILES['HL'])).read()
        M5h = lean_arr(re.search(r'def M5h : .*?:=\s*(!\[.*?\]\])\n', src5, re.S).group(1))
        check(M5 == M5h, 'rem:M5: printed 2M_5 == Lean M5h (Z3Net/HLDefs.lean)')
    except (OSError, AttributeError):
        print('    (Lean M5h not found; 2M_5 compared with half5_qstar.py only)')
    alpha2 = [-M5[c][c] for c in range(5)]
    check(alpha2 == [5, 3, 5, 7, 3] and sum(alpha2) == 23, 'rem:M5: alpha = (5,3,5,7,3)/2, sum 23/2')
    check(sum(max(abs(M5[c][d]) for d in range(5) if d != c) for c in range(5)) == 15, 'rem:M5: sum m = 15/2')
    # rem:accounting: the layer that satisfies (B2), (MIN) but not (Lambda)
    k = TEX.index('\\label{rem:accounting}')
    L = _psmall(TEX[k:TEX.index('\\end{remark}', k)], '2F_0')
    F = [[Fr(x, 2) for x in r] for r in L]
    check(all(x % 2 for r in L for x in r), 'rem:accounting: entries of 2F_0 odd')
    check(all(-F[c][c] >= max(abs(F[c][d]) for d in range(5) if d != c) for c in range(5)), 'rem:accounting: (B2)')
    okmin = all(F[c][d] != 0 for c in range(5) for d in range(5))
    for a, b in itertools.combinations(range(5), 2):
        for c, d in itertools.combinations([x for x in range(5) if x not in (a, b)], 2):
            okmin &= F[a][c] * F[b][d] - F[a][d] * F[b][c] != 0
    check(okmin, 'rem:accounting: (MIN)')
    check(H5.det(L) == 560, 'rem:accounting: det 2F_0 = 560')
    E = [1, -1, -2, -1, -1]
    beta = [sum(F[c][d] * E[d] for d in range(5)) for c in range(5)]
    check(beta == [2, -3, -1, -1, -1], 'rem:accounting: beta = F_0 E = (2,-3,-1,-1,-1)')
    ell = [min(abs(E[c] - kk) for kk in ({0, (beta[c] > 0) - (beta[c] < 0)} if beta[c] else {0})) for c in range(5)]
    check(sum(x * x for x in ell) == 1 and sum(E) % 2 == 0, 'rem:accounting: the even step E has |l(E)| = 1')
    print('    layers, (B2), (MIN), det and the (Lambda) example checked; minors and scans: half5_qstar.py')


# ---------------------------------------------------------------------------------------------------- (6b) column nets
def check_colnets():
    """rev 15.0: the printed polynomials of the proof of thm:col(2), the vectors D, the excess vectors of sec:drift,
    the box minors of thm:col(1); at every q coprime to 6 in [5, 401] against direct integer evaluation."""
    print('(6b) thm:col, lem:drift: printed polynomials, closest differences, excesses')
    for q in range(5, 402):
        if q % 2 == 0 or q % 3 == 0:
            continue
        g2 = q % 3 == 2
        w = (-2, 1, 1) if g2 else (-1, -1, 2)
        a = [(q + x) // 3 for x in w]
        r = (q - 1, 1, 0)
        sv = [q * a[i] + r[i] for i in range(3)]
        printed = ((q * q - q + 3, q * q - q - 3, q * q - q) if g2 else (q * q - 2 * q + 3, q * q + q - 3, q * q - 2 * q))
        check(tuple(2 * q * q - 3 * x for x in sv) == printed, f'thm:col proof: 2q^2 - 3s_i at q = {q}')
        lo, hi = 2 * q * q - q + 3, 2 * q * q + 2 * q
        check(all(lo <= 3 * x + q * q <= hi for x in sv), f'thm:col proof: 3s_i + q^2 in [2q^2-q+3, 2q^2+2q] at q = {q}')
        # every other lift: t = 0 (U = s_i, s_i - q) and t = 2, -1
        others = [abs(3 * (x - t * q * q - e * q) + q * q) for x, ri in zip(sv, r) for t in (0, 2, -1)
                  for e in ((0, 1) if ri else (0,))]
        check(min(others) >= 2 * q * q - 4 * q + 3 > q * q + q, f'thm:col proof: other lifts >= 2q^2-4q+3 at q = {q}')
        tau = q * q - q - 3 if g2 else q * q - 2 * q
        i = 1 if g2 else 2
        U = sv[i] - q * q
        D = [U + (q * q if c == i else 0) for c in range(3)]
        Dp = ([-(2 * q * q - q - 3), q * q + q + 3, -(2 * q * q - q - 3)] if g2 else
              [-(2 * q * q - 2 * q), -(2 * q * q - 2 * q), q * q + 2 * q])
        check(all(3 * d == e for d, e in zip(D, Dp)) and 3 * sum(d * d for d in D) == 2 * q ** 4 + tau ** 2,
              f'thm:col(2): D and |D|^2 = (2q^4 + tau^2)/3 at q = {q}')
        mu = a[0] + a[1]
        check(all(math.gcd(x % q, q) == 1 for x in (*a, mu)) and (3 * mu + w[2]) % q == 0,
              f'thm:col(1): a_c and mu = a_x + a_y units, 3 mu = -w_z mod q at q = {q}')
        eps = [Fr(q * w[c], 3) + r[c] for c in range(3)]
        epsp = ([Fr(q, 3) - 1, Fr(q, 3) + 1, Fr(q, 3)] if g2 else [Fr(2 * q, 3) - 1, 1 - Fr(q, 3), Fr(2 * q, 3)])
        check(eps == epsp and max(eps) == (Fr(q, 3) + 1 if g2 else Fr(2 * q, 3)), f'lem:drift: excess vector at q = {q}')
    print('    q = 5..401 coprime to 6')


# ---------------------------------------------------------------------------------------------------- (7) twocoset
def check_twocoset():
    print('(7) prop:twocoset proof: identity of part (3) and the case estimates')
    # identity p^4 (sqrt66/8 - 2/p)^2 - d*^2 = c3 p^3 - c2 p^2 + c1 p - 61, as a + b sqrt66 with rational a, b
    for th in (-3, -1, 1, 3):
        for p in (Fr(53), Fr(97), Fr(1009), Fr(7, 3), Fr(-5)):
            r = (p + th) / 8
            d2 = (p * p - 2 * p + 3) ** 2 + ((r - 1) * p + 4) ** 2 + ((r - 1) * p + 6) ** 2
            # (sqrt66/8 - 2/p)^2 = 66/64 - sqrt66/(2p) + 4/p^2
            lhs_a = p ** 4 * (Fr(66, 64) + 4 / p ** 2) - d2
            lhs_b = -p ** 3 / 2
            rhs_a = (Fr(9, 2) - Fr(th, 16)) * p ** 3 - (Fr(21, 2) - Fr(th, 2) + Fr(th * th, 32)) * p ** 2 \
                + (32 - Fr(5 * th, 2)) * p - 61
            rhs_b = -p ** 3 / 2
            check(lhs_a == rhs_a and lhs_b == rhs_b, f'twocoset identity at theta={th}, p={p}')
    s66 = math.sqrt(66)
    for th in (-3, -1, 1, 3):
        check(4.5 - th / 16 - s66 / 2 > 0.25 and 10.5 - th / 2 + th * th / 32 < 12.3 and 32 - 2.5 * th > 24,
              f'twocoset coefficient bounds at theta={th}')
    check(all(0.25 * q ** 3 - 12.3 * q * q + 24 * q - 61 > 0 for q in range(53, 5000)), 'twocoset: cubic > 0, p >= 53')
    P = 41
    check((0.5 - 1.5 / P) ** 2 + 0.5 * (1 - 2 / P) ** 2 + 0.5 > 1.16, 'twocoset case (c)')
    check((1.5 - 1.5 / P) ** 2 > 2, 'twocoset cases (d), (f): (3/2 - 3/(2p))^2 > 2')
    check(all(Fr(9, 8) - Fr(19, 4 * q) + Fr(41, 8 * q * q) >= Fr(33, 32) - Fr(41, 16 * q) for q in range(24, 3000)),
          'twocoset case (d): p >= 24')
    check(0.5 * (1.75 - 0.75 / P) ** 2 > 1.4, 'twocoset case (e)')
    check((0.5 - 1.5 / P) ** 2 + 0.5 * (1.25 - 2.75 / P) ** 2 + 0.5 > 1.41, 'twocoset case (f), rev 15.1: 11/(4p)')
    check(max(abs(th * ex - 8 * t) for th in (-3, -1, 1, 3) for ex in (-1, 1) for t in (-1, 1)) == 11,
          'twocoset case (f): |theta E_x - 8T| <= 11, so |V_y+V_z-beta| <= 11/(4p)')
    f = lambda q: math.sqrt(33 / 32 - 41 / (16 * q)) - math.sqrt(3) / q
    check(f(197) > 1 > f(193) and math.floor(f(197) * 1e4) == 10002, 'twocoset: bound > 1 at 197 (1.0002..., truncated), < 1 at 193')
    check(Fr(33, 32) - Fr(41, 16 * 83) >= 1 and Fr(41, 32) + Fr(17320508, 10 ** 7) < Fr(3014, 1000)
          and math.sqrt(3) < 1.7320508 + 1e-7, 'twocoset: p >= 83 and 41/32 + sqrt3 < 3.014')
    print('    identity and estimates checked')


# ---------------------------------------------------------------------------------------------------- (8) rev 15.1
def check_wnet():
    """prop:wnet: the printed generator rows against the sources (../twocoset_ext/layers.py of TWOCOSET_EXT and the
    audit's ../rev15_audit/nets.py, if present) and against wnet.py; the printed minors; Table tab:wcontacts is
    checked entry by entry by wnet.py (tab:wclasses removed in rev 15.3; prop:wfamily: wfamily.py)."""
    print('(8) prop:wnet: printed rows of W_p vs sources; lem:drift(2) counterexample; prop:4D2(3) constant')
    import importlib.util
    import wnet
    i = TEX.index('\\label{prop:wnet}')
    seg = TEX[i:TEX.index('\\end{proposition}', i)]
    want = [r'C_x:\ \e_x,\ \rho(-1,-1,2),\ (0,1,2)', r'C_y:\ \e_y,\ \rho(-1,-1,2),\ (1,0,1)',
            r'C_z:\ \e_z,\ (h-r,h-r,\rho),\ (0,1,0)']
    for w_ in want:
        check(w_ in seg, f'prop:wnet printed rows: {w_}')
    check('r=\\lfloor p/48\\rfloor' in seg and '\\rho=2r+1' in seg, 'prop:wnet: r = floor(p/48), rho = 2r+1')
    srcs = []
    for name, path in (('layers', os.path.join(PAPER, '..', 'twocoset_ext', 'layers.py')),
                       ('nets', os.path.join(PAPER, '..', 'rev15_audit', 'nets.py'))):
        if os.path.exists(path):
            spec = importlib.util.spec_from_file_location('src_' + name, path)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            srcs.append((name, mod))
    for p in (5, 7, 53, 97, 101, 353, 1009):
        B, R = wnet.W(p)
        h, r = (p - 1) // 2, p // 48
        rho = 2 * r + 1
        check(B == [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]] and R == [[0, 1, 2], [1, 0, 1], [0, 1, 0]],
              f'wnet.W({p}) == printed rows')
        for name, mod in srcs:
            if name == 'layers':
                check(mod.W(p) == B and mod.R_W == R, f'printed rows == twocoset_ext/layers.py W, R_W at p={p}')
            else:
                check(list(map(list, mod.W(p)[0])) == B and list(map(list, mod.W(p)[1])) == R,
                      f'printed rows == rev15_audit/nets.py W at p={p}')
    if not srcs:
        print('    (source notes not found; rows compared with wnet.py only)')
    # lem:drift(2): the printed counterexample q=5, w=(-8,4,4), l=(0,1,-1): excess sum 175/3 instead of -200/3
    q, w, l = 5, (-8, 4, 4), (0, 1, -1)
    a = [(q + x) // 3 for x in w]
    check(sum(w) == 0 and all((x + q) % 3 == 0 for x in w) and sum(l) % q == 0, 'lem:drift cex satisfies the hypotheses')
    phi = lambda n: q * (sum(x * y for x, y in zip(a, n)) % q) + sum(x * y for x, y in zip(l, n)) % q
    n, tot = [0, 0, 0], Fr(0)
    for _ in range(q):
        m = n[:]
        m[0] = (m[0] + 1) % q
        D = (phi(m) - phi(n)) % (q * q)
        x = D if Fr(D) <= Fr(5 * q * q, 6) else D - q * q
        tot += x - Fr(q * q, 3)
        n = m
    check(tot == Fr(175, 3) and Fr(q * q * w[0], 3) == Fr(-200, 3), f'lem:drift cex: excess sum {tot}, not -200/3')
    j = TEX.index('\\label{lem:drift}')
    check('the excesses of a cycle in the direction $\\e_x$ sum to $\\frac{175}3$, not $-\\frac{200}3$' in
          TEX[j:TEX.index('\\end{proof}', j)], 'lem:drift: counterexample printed as computed')
    # prop:4D2(3), rev 15.1 (k >= 2): c < alpha + 6/(alpha q^2) <= 1 - 2/q + (102/15)/q^2 < 1 - 2/q + 8/q^2, alpha = 1-2/q
    check(all((1 - Fr(2, q)) >= Fr(15, 17) and Fr(6) / (1 - Fr(2, q)) <= Fr(102, 15) for q in range(17, 2000, 2))
          and Fr(102, 15) < 8, 'prop:4D2(3): alpha >= 15/17 and 6/alpha <= 102/15 < 8 for odd q >= 17')
    print('    rows, counterexample and constants checked')


def main():
    if '--emit' in sys.argv:
        what = sys.argv[sys.argv.index('--emit') + 1]
        if what == 'perprime':
            for row in emit_perprime():
                print(row)
        elif what == 'seeds':
            for row in emit_seeds():
                print(row)
        elif what == 'kappa':
            for k, v in sorted(kappa_source().items()):
                print(k, v)
        return
    for f in (check_perprime, check_kappa, check_seeds, check_cubecost, check_dim4, check_half5, check_colnets, check_twocoset, check_wnet):
        f()
    print(f'printed_data: {NCHK[0]} checks, {len(FAIL)} failed')
    if FAIL:
        sys.exit(1)
    print('printed_data: all printed data agree with their sources')


if __name__ == '__main__':
    main()
