#!/usr/bin/env python3
"""crosscheck.py -- check the nets of explainers/anatomy.html against Python references built from the paper.

Runs the page's own NetCore block under node (check/run_core.mjs), then for every net the page can show:
  * 2D (section 1): rebuilds the Hammersley frame (places infinity, 0: generators J, I), derives its graph form by
    inverting the (k,k) box matrix, applies the gauge moves of lem:box for the turned layer, and compares generator
    matrices mod q and point sets exactly; the plain frame is also compared with {(i, rev_q(i))};
  * P_{k,q} (section 2): generator matrices and points against netdefs.P_mats (the builder behind Table tab:c),
    exact minimum distances against the printed row of tab:c;
  * C_q (sections 2, 3): points against figs_col.col_net (def:col), d^2 against the closed form of thm:col, and the
    cycle heights against figs_col.cycle_heights (fig:drift);
  * all: exact toroidal and Euclidean minimum distances by an independent numpy neighbour-cell computation, closest-pair
    counts, the lattice-image minimum (2D), the lattice minimum lambda_1, the bound c(q) of thm:main;
  * t = 0: net_tparam.t_value_matrices (Niederreiter rank test) for prime q, and an independent count of the points in
    every elementary box for every q (composite q included), compared with the page's own box check.

    uv run --with numpy --with matplotlib python explainers/check/crosscheck.py      (~15 s)
"""
import itertools
import json
import math
import os
import subprocess
import sys
import tempfile
import time
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXPL = os.path.dirname(HERE)
GEO = os.path.dirname(EXPL)
SCRIPTS = os.path.join(GEO, 'paper', 'scripts')
GEN3D = os.path.dirname(GEO)
sys.path.insert(0, SCRIPTS)
sys.path.insert(0, GEN3D)
import netdefs  # noqa: E402  (def:net builder used for tab:c)
import tab_c  # noqa: E402    (reads the printed Table tab:c from core.tex)
import figs_col  # noqa: E402  (def:col builder and fig:drift cycles)
from net_tparam import t_value_matrices  # noqa: E402

NODE = os.environ.get('NODE', '/opt/homebrew/bin/node')
FAILS, OKS = [], []


def check(cond, what):
    (OKS if cond else FAILS).append(what)
    if not cond:
        print('FAIL', what)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** .5) + 1))


# ------------------------------------------------------------------ generic digital-net machinery (numpy)
def points(C, q):
    """integer coordinates (N x s) of the digital net with generator matrices C (s x m x m, any integers)."""
    C = [np.array(Cc, dtype=np.int64) % q for Cc in C]
    m = C[0].shape[0]
    N = q ** m
    idx = np.arange(N, dtype=np.int64)
    V = np.stack([(idx // q ** l) % q for l in range(m)], axis=1)          # v_l, least significant first
    w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
    return np.stack([((V @ Cc.T) % q) @ w for Cc in C], axis=1)


def as_set(P):
    return set(map(tuple, np.asarray(P).tolist()))


def cell_grid(P, q, m, k):
    """arrays Xg[c] of shape (G,)*s with the coordinate of the point in each cell; asserts one point per cell."""
    s = P.shape[1]
    cw, G = q ** (m - k), q ** k
    cells = P // cw
    flat = np.ravel_multi_index(tuple(cells.T), (G,) * s)
    assert len(np.unique(flat)) == len(flat) == G ** s, 'not one point per cell'
    Xg = []
    for c in range(s):
        a = np.empty(G ** s, dtype=np.int64)
        a[flat] = P[:, c]
        Xg.append(a.reshape((G,) * s))
    return Xg, G, cw


def min_dist_np(P, q, m, k, toroidal):
    """exact minimum squared distance over neighbouring cells (|e| <= 1), and the number of closest pairs.
    Exact whenever the result is <= one cell side squared (pairs with |e_c| >= 2 are > 1 cell apart)."""
    Xg, G, cw = cell_grid(P, q, m, k)
    s = len(Xg)
    W = q ** m
    best, hits = None, 0
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e):
            continue
        if toroidal:
            D = [np.roll(Xg[c], shift=tuple(-x for x in e), axis=tuple(range(s))) - Xg[c] for c in range(s)]
            D = [(d + W // 2) % W - W // 2 for d in D]
        else:
            sl_a = tuple(slice(max(0, -x), G - max(0, x)) for x in e)
            sl_b = tuple(slice(max(0, x), G + min(0, x)) for x in e)
            D = [Xg[c][sl_b] - Xg[c][sl_a] for c in range(s)]
        d2 = sum(d.astype(np.int64) ** 2 for d in D)
        if d2.size == 0:
            continue
        mn = int(d2.min())
        if best is None or mn < best:
            best, hits = mn, int((d2 == mn).sum())
        elif mn == best:
            hits += int((d2 == mn).sum())
    exact = best <= cw * cw
    return best, hits // 2, exact, G


def box_counts_ok(P, q, m):
    """t = 0 by counting: every elementary box of volume q^-m holds exactly one point (any q)."""
    s = P.shape[1]
    for d in itertools.product(range(m + 1), repeat=s):
        if sum(d) != m:
            continue
        key = np.zeros(len(P), dtype=np.int64)
        for c in range(s):
            key = key * q ** d[c] + P[:, c] // q ** (m - d[c])
        if len(np.unique(key)) != len(P):
            return False, d
    return True, None


def frac_inv(A):
    n = len(A)
    M = [[Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        iv = 1 / M[c][c]
        M[c] = [x * iv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    R = [r[n:] for r in M]
    assert all(x.denominator == 1 for r in R for x in r)
    return [[int(x) for x in r] for r in R]


# ------------------------------------------------------------------ section 1 reference: Hammersley frame + gauge
def hammersley_ref(k, variant):
    m = 2 * k
    J = [[int(j == m - 1 - i) for j in range(m)] for i in range(m)]     # reading at infinity: digit j = [t^(m-1-j)]V
    I = netdefs.eye(m)                                                  # reading at 0:        digit j = [t^j]V
    frame = [J, I]
    Bk = [frame[c][i] for c in range(2) for i in range(k)]              # box matrix of the depths (k, k)
    Binv = frac_inv(Bk)
    Gf = [netdefs.mul(Cc, Binv) for Cc in frame]                        # graph form (cells as index digits)
    for c in range(2):                                                  # cell rows are unit rows
        for i in range(k):
            assert Gf[c][i] == [int(j == c * k + i) for j in range(m)]
    # off-diagonal blocks of the frame's graph form: Phi_xy = Phi_yx = J_k, diagonal blocks 0
    if variant == 'rotated':
        # gauge (c): L_x = -I on Phi_xy;  gauge (a): row 0 of the diagonal blocks = -1 on the last level k-1
        for r in range(k):
            for j in range(k):
                Gf[0][k + r][k + j] = -Gf[0][k + r][k + j]
        Gf[0][k][k - 1] = -1
        Gf[1][k][2 * k - 1] = -1
    return Gf


def rev_q(i, q, m):
    r = 0
    for _ in range(m):
        r = r * q + i % q
        i //= q
    return r


def lattice_min_ref(M, q, R=5):
    s = len(M)
    A = np.eye(s) + np.array(M, dtype=float) / q
    best = min(np.linalg.norm(A @ np.array(v)) for v in itertools.product(range(-R, R + 1), repeat=s) if any(v))
    return best


# ------------------------------------------------------------------ section 0: the worked example
M_PROPCELL = [[-1, -1, 1], [1, -1, -1], [-1, 1, -1]]       # prop:cell, typed from core.tex
J_PROPCELL = [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]


def ref_generators(name, k, q):
    if name.startswith('H2'):
        return hammersley_ref(k, name.split('-')[1])
    if name.startswith('P'):
        return netdefs.P_mats(k)['C']
    a = [int(x) for x in (q + figs_col.col_w(q)) // 3]
    return [[[int(j == c) for j in range(3)], a, [-1, 1, 0]] for c in range(3)]


def ref_layer(name, k, q):
    """(M, J) of the first offset digit, from the paper: lem:box gauge / Hammersley, prop:cell, def:col."""
    if name.startswith('H2'):
        return ([[-1, -1], [1, -1]] if 'rotated' in name else [[0, 1], [1, 0]]), None
    if name.startswith('P'):
        return M_PROPCELL, (J_PROPCELL if k >= 2 else None)
    a = [int(x) for x in (q + figs_col.col_w(q)) // 3]
    return [a, a, a], None


def check_worked_example(js):
    cache, bad, seen = {}, {}, {}
    for rec in js['explain']:
        name, q, k, i, E = rec['name'], rec['q'], rec['k'], rec['i'], rec['ex']
        key = name
        if key not in cache:
            Cref = ref_generators(name, k, q)
            P = points(Cref, q)
            m = len(Cref[0])
            M, J = ref_layer(name, k, q)
            # the layer formula on ALL points of the net (prop:cell / def:geom / def:col)
            cw = q ** (m - k)
            n = P // cw
            ell, h = n % q, (n // q) % q
            r = (P // q ** (m - k - 1)) % q
            pred = ell @ np.array(M).T + (h @ np.array(J).T if J else 0)
            check(bool(np.all(pred % q == r)), f'{name}: digit k+1 = (M l + J h) mod q on all {len(P)} points')
            cache[key] = (Cref, P, m, M, J)
        Cref, P, m, M, J = cache[key]
        errs = []
        v = [(i // q ** l) % q for l in range(m)]
        if E['v'] != v:
            errs.append('v')
        for c, Cc in enumerate(Cref):
            Cc = [[x % q for x in row] for row in Cc]
            co = E['coords'][c]
            if co['C'] != Cc:
                errs.append('C')
            for j in range(m):
                terms = [Cc[j][l] * v[l] for l in range(m)]
                rw = co['rows'][j]
                if rw['terms'] != terms or rw['sum'] != sum(terms) or rw['d'] != sum(terms) % q or co['d'][j] != rw['d']:
                    errs.append(f'row{c}.{j}')
            if co['X'] != int(P[i][c]):
                errs.append('X')
        s = len(Cref)
        cw = q ** (m - k)
        n = [int(P[i][c]) // cw for c in range(s)]
        ell = [x % q for x in n]
        blk = [x // q for x in n]
        hh = [x % q for x in blk]
        r = [(int(P[i][c]) // q ** (m - k - 1)) % q for c in range(s)]
        if [E['n'], E['ell'], E['blk'], E['h'], E['r']] != [n, ell, blk, hh, r]:
            errs.append('cell digits')
        if E['M'] != M or E['J'] != J:
            errs.append('layer')
        for c in range(s):
            Jh = sum(J[c][d] * hh[d] for d in range(s)) if J else 0
            pre = sum(M[c][d] * ell[d] for d in range(s)) + Jh
            lat = q * n[c] + sum(M[c][d] * n[d] for d in range(s))
            sh = -q * sum(M[c][d] * blk[d] for d in range(s)) + Jh
            img = q * n[c] + r[c]
            want = (pre, pre % q, pre // q, lat, sh, img)
            got = (E['pre'][c], E['rPred'][c], E['kappa'][c], E['latNum'][c], E['shiftNum'][c], E['imgNum'][c])
            if got != want or img != lat + sh - q * (pre // q) or pre % q != r[c]:
                errs.append(f'lattice {c}')
        if not E['ok']:
            errs.append('page identity flag')
        if name.startswith('C'):
            a, phi_all = figs_col.col_net(q)[0], figs_col.col_net(q)[2]
            an = sum(int(a[d]) * n[d] for d in range(3))
            jn = n[1] - n[0]
            phi = q * (an % q) + jn % q
            idx3 = n[0] * q * q + n[1] * q + n[2]                          # itertools.product order of col_net
            want = dict(an=an, hn=an % q, k2=an // q, jn=jn, jv=jn % q, k3=jn // q, phi=phi, lin=q * an + jn)
            if E['col'] != want or int(phi_all[idx3]) != phi or phi != q * an + jn - q * q * (an // q) - q * (jn // q):
                errs.append('column height')
        seen[name] = seen.get(name, 0) + 1
        if errs:
            bad.setdefault(name, []).append((i, errs))
    for name, cnt in seen.items():
        check(name not in bad, f'{name}: worked example, all numbers of steps 1-5 at {cnt} indices '
                               f'{"" if name not in bad else bad[name][:3]}')
    # step 6: execute the printed listing and the full programs
    ns = {}
    exec(js['pyListing'], ns)
    net_points = ns['net_points']
    nchk = 0
    for net in js['nets']:
        if net['N'] > 30000:
            continue
        Pjs = [tuple(t) for t in np.array(net['X'], dtype=np.int64).T.tolist()]
        check(net_points(net['C'], net['q']) == Pjs, f'{net["name"]}: printed Python listing = NetCore.build, in order')
        nchk += 1
    import contextlib
    import io
    for pr in js['programs']:
        buf, ns2 = io.StringIO(), {}
        with contextlib.redirect_stdout(buf):
            exec(pr['text'], ns2)
        Cref = ref_generators(pr['name'], int(pr['name'].split('-k')[-1]) if '-k' in pr['name'] else 1, pr['q'])
        ok = buf.getvalue().strip() == str(tuple(pr['X'])) and ns2['points'] == [tuple(map(int, t)) for t in points(Cref, pr['q'])]
        check(ok, f'{pr["name"]}: full step-6 program runs, prints points[{pr["i"]}] = {tuple(pr["X"])}, all points = reference')
    print(f'worked example: {len(js["explain"])} explained points in {len(seen)} nets; listing run on {nchk} nets')


def det_int(A):
    """exact integer determinant (Fractions)."""
    n = len(A)
    if n == 0:
        return 1
    M = [[Fraction(x) for x in r] for r in A]
    det = Fraction(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if M[i][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        for i in range(c + 1, n):
            f = M[i][c] / M[c][c]
            M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    assert det.denominator == 1
    return int(det)


def occupancy(P, q, m, d):
    """number of points in each elementary box of shape d (any q): (empty, one, many, boxes)"""
    key = np.zeros(len(P), dtype=np.int64)
    for c in range(P.shape[1]):
        key = key * q ** d[c] + P[:, c] // q ** (m - d[c])
    cnt = np.bincount(key, minlength=q ** m)
    return dict(empty=int((cnt == 0).sum()), one=int((cnt == 1).sum()), many=int((cnt > 1).sum()), n=int(q ** m))


def compositions(m, s):
    if s == 1:
        yield (m,)
        return
    for a in range(m + 1):
        for rest in compositions(m - a, s - 1):
            yield (a,) + rest


def check_boxes(js):
    """sections 1-4 and 8 of page 1: box minors (lem:nie) against integer determinants of the reference generator
    rows, box counts on the reference points (with and without the deeper digits), the scramble L from the frame to
    the turned layer (lower triangular, L C_frame = C_turned mod q), the frame's wrap step, the 3D frame."""
    import math as _m
    for rec in js['boxes2d']:
        q, k = rec['q'], rec['k']
        m = 2 * k
        variant = rec['name'].split('-')[1]
        C = hammersley_ref(k, variant)
        P = points(C, q)
        T = P - P % q ** (m - k - 1)
        ok = True
        for d, b, bt, o, ot in zip(compositions(m, 2), rec['full'], rec['trunc'], rec['occ'], rec['occT']):
            A = [C[c][j] for c in range(2) for j in range(d[c])]
            At = [[0] * m if j >= k + 1 else C[c][j] for c in range(2) for j in range(d[c])]
            D, Dt = det_int(A), det_int(At)
            ok = ok and list(d) == b['d'] and b['A'] == A and b['det'] == D and b['mod'] == D % q and b['unit'] == (_m.gcd(D, q) == 1)
            ok = ok and bt['mod'] == Dt % q and bt['unit'] == (_m.gcd(Dt, q) == 1)
            ok = ok and o == occupancy(P, q, m, d) and ot == occupancy(T, q, m, d)
            ok = ok and b['unit'] == (o['one'] == o['n']) and bt['unit'] == (ot['one'] == ot['n'])   # lem:nie both ways
            if variant == 'frame':
                ok = ok and abs(D) == 1                                                             # lem:Ts
        check(ok, f'{rec["name"]}: {m + 1} box minors = integer determinants, box counts with and without the deeper digits, '
                  f'unit <=> one point per box')
        if 'scr' in rec:
            R = hammersley_ref(k, 'rotated')
            ok = True
            for c in range(2):
                L = rec['scr'][c]['L']
                prod = [[sum(L[i][t] * C[c][t][j] for t in range(m)) % q for j in range(m)] for i in range(m)]
                low = all(L[i][j] == 0 for i in range(m) for j in range(i + 1, m)) and all(_m.gcd(L[i][i], q) == 1 for i in range(m))
                deep = ['same' if L[i][i] == 1 else 'negated' if L[i][i] == q - 1 else 'scaled' for i in range(k + 1, m)]
                if any(L[i][j] for i in range(k + 1, m) for j in range(m) if j != i):
                    deep = None
                ok = ok and prod == [[x % q for x in r] for r in R[c]] and low == rec['scr'][c]['lower'] and low
                ok = ok and deep == rec['scr'][c]['deep']
            check(ok, f'H2 q={q} k={k}: frame -> turned is a lower-triangular scramble L per coordinate, L C_frame = C_turned; '
                      f'deeper rows {rec["scr"][0]["deep"]} / {rec["scr"][1]["deep"]}')
            st = rec['step']
            n, n2 = (q - 1, q - 1), (q % q ** k, q % q ** k)
            G = q ** k
            n2 = ((q - 1 + 1) % G, (q - 1 + 1) % G)
            cw = q ** (m - k)
            cells = P // cw
            ia = int(np.where((cells == n).all(1))[0][0])
            ib = int(np.where((cells == n2).all(1))[0][0])
            W = q ** m
            D = [(int(P[ib, c] - P[ia, c]) + W // 2) % W - W // 2 for c in range(2)]
            if any(abs(2 * x) == W for x in D):
                D = st['D']
            dg = [int((P[ib, c] // q ** (m - k - 1)) % q - (P[ia, c] // q ** (m - k - 1)) % q) for c in range(2)]
            check(st['D'] == D and [o['value'] for o in st['digits']] == dg
                  and abs(st['len'] - _m.sqrt(D[0] ** 2 + D[1] ** 2) / cw) < 1e-12,
                  f'H2 frame q={q} k={k}: step (1,1) from cell {n}: digit changes {dg}, difference {D}')
    for rec in js['frame3']:
        k, q = rec['k'], rec['q']
        T, T2 = netdefs.frame(k)
        C = [T2, netdefs.eye(3 * k), T]
        check(rec['C'] == [[[x % q for x in r] for r in Cc] for Cc in C], f'3D frame k={k} q={q}: generators (T^2, I, T)')
        Pm = netdefs.P_mats(k)
        check(all(netdefs.mul(Pm['L'], C[c]) == Pm['C'][c] for c in range(3)), f'3D frame k={k}: P_k = L x frame, L lower triangular'
              if all(Pm['L'][i][j] == 0 for i in range(3 * k) for j in range(i + 1, 3 * k)) else 'L not lower')
        dets = [det_int([C[c][j] for c in range(3) for j in range(d[c])]) for d in compositions(3 * k, 3)]
        check(dets == rec['dets'] and all(abs(x) == 1 for x in dets), f'3D frame k={k}: all {len(dets)} box minors +-1 (lem:Ts)')
        P = points(C, q)
        if rec['X'] is not None:
            check(as_set(P) == as_set(np.array(rec['X']).T), f'3D frame k={k} q={q}: point sets equal')
        d2, _, ex, _ = min_dist_np(P, q, 3 * k, k, True)
        if not ex:
            d2 = min(d2, rec['d2']) if rec['d2'] <= d2 else d2
        check(ex and d2 == rec['d2'], f'3D frame k={k} q={q}: toroidal d^2 = {d2} (numpy)')
        okb, _ = box_counts_ok(P, q, 3 * k)
        check(okb and rec['box'], f'3D frame k={k} q={q}: every elementary box holds one point')
    for rec in js['direct']:
        kind, q = rec['kind'], rec['q']
        if kind == 'C':
            a = [int(x) for x in (q + figs_col.col_w(q)) // 3]
            B, R = [a, a, a], [[-1, 1, 0]] * 3
        elif kind == 'T':
            h, r = (q - 1) // 2, round(q / 8)
            B, R = [[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]
        else:
            h, r = (q - 1) // 2, q // 48
            rho = 2 * r + 1
            B, R = [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]
        C = [[[int(d == c) for d in range(3)], list(B[c]), list(R[c])] for c in range(3)]
        check(rec['C'] == [[[x % q for x in r] for r in Cc] for Cc in C], f'{kind}_{q}: generator rows of the paper')
        P = points(C, q)
        T = P - P % q
        ok = True
        nunit = 0
        for d, b, bt, o, ot in zip(compositions(3, 3), rec['full'], rec['trunc'], rec['occ'], rec['occT']):
            D = det_int([C[c][j] for c in range(3) for j in range(d[c])])
            Dt = det_int([[0, 0, 0] if j >= 2 else C[c][j] for c in range(3) for j in range(d[c])])
            ok = ok and b['mod'] == D % q and bt['mod'] == Dt % q and b['unit'] == (_m.gcd(D, q) == 1) and bt['unit'] == (_m.gcd(Dt, q) == 1)
            ok = ok and o == occupancy(P, q, 3, d) and ot == occupancy(T, q, 3, d)
            ok = ok and b['unit'] == (o['one'] == o['n']) and bt['unit'] == (ot['one'] == ot['n'])
            nunit += b['unit']
        expect_all = not (kind == 'T' and q == 23)
        check(ok and (nunit == 10) == expect_all, f'{kind}_{q}: 10 box minors mod q and box counts, with and without the third digit; '
                                                 f'{"all units" if expect_all else "one minor vanishes (p = 23)"}')


def main():
    t0 = time.time()
    core = os.path.join(EXPL, 'netcore.js')
    with tempfile.TemporaryDirectory() as td:
        outp = os.path.join(td, 'core.json')
        r = subprocess.run([NODE, os.path.join(HERE, 'run_core.mjs'), core, outp], capture_output=True, text=True,
                           timeout=60)
        print(r.stdout.strip(), r.stderr.strip())
        assert r.returncode == 0
        js = json.load(open(outp))
    t_node = time.time() - t0
    printed_cq, printed_p2 = tab_c.printed_tab_c()
    tested_t = []
    for net in js['nets']:
        name, q, s, m, k = net['name'], net['q'], net['s'], net['m'], net['k']
        Pjs = np.array(net['X'], dtype=np.int64).T
        Cjs = net['C']
        if name.startswith('H2'):
            variant = name.split('-')[1]
            Cref = hammersley_ref(k, variant)
        elif name.startswith('P'):
            Cref = netdefs.P_mats(k)['C']
        else:
            Cref = None
        if Cref is not None:
            check([[[x % q for x in r] for r in Cc] for Cc in Cref] == Cjs, f'{name}: generator matrices mod q equal')
            Pref = points(Cref, q)
        else:                                                           # column net, def:col via figs_col
            a, n, phi = figs_col.col_net(q)
            Pref = q * q * n + phi[:, None]
            check(Cjs == [[[int(j == c) for j in range(3)], [int(x) for x in a], [q - 1, 1, 0]] for c in range(3)],
                  f'{name}: generator rows e_c, a, l of def:col')
        check(as_set(Pref) == as_set(Pjs) and len(as_set(Pjs)) == q ** m, f'{name}: point sets equal ({q ** m} points)')
        if name.startswith('H2') and name.split('-')[1] == 'frame':
            ham = {(i, rev_q(i, q, m)) for i in range(q ** m)}
            check(ham == as_set(Pjs), f'{name}: plain frame = Hammersley set {{(i, rev(i))}}')
        # exact minimum distances, independent kernel
        d2t, cnt_t, ex_t, G = min_dist_np(Pref, q, m, k, True)
        d2e, _, ex_e, _ = min_dist_np(Pref, q, m, k, False)
        if ex_t:
            check(d2t == net['tor']['d2'], f'{name}: toroidal d^2 = {d2t}')
            if G >= 3:
                check(cnt_t == net['tor']['count'], f'{name}: {cnt_t} closest pairs')
        else:
            check(net['tor']['d2'] <= d2t, f'{name}: toroidal d^2 beyond one cell; page value <= neighbour value')
        if ex_e:
            check(d2e == net['euc']['d2'], f'{name}: Euclidean d^2 = {d2e}')
        pr = net['tor']['pair']
        if pr:
            D = Pjs[pr['j']] - Pjs[pr['i']]
            W = q ** m
            D = (D + W // 2) % W - W // 2
            check(int((D * D).sum()) == net['tor']['d2'], f'{name}: reported closest pair realizes d^2')
        if 'lat' in net:
            u = q ** (m - k - 1)
            d2l, cnt_l, exl, _ = min_dist_np(Pref - Pref % u, q, m, k, True)
            check(exl and d2l == net['lat']['d2'], f'{name}: lattice-image d^2 = {d2l}')
            Mref = [[-1, -1], [1, -1]] if 'rotated' in name else [[0, 1], [1, 0]]
            check(abs(lattice_min_ref(Mref, q) - net['lam']) < 1e-12, f'{name}: lambda_1 of (I+M/q)Z^2')
        if name.startswith('P') and k == 2 and q in printed_p2:
            c = math.isqrt(d2t * 10 ** 8 // (q ** (m - k)) ** 2)            # floor(10^4 sqrt(d2)/cw)
            check(tab_c.fmt(c) == printed_p2[q], f'{name}: c = {tab_c.fmt(c)} = printed tab:c value {printed_p2[q]}')
        if name.startswith('C'):
            check(d2t == figs_col.d2_closed(q) == net['tor']['d2'], f'{name}: d^2 = (2q^4+tau^2)/3 = {d2t} (thm:col)')
        # t = 0
        okb, bad = box_counts_ok(Pref, q, m)
        check(okb and net['box']['ok'], f'{name}: every elementary box holds one point (python count and page)')
        if is_prime(q):
            t, t0flag = t_value_matrices(q, m, s, [[[x % q for x in r] for r in Cc] for Cc in Cjs])
            check(t == 0 and t0flag, f'{name}: net_tparam t = {t}')
            tested_t.append(name)
    # section 3: cycles and closed-form theory
    for qs, cyc in js['cycles'].items():
        q = int(qs)
        for i in range(3):
            ref = figs_col.cycle_heights(q, i)
            check(list(map(int, ref)) == cyc[i], f'C_{q}: cycle e_{"xyz"[i]} step values = fig:drift builder')
            assert (sum(cyc[i]) * 3) % (q * q) == 0
            check(sum(cyc[i]) * 3 == q * q * (q + list(figs_col.col_w(q))[i]),
                  f'C_{q}: cycle e_{"xyz"[i]} closes at (q + w_i)/3 periods')
        th = js['coltheory'][qs]
        check(th['d2'] == figs_col.d2_closed(q) and th['tau'] == figs_col.tau(q), f'C_{q}: closed form d^2, tau')
        w = list(figs_col.col_w(q))
        eps3 = [q * w[i] + 3 * r for i, r in enumerate((q - 1, 1, 0))]
        check(th['eps3'] == eps3 and th['eta3'] == max(eps3), f'C_{q}: excesses eps and eta (lem:drift)')
    for qs, v in js['cmain'].items():
        ref = math.sqrt(float(tab_c.c_main(int(qs))))   # tab_c.c_main returns c(q)^2
        check(abs(ref - v) < 1e-12, f'c({qs}) of thm:main')
    check_worked_example(js)
    check_boxes(js)
    for k in (1, 2, 3):                 # page 1, section 2: the base-2 frame's closest difference on the torus
        n = next(x for x in js['nets'] if x['name'] == f'H2-frame-q2-k{k}')
        check(n['tor']['d2'] == 2 and sorted(map(abs, n['tor']['pair']['D'])) == [1, 1],
              f'H2 frame q=2 k={k}: closest toroidal difference (1, 1) units, d^2 = 2')
    print(f'node {t_node:.1f}s, total {time.time() - t0:.1f}s; t = 0 by net_tparam for {len(tested_t)} prime-base nets')
    print(f'{len(OKS)} checks passed, {len(FAILS)} failed')
    for name in ('P-q4-k2', 'P-q5-k2', 'P-q6-k2', 'P-q7-k2', 'C-q5', 'C-q7', 'H2-rotated-q5-k2'):
        n = next(x for x in js['nets'] if x['name'] == name)
        print(f'  {name:18s} d2 = {n["tor"]["d2"]:>9d}  c = {math.sqrt(n["tor"]["d2"]) / n["q"] ** (n["m"] - n["k"]):.4f}'
              f'  closest pairs {n["tor"]["count"]}')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
