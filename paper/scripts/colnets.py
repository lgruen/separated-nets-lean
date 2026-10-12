#!/usr/bin/env python3
"""colnets.py -- computations for the column nets C_q (m = 3) and the comparison nets T_p, E_p, J_p.

C_q (q >= 5, gcd(q,6) = 1), graph form with depths (1,1,1) over Z/q: coordinate c of cell n has the digits
n_c, h(n) = a.n, j(n) = n_y - n_x, with a = (q 1 + w)/3, w = (-2,1,1) if q = 2 mod 3 and w = (-1,-1,2) if q = 1 mod 3.
Integer points at scale q^3: X(n) = q^2 n + (q h(n) + j(n)) (1,1,1).  d2 = toroidal min squared distance, c = sqrt(d2)/q^2.

Checks (each is a finite computation over the stated range; none of them proves a general statement):
 (a) Theorem C (d2 = 2q^4/3 + 3g^2 for every column point set X(n) = q^2 n + phi([n]) 1) against an O(N^2) brute
     force on random phi (arbitrary with repeats, random bijections, random Lemma-B nets) at q = 2..13; the
     neighbour-cell kernel of colmind.cpp is checked against the same brute force; d2 <= q^4 on every set.
 (b) the closed forms d2(C_q) = (2q^4 + (q^2-q-3)^2)/3 (q = 2 mod 3), (2q^4 + (q^2-2q)^2)/3 (q = 1 mod 3) against two
     exact kernels (colmind.cpp neighbour cells, certified; cellmin.cpp) at every q coprime to 6 in [5, Q], composites
     included; the "wrong-class" net (a = 3^-1 (-2,1,1) at q = 1 mod 3) against (2q^4 + (q-3)^2)/3.
 (c) t = 0 of C_q: the 10 box determinants of the generator rows e_c, a, (-1,1,0) are units (and lie in
     {+-1, +-a_e, +-(a_x+a_y)}) at every q coprime to 6 up to 241; direct box counting (all 10 shapes) at
     q = 5, 7, 11, 25, 35; the minor criterion agrees with box counting on random (a, l) at q = 5, 7, 11.
 (d) digital shifts (constant digit vectors tau_c added digitwise mod q): random shifts per category at several q,
     and ALL shifts up to torus isometry at small q (only the differences tau_c2 - tau_x2, tau_c3 - tau_x3 matter;
     this reduction is itself checked on every random shift at those q):
       (A) equal across coordinates at digits 2 and 3:  d2 unchanged;
       (B) equal at digit 2, unequal at digit 3:         c >= 1 - (7q-3)/(sqrt3 q^2);
       (C) unequal at digit 2:                           c >= (q^2 - (W+3)q + 3)/(sqrt3 q^2), W = 2 (q=2) / 4 (q=1),
                                                         and c <= sqrt3 (q a_max + q - 1)/q^2, a_max = max_i a_i.
     For (C) the premise of the upper-bound argument (some direction c has a residue whose step e_c wraps the shared
     digit of coordinate c only) is checked exhaustively over all (b_x,b_y,b_z) not all equal (q <= 61; --full: 151),
     and per shift with the per-direction bound 3(q a_c + q - 1)^2.  The stronger a_min version of the upper bound is
     only REPORTED: it fails on shifts lacking a lonely residue for the a_min direction (e.g. q = 5, tau_2 = (0,0,1)).
 (e) T_p (prop:twocoset) exactly by cellmin at every prime 7 <= p <= 199, p != 23; C_p vs T_p.
 (f) E_p (thm:E1) and J_p (Theorem L of the notes) exactly by cellmin at every prime 5 <= p <= 199 (figure data);
     J_p against its formula (q >= 7 resp. 11) and the audited checkpoints; E_p's p(1-c) at 197, 199.
 (g) the digital class maximum by Theorem C over all t=0 digital column nets equals d2(C_q), q coprime to 6, <= 151,
     with 6 (q = 2 mod 3) resp. 3 phi(q) (q = 1 mod 3) maximizers.
The values of (e), (f) are stored in colnets_exact.json and every recomputed value is compared with it.

    g++ -O3 -std=c++17 -o scripts/bin/cellmin scripts/cellmin.cpp
    g++ -O3 -std=c++17 -o scripts/bin/colmind scripts/colmind.cpp
    uv run python scripts/colnets.py            (default, ~25 s on 10 cores, ~3 min on one)
    uv run python scripts/colnets.py --full     (larger ranges in (a), (b), (c), (d); ~2.5 min on 10 cores)
    uv run python scripts/colnets.py --write    (rewrite colnets_exact.json from the recomputed values)
"""
import json
import math
import os
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
CELLMIN = os.path.join(HERE, 'bin', 'cellmin')
COLMIND = os.path.join(HERE, 'bin', 'colmind')
EXACT = os.path.join(HERE, 'colnets_exact.json')
FULL = '--full' in sys.argv
WRITE = '--write' in sys.argv
POOL = ThreadPoolExecutor(max_workers=os.cpu_count() or 4)
FAILS = []


def check(ok, what):
    print(f'  [{"ok" if ok else "FAIL"}] {what}', flush=True)
    if not ok:
        FAILS.append(what)
    return ok


def run(cmd, inp=''):
    return subprocess.run(cmd, input=inp, capture_output=True, text=True, check=True).stdout


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def coprime6(q):
    return math.gcd(q, 6) == 1


def phi_euler(n):
    return sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1)


# ---------------------------------------------------------------- the nets
W_S, W_R = (-2, 1, 1), (-1, -1, 2)
LJ = (-1, 1, 0)                                   # j(n) = n_y - n_x


def own_w(q):
    return W_S if q % 3 == 2 else W_R


def a_vec(q, w):
    """a = 3^-1 w mod q; in the own residue class this is (q 1 + w)/3."""
    i3 = pow(3, -1, q)
    return tuple(x * i3 % q for x in w)


def closed_d2(q):
    if q % 3 == 2:
        d2 = (2 * q**4 + (q * q - q - 3) ** 2) // 3
        assert 3 * d2 == 3 * q**4 - 2 * q**3 - 5 * q * q + 6 * q + 9 and (2 * q**4 + (q * q - q - 3) ** 2) % 3 == 0
    else:
        d2 = (2 * q**4 + (q * q - 2 * q) ** 2) // 3
        assert 3 * d2 == 3 * q**4 - 4 * q**3 + 4 * q * q and (2 * q**4 + (q * q - 2 * q) ** 2) % 3 == 0
    return d2


def cellmin_input(q, B, R):
    return f'{q}\n' + '\n'.join(' '.join(str(x % q) for x in row) for row in list(B) + list(R)) + '\n'


def graph_C(q, w=None):
    a = a_vec(q, w or own_w(q))
    return [a] * 3, [LJ] * 3


def graph_T(p):
    h, r = (p - 1) // 2, round(p / 8)
    return [[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]


def graph_E(p):
    a = p // 3
    return [[a, a, a]] * 3, [[0, 1, 0], [0, 0, 1], [1, 0, 0]]


def graph_J(p):
    a, t = p // 3, (p + 1) // 2
    R = []
    for c in range(3):          # l_c . n = t(-n_c - n_{c+1} + n_{c+2}), indices mod 3
        row = [0, 0, 0]
        row[c] -= t; row[(c + 1) % 3] -= t; row[(c + 2) % 3] += t
        R.append(row)
    return [[a, a, a]] * 3, R


GRAPH = {'C': graph_C, 'T': graph_T, 'E': graph_E, 'J': graph_J}


def cellmin(q, kind):
    return int(run([CELLMIN], cellmin_input(q, *GRAPH[kind](q))).split()[0])


def brute_graph(q, kind):
    return int(run([COLMIND, 'graph'], cellmin_input(q, *GRAPH[kind](q))).split()[0])


def colmind_dist(lines):
    """lines: list of (q, a, l, tau) -> list of (d2, cert); cert 1 = neighbour kernel certified, 2 = brute force"""
    inp = ''.join(f'{q} {" ".join(map(str, a))} {" ".join(map(str, l))} {" ".join(str(x) for row in t for x in row)}\n'
                  for q, a, l, t in lines)
    out = run([COLMIND, 'dist'], inp).split()
    return [(int(out[2 * i]), int(out[2 * i + 1])) for i in range(len(lines))]


ZERO = ((0, 0, 0),) * 3


def c_of(d2, q):
    return math.sqrt(d2) / q**2


# ---------------------------------------------------------------- (a)
def part_a():
    print('(a) Theorem C vs O(N^2) brute force on random column point sets, q = 2..13')
    reps = 120 if FULL else 40
    outs = list(POOL.map(lambda s: run([COLMIND, 'thmC', str(s), str(reps)]), [11, 12, 13]))
    tot = bad = 0
    for o in outs:
        for line in o.splitlines():
            if not line.startswith('thmC'):
                print('   ', line)
        last = [l for l in o.splitlines() if l.startswith('thmC')][0]
        kv = dict(x.split('=') for x in last.split()[1:])
        tot += int(kv['sets'])
        bad += int(kv['formula_mismatch']) + int(kv['nbr_mismatch']) + int(kv['above_q4'])
        print('   ', last)
    check(bad == 0, f'Theorem C == brute force, neighbour kernel == brute force, d2 <= q^4: {tot} sets, {bad} failures')


# ---------------------------------------------------------------- (b)
def part_b():
    Q = 401 if FULL else 241
    qs = [q for q in range(5, Q + 1) if coprime6(q)]
    print(f'(b) closed forms of C_q vs exact kernels at all {len(qs)} q coprime to 6 in [5, {Q}] '
          f'({sum(not is_prime(q) for q in qs)} composites)')
    for q in qs:   # the own-class row is (q 1 + w)/3
        assert a_vec(q, own_w(q)) == tuple((q + x) // 3 for x in own_w(q))
    t = time.time()
    cm = list(POOL.map(lambda q: colmind_dist([(q, a_vec(q, own_w(q)), LJ, ZERO)])[0], qs))
    t1 = time.time() - t
    t = time.time()
    ce = list(POOL.map(lambda q: cellmin(q, 'C'), qs))
    t2 = time.time() - t
    bad = [q for q, (d, cert), d3 in zip(qs, cm, ce) if not (d == d3 == closed_d2(q) and cert in (1, 2))]
    check(not bad, f'd2(C_q) == closed form == colmind (certified) == cellmin at all {len(qs)} q '
                   f'(colmind {t1:.1f} s, cellmin {t2:.1f} s); failures: {bad}')
    print(f'    e.g. C_5 = {cm[0][0]} (c = {c_of(cm[0][0], 5):.4f}), C_7 = {cm[1][0]} (c = {c_of(cm[1][0], 7):.4f}), '
          f'C_{qs[-1]} c = {c_of(cm[-1][0], qs[-1]):.6f}')
    # other residue class: a = 3^-1 (-2,1,1) at q = 1 mod 3
    qo = [q for q in qs if q % 3 == 1 and q <= 151]
    res = list(POOL.map(lambda q: colmind_dist([(q, a_vec(q, W_S), LJ, ZERO)])[0][0], qo))
    bad = [q for q, d in zip(qo, res) if d != (2 * q**4 + (q - 3) ** 2) // 3]
    check(not bad and res[0] == 1606, f'wrong-class net (w = (-2,1,1) at q = 1 mod 3): d2 = (2q^4 + (q-3)^2)/3 at all '
                                      f'{len(qo)} q = 1 mod 3 in [7, 151]; d2 = {res[0]} at q = 7; failures: {bad}')


# ---------------------------------------------------------------- (c)
def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


SHAPES = [(d0, d1, 3 - d0 - d1) for d0 in range(4) for d1 in range(4 - d0)]


def box_minors(q, a, l):
    E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    out = []
    for d in SHAPES:
        rows = []
        for c in range(3):
            rows += [E[c], a, l][:d[c]]
        out.append(det3(rows) % q)
    return out


def part_c():
    qs = [q for q in range(5, 242) if coprime6(q)]
    print(f'(c) t = 0 of C_q: box minors at all {len(qs)} q coprime to 6 up to 241; box counts')
    bad = []
    for q in qs:
        a = a_vec(q, own_w(q))
        mins = box_minors(q, a, LJ)
        allowed = {1, q - 1} | {x % q for e in a for x in (e, -e)} | {(a[0] + a[1]) % q, (-a[0] - a[1]) % q}
        if not all(math.gcd(m, q) == 1 for m in mins) or not set(mins) <= allowed:
            bad.append(q)
    check(not bad and len(SHAPES) == 10, f'all 10 box minors are units, in {{+-1, +-a_e, +-(a_x+a_y)}}: {len(qs)} q; failures {bad}')
    bq = [5, 7, 11, 25, 35] + ([49, 55] if FULL else [])
    out = run([COLMIND, 'box'], ''.join(f'{q} {" ".join(map(str, a_vec(q, own_w(q))))} -1 1 0\n' for q in bq)).split()
    check(all(x == '1' for x in out), f'direct box count, all 10 shapes, C_q is a (0,3,3)-net at q = {bq}')
    rng = random.Random(5)
    lines, pred = [], []
    for q in (5, 7, 11):
        for _ in range(40):
            a, l = [rng.randrange(q) for _ in range(3)], [rng.randrange(q) for _ in range(3)]
            lines.append(f'{q} {" ".join(map(str, a))} {" ".join(map(str, l))}\n')
            pred.append(all(math.gcd(m, q) == 1 for m in box_minors(q, a, l)))
    out = run([COLMIND, 'box'], ''.join(lines)).split()
    agree = sum((o == '1') == p for o, p in zip(out, pred))
    check(agree == len(pred), f'minor criterion == box count on {len(pred)} random (a, l) at q = 5, 7, 11 '
                              f'({sum(pred)} nets); agreements {agree}')


# ---------------------------------------------------------------- (d)
def bounds(q, d2, cat, d2_0, dz2):
    """the claimed bounds for one shift; dz2 = (tau_x2, tau_y2, tau_z2) (only differences matter).
    Returns (ok_claim, info) where info = (premise_holds, fallback_ok)."""
    a = a_vec(q, own_w(q))
    if cat == 'A':
        return d2 == d2_0, None
    if cat == 'B':   # c >= 1 - (7q-3)/(sqrt3 q^2)  <=>  sqrt(3 d2) >= sqrt3 q^2 - (7q-3)
        k = 7 * q - 3
        A = 3 * d2 - 3 * q**4 - k * k   # inequality: A >= -2 sqrt3 q^2 k
        return (A >= 0 or A * A <= 12 * q**4 * k * k), None
    W = 2 if q % 3 == 2 else 4
    L = q * q - (W + 3) * q + 3
    amin, amax = min(a), max(a)

    def lonely(i):   # a residue h whose step e_i wraps the second digit of coordinate i only
        for h in range(q):
            wr = [(h + dz2[c]) % q >= q - a[i] for c in range(3)]
            if wr[i] and sum(wr) == 1:
                return True
        return False
    lon = [lonely(i) for i in range(3)]
    fb = [3 * (q * a[i] + q - 1) ** 2 for i in range(3) if lon[i]]
    info = {'lower': L <= 0 or 3 * d2 >= L * L,                       # c >= (q^2-(W+3)q+3)/(sqrt3 q^2)
            'up_min': d2 <= 3 * (q * amin + q - 1) ** 2,               # claimed: c <= sqrt3 (q a_min + q - 1)/q^2
            'up_max': d2 <= 3 * (q * amax + q - 1) ** 2,               # c <= sqrt3 (q a_max + q - 1)/q^2
            'premise': any(lon[i] for i in range(3) if a[i] == amin),  # lonely residue for a direction with a_min
            'lonely_any': bool(fb),
            'lonely_ok': bool(fb) and d2 <= min(fb)}                   # d2 <= min over lonely i of 3(q a_i+q-1)^2
    return info['lower'] and info['up_max'] and info['lonely_ok'], info


def random_shift(rng, q, cat):
    while True:
        t = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
        if cat == 'A':
            for c in (1, 2):
                t[c][1], t[c][2] = t[0][1], t[0][2]
        elif cat == 'B':
            for c in (1, 2):
                t[c][1] = t[0][1]
            if len({t[c][2] for c in range(3)}) == 1:
                continue
        elif cat == 'C':
            if len({t[c][1] for c in range(3)}) == 1:
                continue
        elif cat == 'C2':   # exactly two digit-2 shifts equal (the case the upper-bound premise can miss)
            i, j = rng.sample(range(3), 2)
            t[j][1] = t[i][1]
            if len({t[c][1] for c in range(3)}) != 2:
                continue
        return t


def category(t2, t3):
    if len(set(t2)) > 1:
        return 'C'
    return 'A' if len(set(t3)) == 1 else 'B'


def lonely_combinatorics(q, full_cube=True):
    """for every (b_x,b_y,b_z) in (Z/q)^3 not all equal (or b_x = 0 only, which suffices by translation): is there a
    direction c and t in J_c^(c) = {b_c - a_c, ..., b_c - 1} with t outside J_d^(c) for both d != c?"""
    import numpy as np
    a = a_vec(q, own_w(q))
    r = np.arange(q)
    bx = r if full_cube else np.array([0])
    B = np.stack(np.meshgrid(bx, r, r, indexing='ij'), -1).reshape(-1, 3)
    B = B[~((B[:, 0] == B[:, 1]) & (B[:, 1] == B[:, 2]))]
    ok = np.zeros(len(B), bool)
    t = r[None, :]
    for c in range(3):
        inJ = [((B[:, d, None] - 1 - t) % q) < a[c] for d in range(3)]   # t in J_d^(c)
        only = inJ[c] & ~inJ[(c + 1) % 3] & ~inJ[(c + 2) % 3]
        ok |= only.any(1)
    return len(B), int((~ok).sum())


def part_d():
    print('(d) digital shifts of C_q')
    QL = 151 if FULL else 61
    t = time.time()
    tot = bad = 0
    for q in [q for q in range(5, QL + 1) if coprime6(q)]:
        n, b = lonely_combinatorics(q, full_cube=q <= 61)
        tot += n; bad += b
    check(bad == 0, f'combinatorial premise of the C upper bound: for every q coprime to 6 up to {QL} and every '
                    f'(b_x,b_y,b_z) not all equal (all of (Z/q)^3 for q <= 61, b_x = 0 beyond), some direction c and '
                    f't lie in J_c^(c) only: {tot} triples, {bad} failures ({time.time() - t:.1f} s)')
    ex_qs = [5, 7, 11, 13] + ([17, 19] if FULL else [])
    rnd_qs = [5, 7, 11, 13, 17, 19, 25, 35, 37, 41] + ([97, 101] if FULL else [])
    nper = 50
    # exhaustive tables (shifts up to isometry: tau_x = 0, tau_c1 = 0)
    tables = {}
    stats = {}

    def ex_job(args):
        q, lo, hi = args
        a = a_vec(q, own_w(q))
        return q, run([COLMIND, 'shiftall', str(q), *map(str, a), *map(str, LJ), str(lo), str(hi)])
    jobs = [(q, dy, dy + 1) for q in ex_qs for dy in range(q)]
    t = time.time()
    for q, out in POOL.map(ex_job, jobs):
        for line in out.splitlines():
            dy, dz, ey, ez, d2, cert = map(int, line.split())
            tables.setdefault(q, {})[(dy, dz, ey, ez)] = (d2, cert)
    t_ex = time.time() - t
    viol = {'A': [], 'B': [], 'C': []}
    Cinfo = []      # (q, shift, d2, info) for every C-shift, exhaustive and random
    nonc = 0
    for q in ex_qs:
        d2_0 = closed_d2(q)
        assert len(tables[q]) == q**4
        for (dy, dz, ey, ez), (d2, cert) in tables[q].items():
            nonc += cert != 1
            cat = category((0, dy, dz), (0, ey, ez))
            ok, info = bounds(q, d2, cat, d2_0, (0, dy, dz))
            st = stats.setdefault(('all', q, cat), [math.inf, 0, 0])
            st[0], st[1], st[2] = min(st[0], d2), max(st[1], d2), st[2] + 1
            if not ok:
                viol[cat].append((q, (dy, dz, ey, ez), d2, info))
            if cat == 'C':
                Cinfo.append((q, f'tau2=(0,{dy},{dz}) tau3=(0,{ey},{ez})', d2, info))
    print(f'    exhaustive (all shifts up to isometry, q^4 per q) at q = {ex_qs}: {sum(q**4 for q in ex_qs)} shifts '
          f'({t_ex:.1f} s)')
    check(nonc == 0, f'every exhaustive value certified by the neighbour kernel (uncertified: {nonc})')
    # random full shifts (all nine digits), ~50 per category
    def rnd_job(q):
        a = a_vec(q, own_w(q))
        shifts = [(cat, random_shift(rng_q, q, cat)) for rng_q in [random.Random(q * 7919 + 1)]
                  for cat in ('A', 'B', 'C', 'C2') for _ in range(nper)]
        res = colmind_dist([(q, a, LJ, t) for _, t in shifts])
        return q, shifts, res
    t = time.time()
    red_bad = 0
    nrand = 0
    for q, shifts, res in POOL.map(rnd_job, rnd_qs):
        d2_0 = closed_d2(q)
        a = a_vec(q, own_w(q))
        for (cat, tt), (d2, cert) in zip(shifts, res):
            nrand += 1
            nonc += cert not in (1, 2)
            # reduction to the isometry representative: digit-1 shift -> common digit-2/3 shifts -a.tau1, -l.tau1
            t1 = [tt[c][0] for c in range(3)]
            b2 = [(tt[c][1] - sum(a[k] * t1[k] for k in range(3))) % q for c in range(3)]
            b3 = [(tt[c][2] - sum(LJ[k] * t1[k] for k in range(3))) % q for c in range(3)]
            dz2 = (0, (b2[1] - b2[0]) % q, (b2[2] - b2[0]) % q)
            dz3 = (0, (b3[1] - b3[0]) % q, (b3[2] - b3[0]) % q)
            if q in tables:
                red_bad += tables[q][dz2[1:] + dz3[1:]][0] != d2
            ccat = category(dz2, dz3)
            assert ccat == (cat if cat != 'C2' else 'C')
            ok, info = bounds(q, d2, ccat, d2_0, dz2)
            st = stats.setdefault(('rnd', q, cat), [math.inf, 0, 0])
            st[0], st[1], st[2] = min(st[0], d2), max(st[1], d2), st[2] + 1
            if not ok:
                viol[ccat].append((q, tt, d2, info))
            if ccat == 'C':
                Cinfo.append((q, f'tau={tt}', d2, info))
    t_r = time.time() - t
    print(f'    random full shifts (9 digits), {nper} per category A, B, C and C2 (C with exactly two equal digit-2 '
          f'shifts) at q = {rnd_qs}: {nrand} shifts ({t_r:.1f} s)')
    check(nonc == 0, 'every value certified (neighbour kernel) or brute force')
    check(red_bad == 0, f'random full shifts == their isometry representative in the exhaustive tables '
                        f'(q in {[q for q in rnd_qs if q in tables]}): {red_bad} mismatches')
    print('    c per category: q: A min/max | B min/max | C min/max   [B lower, C lower, C upper a_min, C upper a_max]')
    for q in sorted({k[1] for k in stats}):
        d2_0 = closed_d2(q)
        W = 2 if q % 3 == 2 else 4
        amin = min(a_vec(q, own_w(q)))
        bl = 1 - (7 * q - 3) / (math.sqrt(3) * q * q)
        cl = (q * q - (W + 3) * q + 3) / (math.sqrt(3) * q * q)
        cu = math.sqrt(3) * (q * amin + q - 1) / q**2
        cU = math.sqrt(3) * (q * max(a_vec(q, own_w(q))) + q - 1) / q**2
        parts = []
        for cat in ('A', 'B', 'C'):
            ks = [k for k in stats if k[1] == q and (k[2] == cat or (cat == 'C' and k[2] == 'C2'))]
            if ks:
                mn, mx = min(stats[k][0] for k in ks), max(stats[k][1] for k in ks)
                parts.append(f'{c_of(mn, q):.4f}/{c_of(mx, q):.4f}')
        print(f'    q={q:<3d} (unshifted {c_of(d2_0, q):.4f}): ' + ' | '.join(parts) +
              f'   [{bl:.4f}, {cl:.4f}, {cu:.4f}, {cU:.4f}]')
    for cat in ('A', 'B'):
        check(not viol[cat], f'category {cat}: ' + ('d2 unchanged' if cat == 'A' else 'c >= 1 - (7q-3)/(sqrt3 q^2)') +
              f' on every shift; violations {len(viol[cat])}')
    nC = len(Cinfo)
    cnt = lambda key: sum(1 for x in Cinfo if not x[3][key])
    check(cnt('lower') == 0, f'category C: c >= (q^2-(W+3)q+3)/(sqrt3 q^2) on all {nC} C-shifts; violations {cnt("lower")}')
    check(cnt('lonely_any') == 0 and cnt('lonely_ok') == 0,
          f'category C: some direction i has a residue whose step e_i wraps the second digit of coordinate i only, and '
          f'd2 <= 3(q a_i + q - 1)^2 for every such i, on all {nC} C-shifts; failures {cnt("lonely_any")}, {cnt("lonely_ok")}')
    check(cnt('up_max') == 0, f'category C: c <= sqrt3 (q a_max + q - 1)/q^2 (a_max = max_i a_i) on all {nC} C-shifts; '
                              f'violations {cnt("up_max")}')
    pv = [x for x in Cinfo if x[3]['premise'] and not x[3]['up_min']]
    check(not pv, f'category C: c <= sqrt3 (q a_min + q - 1)/q^2 on every C-shift where a direction with a_i = a_min has '
                  f'a lonely residue ({sum(1 for x in Cinfo if x[3]["premise"])} shifts); violations {len(pv)}')
    um = [x for x in Cinfo if not x[3]['up_min']]
    if um:
        print(f'    !!! NOTE: the bound c <= sqrt3 (q a_min + q - 1)/q^2 FAILS on {len(um)} of {nC} C-shifts, at q = '
              f'{sorted({x[0] for x in um})}; all of them lack a lonely residue for the a_min direction(s).  Worst per q:')
        for q in sorted({x[0] for x in um}):
            amin = min(a_vec(q, own_w(q)))
            w = max((x for x in um if x[0] == q), key=lambda x: x[2])
            print(f'        q={q}: d2={w[2]} > 3(q a_min+q-1)^2 = {3 * (q * amin + q - 1) ** 2}  '
                  f'(c = {c_of(w[2], q):.4f} > {math.sqrt(3) * (q * amin + q - 1) / q**2:.4f})  {w[1]}')
    else:
        print('    the a_min upper bound held on every C-shift')


# ---------------------------------------------------------------- (e), (f)
def part_ef(stored):
    print('(e) T_p and (f) E_p, J_p exactly by cellmin')
    P = {'T': [p for p in range(7, 200) if is_prime(p) and p != 23],
         'E': [p for p in range(5, 200) if is_prime(p)],
         'J': [p for p in range(5, 200) if is_prime(p)]}
    jobs = [(k, p) for k in P for p in P[k]]
    t = time.time()
    vals = dict(zip(jobs, POOL.map(lambda kp: cellmin(kp[1], kp[0]), jobs)))
    print(f'    {len(jobs)} cellmin runs ({time.time() - t:.1f} s)')
    small = [(k, p) for k, p in jobs if p <= 13]
    bb = dict(zip(small, POOL.map(lambda kp: brute_graph(kp[1], kp[0]), small)))
    check(all(bb[x] == vals[x] for x in small), f'cellmin == O(N^2) brute force at {len(small)} small cases (p <= 13)')
    new = {k: {str(p): {'d2': vals[(k, p)], 'c': round(c_of(vals[(k, p)], p), 6)} for p in P[k]} for k in P}
    if stored is not None:
        diff = [(k, p) for k in P for p in P[k] if stored.get(k, {}).get(str(p), {}).get('d2') != vals[(k, p)]]
        check(not diff, f'every recomputed value == colnets_exact.json ({len(jobs)} values); differences {diff}')
    tc = json.load(open(os.path.join(HERE, 'twocoset_exact.json')))
    cons = [vals[('T', int(p))] == r['d2'] for p, r in tc['twocoset'].items() if int(p) <= 199] + \
           [vals[('E', int(p))] == r['d2'] for p, r in tc['E'].items() if int(p) <= 199]
    check(all(cons), f'agrees with twocoset_exact.json where both exist ({len(cons)} values)')
    # (e) comparison
    dstar = lambda p: (p * p - 2 * p + 3) ** 2 + (((p + 4) // 8 - 1) * p + 4) ** 2 + (((p + 4) // 8 - 1) * p + 6) ** 2
    eq = [p for p in P['T'] if vals[('T', p)] == dstar(p)]
    check(all(vals[('T', p)] <= dstar(p) for p in P['T']) and eq == [p for p in P['T'] if p not in (7, 13)],
          f'exact T_p <= the pair value d_*^2 of prop:twocoset(3) at every p, with equality at every p except '
          f'{[p for p in P["T"] if p not in eq]}')
    c_ahead = [p for p in P['T'] if closed_d2(p) > vals[('T', p)]]
    t_ahead = [p for p in P['T'] if closed_d2(p) < vals[('T', p)]]
    exp_c = [p for p in P['T'] if p <= 113 and p not in (103, 109)]
    check(c_ahead == exp_c and t_ahead == [p for p in P['T'] if p not in exp_c],
          f'C_p > T_p exactly at the primes 7..113 except {[p for p in P["T"] if p <= 113 and p not in c_ahead]} '
          f'(and 23); T_p > C_p exactly at {t_ahead}; ties: {[p for p in P["T"] if closed_d2(p) == vals[("T", p)]]}')
    for p in (101, 103, 107, 109, 113, 127, 199):
        print(f'      p={p}: c(C_p) = {c_of(closed_d2(p), p):.6f}, c(T_p) = {c_of(vals[("T", p)], p):.6f}')
    # (f) J formula + checkpoints, E checkpoints
    def jform(q):
        g = 1 if q % 3 == 1 else 2
        num = 3 * q**4 - 4 * q**3 + 4 * q + 3 if g == 1 else 3 * q**4 - 8 * q**3 + 12 * q * q + 8 * q + 3
        assert num % 3 == 0
        return num // 3
    jbad = [p for p in P['J'] if (p >= 7 if p % 3 == 1 else p >= 11) and vals[('J', p)] != jform(p)]
    check(not jbad, f'J_p == Theorem L formula at all primes 7..199 (g=1: q>=7, g=2: q>=11); failures {jbad}')
    check((vals[('J', 5)], vals[('J', 7)], vals[('J', 11)]) == (406, 1954, 11606), 'J_5, J_7, J_11 = 406, 1954, 11606')
    e199 = 199 * (1 - c_of(vals[('E', 199)], 199))
    e197 = 197 * (1 - c_of(vals[('E', 197)], 197))
    check(f'{e199:.4f}' == '1.3269' and f'{e197:.4f}' == '1.9856',
          f'E_p: p(1-c) = {e199:.4f} at p = 199, {e197:.4f} at p = 197 (audit: 1.3269, 1.9856)')
    return new


# ---------------------------------------------------------------- (g)
def part_g():
    Q = 151
    qs = [q for q in range(5, Q + 1) if coprime6(q)]
    print(f'(g) digital class maximum via Theorem C at all {len(qs)} q coprime to 6 up to {Q}')
    t = time.time()
    outs = POOL.map(lambda q: run([COLMIND, 'classmax', str(q), str(q)]), qs[::-1])
    res = {}
    for o in outs:
        q, d2, n = map(int, o.split())
        res[q] = (d2, n)
    bad = [q for q in qs if res[q] != (closed_d2(q), 6 if q % 3 == 2 else 3 * phi_euler(q))]
    check(not bad, f'max == d2(C_q), #maximizers == 6 (q=2 mod 3) / 3 phi(q) (q=1 mod 3) at all {len(qs)} q '
                   f'({time.time() - t:.1f} s); failures {bad}')


def main():
    for b in (CELLMIN, COLMIND):
        if not os.path.exists(b):
            sys.exit(f'build first: g++ -O3 -std=c++17 -o {b} {os.path.join(HERE, os.path.basename(b) + ".cpp")}')
    stored = None if WRITE else json.load(open(EXACT))
    T0 = time.time()
    for f in (part_a, part_b, part_c, part_d):
        t = time.time(); f(); print(f'    ({time.time() - t:.1f} s)')
    t = time.time(); new = part_ef(stored); print(f'    ({time.time() - t:.1f} s)')
    t = time.time(); part_g(); print(f'    ({time.time() - t:.1f} s)')
    if WRITE:
        new = {'note': ('Exact toroidal minimum distances d2 (integer scale p^3; c = sqrt(d2)/p^2) computed '
                        f'{time.strftime("%Y-%m-%d")} by colnets.py --write with the cell-scan oracle cellmin.cpp '
                        '(g++ -O3), cross-checked against an O(N^2) brute force for p <= 13. '
                        'T = two-coset net of prop:twocoset (rows C_x: e_x,(0,h,h),(0,1,2); C_y: e_y,(r,-1,1),(3,0,1); '
                        'C_z: e_z,(r,-1,1),(1,5,0); h=(p-1)/2, r=round(p/8)), every prime 7..199 except 23 '
                        '(T_23 is not a net). E = net of thm:E1 (digits n_c, a sigma(n), n_{c+1}, a = floor(p/3)); '
                        'J = lean net J_q of EIS_GENERALIZE Theorem L (digits n_c, a sigma(n), '
                        't(-n_c-n_{c+1}+n_{c+2}), t=(p+1)/2); E, J at every prime 5..199.'), **new}
        with open(EXACT, 'w') as fh:
            json.dump(new, fh, indent=1)
        print(f'wrote {EXACT}')
    print(f'total {time.time() - T0:.1f} s')
    if FAILS:
        print(f'colnets: {len(FAILS)} FAILURE(S):')
        for f in FAILS:
            print('  -', f)
        sys.exit(1)
    print('colnets: ALL OK')


if __name__ == '__main__':
    main()
