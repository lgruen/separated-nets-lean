#!/usr/bin/env python3
"""Data of entry S5R2 (prop:s5r2, tab:s5r2), read from
`witnesses/codes/e2_s5r2_frameorbit_designs.txt.` (research repository)

Coordinates (Lean order): x1 = 0, x2 = 1 (full, depth k + 1), z1 = 2, z2 = 3, z3 = 4 (skeleton,
depth k).  For every design this script recomputes, in exact integer arithmetic, and asserts:

* the table values of tab:s5r2: lambda_inf(Lambda_kappa), floor(p^(3/5)), M_p, J_p^2 and the printed
  truncations of (M_p - 1) p^(-3/5) and J_p p^(-3/5) (thousandths);
* M_p and J_p^2 as the minima of the relaxation of the proof (the pruned enumeration that the Lean
  check `chk` performs, see Z3Net/S5Cert.lean; for p <= 53 also the unpruned enumeration over all
  |a_x| < p/2), with attaining solutions; an attaining lattice vector;
* the reachability witness.  The paper's places are all finite; the frame of `sec:frames` (and the
  Lean definition `frameRead`) has one place at infinity.  The Moebius map u = 1/(t - b_1) sends the
  place b_1 of x1 to infinity and every other place a to 1/(a - b_1); the frame orbit is unchanged by
  it (the readings change by lower-triangular scrambles and the index by an invertible map).  The
  witness solves the residual problem of prop:skelcomp(i) on the rows S = {z1, z2, z3} for the
  Moebius-image places: row scalars lam (shared by all columns) and per column an upper-triangular
  gauge U_d with unit diagonal:
      F_n[c][d] = lam_c sum_{n' <= n} w_cd y_cd^n' U_d[n', n],
  w = 1, y = a_c on the column at infinity, w = y = 1/(a_c - a_d) on a finite column; F_0, F_1, F_2 =
  kappa, beta, eta on a full column, F_0, F_1 = g, H on a skeleton column.
Imported by gen_s5r2.py."""
import itertools, math, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WIT = os.path.join(ROOT, '..', 'witnesses', 'codes', 'e2_s5r2_frameorbit_designs.txt')

# tab:s5r2 as printed: p -> (lambda_inf, floor p^(3/5), M_p, (M_p-1)p^(-3/5) [thousandths], J_p^2,
# J_p p^(-3/5) [thousandths])
PAPER = {31: (6, 7, 4, 382, 18, 540), 37: (7, 8, 5, 458, 30, 627), 53: (9, 10, 6, 461, 54, 678),
         71: (10, 12, 7, 464, 97, 763), 101: (13, 15, 8, 439, 149, 765),
         151: (16, 20, 14, 640, 283, 828), 199: (19, 23, 16, 626, 456, 891)}
PRIMES = [31, 37, 53, 71, 101, 151, 199]
PATS = [(0, 0), (1, 0), (1, 1), (-1, 0), (-1, -1)]


def cen(v, p):
    r = v % p
    return r if 2 * r < p else r - p


def sgn(a):
    return (a > 0) - (a < 0)


def inv(x, p):
    x %= p
    assert x != 0
    return pow(x, p - 2, p)


def pats_of(a):
    s = sgn(a)
    return [(0, 0), (s, 0), (s, s)]


def pat_ok(a, x):
    s = sgn(a)
    return x[0] in (0, s) and x[1] in (0, s) and (x[1] == 0 or x[0] != 0)


def jit(a):
    return sum(max(abs(t) - 1, 0) ** 2 for t in a)


def parse():
    out = {}
    for line in open(WIT):
        if not line.startswith('mode2'):
            continue
        head, *parts = line.split('|')
        p = int(head.split()[1].split('=')[1])
        f, key = {}, None
        for w in ' '.join(parts).split():
            if w.lstrip('-').isdigit():
                f[key].append(int(w))
            else:
                key = w
                f[key] = []
        D = dict(p=p, places=f['places'])
        D['kappa'] = [[f['kappa'][2 * i + d] for d in range(2)] for i in range(3)]
        D['beta'] = [[f['beta'][2 * i + d] for d in range(2)] for i in range(3)]
        D['eta'] = [[f['eta'][2 * i + d] for d in range(2)] for i in range(3)]
        G = [[f['G'][3 * i + j] for j in range(3)] for i in range(3)]
        H = [[f['H'][3 * i + j] for j in range(3)] for i in range(3)]
        D['g'] = [[G[i][j] if i != j else 0 for j in range(3)] for i in range(3)]
        D['o'] = [G[i][i] for i in range(3)]
        assert all(H[i][i] == 0 for i in range(3))
        D['H'] = H
        D['lam_paper'], D['mu_paper'] = f['lam'], f['mu']
        lat, pig, M, tabM, J2, tabJ = PAPER[p]
        D.update(lat=lat, pig=pig, M=M, tabM=tabM, J2=J2, tabJ=tabJ)
        out[p] = D
    assert sorted(out) == PRIMES
    return [out[p] for p in PRIMES]


def base(D, a1, a2, xp1, xp2, i):
    k, b, e = D['kappa'][i], D['beta'][i], D['eta'][i]
    return k[0] * a1 + k[1] * a2 + b[0] * xp1[0] + b[1] * xp2[0] + e[0] * xp1[1] + e[1] * xp2[1]


def zoff(D, zp, i):
    v = 0
    for j in range(3):
        if j == i:
            v += D['o'][i] * zp[j][0]
        else:
            v += D['g'][i][j] * zp[j][0] + D['H'][i][j] * zp[j][1]
    return v


def bz(D, i):
    return abs(D['o'][i]) + sum(abs(D['g'][i][j]) + abs(D['H'][i][j]) for j in range(3) if j != i)


def thresh(D):
    """least T with M <= T and J2 <= (T - 1)^2"""
    T = D['M']
    while (T - 1) ** 2 < D['J2']:
        T += 1
    return T


def box(D):
    """least A >= M - 1 with A^2 >= J2 (then |a_1| > A or |a_2| > A gives |a_x|_inf >= M and
    jit_x >= J2)."""
    A = max(D['M'] - 1, 0)
    while A * A < D['J2']:
        A += 1
    return A


def chk(D, full=False):
    """The Lean check `chk` (pruned) with the minima it sees, or (full=True) the unpruned
    enumeration over all |a_x| < p/2.  Returns (ok, minM, minJ, argM, argJ, cases)."""
    p, M, J2 = D['p'], D['M'], D['J2']
    T, A = thresh(D), box(D)
    h = (p - 1) // 2
    rng1 = range(0, h + 1) if full else range(0, A + 1)
    rng2 = range(-h, h + 1) if full else range(-A, A + 1)
    ok, minM, minJ, argM, argJ, cases = True, None, None, None, None, 0
    for a1 in rng1:
        for a2 in rng2:
            jx = jit([a1, a2])
            if not full and jx >= J2 and max(abs(a1), abs(a2)) >= M:
                continue
            for xp1 in pats_of(a1):
                for xp2 in pats_of(a2):
                    b = [base(D, a1, a2, xp1, xp2, i) for i in range(3)]
                    if not full and any(abs(cen(b[i], p)) >= T + bz(D, i) for i in range(3)):
                        continue
                    for zp in itertools.product(PATS, repeat=3):
                        cases += 1
                        az = [cen(b[i] + zoff(D, zp, i), p) for i in range(3)]
                        if not all(pat_ok(az[i], zp[i]) for i in range(3)):
                            continue
                        a = [a1, a2] + az
                        if not any(a):
                            continue
                        m, j = max(abs(t) for t in a), jit(a)
                        if not (M <= m and J2 <= j):
                            ok = False
                        sol = (a, [xp1[0], xp2[0]] + [z[0] for z in zp], [xp1[1], xp2[1]] + [z[1] for z in zp])
                        if minM is None or m < minM:
                            minM, argM = m, sol
                        if minJ is None or j < minJ:
                            minJ, argJ = j, sol
    return ok, minM, minJ, argM, argJ, cases


def lattice(D):
    p, kap = D['p'], D['kappa']
    best, arg = None, None
    h = (p - 1) // 2
    for x1 in range(0, h + 1):
        for x2 in range(-h, h + 1):
            if x1 == 0 and x2 <= 0:
                continue
            u = [x1, x2] + [cen(kap[i][0] * x1 + kap[i][1] * x2, p) for i in range(3)]
            m = max(abs(t) for t in u)
            if best is None or m < best:
                best, arg = m, u
    return best, arg


def latchk_cases(D):
    L = D['lat']
    return sum(1 for x1 in range(0, L) for x2 in range(-(L - 1), L))


def solve_mod(rows, rhs, p):
    """Solve rows * u = rhs mod p (overdetermined allowed); return u, assert consistent+unique."""
    n = len(rows[0])
    A = [[r % p for r in row] + [v % p] for row, v in zip(rows, rhs)]
    piv = []
    rk = 0
    for c in range(n):
        pr = next((r for r in range(rk, len(A)) if A[r][c]), None)
        assert pr is not None, 'singular'
        A[rk], A[pr] = A[pr], A[rk]
        iv = inv(A[rk][c], p)
        A[rk] = [x * iv % p for x in A[rk]]
        for r in range(len(A)):
            if r != rk and A[r][c]:
                f = A[r][c]
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[rk])]
        piv.append(c)
        rk += 1
    for r in range(rk, len(A)):
        assert A[r][n] == 0, 'inconsistent'
    return [A[i][n] for i in range(n)]


def mobius(D):
    p = D['p']
    b1 = D['places'][0]
    return [None] + [inv(a - b1, p) for a in D['places'][1:]]


def witness(D):
    """lam (rows z1..z3), U[d] (upper triangular, l_d x l_d) for the Moebius-image places with the
    column x1 at infinity; asserted against the residual equations (in the multiplied form used by
    the Lean check `wchk`)."""
    p = D['p']
    pl = mobius(D)
    rows = [2, 3, 4]

    def F(n, i, d):  # i in 0..2 (z_{i+1}), d in 0..4
        if d < 2:
            return [D['kappa'], D['beta'], D['eta']][n][i][d]
        j = d - 2
        return [D['g'], D['H']][n][i][j]

    def wy(c, d):
        if d == 0:
            return 1, pl[c]
        t = inv(pl[c] - pl[d], p)
        return t, t

    lam = [D['kappa'][i][0] % p for i in range(3)]   # U_0[0][0] = 1
    U = []
    for d in range(5):
        rs = [c for c in rows if c != d]
        l = len(rs)
        Ud = [[0] * l for _ in range(l)]
        for n in range(l):
            eqs, rhs = [], []
            for c in rs:
                w, y = wy(c, d)
                eqs.append([lam[c - 2] * w * pow(y, m, p) % p for m in range(n + 1)])
                rhs.append(F(n, c - 2, d))
            col = solve_mod(eqs, rhs, p)
            for m in range(n + 1):
                Ud[m][n] = col[m]
        assert all(Ud[n][n] % p for n in range(l)), 'non-unit diagonal'
        U.append(Ud)
    assert all(x % p for x in lam)
    # re-check in the multiplied (inverse-free) form of wchk: column 0 (infinity):
    #   F_n[i][0] = lam_i sum_{m<=n} A_i^m U0[m][n]
    # finite column d (place P_d), t = A_c - P_d:
    #   F_n[i][d] t^(n+1) = lam_i sum_{m<=n} t^(n-m) Ud[m][n]
    P = [0] + [pl[c] for c in range(1, 5)]
    for i in range(3):
        c = i + 2
        for n in range(3):
            s = lam[i] * sum(pow(P[c], m, p) * U[0][m][n] for m in range(n + 1))
            assert (F(n, i, 0) - s) % p == 0
        for d in range(1, 5):
            if d == c:
                continue
            rs = [cc for cc in rows if cc != d]
            l = len(rs)
            t = (P[c] - P[d]) % p
            for n in range(l):
                s = lam[i] * sum(pow(t, n - m, p) * U[d][m][n] for m in range(n + 1))
                assert (F(n, i, d) * pow(t, n + 1, p) - s) % p == 0
    return dict(pl=P, lam=lam, U=U)


def check_N12(D):
    """(N1) every entry and 2x2 minor of kappa nonzero mod p; (N2) g_ij != 0 (here +-1)."""
    p, K = D['p'], D['kappa']
    assert all(K[i][d] % p for i in range(3) for d in range(2))
    for i, j in itertools.combinations(range(3), 2):
        assert (K[i][0] * K[j][1] - K[i][1] * K[j][0]) % p
    assert all(abs(D['g'][i][j]) == 1 for i in range(3) for j in range(3) if i != j)
    assert len(set(x % p for x in D['places'])) == 5


def designs(full_upto=0):
    out = []
    for D in parse():
        p = D['p']
        check_N12(D)
        T, A = thresh(D), box(D)
        assert 2 * T <= p - 1 and 4 * D['J2'] <= (p - 1) ** 2 and 2 * D['M'] <= p + 1
        ok, mM, mJ, argM, argJ, cases = chk(D)
        assert ok and mM == D['M'] and mJ == D['J2'], (p, ok, mM, mJ)
        if p <= full_upto:
            okf, fM, fJ, _, _, _ = chk(D, full=True)
            assert okf and fM == D['M'] and fJ == D['J2'], (p, fM, fJ)
        lat, larg = lattice(D)
        assert lat == D['lat'], (p, lat)
        pg = D['pig']
        assert pg ** 5 <= p ** 3 < (pg + 1) ** 5 and lat <= pg
        tM, tJ = D['tabM'], D['tabJ']
        assert tM ** 5 * p ** 3 <= (D['M'] - 1) ** 5 * 10 ** 15 < (tM + 1) ** 5 * p ** 3
        assert tJ ** 10 * p ** 6 <= D['J2'] ** 5 * 10 ** 30 < (tJ + 1) ** 10 * p ** 6
        D['T'], D['A'] = T, A
        D['wit'] = witness(D)
        D['argM'], D['argJ'], D['latarg'], D['cases'] = argM, argJ, larg, cases
        out.append(D)
    return out


if __name__ == '__main__':
    import sys, time
    full = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    t0 = time.time()
    for D in designs(full):
        print(D['p'], 'M', D['M'], 'J2', D['J2'], 'lat', D['lat'], 'T', D['T'], 'A', D['A'],
              'zcases', D['cases'], 'latcases', latchk_cases(D), 'places', D['wit']['pl'],
              'lam', D['wit']['lam'])
    print('elapsed %.1fs' % (time.time() - t0))
