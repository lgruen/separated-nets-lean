#!/usr/bin/env python3
"""Data of entry T3S4 (prop:t3s4, tab:t3s4), read from `witnesses/skel/t3_s4.json.` (research repository)

For every design: the paper's table values (M_p, lambda_inf(kappa), printed (M_p - 1) p^(-3/4)), the
frame-orbit witness of the reachability conditions (row scalars lam, column gauges ux, uz; places
x = inf, z = (0, 1, a3)), an attaining relaxation solution (a, xi1, xi2) with |a|_inf = M_p, and an
attaining Korobov lattice vector.  Everything is recomputed here (exact integer arithmetic) and
asserted; the Lean side re-checks every fact by kernel reduction.  Imported by gen_t3s4.py."""
import itertools, json, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WIT = os.path.join(ROOT, '..', 'witnesses', 'skel', 't3_s4.json')
ORDER = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]  # row-major, as in the tab:t3s4 caption
# printed (M_p - 1) p^(-3/4) of tab:t3s4, in thousandths (truncated); p = 5: 0 (caption)
PRINTED = {5: 0, 7: 232, 11: 331, 13: 438, 17: 477, 19: 549, 23: 476, 29: 560, 31: 532, 37: 666,
           41: 678, 43: 714, 47: 668, 53: 712, 59: 751, 61: 733, 67: 683, 71: 695, 73: 680, 79: 754,
           83: 763}
PAPER_ML = {7: (2, 3), 11: (3, 4), 13: (4, 5), 17: (5, 6), 19: (6, 7), 23: (6, 8), 29: (8, 10),
            31: (8, 10), 37: (11, 12), 41: (12, 12), 43: (13, 13), 47: (13, 14), 53: (15, 15),
            59: (17, 17), 61: (17, 17), 67: (17, 19), 71: (18, 20), 73: (18, 19), 79: (21, 21),
            83: (22, 23)}


def cen(v, p):
    r = v % p
    return r if 2 * r < p else r - p


def sgn(a):
    return (a > 0) - (a < 0)


def inv(x, p):
    x %= p
    assert x != 0
    return pow(x, p - 2, p)


def design(p, e):
    G = [[0] * 3 for _ in range(3)]
    for (i, j), v in zip(ORDER, e['g']):
        G[i][j] = v
    return dict(p=p, a3=e['tau'], kappa=e['kappa'], beta=e['beta'], eta=e['eta'], g=G, H=e['H'],
                o=e['own'], M=e['cert_M'], lat=e['lat'], tab=PRINTED[p])


def rhs(D, ax, xp, zp, i):
    v = D['kappa'][i] * ax + D['beta'][i] * xp[0] + D['eta'][i] * xp[1]
    for j in range(3):
        if j == i:
            v += D['o'][i] * zp[j][0]
        else:
            v += D['g'][i][j] * zp[j][0] + D['H'][i][j] * zp[j][1]
    return v


PATS = [(0, 0), (1, 0), (1, 1), (-1, 0), (-1, -1)]


def pat_ok(a, x):
    s = sgn(a)
    return x[0] in (0, s) and x[1] in (0, s) and (x[1] == 0 or x[0] != 0)


def relax(D):
    """min |a|_inf over nonzero relaxation solutions, and an attaining (a, xi1, xi2)."""
    p = D['p']
    best, arg = None, None
    for ax in range(-(p // 2), p // 2 + 1):
        for xp in PATS:
            if not pat_ok(ax, xp):
                continue
            for zp in itertools.product(PATS, repeat=3):
                az = [cen(rhs(D, ax, xp, zp, i), p) for i in range(3)]
                if not all(pat_ok(az[i], zp[i]) for i in range(3)):
                    continue
                if ax == 0 and not any(az):
                    continue
                m = max([abs(ax)] + [abs(a) for a in az])
                if best is None or m < best:
                    best = m
                    arg = ([ax] + az, [xp[0]] + [z[0] for z in zp], [xp[1]] + [z[1] for z in zp])
    return best, arg


def lattice(D):
    p, kap = D['p'], D['kappa']
    best, arg = None, None
    for x in range(1, p // 2 + 1):
        u = [x] + [cen(k * x, p) for k in kap]
        m = max(abs(t) for t in u)
        if best is None or m < best:
            best, arg = m, u
    return best, arg


def witness(D):
    """lam, ux (3x3 upper triangular), uz (per skeleton column j, 2x2 upper triangular), all mod p,
    with: Fx_n,i = lam_i sum_{n'<=n} a_i^n' ux[n'][n]  (Fx_0 = kappa, Fx_1 = beta, Fx_2 = eta), and
    for i != j: Fz_n,i,j (a_i - a_j)^(n+1) = lam_i sum_{n'<=n} (a_i - a_j)^(n-n') uz[j][n'][n]
    (Fz_0 = g, Fz_1 = H)."""
    p = D['p']
    a = [0, 1, D['a3']]
    lam = [k % p for k in D['kappa']]          # mu_x = ux[0][0] = 1
    q = [D['beta'][i] * inv(lam[i], p) % p for i in range(3)]
    u01 = q[0]
    u11 = (q[1] - q[0]) % p
    assert (q[2] - (u01 + a[2] * u11)) % p == 0, 'beta not in span(kappa, kappa*a)'
    r = [D['eta'][i] * inv(lam[i], p) % p for i in range(3)]
    # u02 + a_i u12 + a_i^2 u22 = r_i, a = (0, 1, a3)
    u02 = r[0]
    # u12 + u22 = r1 - u02 ; a3 u12 + a3^2 u22 = r2 - u02
    b1 = (r[1] - u02) % p
    b2 = (r[2] - u02) % p
    t = a[2]
    # u22 (t^2 - t) = b2 - t b1
    u22 = (b2 - t * b1) * inv(t * t - t, p) % p
    u12 = (b1 - u22) % p
    ux = [[1, u01, u02], [0, u11, u12], [0, 0, u22]]
    uz = []
    for j in range(3):
        oth = [i for i in range(3) if i != j]
        mus = [D['g'][i][j] * (a[i] - a[j]) * inv(lam[i], p) % p for i in oth]
        assert mus[0] == mus[1], 'g not of Cauchy form'
        mu = mus[0]
        # H_ij d_i^2 = lam_i (u01 d_i + u11), d_i = a_i - a_j
        (i1, i2) = oth
        d1, d2 = a[i1] - a[j], a[i2] - a[j]
        c1 = D['H'][i1][j] * d1 * d1 * inv(lam[i1], p) % p
        c2 = D['H'][i2][j] * d2 * d2 * inv(lam[i2], p) % p
        # u01 d1 + u11 = c1 ; u01 d2 + u11 = c2
        v01 = (c1 - c2) * inv(d1 - d2, p) % p
        v11 = (c1 - v01 * d1) % p
        uz.append([[mu, v01], [0, v11]])
    # checks
    assert all(x % p for x in lam) and u11 % p and u22 % p and all(u[0][0] % p and u[1][1] % p for u in uz)
    F = [D['kappa'], D['beta'], D['eta']]
    for i in range(3):
        for n in range(3):
            s = lam[i] * sum(a[i] ** m * ux[m][n] for m in range(n + 1))
            assert (F[n][i] - s) % p == 0
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            d = a[i] - a[j]
            for n, Fz in enumerate((D['g'][i][j], D['H'][i][j])):
                s = lam[i] * sum(d ** (n - m) * uz[j][m][n] for m in range(n + 1))
                assert (Fz * d ** (n + 1) - s) % p == 0
    return dict(lam=lam, ux=ux, uz=uz)


def designs():
    W = json.load(open(WIT))
    out = []
    for ps in sorted(W, key=int):
        p = int(ps)
        D = design(p, W[ps])
        assert D['a3'] % p not in (0, 1)
        M, arg = relax(D)
        lat, larg = lattice(D)
        assert M == D['M'] and lat == D['lat'], (p, M, lat)
        if p in PAPER_ML:
            assert (M, lat) == PAPER_ML[p]
        assert 2 * M <= p + 1 and 2 * lat <= p + 1
        # printed truncation: tab/1000 <= (M-1) p^(-3/4) < (tab+1)/1000  <=>  integer 4th powers
        t = D['tab']
        assert t ** 4 * p ** 3 <= (M - 1) ** 4 * 10 ** 12 < (t + 1) ** 4 * p ** 3, p
        assert all(abs(D['g'][i][j]) == 1 for i in range(3) for j in range(3) if i != j)
        D['wit'] = witness(D)
        D['relarg'] = arg
        D['latarg'] = larg
        out.append(D)
    return out


if __name__ == '__main__':
    for D in designs():
        print(D['p'], D['a3'], D['M'], D['lat'], D['tab'], D['wit'], D['relarg'], D['latarg'])
