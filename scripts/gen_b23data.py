#!/usr/bin/env python3
"""V14 stage S14′: generate the data modules of `thm:base23` (bases two and three).

* `Z3Net/B23Nets.lean` (statement side): the seeds of `tab:b23seeds` (printed row integers), the lift parameters
  `s_A`, `s_B` of the R1 chains (codes per coordinate), the small-m witnesses (column codes).
* `Z3Net/B23Data.lean` (proof side): the certificate data — the functionals `λ^{cc'}_e` of every lift (admissibility),
  the matrices `G_x`, `G_y` at the certificate levels, the matrices `M^x_c, M^y_c, M^z_c` and the targets `U` at the
  levels between the seed and `L`, and the targets of the small witnesses.

Inputs: the replayed R1 chains (`NET` files written by `paper/certificates/base23_everyshift/run_everyshift.sh build`, i.e. by
`ba_dump` from `paper/certificates/witnesses/r1/*`), the small witnesses `paper/certificates/base23_audit/witness_smallm/*.net` and
`paper/certificates/base23_everyshift/witness_smallm_es/*.net`. All numbers are recomputed here from the definitions (exact
`μ` by brute-force-verified recursion); the Lean kernel re-checks every certificate.

Usage (from the repository root): uv run --no-project python scripts/gen_b23data.py NETDIR"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
GEO = os.path.join(HERE, '..', '..')
FAMS = {(2, 0): ('b2_mod0', 9, 30), (2, 1): ('b2_mod1', 10, 28), (2, 2): ('b2_mod2', 11, 20),
        (3, 0): ('b3_mod0', 6, 18), (3, 1): ('b3_mod1', 7, 22), (3, 2): ('b3_mod2', 8, 20)}
# tab:b23seeds (core.tex): rows of A_y, rows of A_z, (tau_y, tau_z)
SEEDS = {(2, 0): ([135, 45, 3, 498, 194, 440, 335, 219, 392], [481, 146, 111, 183, 386, 325, 223, 361, 358], (414, 211)),
         (2, 1): ([209, 382, 805, 151, 314, 829, 673, 883, 1010, 361], [947, 597, 575, 978, 901, 1020, 856, 754, 73, 687], (570, 524)),
         (2, 2): ([983, 1182, 492, 1089, 1674, 1177, 538, 1803, 1473, 939, 333], [701, 54, 431, 771, 1929, 1550, 1860, 1141, 1802, 734, 1278], (62, 919)),
         (3, 0): ([404, 542, 48, 70, 11, 52], [316, 557, 650, 282, 551, 247], (626, 448)),
         (3, 1): ([1495, 822, 993, 989, 391, 477, 1366], [1192, 1811, 657, 430, 705, 1663, 87], (614, 1328)),
         (3, 2): ([2902, 3540, 5732, 4163, 4228, 2472, 696, 593], [5695, 1981, 2605, 6323, 2624, 3996, 209, 3923], (703, 1559))}
VCERT = {(2, 0): 168, (2, 1): 110, (2, 2): 3, (3, 0): 8, (3, 1): 86, (3, 2): 9}


def readnet(fn):
    t = open(fn).read().split()
    b, M = int(t[1]), int(t[2])
    a = list(map(int, t[3:]))
    return b, M, [a[i * 3 * M:(i + 1) * 3 * M] for i in range(M)], a[3 * M * M:3 * M * M + 3 * M]


def code(dg, b):
    v = 0
    for d in dg:
        v = v * b + d
    return v


def digs(x, b, n):
    return [(x // b ** (n - 1 - j)) % b for j in range(n)]


def mu(x, b, n):  # exact mu_n of the code x (the recursion of `Fm`, verified against brute force)
    if x == 0:
        return 0
    ds = [(x // b ** k) % b for k in range(n)]  # weight index

    def F(k, T):
        if k == 0:
            return abs(T)
        if ds[k - 1] == 0:
            return F(k - 1, T)
        R = sum(b ** (j + 1) for j in range(k - 1) if ds[j])

        def g(Tp):
            if Tp < 0:
                return -Tp
            if Tp > R:
                return Tp - R
            return F(k - 1, Tp)
        return min(g(T), g(T - b ** k))
    N = b ** n
    return min(F(n, x), F(n, x - N), F(n, x + N))


def hW(t):
    return max(0, t - 1) ** 2


# ---------------------------------------------------------------- the chains (column codes, as in Lean)
def seed_cols(b, M, ry, rz):
    cx = [b ** (M - 1 - i) for i in range(M)]
    cy = [code([digs(ry[d], b, M)[i] for d in range(M)], b) for i in range(M)]
    cz = [code([digs(rz[d], b, M)[i] for d in range(M)], b) for i in range(M)]
    return [cx, cy, cz]


def lift_cols(b, M, cols, sA, sB):
    T, q = b ** (M + 2), b * b
    return [[c * q for c in cols[0]] + [T, sA[0] * q + 1, sB[0] * q + b],
            [c * q for c in cols[1]] + [T, T + sA[1] * q + b + 1, sB[1] * q + b],
            [c * q for c in cols[2]] + [T, T + sA[2] * q + b, T + sB[2] * q + 1]]


def lift_params(netdir, fam, M0, L):
    out = []
    M = M0
    while M < L:
        b, M2, g2, _ = readnet(os.path.join(netdir, f'{fam}_m{M + 3}.net'))
        blk = lambda v: [code(v[c * M2 + 1:c * M2 + 1 + M], b) for c in range(3)]
        out.append((blk(g2[M + 1]), blk(g2[M + 2])))
        M += 3
    return out


def dadd(b, x, y, n):
    return code([(p + q) % b for p, q in zip(digs(x, b, n), digs(y, b, n))], b)


def colvec(cols, c, i, b, n):
    return digs(cols[c][i], b, n)


def mat_rows(cols, c, b, n, nrows=None):  # matrix C_c as rows (digit position) x columns
    m = len(cols[c])
    return [[digs(cols[c][i], b, n)[r] for i in range(m)] for r in range(nrows if nrows else n)]


def matinv(A, b):
    n = len(A)
    Mx = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(A)]
    r = 0
    for c in range(n):
        p = next(i for i in range(r, n) if Mx[i][c] % b)
        Mx[r], Mx[p] = Mx[p], Mx[r]
        iv = pow(Mx[r][c], b - 2, b)
        Mx[r] = [(x * iv) % b for x in Mx[r]]
        for i in range(n):
            if i != r and Mx[i][c]:
                f = Mx[i][c]
                Mx[i] = [(x - f * y) % b for x, y in zip(Mx[i], Mx[r])]
        r += 1
    return [row[n:] for row in Mx]


def matmul(A, B, b):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) % b for j in range(len(B[0]))] for i in range(len(A))]


def nullvec(A, b, ncols):  # one nonzero vector x with A x = 0 (A: rows x ncols), kernel of dim 1 expected
    rows = [r[:] for r in A]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if rows[i][c] % b), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        iv = pow(rows[r][c], b - 2, b)
        rows[r] = [(x * iv) % b for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % b for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    assert len(free) == 1, (len(free),)
    x = [0] * ncols
    x[free[0]] = 1
    for i, c in enumerate(piv):
        x[c] = (-rows[i][free[0]]) % b
    return x


def lam_cert(b, M, cols, c, cp, e, s1, s2):
    # unknowns: lambda1 on digits 0..e-1 of c, lambda2 on digits 0..M-e of c'
    n1, n2 = e, M + 1 - e
    A = []
    for i in range(M):
        u, up = digs(cols[c][i], b, M), digs(cols[cp][i], b, M)
        A.append(u[:n1] + up[:n2])
    x = nullvec(A, b, n1 + n2)
    l1 = code(x[:n1] + [0] * (M - n1), b)
    l2 = code(x[n1:] + [0] * (M - n2), b)
    d = (sum(p * q for p, q in zip(digs(l1, b, M), digs(s1, b, M))) + sum(p * q for p, q in zip(digs(l2, b, M), digs(s2, b, M)))) % b
    assert d != 0, 'not admissible'
    return l1, l2


def dsub(b, x, y, n):
    return code([(p - q) % b for p, q in zip(digs(x, b, n), digs(y, b, n))], b)


def window_U(b, m, cols):
    """exact every-shift d2 at level m by the window method of `chk2` (data Mx, My, Mz and the minimum U)."""
    Hp = (m + 2) // 3
    zl = m - 2 * Hp
    C = [mat_rows(cols, c, b, m) for c in range(3)]
    Box = C[0][:Hp] + C[1][:Hp] + C[2][:zl]
    Bi = matinv(Box, b)
    Mf = [matmul(C[c], Bi, b) for c in range(3)]  # m x m, columns = box digits
    colsM = [[code([Mf[c][r][k] for r in range(m)], b) for k in range(m)] for c in range(3)]
    Mx = [cm[:Hp] for cm in colsM]
    My = [cm[Hp:2 * Hp] for cm in colsM]
    Mz = [cm[2 * Hp:] for cm in colsM]
    St = [x for x in range(b ** Hp) if mu(x, b, Hp) <= 1]
    Z = [s // b ** (3 * Hp - m) for s in St]
    best = None
    for tx in St:
        for ty in St:
            for z in Z:
                if tx == 0 and ty == 0 and z == 0:
                    continue
                beta = digs(tx, b, Hp) + digs(ty, b, Hp) + digs(z, b, zl)
                D = [code([sum(Mf[c][r][k] * beta[k] for k in range(m)) % b for r in range(m)], b) for c in range(3)]
                if any(mu(D[c] // b ** (m - Hp), b, Hp) > 1 for c in range(3)):
                    continue
                w = sum(mu(D[c], b, m) ** 2 for c in range(3))
                best = w if best is None else min(best, w)
    assert best <= (b ** (m - Hp)) ** 2
    return Hp, best, Mx, My, Mz


def brute_U(b, m, cols):
    best = None
    for n in range(1, b ** m):
        nd = digs(n, b, m)
        w = 0
        for c in range(3):
            D = code([sum(digs(cols[c][i], b, m)[r] * nd[i] for i in range(m)) % b for r in range(m)], b)
            w += mu(D, b, m) ** 2
        best = w if best is None else min(best, w)
    return best


def net_cols(fn):
    b, M, g, sh = readnet(fn)
    return b, M, [[code(g[i][c * M:(c + 1) * M], b) for i in range(M)] for c in range(3)], [code(sh[c * M:(c + 1) * M], b) for c in range(3)]


def L(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def LL(xss):
    return '[' + ', '.join(L(x) for x in xss) + ']'


def main():
    netdir = sys.argv[1]
    nets, data, report = [], [], []
    for (b, r), (fam, M0, Lc) in FAMS.items():
        ry, rz, (ty, tz) = SEEDS[(b, r)]
        lp = lift_params(netdir, fam, M0, Lc)
        nets.append(dict(b=b, r=r, M0=M0, L=Lc, ry=ry, rz=rz, ty=ty, tz=tz, lp=lp))
        # chain
        cols = seed_cols(b, M0, ry, rz)
        levels = [(M0, cols)]
        M = M0
        lams = []
        for sA, sB in lp:
            lam = []
            for e in range(1, M + 1):
                l_yz = lam_cert(b, M, cols, 1, 2, e, sA[1], sA[2])
                l_xy = lam_cert(b, M, cols, 0, 1, e, sB[0], sB[1])
                l_xz = lam_cert(b, M, cols, 0, 2, e, dsub(b, sB[0], sA[0], M), dsub(b, sB[2], sA[2], M))
                lam.append([l_yz[0], l_yz[1], l_xy[0], l_xy[1], l_xz[0], l_xz[1]])
            lams.append(lam)
            cols = lift_cols(b, M, cols, sA, sB)
            M += 3
            levels.append((M, cols))
        assert M == Lc
        # certificate level: G
        H = Lc // 2
        C = [mat_rows(cols, c, b, Lc, H) for c in range(3)]
        Gm = matmul(C[2], matinv(C[0] + C[1], b), b)
        gx = [code([Gm[d][k] for d in range(H)], b) for k in range(H)]
        gy = [code([Gm[d][H + k] for d in range(H)], b) for k in range(H)]
        v = VCERT[(b, r)]
        rr = next(t for t in range(H + 1) if b ** (2 * t) >= v and t >= 1)
        # cost-minimizing r: candidates |St(H-r)| * b^r plus enumeration b^(H-r)
        best = None
        for t in range(rr, H):
            cost = b ** (H - t) + 3 * len([x for x in range(min(b ** (H - t), 1)) ]) + b ** t * (1 + (b - 1) * (H - t))
            if best is None or cost < best[0]:
                best = (cost, t)
        rr = best[1]
        # intermediate levels
        mids = []
        for (m, cl) in levels[:-1]:
            Hp, U, Mx, My, Mz = window_U(b, m, cl)
            mids.append(dict(m=m, Hp=Hp, U=U, Mx=Mx, My=My, Mz=Mz))
            report.append(f'b{b} r{r} m{m}: U={U} c={U ** 0.5 * b ** (-2 * m / 3):.6f}')
        data.append(dict(b=b, r=r, lams=lams, gx=gx, gy=gy, H=H, rr=rr, v=v, mids=mids))
        report.append(f'b{b} r{r} L{Lc}: H={H} r={rr} v={v}')
    # witnesses
    wits = {}
    for fn in sorted(os.listdir(os.path.join(GEO, 'base23_audit', 'witness_smallm'))):
        b, M, cl, sh = net_cols(os.path.join(GEO, 'base23_audit', 'witness_smallm', fn))
        wits[(b, M, 'cur')] = (cl, sh)
    for fn in sorted(os.listdir(os.path.join(GEO, 'base23_everyshift', 'witness_smallm_es'))):
        b, M, cl, sh = net_cols(os.path.join(GEO, 'base23_everyshift', 'witness_smallm_es', fn))
        wits[(b, M, 'repl')] = (cl, sh)
    wU = {}
    for k, (cl, sh) in wits.items():
        wU[k] = brute_U(k[0], k[1], cl)
        report.append(f'witness {k}: U={wU[k]} c={wU[k] ** 0.5 * k[0] ** (-2 * k[1] / 3):.6f} shift={sh}')
    print('\n'.join(report))
    write_nets(nets, wits)
    write_data(data, wits, wU)


HDR = open(os.path.join(HERE, '..', 'Z3Net', 'B23Defs.lean')).read().split('module\n')[0]


def write_nets(nets, wits):
    o = [HDR + 'module\npublic import Z3Net.B23Defs\n\n@[expose] public section\n',
         '/-!\n# Data: the nets of `thm:base23` (generated by `scripts/gen_b23data.py`)\n\n'
         '* `b23SeedM b r`, `b23RowsY b r`, `b23RowsZ b r`, `b23Tau b r`: the seeds of `tab:b23seeds` (`r = m mod 3`).\n'
         '* `b23Lifts b r`: the lift parameters of the fixed chains up to the certificate level `b23L b r`: per lift the\n'
         '  codes of `s_A` and of `s_B` (one per coordinate, `ℓ` digits at level `ℓ`), replayed from the R1 witnesses.\n'
         '* `b23Wit b m`: the explicit witnesses below the seed levels (column codes), with the replacement witnesses of\n'
         '  the research notes for `b = 2`, `m = 6, 7`; `b23WitCur 2 m` the current witnesses there.\n-/\n',
         '\nnamespace Z3NetB23\n\n']
    def mat(name, typ, f):
        o.append(f'/-- {name[1]} -/\ndef {name[0]} : {typ}\n' + ''.join(f'  | {n["b"]}, {n["r"]} => {f(n)}\n' for n in nets) + '  | _, _ => ' + ('[]' if 'List' in typ else '0') + '\n\n')
    mat(('b23SeedM', 'The seed level `M` (`tab:base23`, `tab:b23seeds`).'), 'ℕ → ℕ → ℕ', lambda n: n['M0'])
    mat(('b23L', 'The certificate level `L` (`tab:base23`).'), 'ℕ → ℕ → ℕ', lambda n: n['L'])
    mat(('b23RowsY', 'The rows of `A_y` as printed in `tab:b23seeds`.'), 'ℕ → ℕ → List ℕ', lambda n: L(n['ry']))
    mat(('b23RowsZ', 'The rows of `A_z` as printed in `tab:b23seeds`.'), 'ℕ → ℕ → List ℕ', lambda n: L(n['rz']))
    mat(('b23Tau', 'The shift `(τ_x, τ_y, τ_z) = (0, τ_y, τ_z)` of the seed (`tab:b23seeds`).'), 'ℕ → ℕ → List ℕ', lambda n: L([0, n['ty'], n['tz']]))
    mat(('b23Lifts', 'The lift parameters: per lift the codes of `s_A` and of `s_B` (`x, y, z`).'), 'ℕ → ℕ → List (List ℕ × List ℕ)',
        lambda n: '[' + ', '.join(f'({L(a)}, {L(bb)})' for a, bb in n['lp']) + ']')
    o.append('/-- The witnesses below the seed levels (column codes of `C_x, C_y, C_z`), with the replacement witnesses for\n`b = 2`, `m = 6, 7`. -/\ndef b23Wit : ℕ → ℕ → List (List ℕ)\n')
    for (b, M, kind), (cl, sh) in sorted(wits.items()):
        if kind == 'cur' and b == 2 and M in (6, 7):
            continue
        o.append(f'  | {b}, {M} => {LL(cl)}\n')
    o.append('  | _, _ => []\n\n')
    o.append('/-- The current witnesses for `b = 2`, `m = 6, 7` (`base23_audit/witness_smallm`). -/\ndef b23WitCur : ℕ → List (List ℕ)\n')
    for (b, M, kind), (cl, sh) in sorted(wits.items()):
        if kind == 'cur' and b == 2 and M in (6, 7):
            o.append(f'  | {M} => {LL(cl)}\n')
    o.append('  | _ => []\n\nend Z3NetB23\n')
    open(os.path.join(HERE, '..', 'Z3Net', 'B23Nets.lean'), 'w').write(''.join(o))


def write_data(data, wits, wU):
    o = [HDR + 'module\npublic import Z3Net.B23Nets\n\n@[expose] public section\n',
         '/-!\n# Certificate data of `thm:base23` (generated by `scripts/gen_b23data.py`)\n\n'
         '* `b23Lam b r k`: for the lift number `k`, for every `e = 1 … ℓ`, the functionals `λ^{yz}_e, λ^{xy}_e, λ^{xz}_e`\n'
         '  as six codes `(l₁, l₂)` (admissibility, `def:lift`).\n'
         '* `b23Gx b r`, `b23Gy b r`, `b23R b r`, `b23V b r`: `Δ_z = G_x Δ_x + G_y Δ_y` on the top `L/2` digits at the\n'
         '  certificate level, the window parameter and the certified `v°_L ≥ v`.\n'
         '* `b23Mid b r k`: at the chain level `k` below `L`: `(H′, U, M^x, M^y, M^z)` (the every-shift distance `≥ U`).\n'
         '* `b23WitU b m`, `b23WitCurU m`: the every-shift `d²` of the witnesses.\n-/\n', '\nnamespace Z3NetB23\n\n']
    def fn(name, doc, typ, f, default):
        o.append(f'/-- {doc} -/\ndef {name} : {typ}\n' + ''.join(f'  | {d["b"]}, {d["r"]} => {f(d)}\n' for d in data) + f'  | _, _ => {default}\n\n')
    fn('b23Lam', 'The admissibility functionals of every lift.', 'ℕ → ℕ → List (List (List ℕ))', lambda d: '[' + ', '.join(LL(l) for l in d['lams']) + ']', '[]')
    fn('b23Gx', '`G_x` (column codes).', 'ℕ → ℕ → List ℕ', lambda d: L(d['gx']), '[]')
    fn('b23Gy', '`G_y` (column codes).', 'ℕ → ℕ → List ℕ', lambda d: L(d['gy']), '[]')
    fn('b23R', 'The window parameter `r` of `chk1`.', 'ℕ → ℕ → ℕ', lambda d: d['rr'], '0')
    fn('b23V', 'The certified `v°_L ≥ v`.', 'ℕ → ℕ → ℕ', lambda d: d['v'], '0')
    fn('b23Mid', 'The levels between the seed and `L`: `(H′, U, M^x, M^y, M^z)`.', 'ℕ → ℕ → List (ℕ × ℕ × List (List ℕ) × List (List ℕ) × List (List ℕ))',
       lambda d: '[' + ', '.join(f'({x["Hp"]}, {x["U"]}, {LL(x["Mx"])}, {LL(x["My"])}, {LL(x["Mz"])})' for x in d['mids']) + ']', '[]')
    o.append('/-- The every-shift `d²` of the witnesses (`b23Wit`). -/\ndef b23WitU : ℕ → ℕ → ℕ\n')
    for (b, M, kind) in sorted(wits):
        if kind == 'cur' and b == 2 and M in (6, 7):
            continue
        o.append(f'  | {b}, {M} => {wU[(b, M, kind)]}\n')
    o.append('  | _, _ => 0\n\n/-- The every-shift `d²` of the current witnesses `b23WitCur`. -/\ndef b23WitCurU : ℕ → ℕ\n')
    for (b, M, kind) in sorted(wits):
        if kind == 'cur' and b == 2 and M in (6, 7):
            o.append(f'  | {M} => {wU[(b, M, kind)]}\n')
    o.append('  | _ => 0\n\nend Z3NetB23\n')
    open(os.path.join(HERE, '..', 'Z3Net', 'B23Data.lean'), 'w').write(''.join(o))


main()
