"""SkCert certificate generator / node counter for tab:S1E.

Certificate for lamJit2 s p kappa = J:
  B  : s integer basis rows (LLL-reduced) with W*B = E (E = standard basis of Lambda_kappa)
  proj levels k=0..s-1: scale d_k > 0, vectors P[k][j] (j>=k), with
     <P[k][j'], b_i> = 0 (i<k, j'>=k),  <P[k][j'], d_k b_j - P[k][j]> = 0 (j,j'>=k)
  so d_k^2 ||sum y_j b_j||^2 >= ||sum_{j>=k} y_j P[k][j]||^2.
  enumeration: R2 = (J-1) + 2*isqrt(s*(J-1)) + s.
"""
import sys, math, json, re, os
from fractions import Fraction
sys.path.insert(0, '`geo` (research repository)')
sys.path.insert(0, '`paper` (research repository)')
from codesaudit_e1 import lll


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def jit2(a):
    return sum((abs(x) - 1) ** 2 for x in a if abs(x) > 1)


def stdbasis(p, kap):
    s = len(kap) + 1
    E = []
    for d, k in enumerate(kap):
        v = [0] * s; v[d] = 1; v[s - 1] = k % p; E.append(v)
    v = [0] * s; v[s - 1] = p; E.append(v)
    return E


def solveW(B, E):
    # W with W*B = E : W = E * B^{-1}
    s = len(B)
    M = [[Fraction(x) for x in row] for row in B]
    # invert
    n = s
    A = [M[i] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    Binv = [row[n:] for row in A]
    W = [[sum(Fraction(E[i][t]) * Binv[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
    for row in W:
        for x in row:
            assert x.denominator == 1
    W = [[int(x) for x in row] for row in W]
    for i in range(n):
        for j in range(n):
            assert sum(W[i][t] * B[t][j] for t in range(n)) == E[i][j]
    return W


def projections(B):
    s = len(B)
    # rational GS
    Bs = []
    for i in range(s):
        v = [Fraction(x) for x in B[i]]
        for j in range(i):
            mu = dot(B[i], Bs[j]) / dot(Bs[j], Bs[j])
            v = [a - mu * b for a, b in zip(v, Bs[j])]
        Bs.append(v)
    levels = []
    for k in range(s):
        # pi_k(b_j) = b_j - sum_{i<k} <b_j,Bs_i>/|Bs_i|^2 Bs_i
        Ps = []
        for j in range(k, s):
            v = [Fraction(x) for x in B[j]]
            for i in range(k):
                mu = dot(B[j], Bs[i]) / dot(Bs[i], Bs[i])
                v = [a - mu * b for a, b in zip(v, Bs[i])]
            Ps.append(v)
        den = 1
        for v in Ps:
            for x in v:
                den = den * x.denominator // math.gcd(den, x.denominator)
        P = [[int(x * den) for x in v] for v in Ps]
        g = den
        for v in P:
            for x in v:
                g = math.gcd(g, x)
        d = den // g
        P = [[x // g for x in v] for v in P]
        levels.append((d, P))
    # verify certificate conditions
    for k, (d, P) in enumerate(levels):
        for jj in range(k, s):
            for i in range(k):
                assert dot(P[jj - k], B[i]) == 0
            for j in range(k, s):
                w = [d * x - y for x, y in zip(B[j], P[j - k])]
                assert dot(P[jj - k], w) == 0
    return levels


def enumerate_tree(B, levels, R2, J):
    """returns (nodes, leaves, ok, minjit) - integer version exactly as Lean checker."""
    s = len(B)
    stats = dict(nodes=0, leafvecs=0, bad=None)

    def rec(k, ys):  # ys = dict j->y for j>k
        d, P = levels[k]
        v = P[0]
        w = [0] * s
        for j in range(k + 1, s):
            yj = ys[j]
            w = [a + yj * b for a, b in zip(w, P[j - k])]
        T = d * d * R2
        A = dot(v, v); Bc = dot(v, w); ww = dot(w, w)
        D = A * (T - ww) + Bc * Bc
        stats['nodes'] += 1
        if D < 0:
            return True
        r = math.isqrt(D)
        lo = -((r + Bc) // A)  # ceil((-r-Bc)/A)
        hi = (r - Bc) // A
        for y in range(lo, hi + 1):
            ys[k] = y
            if k == 0:
                a = [w[t] + y * v[t] for t in range(s)]
                stats['leafvecs'] += 1
                if any(a) and jit2(a) < J:
                    stats['bad'] = a
                    return False
            else:
                if not rec(k - 1, ys):
                    return False
        return True
    ok = rec(s - 1, {})
    return ok, stats


def cert(p, kap, J):
    s = len(kap) + 1
    E = stdbasis(p, kap)
    B = lll(E)
    W = solveW(B, E)
    levels = projections(B)
    Jm = J - 1
    R2 = Jm + 2 * math.isqrt(s * Jm) + s
    ok, st = enumerate_tree(B, levels, R2, J)
    return dict(s=s, p=p, kappa=kap, J=J, B=B, W=W, levels=[(d, P) for d, P in levels], R2=R2, ok=ok, stats=st)


if __name__ == '__main__':
    from s1e_certs import rows
    from codesaudit_e1 import analyse
    import time
    out = []
    for src, s, p, kap in rows():
        r = analyse(p, kap)
        J = r['lamjit2']
        t = time.time()
        c = cert(p, kap, J)
        mx = max(abs(x) for d, P in c['levels'] for v in P for x in v)
        md = max(d for d, P in c['levels'])
        print('%-16s s=%d p=%-12d J=%-7d ok=%s nodes=%-7d leaves=%-7d maxP=%.1e maxd=%.1e  %.2fs' % (
            src, s, p, J, c['ok'], c['stats']['nodes'], c['stats']['leafvecs'], mx, md, time.time() - t), flush=True)
        c['src'] = src
        c['stats'] = c['stats']
        out.append(c)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certs.json'), 'w'))
