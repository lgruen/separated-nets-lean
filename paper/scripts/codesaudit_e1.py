"""codesaudit_e1.py -- exact lattice minima for Proposition prop:S1E (Euclidean form of Theorem thm:S1).

For Lambda_h = {a in Z^s : a_z == sum_d kappa_d a_{x_d} (mod p)} (z = last coordinate) compute EXACTLY
  lam2   = min ||a||_2 over a != 0,
  lamjit = min ||(|a|-1)_+||_2 over a != 0   (the Euclidean jitter functional of Lemma skelred(i)),
by exact-rational LLL + Fincke-Pohst enumeration of all vectors with ||a|| <= T + sqrt(s) (T = running best
lamjit; ||(|a|-1)_+|| >= ||a|| - sqrt(s), so this radius is complete), every candidate re-evaluated in integers.
Also: deterministic Miller-Rabin primality of p, kappa units mod p.
usage: python3 codesaudit_e1.py p kappa_csv [p kappa_csv ...]      (own code; no repo imports)
"""
import sys, math
from fractions import Fraction


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2; r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):  # deterministic for n < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def lll(B, delta=Fraction(99, 100)):
    B = [list(b) for b in B]
    n = len(B)

    def gso(B):
        Bs, mu = [], [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            v = [Fraction(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = Fraction(dot(B[i], Bs[j])) / dot(Bs[j], Bs[j])
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
        return Bs, mu
    Bs, mu = gso(B)
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]
                Bs, mu = gso(B)
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]):
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu = gso(B)
            k = max(k - 1, 1)
    return B


def jit2(a):
    return sum((abs(x) - 1) ** 2 for x in a if abs(x) > 1)


def enum_short(B, R2):
    """all nonzero integer combos v = sum c_i B_i with ||v||^2 <= R2 (float GSO on an LLL basis, margin)."""
    n = len(B)
    Bf = [[float(x) for x in b] for b in B]
    Bs, mu = [], [[0.0] * n for _ in range(n)]
    for i in range(n):
        v = Bf[i][:]
        for j in range(i):
            mu[i][j] = dot(Bf[i], Bs[j]) / dot(Bs[j], Bs[j])
            v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
        Bs.append(v)
    bn = [dot(b, b) for b in Bs]
    R2m = R2 * (1 + 1e-9) + 1e-6
    out, c = [], [0] * n

    def rec(i, partial):
        ctr = -sum(c[j] * mu[j][i] for j in range(i + 1, n))
        rad = math.sqrt(max(0.0, (R2m - partial) / bn[i]))
        for ci in range(math.ceil(ctr - rad), math.floor(ctr + rad) + 1):
            c[i] = ci
            pp = partial + (ci - ctr) ** 2 * bn[i]
            if pp > R2m:
                continue
            if i == 0:
                if any(c):
                    out.append([sum(c[j] * B[j][t] for j in range(n)) for t in range(len(B[0]))])
            else:
                rec(i - 1, pp)
        c[i] = 0
    rec(n - 1, 0.0)
    return out


def analyse(p, kap):
    s = len(kap) + 1
    assert is_prime(p), "p not prime"
    assert all(k % p for k in kap), "kappa not units"
    B = []
    for d, k in enumerate(kap):
        v = [0] * s; v[d] = 1; v[s - 1] = k % p; B.append(v)
    v = [0] * s; v[s - 1] = p; B.append(v)
    L = lll(B)
    for b in L:  # exact membership
        assert (b[s - 1] - sum(k * x for k, x in zip(kap, b[:s - 1]))) % p == 0
    best_j = min(jit2(b) for b in L)
    R = math.sqrt(best_j) + math.sqrt(s)
    vecs = enum_short(L, R * R)
    for v in vecs:
        assert (v[s - 1] - sum(k * x for k, x in zip(kap, v[:s - 1]))) % p == 0
    lam2sq = min(dot(v, v) for v in vecs + [list(b) for b in L])
    lamjsq = min([best_j] + [jit2(v) for v in vecs])
    arg = min(vecs, key=jit2) if vecs else None
    return dict(s=s, p=p, lam2=math.sqrt(lam2sq), lamjit=math.sqrt(lamjsq), lamjit2=lamjsq,
                c_jit=math.sqrt(lamjsq) * p ** (-1 / s), c_l2=math.sqrt(lam2sq) * p ** (-1 / s),
                nvec=len(vecs), argmin=arg,
                paper_S1=(math.floor(round(p ** (1 / s), 9)) - 1) * p ** (-1 / s))


if __name__ == "__main__":
    a = sys.argv[1:]
    for i in range(0, len(a), 2):
        p = int(a[i]); kap = [int(x) for x in a[i + 1].split(',') if x]
        r = analyse(p, kap)
        print("s=%d p=%d lam2=%.4f c_l2=%.4f lamjit=%.4f (sq %d) c_jit=%.4f  [thmS1 (rho-1)p^-1/s=%.4f]  #vec=%d argmin=%s"
              % (r['s'], p, r['lam2'], r['c_l2'], r['lamjit'], r['lamjit2'], r['c_jit'], r['paper_S1'], r['nvec'], r['argmin']))
