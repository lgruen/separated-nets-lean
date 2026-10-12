# ba_cert.py -- exact certification of the per-residue family floors (the research notes).
# Every value is reduced to an integer X and level m with  value^6 = X^3 / b^(4m):
#   exact separation  c_m = sqrt(d2) b^(-2m/3)            -> X = d2
#   certificate       gsep_L = W sqrt(v*) b^(-2L/3), W=b^(L-floor(L/2)) -> X = W^2 v*
#   same-ancestor term (b^L - W) b^(-2L/3)                -> value^6 = (b^L-W)^6 / b^(4L)
# so all comparisons are exact integer/rational comparisons (no floating point in any verdict).
# d2 and v* come from ./ba (materialised, or the generic block evaluator for large levels; cross-validated in the notes).
# usage: python3 ba_cert.py NETDIR      (NETDIR holds <fam>_m<m>.net from ba_dump and u/u_<fam>_m<m>.net shift-free copies)
import sys, subprocess, os
from fractions import Fraction as F
ND = sys.argv[1]
FAM = {'b2_mod0': (2, 9, 30), 'b2_mod1': (2, 10, 28), 'b2_mod2': (2, 11, 29),
       'b3_mod0': (3, 6, 18), 'b3_mod1': (3, 7, 22), 'b3_mod2': (3, 8, 20)}
def ba(*a): return subprocess.run(['./ba'] + list(a), capture_output=True, text=True, check=True).stdout
def measure(fn, b, m, need_c=True):
    small = (b == 2 and m <= 25) or (b == 3 and m <= 16)
    j = 6 if b == 2 else 4
    if small:
        d2 = int(ba('mind', fn).split('d2=')[1].split()[0]) if need_c else None
        v = int(ba('vstar', fn).split('v*=')[1].split()[0])
    else:
        d2 = int(ba('block', fn, 'exact', str(j)).split('d2=')[1].split()[0]) if need_c else None
        v = int(ba('block', fn, 'trunc', str(j)).split('v*=')[1].split()[0])
    return d2, v
def six(X, b, m): return F(X ** 3, b ** (4 * m))
def trunc4(v6):  # largest k/10^4 with (k/10^4)^6 <= v6
    k = int(float(v6) ** (1 / 6) * 1e4) + 2
    while F(k, 10 ** 4) ** 6 > v6: k -= 1
    return k / 1e4
def rnd(v6): return float(v6) ** (1 / 6)
claims = {}
for shift in ('witness', 'free'):
    print(f"\n=== {'WITH the witness digital shift (DGS Def. 2.2 type)' if shift=='witness' else 'SHIFT-FREE (strict digital net, DGS Def. 2.1 / paper convention)'}")
    for fam, (b, m0, mmax) in FAM.items():
        rows = []
        for m in range(m0, mmax + 1, 3):
            fn = os.path.join(ND, f'{fam}_m{m}.net') if shift == 'witness' else os.path.join(ND, 'u', f'u_{fam}_m{m}.net')
            need_c = not (b == 3 and m >= 21)          # c at the top certificate level is never needed
            d2, v = measure(fn, b, m, need_c)
            H = m // 2; W = b ** (m - H)
            rows.append((m, d2, v, W))
        best = None
        out = []
        for i, (L, _, v, W) in enumerate(rows):
            if v == 0: out.append(f"L={L}:gsep=0"); continue
            g6 = six(W * W * v, b, L)
            same6 = F((b ** L - W) ** 6, b ** (4 * L))
            assert same6 >= g6, "same-ancestor proviso fails"
            cands = [g6] + [six(d2, b, mm) for (mm, d2, _, _) in rows[:i]]
            fl = min(cands)
            out.append(f"L={L}: v*={v} gsep={rnd(g6):.6f} floor={rnd(fl):.6f} (trunc {trunc4(fl):.4f})")
            if best is None or fl > best[1]: best = (L, fl)
        cs = ' '.join(f"{rnd(six(d2,b,mm)):.5f}" for (mm, d2, _, _) in rows if d2 is not None)
        print(f"{fam}: c per level (m={m0}..): {cs}")
        for o in out: print("   ", o)
        print(f"  -> best certified family floor for all m>={m0}, m=={m0%3} mod 3: {trunc4(best[1]):.4f} (cert level L={best[0]})")
        claims[(shift, fam)] = (best, {L: (six(W*W*v,b,L) if v else F(0)) for (L,_,v,W) in rows}, rows)
# check the printed constants of BASE23_VETTING / the task prompt
print("\n=== printed constants vs exact values (certified bounds must be TRUNCATED, paper convention sec:conv)")
def famfloor(shift, fam, L):
    b = FAM[fam][0]; best, gs, rows = claims[(shift, fam)]
    i = [r[0] for r in rows].index(L); return min([gs[L]] + [six(d2, b, mm) for (mm, d2, _, _) in rows[:i]])
tiers = {'b2 small': [('b2_mod2', 11), ('b2_mod0', 12), ('b2_mod1', 16)], 'b2 mat': [('b2_mod2', 20), ('b2_mod0', 24), ('b2_mod1', 22)],
         'b2 R1': [('b2_mod2', 26), ('b2_mod0', 30), ('b2_mod1', 28)],
         'b3 small': [('b3_mod0', 6), ('b3_mod1', 10), ('b3_mod2', 8)], 'b3 mat': [('b3_mod0', 12), ('b3_mod1', 10), ('b3_mod2', 14)],
         'b3 R1': [('b3_mod0', 18), ('b3_mod1', 22), ('b3_mod2', 20)]}
printed = {'b2 small': 0.25, 'b2 mat': 0.3609, 'b2 R1': 0.413, 'b3 small': 0.2266, 'b3 mat': 0.2266, 'b3 R1': 0.354}
for t, lst in tiers.items():
    v6 = min(famfloor('witness', f, L) for f, L in lst)
    p = printed[t]; ok = F(p).limit_denominator(10**6) ** 6 <= v6
    print(f"{t:9s}: exact floor {rnd(v6):.6f}, truncated {trunc4(v6):.4f}; printed {p} -> {'OK (certified)' if ok else 'NOT CERTIFIED (rounded up)'}")
