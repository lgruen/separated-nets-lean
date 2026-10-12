# es_cert.py -- exact certification of the EVERY-DIGITAL-SHIFT floors of the base-2/3 nets of thm:base23
# (the research notes). All verdicts are exact integer / rational comparisons (value^6 = X^3 / b^(4m), as ba_cert.py):
#   exact every-shift separation at level m:  c_unif(m)   = sqrt(d2_unif) b^(-2m/3)          X = d2_unif
#   every-shift certificate at level L:       gsep_unif(L) = W sqrt(v*_unif) b^(-2L/3)        X = W^2 v*_unif, W=b^(L-floor(L/2))
#   same-ancestor proviso:                    (b^L - W) b^(-2L/3) >= gsep_unif(L)
# Inputs come from ./es (vunif, cunif2, cunif, freeze), whose methods are proved in the research notes-§3.
# Scope: the nets of thm:base23 = R1 chain up to the certificate level Lc of tab:base23, then ANY continuation with
# D_l = floor(l/2); the every-shift certificate level L* must be <= Lc and P_{Lc} must be frozen relative to P_{L*}
# (checked with ./es freeze for every R1 level in (L*, Lc]); beyond Lc the canonical D condition preserves freezing.
# usage: uv run python es_cert.py NETDIR SMALLM_DIR [SMALLM_ALT_DIR]
import sys, subprocess, os
from fractions import Fraction as F
ND, SM = sys.argv[1], sys.argv[2]
ALT = sys.argv[3] if len(sys.argv) > 3 else None
def es(*a):
    r = subprocess.run(['./es'] + list(a), capture_output=True, text=True)
    return r.returncode, r.stdout
def six(X, b, m): return F(X ** 3, b ** (4 * m))
def trunc4(v6):
    k = int(float(v6) ** (1 / 6) * 1e4) + 2
    while F(k, 10 ** 4) ** 6 > v6: k -= 1
    return k / 1e4
def val(v6): return float(v6) ** (1 / 6)
# family: base, seed level, certificate level Lc of tab:base23 (shifted column)
FAM = {'b2_mod0': (2, 9, 30), 'b2_mod1': (2, 10, 28), 'b2_mod2': (2, 11, 20),
       'b3_mod0': (3, 6, 18), 'b3_mod1': (3, 7, 22), 'b3_mod2': (3, 8, 20)}
res = {}
for fam, (b, m0, Lc) in FAM.items():
    r = m0 % 3
    levels = list(range(m0, Lc + 1, 3))
    # exact every-shift d2 at every explicit lifted level (toroidal and non-toroidal)
    exact = {}
    for m in levels:
        _, o = es('cunif2', f'{ND}/{fam}_m{m}.net')
        d2 = int(o.split('d2_unif=')[1].split()[0]); d2nt = int(o.split('d2nt_unif=')[1].split()[0])
        exact[m] = (d2, d2nt)
    # small m (explicit witnesses below the seed), same residue class
    small = {}; small_alt = {}
    for mm in range(1, m0):
        if mm % 3 != r: continue
        _, o = es('cunif', f'{SM}/b{b}_m{mm}.net'); small[mm] = int(o.split('d2_unif=')[1].split()[0])
        alt = f'{ALT}/b{b}_m{mm}_everyshift.net' if ALT else None
        if alt and os.path.exists(alt):
            _, o = es('cunif', alt); small_alt[mm] = int(o.split('d2_unif=')[1].split()[0])
        else: small_alt[mm] = small[mm]
    # candidate certificate levels L* <= Lc with freezing to every R1 level in (L*, Lc]
    cands = []
    for L in levels:
        frozen = all(es('freeze', f'{ND}/{fam}_m{L}.net', f'{ND}/{fam}_m{m}.net')[0] == 0 for m in levels if m > L)
        _, o = es('vunif', f'{ND}/{fam}_m{L}.net'); v = int(o.split('v*_unif=')[1].split()[0])
        assert 'witness_pair_recheck' in o and o.strip().endswith('OK'), o
        H = L // 2; W = b ** (L - H)
        g6 = six(W * W * v, b, L) if v > 0 else F(0)
        same6 = F((b ** L - W) ** 6, b ** (4 * L))
        if v > 0: assert same6 >= g6, 'proviso'
        cands.append((L, v, frozen, g6))
    usable = [(L, v, g6) for (L, v, fz, g6) in cands if fz and v > 0]
    Ls, vs, gs = max(usable, key=lambda t: (t[2], t[0]))   # ties -> the larger level (the table certificate level)
    # floor for all m >= m0 (lifted levels): exact c_unif at levels <= Lc, and gsep_unif(L*) for every m (>= L*)
    lift_floor = min([gs] + [six(exact[m][0], b, m) for m in levels])
    all_floor = min([lift_floor] + [six(d2, b, mm) for mm, d2 in small.items()])
    # upper bound valid for EVERY continuation: c_unif(m) <= non-toroidal every-shift c of P_L for all m >= L
    ub = min(six(exact[m][1], b, m) for m in levels)
    print(f"\n{fam}: levels {levels[0]}..{Lc}; exact every-shift c (toroidal) per level: " +
          ' '.join(f"m{m}:{val(six(exact[m][0], b, m)):.6f}" for m in levels))
    print("  small-m witnesses (every shift): " + ' '.join(f"m{mm}:{val(six(d2, b, mm)):.6f}" for mm, d2 in small.items()))
    print("  certificates v*_unif (frozen to Lc?): " + ' '.join(f"L{L}:{v}{'' if fz else '(not frozen)'}" for (L, v, fz, g6) in cands))
    print(f"  best usable every-shift certificate: L*={Ls} v*_unif={vs} gsep_unif={val(gs):.6f} (proviso holds exactly)")
    print(f"  PROVED floor, all m>={m0} (m={r} mod 3), every digital shift, any D=floor(l/2) continuation after {Lc}: "
          f"{val(lift_floor):.6f} -> trunc {trunc4(lift_floor):.4f}")
    print(f"  PROVED floor incl. the small-m witnesses (all m>=1 in the class): {val(all_floor):.6f} -> trunc {trunc4(all_floor):.4f}")
    print(f"  PROVED upper bound for the infimum (every continuation): {val(ub):.6f}")
    alt_floor = min([lift_floor] + [six(d2, b, mm) for mm, d2 in small_alt.items()])
    if small_alt != small:
        print(f"  with the replacement witnesses of {ALT} (" + ' '.join(f"m{mm}:{val(six(d2, b, mm)):.6f}" for mm, d2 in small_alt.items() if small_alt[mm] != small[mm]) +
              f"): floor for all m>=1 in the class {val(alt_floor):.6f} -> trunc {trunc4(alt_floor):.4f}")
    res[fam] = (lift_floor, all_floor, ub, Ls, alt_floor)
print("\n=== per base (min over the three classes, all m >= 1, every digital shift)")
for b in (2, 3):
    v6 = min(res[f][1] for f in res if f.startswith(f'b{b}'))
    print(f"b={b}: {val(v6):.6f} -> trunc {trunc4(v6):.4f}")
if ALT:
    print("with the replacement witnesses:")
    for b in (2, 3):
        v6 = min(res[f][4] for f in res if f.startswith(f'b{b}'))
        print(f"b={b}: {val(v6):.6f} -> trunc {trunc4(v6):.4f}")
