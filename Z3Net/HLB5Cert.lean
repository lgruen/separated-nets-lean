module
public import Mathlib
public import Z3Net.HLB5

@[expose] public section

/-!
# Entry HL, part 11: the `s = 5` certificate (definitions for the kernel check)

For every cell-step vector `E = (e₀, …, e₄) ∈ {-2,…,2}^5 \ {0}`:

* level 1 (decoupled): per coordinate `c`, `S_c = ∑_d ctrF d e_d J_d c` lies in
  `[lo_c, hi_c]` (per-axis min/max over `J_d ∈ {0,…,3}`), so
  `lbq ≥ lb1 = max(0, q·a₁ - max(|lo_c|, |hi_c|) - 2)`; if `∑_c lb1² ≥ T` the vector is done;
* level 2 (exact): otherwise every carry vector `J` (with `J_d = 0` on still axes) is checked.

`T`: `100000² ∑_c lb² ≥ 205304² · 1511²`, i.e. `δ N^(1/5) ≥ 1.02652` at `q₁ = 1511`; the
monotone form (`lbq = max(0, a q - b)`) carries it to every `q ≥ 1511`. All definitions are
plain recursion-free arithmetic on explicit 5-tuples, for a fast `decide +kernel`.
-/

namespace Z3NetHL.Proofs

/-- `F2[x][c][d]` with natural-number indices. -/
def F2v (x c d : ℕ) : ℤ := ((F2TabB5.getD x []).getD c []).getD d 0

/-- Contribution of axis `d` (step `E`, carry length `J ≤ 3`) to `2σ_c`. -/
def ctrF (d : ℕ) (E : ℤ) (J : ℕ) (c : ℕ) : ℤ :=
  E * F2v 0 c d + E.sign * ((if 1 ≤ J then F2v 1 c d else 0) + (if 2 ≤ J then F2v 2 c d else 0) +
    (if 3 ≤ J then F2v 3 c d else 0))

def cminF (d : ℕ) (E : ℤ) (c : ℕ) : ℤ :=
  min (min (ctrF d E 0 c) (ctrF d E 1 c)) (min (ctrF d E 2 c) (ctrF d E 3 c))

def cmaxF (d : ℕ) (E : ℤ) (c : ℕ) : ℤ :=
  max (max (ctrF d E 0 c) (ctrF d E 1 c)) (max (ctrF d E 2 c) (ctrF d E 3 c))

def loF (e0 e1 e2 e3 e4 : ℤ) (c : ℕ) : ℤ :=
  cminF 0 e0 c + cminF 1 e1 c + cminF 2 e2 c + cminF 3 e3 c + cminF 4 e4 c

def hiF (e0 e1 e2 e3 e4 : ℤ) (c : ℕ) : ℤ :=
  cmaxF 0 e0 c + cmaxF 1 e1 c + cmaxF 2 e2 c + cmaxF 3 e3 c + cmaxF 4 e4 c

def SF (e0 e1 e2 e3 e4 : ℤ) (j0 j1 j2 j3 j4 : ℕ) (c : ℕ) : ℤ :=
  ctrF 0 e0 j0 c + ctrF 1 e1 j1 c + ctrF 2 e2 j2 c + ctrF 3 e3 j3 c + ctrF 4 e4 j4 c

/-- Multiplier of `q` (in half units) for the exact `S`. -/
def aS (odd : Bool) (E S : ℤ) : ℤ :=
  if odd then min |2 * E + 1| |2 * E - 1|
  else if S = 0 then |2 * E|
  else if 0 < S then min |2 * E| |2 * E - 2| else min |2 * E| |2 * E + 2|

/-- Lower bound (half units) for `S` known exactly. -/
def lbq (q : ℤ) (odd : Bool) (E S : ℤ) : ℤ := max 0 (q * aS odd E S - |S| - 2)

/-- Multiplier of `q` (half units) valid on `[lo, hi]`. -/
def a1 (odd : Bool) (E lo hi : ℤ) : ℤ :=
  if odd then min |2 * E + 1| |2 * E - 1|
  else if 0 < lo then min |2 * E| |2 * E - 2|
  else if hi < 0 then min |2 * E| |2 * E + 2|
  else min (min |2 * E| |2 * E - 2|) |2 * E + 2|

/-- Lower bound (half units) valid on `[lo, hi]`. -/
def lb1 (q : ℤ) (odd : Bool) (E lo hi : ℤ) : ℤ := max 0 (q * a1 odd E lo hi - max |lo| |hi| - 2)

def q1 : ℤ := 1511
def Tq : ℤ := 205304 ^ 2 * 1511 ^ 2

def oddF (e0 e1 e2 e3 e4 : ℤ) : Bool := decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1)

def okSF (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (max |loF e0 e1 e2 e3 e4 0| |hiF e0 e1 e2 e3 e4 0| < q1) &&
  decide (max |loF e0 e1 e2 e3 e4 1| |hiF e0 e1 e2 e3 e4 1| < q1) &&
  decide (max |loF e0 e1 e2 e3 e4 2| |hiF e0 e1 e2 e3 e4 2| < q1) &&
  decide (max |loF e0 e1 e2 e3 e4 3| |hiF e0 e1 e2 e3 e4 3| < q1) &&
  decide (max |loF e0 e1 e2 e3 e4 4| |hiF e0 e1 e2 e3 e4 4| < q1)

def ok1F (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (Tq ≤ 100000 ^ 2 *
    (lb1 q1 (oddF e0 e1 e2 e3 e4) e0 (loF e0 e1 e2 e3 e4 0) (hiF e0 e1 e2 e3 e4 0) ^ 2 +
     lb1 q1 (oddF e0 e1 e2 e3 e4) e1 (loF e0 e1 e2 e3 e4 1) (hiF e0 e1 e2 e3 e4 1) ^ 2 +
     lb1 q1 (oddF e0 e1 e2 e3 e4) e2 (loF e0 e1 e2 e3 e4 2) (hiF e0 e1 e2 e3 e4 2) ^ 2 +
     lb1 q1 (oddF e0 e1 e2 e3 e4) e3 (loF e0 e1 e2 e3 e4 3) (hiF e0 e1 e2 e3 e4 3) ^ 2 +
     lb1 q1 (oddF e0 e1 e2 e3 e4) e4 (loF e0 e1 e2 e3 e4 4) (hiF e0 e1 e2 e3 e4 4) ^ 2))

def okJF (e0 e1 e2 e3 e4 : ℤ) (j0 j1 j2 j3 j4 : ℕ) : Bool :=
  decide (Tq ≤ 100000 ^ 2 *
    (lbq q1 (oddF e0 e1 e2 e3 e4) e0 (SF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4 0) ^ 2 +
     lbq q1 (oddF e0 e1 e2 e3 e4) e1 (SF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4 1) ^ 2 +
     lbq q1 (oddF e0 e1 e2 e3 e4) e2 (SF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4 2) ^ 2 +
     lbq q1 (oddF e0 e1 e2 e3 e4) e3 (SF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4 3) ^ 2 +
     lbq q1 (oddF e0 e1 e2 e3 e4) e4 (SF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4 4) ^ 2))

def jOpts (e : ℤ) : List ℕ := if e = 0 then [0] else [0, 1, 2, 3]

def ok2F (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  (jOpts e0).all fun j0 => (jOpts e1).all fun j1 => (jOpts e2).all fun j2 =>
    (jOpts e3).all fun j3 => (jOpts e4).all fun j4 => okJF e0 e1 e2 e3 e4 j0 j1 j2 j3 j4

def okEF (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  okSF e0 e1 e2 e3 e4 &&
    (decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) || ok1F e0 e1 e2 e3 e4 || ok2F e0 e1 e2 e3 e4)

def vals : List ℤ := [-2, -1, 0, 1, 2]

/-- The certificate, split by the first coordinate. -/
def checkE0 (e0 : ℤ) : Bool :=
  vals.all fun e1 => vals.all fun e2 => vals.all fun e3 => vals.all fun e4 => okEF e0 e1 e2 e3 e4

end Z3NetHL.Proofs
