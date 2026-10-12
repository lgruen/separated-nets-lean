/-
Definitions for `rem:accounting` (first-order accounting of the `s = 5` layers at one resolution) of the manuscript
*Low-discrepancy quasi-uniform digital nets in every dimension* (`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Q5Defs

@[expose] public section

/-!
# Definitions for `rem:accounting` (V14 stage S13′)

All quantities are doubled to stay in `ℤ`, as `drift2` of `Z3Net/Q5Defs.lean` (`F2 = 2F₀`, `2β = F2 E`, `v = D₁E`):
* `sgnS F2 E c` = `s_c(E)` of `sec:halfms`: `E_c` if `E_c ≠ 0`, `−sgn β_c` if `E_c = 0`;
* `nHarm F2 D1 E` = the number of harmful coordinates (`v_c ≠ 0` and `sgn v_c = s_c(E)`);
* `dj2 F2 D1` = `2 dj(F₀, D₁)` = the maximum of `2 dr(E) + 2 #harmful` over the binding steps;
* `ell2 F2 E c` = `2ℓ_c(E)` of the proof of `prop:half5` (an integer); `LamHyp F2` = the hypothesis (Λ);
* `halfNet p F2 D` = the digital point set over `ℤ/pℤ` with first offset rows `F₀ = F2/2` (`½ ≡ (p+1)/2`) and deeper
  rows `D c r` (`r = 1, 2, 3`), i.e. `GFpoint 5 p 1 (halfPhi 5 p F2 D)`; `Qstar p = halfNet p F2star Dstar`;
* `sepN p X` = `δN^{1/5}` (toroidal) of a point set `X` with `N = p⁵` points; `Keff p X` = `K_eff(p)`;
* `F2cex` = the doubled layer `2F₀` printed after `rem:accounting` ("(Λ) is a genuine hypothesis").
-/

namespace Z3NetHL

open Finset

/-- **`s_c(E)`** (`sec:halfms`): `E_c` if `E_c ≠ 0`, and `−sgn β_c` if `E_c = 0` (`sgn β_c = sgn (F2 E)_c`). -/
def sgnS (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  if E c = 0 then -Int.sign (dotR F2 E c) else E c

/-- **The number of harmful coordinates** of the step `E` (`sec:halfms`): coordinate `c` is harmful if `v_c ≠ 0` and
`sgn v_c = s_c(E)`, where `v = D₁ E`. -/
def nHarm (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) : ℕ :=
  (univ.filter fun c => dotR D1 E c ≠ 0 ∧ Int.sign (dotR D1 E c) = sgnS F2 E c).card

/-- **`2 dj(F₀, D₁)`** (`sec:halfms`): the maximum of `2 dr(E) + 2 · #{c harmful}` over the binding steps `E`. -/
def dj2 (F2 D1 : Fin 5 → Fin 5 → ℤ) : ℤ :=
  bind5.sup' bind5_nonempty fun E => drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)

/-- **`2ℓ_c(E)`** of the proof of `prop:half5` (an integer): `min(|2E_c + 1|, |2E_c − 1|)` if `σ_E = ∑ E` is odd, and
`min_κ |2E_c − 2κ|` over `κ ∈ {0, sgn β_c}` (over `{0}` if `β_c = 0`) if `σ_E` is even. This is `2 · halfEllInf` of
S11′ (`Z3Net/HLDefs.lean`). -/
def ell2 (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  if (∑ d, E d) % 2 = 1 then min |2 * E c + 1| |2 * E c - 1|
  else min |2 * E c| |2 * E c - 2 * Int.sign (dotR F2 E c)|

/-- **(Λ)** of `rem:accounting`: `|ℓ(E)| > √5/2`, i.e. `∑_c (2ℓ_c(E))² > 5`, for every `0 ≠ E ∈ {-2, …, 2}⁵` that
is not a binding step. -/
def LamHyp (F2 : Fin 5 → Fin 5 → ℤ) : Prop :=
  ∀ E ∈ halfSteps 5, E ∉ bind5 → 5 < ∑ c, ell2 F2 E c ^ 2

/-- The digital point set over `ℤ/pℤ` (index `n ∈ (ℤ/pℤ)⁵`, integer points in `[0, p⁵)⁵`) whose coordinate `c` has the
digits `n_c`, `(F₀ n)_c` with `F₀ = F2/2` (`½ ≡ (p+1)/2`), and `∑_d D c r d · n_d` for `r = 1, 2, 3` (so
`D₁ = fun c d => D c 1 d`); `Qstar p = halfNet p F2star Dstar`. -/
def halfNet (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) :
    (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ :=
  GFpoint 5 p 1 (halfPhi 5 p F2 D)

/-- **`δN^{1/5}`** (toroidal) of a point set `X` with `N = p⁵` points (integer points in `[0, p⁵)⁵`, indexed by
`(ℤ/pℤ)⁵`): `N^{1/5} = p` times the least toroidal distance of two points with distinct indices. (An infimum over
the pairs; `sepN_spec` shows that it is a minimum for `p ≥ 2`.) -/
noncomputable def sepN (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) : ℝ :=
  ⨅ xy : {xy : (Fin (5 * 1) → ZMod p) × (Fin (5 * 1) → ZMod p) // xy.1 ≠ xy.2},
    (p : ℝ) * Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((X xy.1.1 c : ℤ) - (X xy.1.2 c : ℤ)) : ℝ) /
      (p : ℝ) ^ (5 * 1)) ^ 2)

/-- **`K_eff(p)`** of `rem:accounting`: `(5p/2)(1 − δN^{1/5}/(√5/2))`. -/
noncomputable def Keff (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) : ℝ :=
  5 * (p : ℝ) / 2 * (1 - sepN p X / (Real.sqrt 5 / 2))

/-- The layer `2F₀` printed after `rem:accounting` (it satisfies (B2) and (MIN) but not (Λ)). -/
def F2cex : Fin 5 → Fin 5 → ℤ :=
  ![![-3, 1, -1, -3, -3],
    ![-3, -3, 3, 1, -1],
    ![-3, 1, -3, 3, 1],
    ![1, -1, 3, -3, 1],
    ![1, 1, 1, 1, -1]]

end Z3NetHL
