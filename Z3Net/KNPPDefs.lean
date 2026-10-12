/-
Definitions of `def:pprelax` (stage 11, entry KNPP), moved verbatim from `Z3Net/KNPPS11.lean`
(stage 13b) so that statement and proof modules import the same constants.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.KNDefs

@[expose] public section

/-!
# `def:pprelax` (certificate), as in `ChallengeKNPP.lean`

`rlxLin`, `rlxRes`, `rlxT`, `rlxTerm`, `IsPPCert` (verbatim copies of the definitions of
`ChallengeKNPP.lean`); the bridge to `KNRelax` and `ppsep_general` are in `Z3Net/KNPPS11.lean`.
-/

namespace Z3NetKN

/-- `∑_i row|d^(i) Δ_{d,i}` for one block: `Δ_{d,0} = δ_d`, `Δ_{d,i} = sgn(δ_d) [i ≤ h_d]`
(`i ≥ 1`; window index `i`, `0` the last level). -/
def rlxLin (row : Fin 4 → ℤ) (δ : ℤ) (h : ℕ) : ℤ :=
  ∑ i : Fin 4, row i * (if (i : ℕ) = 0 then δ else if (i : ℕ) ≤ h then (if 0 < δ then 1 else -1)
    else 0)

/-- The residue in `{0, …, p-1}` of `∑_{d,i} R|d^(i) Δ_{d,i}` for a row `R` of coordinate `c`. -/
def rlxRes (p : ℕ) (rows : Fin 3 → Fin 4 → ℤ) (δ : Fin 3 → ℤ) (h : Fin 3 → ℕ) : ℤ :=
  (∑ d : Fin 3, rlxLin (rows d) (δ d) (h d)) % (p : ℤ)

/-- `min_{j ∈ A(ι)} (|b + j| - ε)⁺` with `A(ι) = {ι, ι - p}` for `ι ≠ 0`, `A(0) = {0}`. -/
def rlxT (p : ℕ) (b ι ε : ℤ) : ℕ :=
  if ι = 0 then (|b| - ε).toNat else min (|b + ι| - ε).toNat (|b + ι - p| - ε).toNat

/-- `t_c` of `def:pprelax` for the design `R` for `(p, r)` (coordinates `c < r` full). -/
def rlxTerm (p r : ℕ) (R : Rows) (δ : Fin 3 → ℤ) (h : Fin 3 → ℕ) (c : Fin 3) : ℕ :=
  if (c : ℕ) < r then
    rlxT p (p * δ c) (rlxRes p (R.jt c) δ h) (if ∀ d, d ≠ c → δ d = 0 then 0 else 1)
  else if rlxRes p (R.sk c) δ h = 0 then
    rlxT p (p * (p * δ c)) (rlxRes p (R.jt c) δ h) (if ∀ d, d ≠ c → δ d = 0 then 0 else 1)
  else min
    (rlxT p (p * (p * δ c + rlxRes p (R.sk c) δ h)) (rlxRes p (R.jt c) δ h)
      (if ∀ d, d ≠ c → δ d = 0 then 0 else 1))
    (rlxT p (p * (p * δ c + rlxRes p (R.sk c) δ h - p)) (rlxRes p (R.jt c) δ h)
      (if ∀ d, d ≠ c → δ d = 0 then 0 else 1))

/-- **`def:pprelax`** (certificate). `(T, Rg)` is a certificate for the design `R` for `(p, r)`:
`T ≤ t_x² + t_y² + t_z²` for every configuration `(δ, h)` (`δ ≠ 0`, `|δ_c| ≤ Rg_c`,
`h_c < L_c = win r c`, `h_c = 0` if `δ_c = 0`), `Rg_c < p` for all `c`, `T ≤ p² Rg_c²` for full `c`,
and `Rg_c = 1`, `T ≤ p⁴` for skeleton `c`. -/
def IsPPCert (p r : ℕ) (Rg : Fin 3 → ℕ) (R : Rows) (T : ℕ) : Prop :=
  (∀ δ : Fin 3 → ℤ, δ ≠ 0 → (∀ c, |δ c| ≤ (Rg c : ℤ)) → ∀ h : Fin 3 → ℕ, (∀ c, h c < win r c) →
      (∀ c, δ c = 0 → h c = 0) → T ≤ ∑ c : Fin 3, rlxTerm p r R δ h c ^ 2) ∧
    (∀ c, Rg c < p) ∧ (∀ c : Fin 3, (c : ℕ) < r → T ≤ (p * Rg c) ^ 2) ∧
    (∀ c : Fin 3, r ≤ (c : ℕ) → Rg c = 1 ∧ T ≤ (p * p) ^ 2)

end Z3NetKN
