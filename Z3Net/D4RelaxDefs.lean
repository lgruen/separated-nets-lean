/-
Definitions of `prop:C4` (stage 11, entry Dim34), moved verbatim from `Z3Net/D4RelaxS11.lean`
(stage 13b) so that statement and proof modules import the same constants.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D4Defs

@[expose] public section

/-!
# The relaxation of `lem:Ss` for design A (`prop:C4`)

`Mpart`, `relaxSigma`, `relaxJit`, `relaxB`, `relaxLB` (verbatim copies of the definitions of
`ChallengeDim34.lean`); the value is `Z3NetD4.D4_relax_value` (`Z3Net/D4RelaxS11.lean`).
-/

namespace Z3NetD4

open Matrix Finset

/-! ## The relaxation of `lem:Ss` for design A (`prop:C4`) -/

/-- Partial sum `M^(j) = F_0 + ⋯ + F_j` of design A (`F_l = 0` for `l ≥ 3`). -/
def Mpart (j : ℕ) : Matrix (Fin 4) (Fin 4) ℤ := ∑ l ∈ range (j + 1), Fdes l

/-- `σ_i = ∑_d e_d M^(min(j_d, L-1))[i][d]` (`lem:Ss`) for a step `e` with carry lengths `j`, in
the relaxation with `L` levels of design A; for `L = 2` only `(F_0, F_1)` enter. -/
def relaxSigma (L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (i : Fin 4) : ℤ :=
  ∑ d, e d * Mpart (min (j d) (L - 1)) i d

/-- The jitter `jit_i` of `lem:Ss`: `0` if `e = ±e_i` (only axis `i` moves), `1` otherwise. -/
def relaxJit (e : Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1

/-- `b_i = min_t max(0, |e_i q + t| - jit_i)` of `lem:Ss`, `δ_i = σ_i mod q ∈ [0, q)`, the minimum
over `t ∈ {δ_i, δ_i - q}` if `δ_i ≠ 0` and over `t = 0` if `δ_i = 0`. -/
def relaxB (q L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (i : Fin 4) : ℤ :=
  if relaxSigma L e j i % (q : ℤ) = 0 then max 0 (|e i * q + 0| - relaxJit e i)
  else min (max 0 (|e i * q + relaxSigma L e j i % (q : ℤ)| - relaxJit e i))
    (max 0 (|e i * q + (relaxSigma L e j i % (q : ℤ) - q)| - relaxJit e i))

/-- `LB = min(1, min_{e,j} (∑_i b_i²)^(1/2) / q)` of `lem:Ss` for design A with `L` levels, over
the steps `e ∈ {-1,0,1}⁴ \ {0}` and all carry lengths `j` (only `min(j_d, L-1)` enters). -/
noncomputable def relaxLB (q L : ℕ) : ℝ :=
  min 1 (sInf {x : ℝ | ∃ (e : Fin 4 → ℤ) (j : Fin 4 → ℕ),
    (∀ d, e d = -1 ∨ e d = 0 ∨ e d = 1) ∧ e ≠ 0 ∧
      x = Real.sqrt (∑ i, (relaxB q L e j i : ℝ) ^ 2) / q})

end Z3NetD4
