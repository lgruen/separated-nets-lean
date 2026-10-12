/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.D4D2Defs
public import Z3Net.DeficitDefs

@[expose] public section

/-!
# V14 stage S8: `prop:4D2`, kernel certificates for `K(F) = 2` and `S(F) = 7`

Full enumeration (`decide +kernel`; no `native_decide`) of the configurations of `def:K` for the
design `F4D2` of `prop:4D2` with its `L = 3` levels, coded by digits in `Fin 3` (`e_d = code - 1`,
carry class `j_d`; carry class `0` on the axes that do not move, as in the paper's count
`(2L+1)^4 - 1 = 2400`; `σ` does not depend on the carry classes of those axes). The soundness of the
coding (every configuration of `cfgs 4 3` has the `σ` of a coded one) is `Z3Net/D4D2Cert.lean`.
-/

namespace Z3NetF.Proofs.D4D2

open Finset Z3NetF

/-- Steps coded by `Fin 3` digits (`e_d = code - 1`). -/
def eC (e0 e1 e2 e3 : Fin 3) : Fin 4 → ℤ :=
  ![(e0 : ℤ) - 1, (e1 : ℤ) - 1, (e2 : ℤ) - 1, (e3 : ℤ) - 1]

/-- Carry classes coded by `Fin 3` digits. -/
def jC (j0 j1 j2 j3 : Fin 3) : Fin 4 → ℕ := ![(j0 : ℕ), j1, j2, j3]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
/-- Every coded configuration costs at most `2` (`def:K`; in particular none costs `+∞`). -/
theorem cost_le : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    cost F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) ≤ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
/-- Every coded configuration has `|σ_i| ≤ 7`. -/
theorem sigma_le : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    ∀ i, (sigma F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i).natAbs ≤ 7 := by
  decide +kernel

end Z3NetF.Proofs.D4D2
