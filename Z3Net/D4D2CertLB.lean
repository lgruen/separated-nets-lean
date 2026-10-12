/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.D4D2CertKS

@[expose] public section

/-!
# V14 stage S8: `prop:4D2`, kernel certificates for the exact relaxation at `q = 17, 19, 21`

For every coded configuration (`Z3Net/D4D2CertKS.lean`) of `lem:Ss` with `L = 3` levels,
`∑_i b_i² ≥ (q - 2)²` (`decide +kernel`; no `native_decide`).
-/

namespace Z3NetF.Proofs.D4D2

open Finset Z3NetF

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
theorem bnd17 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    (15 : ℤ) ^ 2 ≤ ∑ i, bval 17 F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
theorem bnd19 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    (17 : ℤ) ^ 2 ≤ ∑ i, bval 19 F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
theorem bnd21 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    (19 : ℤ) ^ 2 ≤ ∑ i, bval 21 F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

end Z3NetF.Proofs.D4D2
