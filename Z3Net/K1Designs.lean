/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DeficitDefs

@[expose] public section

/-!
# V14 stage S2: the deficits `K₁` of the layers of `tab:practical` (`prop:k1designs`)

Kernel certificates (`decide +kernel`; no `native_decide`): `K((F₀)) = K₁` for the six printed
level-0 layers (the `(2L+1)^s - 1 = 3^s - 1` configurations of `def:K` at `L = 1`), and the Cauchy
form `λ'_c μ_d w_cd` of the off-diagonal entries of the `s = 6` frame layer.
-/

namespace Z3NetF.Proofs.K1Designs

open Z3NetF

theorem frame4_K : Kdef (layer1 k1Frame4) 1 = 2 := by decide +kernel
theorem frame5_K : Kdef (layer1 k1Frame5) 1 = 3 := by decide +kernel
theorem frame6_K : Kdef (layer1 k1Frame6) 1 = 6 := by decide +kernel
theorem free5_K : Kdef (layer1 k1Free5) 1 = 2 := by decide +kernel
theorem free6a_K : Kdef (layer1 k1Free6a) 1 = 3 := by decide +kernel
theorem free6b_K : Kdef (layer1 k1Free6b) 1 = 5 := by decide +kernel

theorem places6_ok : PlacesOK (0 : Fin 6) k1Places6 := by
  intro c d hc hd hcd
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  fin_cases c <;> fin_cases d <;> simp_all [k1Places6]

theorem frame6_cauchy (c d : Fin 6) (hcd : c ≠ d) :
    (k1Frame6 c d : ℚ) = k1Lam6 c * k1Mu6 d * wN (0 : Fin 6) k1Places6 c d := by
  fin_cases c <;> fin_cases d <;> simp_all [k1Frame6, k1Lam6, k1Mu6, wN, k1Places6] <;> norm_num

theorem free_small : (∀ c d, |k1Free5 c d| ≤ 3) ∧ (∀ c d, |k1Free6a c d| ≤ 3) := by
  decide +kernel

end Z3NetF.Proofs.K1Designs
