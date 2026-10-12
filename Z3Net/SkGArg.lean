module
public import Mathlib

@[expose] public section

/-!
# Entry S2: the argument of a product of Gaussian integers `c_j + i`

`gauss_prod_pos`: if all `c_j > 0` (`j ∈ S`) and `∑_{j∈S} arctan(1/c_j) < π/2`, then
`∏_{j∈S} (c_j + i)` has positive real part, and positive imaginary part if `S ≠ ∅`.
Proof: `c + i = (c / cos α) e^{iα}` with `α = arctan(1/c)`, so the product is a positive real
multiple of `e^{iθ}`, `θ = ∑ α_j ∈ [0, π/2)`.
-/

namespace Z3NetF.Proofs

open Finset Complex

namespace SkG

lemma mk_one_eq_polar (c : ℤ) (hc : 0 < c) :
    (((⟨c, 1⟩ : GaussianInt)) : ℂ) =
      (((c : ℝ) / Real.cos (Real.arctan (1 / (c : ℝ))) : ℝ) : ℂ) *
        exp ((Real.arctan (1 / (c : ℝ)) : ℝ) * I) := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hcos := Real.cos_arctan_pos (1 / (c : ℝ))
  have htan := Real.tan_arctan (1 / (c : ℝ))
  rw [Real.tan_eq_sin_div_cos] at htan
  apply Complex.ext
  · rw [GaussianInt.re_toComplex, re_ofReal_mul, exp_ofReal_mul_I_re]
    field_simp
  · rw [GaussianInt.im_toComplex, im_ofReal_mul, exp_ofReal_mul_I_im]
    have hsin : Real.sin (Real.arctan (1 / (c : ℝ))) = Real.cos (Real.arctan (1 / (c : ℝ))) / c := by
      field_simp at htan ⊢; linarith
    rw [hsin]; field_simp; simp

lemma gauss_prod_pos (S : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ j ∈ S, 0 < c j)
    (harc : ∑ j ∈ S, Real.arctan (1 / (c j : ℝ)) < Real.pi / 2) :
    0 < (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).re ∧
      (S.Nonempty → 0 < (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).im) := by
  set α : ℕ → ℝ := fun j => Real.arctan (1 / (c j : ℝ)) with hα
  set R : ℕ → ℝ := fun j => (c j : ℝ) / Real.cos (α j) with hR
  set θ : ℝ := ∑ j ∈ S, α j with hθ
  have hRpos : 0 < ∏ j ∈ S, R j := by
    apply prod_pos
    intro j hj
    have := Real.cos_arctan_pos (1 / (c j : ℝ))
    have : (0 : ℝ) < c j := by exact_mod_cast hc j hj
    positivity
  have hprod : (((∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)) : GaussianInt) : ℂ) =
      ((∏ j ∈ S, R j : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
    rw [map_prod GaussianInt.toComplex]
    rw [prod_congr rfl fun j hj => mk_one_eq_polar (c j) (hc j hj)]
    rw [prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod, hθ, Complex.ofReal_sum,
      sum_mul]
  have hθ0 : 0 ≤ θ := sum_nonneg fun j hj => by
    have : (0 : ℝ) < c j := by exact_mod_cast hc j hj
    exact (Real.arctan_pos.mpr (by positivity)).le
  have hre := GaussianInt.intCast_re (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt))
  have him := GaussianInt.intCast_im (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt))
  rw [hprod, re_ofReal_mul, exp_ofReal_mul_I_re] at hre
  rw [hprod, im_ofReal_mul, exp_ofReal_mul_I_im] at him
  constructor
  · have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], harc⟩
    have : (0 : ℝ) < ((∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).re : ℝ) := by
      rw [hre]; positivity
    exact_mod_cast this
  · intro hS
    obtain ⟨j0, hj0⟩ := hS
    have hθpos : 0 < θ := by
      have h1 : α j0 ≤ θ := single_le_sum (f := α) (fun j hj => by
        have : (0 : ℝ) < c j := by exact_mod_cast hc j hj
        exact (Real.arctan_pos.mpr (by positivity)).le) hj0
      have : (0 : ℝ) < c j0 := by exact_mod_cast hc j0 hj0
      have h2 : 0 < α j0 := Real.arctan_pos.mpr (by positivity)
      linarith
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])
    have : (0 : ℝ) < ((∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).im : ℝ) := by
      rw [him]; positivity
    exact_mod_cast this

end SkG

end Z3NetF.Proofs
