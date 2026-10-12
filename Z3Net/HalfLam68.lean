module
public import Mathlib
public import Z3Net.HalfLam

@[expose] public section

/-!
# Entry Half: the `s = 6, 8` designs of `tab:half` are dominant (`half68_lam`)
-/

namespace Z3NetHL.Proofs

open Matrix Finset

theorem M6h_dom : ∀ c, M6h c c ≤ -∑ d ∈ univ.erase c, |M6h c d| := by
  decide

theorem M8h_dom : ∀ c, M8h c c ≤ -∑ d ∈ univ.erase c, |M8h c d| := by
  decide

theorem half68_lam :
    (∀ c, M6h c c ≤ -∑ d ∈ univ.erase c, |M6h c d|) ∧ halfLam M6h = Real.sqrt 6 / 2 ∧
    (∀ c, M8h c c ≤ -∑ d ∈ univ.erase c, |M8h c d|) ∧ halfLam M8h = Real.sqrt 2 := by
  refine ⟨M6h_dom, ?_, M8h_dom, ?_⟩
  · rw [half_lam_dom 6 (by norm_num) M6h M6h_dom]
    apply min_eq_left
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    rw [show Real.sqrt 2 * 2 = Real.sqrt 8 by
      rw [show (8:ℝ) = 2 * 4 by norm_num, Real.sqrt_mul (by norm_num),
        show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [half_lam_dom 8 (by norm_num) M8h M8h_dom]
    apply min_eq_right
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    rw [show ((8:ℕ):ℝ) = 2 * 4 by norm_num, Real.sqrt_mul (by norm_num),
        show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end Z3NetHL.Proofs
