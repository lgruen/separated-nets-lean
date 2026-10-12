/-
Proof module (stage 6, main entry): the expansion of `c*(q)` in `thm:two`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.Defs

@[expose] public section

/-!
# `thm:two`: `c*(q) = 1 - 1/q + 1/q² - O(q^(-3))`

With `x = 1/q` and `α = 1 - x + x²`: `c*(q)² = α² - 4x³(1 - x)`, so `c*(q) < α`, and
`(α - 3x³)² ≤ c*(q)²` because `x³ (2 - 2x + 6x² - 9x³) ≥ 0` for `0 < x ≤ 1/2`.
-/

namespace Z3Net.Proofs

theorem cQ_expansion (q : ℕ) (hq : 2 ≤ q) :
    1 - 1 / (q : ℝ) + 1 / (q : ℝ) ^ 2 - 3 / (q : ℝ) ^ 3 ≤ cQ q ∧
      cQ q < 1 - 1 / (q : ℝ) + 1 / (q : ℝ) ^ 2 := by
  have hq0 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set x : ℝ := 1 / (q : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hq0
  have hqx : (q : ℝ) = 1 / x := by rw [hx, one_div_one_div]
  have hE : (1 - 1 / (q : ℝ)) ^ 2 + (((q : ℝ) - 1) ^ 2 + ((q : ℝ) - 2) ^ 2) / (q : ℝ) ^ 4 =
      (1 - x + x ^ 2) ^ 2 - 4 * x ^ 3 * (1 - x) := by
    rw [hqx]; field_simp; ring
  have e2 : 1 / (q : ℝ) ^ 2 = x ^ 2 := by rw [hx, one_div_pow]
  have e3 : 3 / (q : ℝ) ^ 3 = 3 * x ^ 3 := by rw [hx, div_pow, one_pow]; ring
  unfold cQ
  rw [hE, e2, e3]
  have hα : 0 < 1 - x + x ^ 2 := by nlinarith
  constructor
  · by_cases h : 1 - x + x ^ 2 - 3 * x ^ 3 ≤ 0
    · exact le_trans h (Real.sqrt_nonneg _)
    · push Not at h
      apply Real.le_sqrt_of_sq_le
      have : 0 ≤ x ^ 3 * (2 - 2 * x + 6 * x ^ 2 - 9 * x ^ 3) := by
        apply mul_nonneg (by positivity)
        nlinarith
      nlinarith
  · rw [Real.sqrt_lt' hα]
    have : 0 < 4 * x ^ 3 * (1 - x) := by
      apply mul_pos (by positivity); linarith
    linarith

end Z3Net.Proofs
