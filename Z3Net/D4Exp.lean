/-
Proof module (stage 6, entry 4D): the expansion of `c₄(q)` in `thm:4D`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D4Defs

@[expose] public section

/-!
# `thm:4D`: `c₄(q) = 1 - 5/q + 2/q² + O(q^(-3))`

With `x = 1/q` and `α = 1 - 5x + 2x²`: `c₄(q)² = 1 - 10x + 29x² = α² + 20x³ - 4x⁴`, so `c₄ > α`, and
`c₄ ≤ α + 20x³` because `(α + 20x³)² - c₄² = 20x³ - 196x⁴ + 80x⁵ + 400x⁶ ≥ 0` for `x ≤ 1/11`.
-/

namespace Z3NetD4.Proofs

theorem c4_expansion (q : ℕ) (hq : 11 ≤ q) :
    1 - 5 / (q : ℝ) + 2 / (q : ℝ) ^ 2 < c4 q ∧
      c4 q ≤ 1 - 5 / (q : ℝ) + 2 / (q : ℝ) ^ 2 + 20 / (q : ℝ) ^ 3 := by
  have hq0 : (11 : ℝ) ≤ q := by exact_mod_cast hq
  have hK : (K4 q : ℝ) = ((q : ℝ) - 5) ^ 2 + 4 := by
    unfold K4; rw [if_neg (by omega), if_neg (by omega)]; push_cast; ring
  have hc : c4 q = Real.sqrt (1 - 10 * (1 / (q : ℝ)) + 29 * (1 / (q : ℝ)) ^ 2) := by
    unfold c4
    rw [hK]
    have hqpos : (0 : ℝ) < q := by linarith
    rw [show ((q : ℝ) - 5) ^ 2 + 4 = (q : ℝ) ^ 2 * (1 - 10 * (1 / (q : ℝ)) + 29 * (1 / (q : ℝ)) ^ 2) by
      field_simp; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hqpos.le]
    field_simp
  set x : ℝ := 1 / (q : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 11 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hq0
  have e5 : 5 / (q : ℝ) = 5 * x := by rw [hx]; ring
  have e2 : 2 / (q : ℝ) ^ 2 = 2 * x ^ 2 := by rw [hx, div_pow, one_pow]; ring
  have e20 : 20 / (q : ℝ) ^ 3 = 20 * x ^ 3 := by rw [hx, div_pow, one_pow]; ring
  rw [hc, e5, e2, e20]
  have hα : 0 < 1 - 5 * x + 2 * x ^ 2 := by nlinarith
  constructor
  · rw [Real.lt_sqrt hα.le]
    nlinarith [pow_pos hx0 3, pow_pos hx0 4]
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [pow_pos hx0 3, pow_pos hx0 4, pow_pos hx0 5, pow_pos hx0 6, mul_pos hx0 hx0]

end Z3NetD4.Proofs
