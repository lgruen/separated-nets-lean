/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# Theorem A, generic parts: covering radius of a graph form, real form of a separation bound

V14 stage S3. Factored out of the design-`U_s` proofs (`Z3Net/SUCover.lean`, which now uses
them) so that Theorem A (`Z3Net/ThmAMain.lean`) and `thm:U` share them.

* `cover_of_cells`: if every cell `∏_c [a_c q^(-k), (a_c+1) q^(-k))` of the integer points
  `X v ∈ ℕ^s` (scale `q^(sk)`) holds a point, every `x ∈ [0,1]^s` is within Euclidean distance
  `√s q^(-k)` of a point (no condition on `q ≥ 2` beyond that, and no net property).
* `sep_real_of_int`: the integer form `q^(2(sk-k)) (q-a)² ≤ q² S` of a separation bound gives
  `(1 - a/q) N^(-1/s) ≤ √(S / N²)`, `N = q^(sk)`.
-/

namespace Z3NetA.Proofs

open Finset

theorem cover_of_cells {ι : Type*} {s q k : ℕ} (hs : 1 ≤ s) (hq : 2 ≤ q) (X : ι → Fin s → ℕ)
    (hX : ∀ a : Fin s → ℕ, (∀ c, a c < q ^ k) → ∃ v, ∀ c, X v c / q ^ (s * k - k) = a c)
    (x : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v, ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by
  have hG : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  let a : Fin s → ℕ := fun c => min ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1)
  have ha : ∀ c, a c < q ^ k := fun c => lt_of_le_of_lt (min_le_right _ _) (by omega)
  obtain ⟨v, hv⟩ := hX a ha
  refine ⟨v, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hGpos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqpos k
  have key : ∀ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ 1 / ((q : ℝ) ^ k) ^ 2 := by
    intro c
    set Xc := X v c
    have hdiv : Xc / q ^ (s * k - k) = a c := hv c
    set y := x c * (q : ℝ) ^ k
    set z := (Xc : ℝ) / (q : ℝ) ^ (s * k - k)
    have hy0 : 0 ≤ y := mul_nonneg (hx c).1 hGpos.le
    have hay : (a c : ℝ) ≤ y := by
      have : a c ≤ ⌊y⌋₊ := min_le_left _ _
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0)
    have hya : y ≤ (a c : ℝ) + 1 := by
      by_cases hfl : ⌊y⌋₊ ≤ q ^ k - 1
      · have : a c = ⌊y⌋₊ := min_eq_left hfl
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · have hfl' : ¬ ⌊x c * (q : ℝ) ^ k⌋₊ ≤ q ^ k - 1 := hfl
        have : a c = q ^ k - 1 := min_eq_right (by omega)
        rw [this, Nat.cast_sub hG]
        have : y ≤ (q : ℝ) ^ k := by
          have := mul_le_mul_of_nonneg_right (hx c).2 hGpos.le
          simpa [y] using this
        push_cast; linarith
    have hQ : (0 : ℝ) < (q : ℝ) ^ (s * k - k) := pow_pos hqpos _
    have hXeq : (Xc : ℝ) = (q : ℝ) ^ (s * k - k) * (a c) + (Xc % q ^ (s * k - k) : ℕ) := by
      have := Nat.div_add_mod Xc (q ^ (s * k - k))
      rw [hdiv] at this
      exact_mod_cast this.symm
    have hrem : ((Xc % q ^ (s * k - k) : ℕ) : ℝ) < (q : ℝ) ^ (s * k - k) := by
      exact_mod_cast Nat.mod_lt _ (pow_pos (by omega) _)
    have haz : (a c : ℝ) ≤ z := by
      rw [le_div_iff₀ hQ, hXeq]
      have : (0 : ℝ) ≤ ((Xc % q ^ (s * k - k) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hza : z ≤ (a c : ℝ) + 1 := by
      rw [div_le_iff₀ hQ, hXeq]
      nlinarith
    have hxz : x c - (Xc : ℝ) / (q : ℝ) ^ (s * k) = (y - z) / (q : ℝ) ^ k := by
      have hpw : (q : ℝ) ^ (s * k) = (q : ℝ) ^ (s * k - k) * (q : ℝ) ^ k := by
        rw [← pow_add]; congr 1; have := Nat.mul_le_mul_right k hs; omega
      simp only [y, z]
      rw [hpw]
      field_simp
    rw [hxz, div_pow, one_div, div_eq_mul_inv]
    have hsq : (y - z) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    calc (y - z) ^ 2 * (((q : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 * (((q : ℝ) ^ k) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (by positivity))
      _ = (((q : ℝ) ^ k) ^ 2)⁻¹ := by rw [one_mul]
  calc ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
      ≤ ∑ _c : Fin s, 1 / ((q : ℝ) ^ k) ^ 2 := Finset.sum_le_sum fun c _ => key c
    _ = (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by simp; ring

theorem sep_real_of_int {s q k a : ℕ} (hs : 1 ≤ s) (hq : 0 < q) (S : ℝ)
    (h : (q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) - a) ^ 2 ≤ (q : ℝ) ^ 2 * S) :
    (1 - (a : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (S / ((q : ℝ) ^ (s * k)) ^ 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hrp : ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((s * k : ℕ) : ℝ) * (-(1 / (s : ℝ))) =
      -(k : ℝ) by push_cast; field_simp, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]
  rw [hrp]
  apply Real.le_sqrt_of_sq_le
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have e0 : (1 - (a : ℝ) / q) * (1 / (q : ℝ) ^ k) = ((q : ℝ) - a) / ((q : ℝ) * (q : ℝ) ^ k) := by
    field_simp
  rw [e0, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((q : ℝ) ^ (s * k)) ^ 2 = (q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1
    have := Nat.mul_le_mul_right k hs; omega
  rw [e1]
  have hk2 : (0 : ℝ) ≤ ((q : ℝ) ^ k) ^ 2 := by positivity
  calc ((q : ℝ) - a) ^ 2 * ((q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) ^ k) ^ 2)
      = ((q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) - a) ^ 2) * ((q : ℝ) ^ k) ^ 2 := by ring
    _ ≤ ((q : ℝ) ^ 2 * S) * ((q : ℝ) ^ k) ^ 2 := mul_le_mul_of_nonneg_right h hk2
    _ = S * ((q : ℝ) * (q : ℝ) ^ k) ^ 2 := by ring

end Z3NetA.Proofs
