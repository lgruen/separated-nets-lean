module
public import Mathlib
public import Z3Net.SUPoly

@[expose] public section

/-!
# Entry U, part 10: the constant `a_s ≤ L_s (s² + 2^(s-2))`

Every partial sum is bounded by `L_s 2^(s-2)` in the `∞` column (`∑_t binom(a_c, t) ≤ 2^(a_c)`),
by `(s-1) L_s` in a finite column (`|L_s/(a_c-a_d)^(t+1)| ≤ L_s`), and by `1` in the `∞` row.
-/

namespace Z3NetU.Proofs

open Finset Z3NetU

lemma Lcst_pos (s : ℕ) : 1 ≤ Lcst s := by
  unfold Lcst
  apply Nat.one_le_pow
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

lemma choose_sum_le (n j : ℕ) : ∑ t ∈ range (j + 1), n.choose t ≤ 2 ^ n := by
  rw [← Nat.sum_range_choose n]
  by_cases hj : j ≤ n
  · exact Finset.sum_le_sum_of_subset (range_subset_range.mpr (by omega))
  · rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ j + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Ico (n + 1) (j + 1)) (fun t ht => by
      rw [mem_Ico] at ht; exact Nat.choose_eq_zero_of_lt (by omega)), add_zero]

/-- Bound for one partial sum, depending only on the column. -/
def Bcol (s : ℕ) (d : Fin s) : ℕ := if (d : ℕ) = 0 then Lcst s * 2 ^ (s - 2) else (s - 1) * Lcst s

lemma Msum_bound (s : ℕ) (hs : 3 ≤ s) (c d : Fin s) (hcd : d ≠ c) (j : ℕ) (hj : j < s - 1) :
    (Msum s j c d).natAbs ≤ Bcol s d := by
  have hL := Lcst_pos s
  have hF : ∀ t ∈ range (j + 1), Foff s t c d =
      if (c : ℕ) = 0 then (if t = 0 then 1 else 0)
      else if (d : ℕ) = 0 then (Lcst s : ℤ) * ((((c : ℕ) - 1).choose t : ℕ) : ℤ)
      else (Lcst s : ℤ) / ((c : ℤ) - d) ^ (t + 1) := by
    intro t ht; rw [mem_range] at ht; rw [Foff, if_neg (by omega)]
  unfold Msum Bcol
  rw [Finset.sum_congr rfl hF]
  by_cases hc : (c : ℕ) = 0
  · have hd : (d : ℕ) ≠ 0 := fun h => hcd (Fin.ext (by rw [h, hc]))
    simp only [hc, if_true, if_neg hd]
    rw [Finset.sum_ite_eq' (range (j + 1)) 0, if_pos (by simp)]
    simp only [Int.natAbs_one]
    nlinarith
  · simp only [hc, if_false]
    by_cases hd : (d : ℕ) = 0
    · simp only [hd, if_true]
      rw [← Finset.mul_sum, Int.natAbs_mul, Int.natAbs_natCast]
      have h1 : (∑ t ∈ range (j + 1), ((((c : ℕ) - 1).choose t : ℕ) : ℤ)).natAbs ≤ 2 ^ (s - 2) := by
        rw [← Nat.cast_sum, Int.natAbs_natCast]
        refine (choose_sum_le _ _).trans (Nat.pow_le_pow_right (by norm_num) ?_)
        have := c.isLt; omega
      exact Nat.mul_le_mul_left _ h1
    · simp only [hd, if_false]
      refine (Int.natAbs_sum_le _ _).trans ?_
      calc ∑ t ∈ range (j + 1), ((Lcst s : ℤ) / ((c : ℤ) - d) ^ (t + 1)).natAbs
          ≤ ∑ _t ∈ range (j + 1), Lcst s := Finset.sum_le_sum fun t _ =>
            (Int.natAbs_ediv_le_natAbs _ _).trans (by simp)
        _ = (j + 1) * Lcst s := by simp
        _ ≤ (s - 1) * Lcst s := Nat.mul_le_mul_right _ (by omega)

lemma acoef_bound (s : ℕ) (hs : 3 ≤ s) (c : Fin s) :
    acoef s c ≤ Lcst s * (s ^ 2 + 2 ^ (s - 2)) := by
  have hs0 : 0 < s := by omega
  have h1 : acoef s c ≤ ∑ d, Bcol s d := by
    unfold acoef
    refine (Finset.sum_le_sum fun d hd => Finset.sup_le fun j hj =>
      Msum_bound s hs c d (by rw [mem_filter] at hd; exact hd.2) j (by simpa using hj)).trans ?_
    exact Finset.sum_le_sum_of_subset (filter_subset _ _)
  have h2 : ∑ d, Bcol s d = Lcst s * 2 ^ (s - 2) + (s - 1) * ((s - 1) * Lcst s) := by
    rw [sum_erase_c0 hs0]
    have hb0 : Bcol s (c0 hs0) = Lcst s * 2 ^ (s - 2) := by simp [Bcol, c0]
    have hrest : ∑ d ∈ univ.erase (c0 hs0), Bcol s d = (s - 1) * ((s - 1) * Lcst s) := by
      rw [Finset.sum_const_nat (m := (s - 1) * Lcst s) (fun d hd => by
        rw [mem_erase] at hd
        have : (d : ℕ) ≠ 0 := fun h => hd.1 (Fin.ext h)
        simp only [Bcol, if_neg this]), card_erase_c0]
    rw [hb0, hrest]
  rw [h2] at h1
  refine h1.trans ?_
  have : (s - 1) * ((s - 1) * Lcst s) ≤ Lcst s * s ^ 2 := by
    have := Nat.mul_le_mul (show s - 1 ≤ s by omega) (show s - 1 ≤ s by omega)
    nlinarith
  nlinarith

/-- **The constant.** `a_s ≤ L_s (s² + 2^(s-2))`. -/
theorem U_aBound (s : ℕ) (hs : 3 ≤ s) : aU s ≤ Lcst s * (s ^ 2 + 2 ^ (s - 2)) :=
  Finset.sup_le fun c _ => acoef_bound s hs c

end Z3NetU.Proofs
