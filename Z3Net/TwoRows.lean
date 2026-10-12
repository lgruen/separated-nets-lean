module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.TwoPoly

@[expose] public section

/-!
# Theorem 2 (`thm:two`), part 2: the first two offset rows (`prop:rows`, `cor:rows`)

Rows `0, 1` of the frame blocks `B = Φ^F_{x,y}`, `C = Φ^F_{x,z}` in generating-function form
(`prop:rows`): with `E1 = (1-t)⁻¹`,
`B_{0,l} = [t^(k-1)] t^l E1^k`, `(B_1 + (k-1)B_0)_l = [t^(k-1)] t^l (-t E1^k)`,
`C_{0,l} = [t^(k-1)] t^l (-E1^(k+1))`, `(C_1 + (k-1)C_0)_l = [t^(k-1)] t^l E1^(k+2)`;
then the gauge `U_0`, `V` of `def:Q` (`cor:rows`).
-/

namespace Z3Net.Two

open Polynomial Finset Matrix

noncomputable section

/-! ## Low coefficients -/

lemma coeff_zero_tauL (n : ℕ) (Q : ℤ[X]) :
    (tauL n Q).coeff 0 = ∑ i ∈ range (n + 1), Q.coeff i := by
  rw [tauL_apply, finset_sum_coeff]; simp [coeff_C_mul, coeff_one_sub_X_pow]

lemma coeff_one_tauL (n : ℕ) (Q : ℤ[X]) :
    (tauL n Q).coeff 1 = -∑ i ∈ range (n + 1), Q.coeff i * ((n - i : ℕ) : ℤ) := by
  rw [tauL_apply, finset_sum_coeff, ← sum_neg_distrib]
  simp [coeff_C_mul, coeff_one_sub_X_pow]

lemma coeff_zero_one_sub_X_pow_mul (k : ℕ) (P : ℤ[X]) : ((1 - X) ^ k * P).coeff 0 = P.coeff 0 := by
  rw [mul_coeff_zero, coeff_one_sub_X_pow]; simp

lemma coeff_one_one_sub_X_pow_mul (k : ℕ) (P : ℤ[X]) :
    ((1 - X) ^ k * P).coeff 1 = P.coeff 1 - k * P.coeff 0 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [coeff_one_sub_X_pow]; ring

lemma coeff_neg_X_pow_mul (a j : ℕ) (Q : ℤ[X]) :
    ((-X) ^ a * Q).coeff j = if a ≤ j then (-1) ^ a * Q.coeff (j - a) else 0 := by
  rw [neg_pow, show ((-1 : ℤ[X]) ^ a) = C ((-1) ^ a) by simp, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul']
  split_ifs <;> simp

lemma tauL_tauL_X_pow {n i : ℕ} (h : i ≤ n) :
    tauL n (tauL n (X ^ i)) = (-X) ^ (n - i) * (1 - X) ^ i := by
  rw [tauL_X_pow h]
  have := tauL_mul (n - i) i ((1 - X) ^ (n - i)) 1 (natDegree_one_sub_X_pow_le _) (by simp)
  rw [mul_one, show n - i + i = n by omega] at this
  rw [this, tauL_one_sub_X_pow, tauL_one]

lemma tauL_tauL_eq (n : ℕ) (A : ℤ[X]) (hA : A.natDegree ≤ n) :
    tauL n (tauL n A) = ∑ l ∈ range (n + 1), C (A.coeff l) * ((-X) ^ (n - l) * (1 - X) ^ l) := by
  conv_lhs => rw [as_sum_range' A (n + 1) (by omega)]
  simp only [map_sum]
  refine sum_congr rfl fun l hl => ?_
  simp only [mem_range] at hl
  rw [← C_mul_X_pow_eq_monomial, tauL_C_mul, tauL_C_mul, tauL_tauL_X_pow (by omega)]

lemma coeff_zero_tauL_tauL (n : ℕ) (A : ℤ[X]) (hA : A.natDegree ≤ n) :
    (tauL n (tauL n A)).coeff 0 = A.coeff n := by
  rw [tauL_tauL_eq n A hA, finset_sum_coeff, sum_range_succ]
  simp only [coeff_C_mul, coeff_neg_X_pow_mul, Nat.sub_self, le_refl, if_true, pow_zero, one_mul,
    coeff_one_sub_X_pow]
  rw [sum_eq_zero]
  · simp
  · intro l hl; simp only [mem_range] at hl; rw [if_neg (by omega)]; simp

lemma coeff_one_tauL_tauL (n : ℕ) (hn : 1 ≤ n) (A : ℤ[X]) (hA : A.natDegree ≤ n) :
    (tauL n (tauL n A)).coeff 1 = -(n : ℤ) * A.coeff n - A.coeff (n - 1) := by
  rw [tauL_tauL_eq n A hA, finset_sum_coeff, show n + 1 = (n - 1) + 1 + 1 by omega,
    sum_range_succ, sum_range_succ]
  simp only [coeff_C_mul, coeff_neg_X_pow_mul, coeff_one_sub_X_pow]
  rw [sum_eq_zero]
  · rw [show n - 1 + 1 = n by omega, Nat.sub_self, if_pos (by omega), if_pos (by omega),
      show n - (n - 1) = 1 by omega]
    simp; ring
  · intro l hl; simp only [mem_range] at hl; rw [if_neg (by omega)]; simp

/-! ## Coefficients of `A_j` and the four frame rows -/

lemma coeff_Apoly (k j i : ℕ) (hi : i < k) :
    (Apoly k j).coeff i = PowerSeries.coeff i (PowerSeries.X ^ j * Gk k) := by
  rw [Apoly, PowerSeries.coeff_trunc, if_pos hi]

lemma PS_coeff_neg_one_pow_mul (n k : ℕ) (F : PowerSeries ℤ) :
    PowerSeries.coeff n ((-1) ^ k * F) = (-1) ^ k * PowerSeries.coeff n F := by
  rw [show ((-1 : PowerSeries ℤ) ^ k) = PowerSeries.C ((-1) ^ k) by simp, PowerSeries.coeff_C_mul]

lemma Gk_eq (k : ℕ) : Gk k = (-1) ^ k * E1 ^ k := rfl

/-- Partial sums of coefficients. -/
lemma sum_coeff_eq_coeff_mul_E1 (n : ℕ) (F : PowerSeries ℤ) :
    ∑ i ∈ range (n + 1), PowerSeries.coeff i F = PowerSeries.coeff n (F * E1) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [E1, PowerSeries.coeff_mk]

lemma coeff_E1_sq (j : ℕ) : PowerSeries.coeff j (E1 ^ 2) = (j : ℤ) + 1 := by
  have := PowerSeries.mk_one_pow_eq_mk_choose_add (S := ℤ) (d := 1)
  rw [E1, this, PowerSeries.coeff_mk]; simp; ring

lemma sum_coeff_weight_eq_coeff_mul_E1sq (n : ℕ) (F : PowerSeries ℤ) :
    ∑ i ∈ range (n + 1), PowerSeries.coeff i F * ((n - i : ℕ) + 1 : ℤ) =
      PowerSeries.coeff n (F * E1 ^ 2) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [coeff_E1_sq]

lemma sum_coeff_eq_coeff_mul_E1' (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ) :
    ∑ i ∈ range n, PowerSeries.coeff i F = PowerSeries.coeff (n - 1) (F * E1) := by
  rw [← sum_coeff_eq_coeff_mul_E1, show n - 1 + 1 = n by omega]

lemma sum_coeff_weight_eq_coeff_mul_E1sq' (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ) :
    ∑ i ∈ range n, PowerSeries.coeff i F * ((n - 1 - i : ℕ) + 1 : ℤ) =
      PowerSeries.coeff (n - 1) (F * E1 ^ 2) := by
  rw [← sum_coeff_weight_eq_coeff_mul_E1sq, show n - 1 + 1 = n by omega]

/-- `prop:rows`, `β₀`. -/
lemma frameB_row0 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    frameB k ⟨0, by omega⟩ l = PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * E1 ^ k) := by
  rw [frameB_eq k (by omega), vec_eq_coeff_pv (T k ^ 2 *ᵥ Yv k l), pv_T2_Yv k l (by omega)]
  show ((-X) ^ k * _).coeff (k + 0) = _
  rw [coeff_neg_X_pow_mul, if_pos (by omega), show k + 0 - k = 0 by omega]
  rw [Atil, coeff_zero_tauL_tauL _ _ (natDegree_Apoly_le k l (by omega)), coeff_Apoly _ _ _ (by omega),
    Gk_eq, mul_left_comm, PS_coeff_neg_one_pow_mul, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩,
    one_mul]

lemma frameB_digit (k : ℕ) (hk : 2 ≤ k) (r : Fin (2 * k)) (l : Fin k) :
    frameB k r l = (-1) ^ k * (tauL (k - 1) (tauL (k - 1) (Apoly k l))).coeff r := by
  rw [frameB_eq k (by omega), vec_eq_coeff_pv (T k ^ 2 *ᵥ Yv k l), pv_T2_Yv k l (by omega)]
  show ((-X) ^ k * _).coeff (k + r) = _
  rw [coeff_neg_X_pow_mul, if_pos (by omega), show k + (r : ℕ) - k = r by omega, Atil]

lemma frameC_digit (k : ℕ) (hk : 2 ≤ k) (r : Fin (2 * k)) (l : Fin k) :
    frameC k r l = (-1) ^ (k + 1) * ((1 - X) ^ k * Atil k l).coeff r := by
  rw [frameC_eq k (by omega), vec_eq_coeff_pv (T k *ᵥ Yv k l), pv_T_Yv k l (by omega)]
  show (C _ * _).coeff (k + r) = _
  rw [coeff_C_mul, mul_assoc, coeff_X_pow_mul', if_pos (by omega), show k + (r : ℕ) - k = r by omega]

lemma neg_one_pow_sq_PS (k : ℕ) : ((-1 : PowerSeries ℤ) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

lemma Gk_mul_sign (k : ℕ) : (-1) ^ k * Gk k = E1 ^ k := by
  rw [Gk_eq, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-- `prop:rows`, `β'₁ = β₁ + (k-1)β₀`. -/
lemma frameB_row1' (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    frameB k ⟨1, by omega⟩ l + ((k : ℤ) - 1) * frameB k ⟨0, by omega⟩ l =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * -(PowerSeries.X * E1 ^ k)) := by
  rw [frameB_digit k hk, frameB_digit k hk]
  show (-1) ^ k * (tauL (k - 1) (tauL (k - 1) (Apoly k l))).coeff 1 +
    ((k : ℤ) - 1) * ((-1) ^ k * (tauL (k - 1) (tauL (k - 1) (Apoly k l))).coeff 0) = _
  rw [coeff_one_tauL_tauL _ (by omega) _ (natDegree_Apoly_le k l (by omega)),
    coeff_zero_tauL_tauL _ _ (natDegree_Apoly_le k l (by omega)),
    coeff_Apoly _ _ _ (by omega), coeff_Apoly _ _ _ (by omega)]
  have hR : PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * -(PowerSeries.X * E1 ^ k)) =
      -((-1) ^ k * PowerSeries.coeff (k - 2) (PowerSeries.X ^ (l : ℕ) * Gk k)) := by
    rw [show PowerSeries.X ^ (l : ℕ) * -(PowerSeries.X * E1 ^ k) =
      -(PowerSeries.X * ((-1) ^ k * (PowerSeries.X ^ (l : ℕ) * Gk k))) by rw [← Gk_mul_sign]; ring,
      map_neg, show k - 1 = (k - 2) + 1 by omega, PowerSeries.coeff_succ_X_mul,
      PS_coeff_neg_one_pow_mul]
  rw [hR, show k - 1 - 1 = k - 2 by omega]
  push_cast [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega]
  ring

/-- `prop:rows`, `γ₀`. -/
lemma frameC_row0 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    frameC k ⟨0, by omega⟩ l =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * -(E1 ^ (k + 1))) := by
  rw [frameC_digit k hk]
  show (-1) ^ (k + 1) * ((1 - X) ^ k * Atil k l).coeff 0 = _
  rw [coeff_zero_one_sub_X_pow_mul, Atil, coeff_zero_tauL, show k - 1 + 1 = k by omega]
  rw [sum_congr rfl (fun i hi => coeff_Apoly k l i (by simpa using hi)),
    sum_coeff_eq_coeff_mul_E1' k (by omega)]
  rw [show PowerSeries.X ^ (l : ℕ) * -(E1 ^ (k + 1)) =
      (-1) ^ (k + 1) * (PowerSeries.X ^ (l : ℕ) * Gk k * E1) by
      rw [Gk_eq]; linear_combination (PowerSeries.X ^ (l : ℕ) * E1 ^ (k + 1)) * neg_one_pow_sq_PS k,
    PS_coeff_neg_one_pow_mul]

/-- `prop:rows`, `γ'₁ = γ₁ + (k-1)γ₀`. -/
lemma frameC_row1' (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    frameC k ⟨1, by omega⟩ l + ((k : ℤ) - 1) * frameC k ⟨0, by omega⟩ l =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * E1 ^ (k + 2)) := by
  rw [frameC_digit k hk, frameC_digit k hk]
  show (-1) ^ (k + 1) * ((1 - X) ^ k * Atil k l).coeff 1 +
    ((k : ℤ) - 1) * ((-1) ^ (k + 1) * ((1 - X) ^ k * Atil k l).coeff 0) = _
  rw [coeff_one_one_sub_X_pow_mul, coeff_zero_one_sub_X_pow_mul, Atil, coeff_zero_tauL,
    coeff_one_tauL, show k - 1 + 1 = k by omega]
  have hs : ∀ (f : ℕ → ℤ), ∑ i ∈ range k, (Apoly k l).coeff i * f i =
      ∑ i ∈ range k, PowerSeries.coeff i (PowerSeries.X ^ (l : ℕ) * Gk k) * f i :=
    fun f => sum_congr rfl (fun i hi => by rw [coeff_Apoly k l i (by simpa using hi)])
  have hs0 := hs (fun _ => 1)
  simp only [mul_one] at hs0
  have hsum : (-1 : ℤ) ^ (k + 1) * (-∑ i ∈ range k, (Apoly k l).coeff i * ((k - 1 - i : ℕ) : ℤ) -
      (k : ℤ) * ∑ i ∈ range k, (Apoly k l).coeff i) + ((k : ℤ) - 1) * ((-1) ^ (k + 1) *
      ∑ i ∈ range k, (Apoly k l).coeff i) =
      (-1) ^ k * ∑ i ∈ range k, (Apoly k l).coeff i * (((k - 1 - i : ℕ) : ℤ) + 1) := by
    simp only [mul_add, mul_one, sum_add_distrib, pow_succ]; ring
  rw [hsum, hs (fun i => ((k - 1 - i : ℕ) : ℤ) + 1)]
  rw [sum_coeff_weight_eq_coeff_mul_E1sq' k (by omega), ← PS_coeff_neg_one_pow_mul]
  congr 1
  rw [Gk_eq]; linear_combination (PowerSeries.X ^ (l : ℕ) * E1 ^ (k + 2)) * neg_one_pow_sq_PS k

/-! ## The column gauges `U_0`, `V` -/

lemma PS_coeff_one_sub_X_pow (n j : ℕ) :
    PowerSeries.coeff j ((1 - PowerSeries.X : PowerSeries ℤ) ^ n) = (-1) ^ j * (n.choose j : ℤ) := by
  rw [show (1 - PowerSeries.X : PowerSeries ℤ) ^ n = (((1 - X : ℤ[X]) ^ n : ℤ[X]) : PowerSeries ℤ) by
    simp, Polynomial.coeff_coe, coeff_one_sub_X_pow]

/-- Right multiplication by `U_0 = U_{(1-t)^(k+1)}` multiplies the reverse-level generating function
by `(1-t)^(k+1)`. -/
lemma sum_mul_U0 (k : ℕ) (hk : 1 ≤ k) (F : PowerSeries ℤ) (l : Fin k) :
    ∑ j : Fin k, PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * F) * U0 k j l =
      PowerSeries.coeff (k - 1 - l) (F * (1 - PowerSeries.X) ^ (k + 1)) := by
  have hl := l.isLt
  have hU : ∀ j : Fin k, U0 k j l =
      if (l : ℕ) ≤ j then (-1) ^ ((j : ℕ) - l) * ((k + 1).choose ((j : ℕ) - l) : ℤ) else 0 :=
    fun j => by simp only [U0, Fin.le_def]
  simp_rw [hU]
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.coeff (k - 1) (PowerSeries.X ^ j * F) *
    (if (l : ℕ) ≤ j then (-1) ^ (j - (l : ℕ)) * ((k + 1).choose (j - l) : ℤ) else 0)) k]
  rw [← Finset.sum_range_add_sum_Ico _ (show (l : ℕ) ≤ k by omega), Finset.sum_Ico_eq_sum_range]
  rw [Finset.sum_eq_zero (fun j hj => by simp only [mem_range] at hj; rw [if_neg (by omega)]; simp),
    zero_add, mul_comm F, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one, show k - 1 - (l : ℕ) + 1 = k - l by omega]
  refine sum_congr rfl fun b hb => ?_
  simp only [mem_range] at hb
  rw [if_pos (by omega), PowerSeries.coeff_X_pow_mul', if_pos (by omega), PS_coeff_one_sub_X_pow,
    show (l : ℕ) + b - l = b by omega, show k - 1 - ((l : ℕ) + b) = k - 1 - l - b by omega]
  ring

/-- The effect of `V` on the reverse-level generating function `h` (at `c = k-1-l`). -/
def Vrow (h : ℕ → ℤ) (c : ℕ) : ℤ :=
  if c = 0 then -h 0 else if c = 1 then h 1 else if c = 2 then -2 * h 2
  else if c = 3 then 4 * h 3 - 2 * h 2 else h c - h 3

lemma sum_mul_Vmat (k : ℕ) (h : ℕ → ℤ) (l : Fin k) :
    ∑ i : Fin k, h (k - 1 - i) * Vmat k i l = Vrow h (k - 1 - l) := by
  have hl := l.isLt
  unfold Vrow
  by_cases c0 : k - 1 - (l : ℕ) = 0
  · rw [if_pos c0, Fintype.sum_eq_single l]
    · rw [show Vmat k l l = -1 by simp only [Vmat]; split_ifs <;> omega, c0]; ring
    · intro i hi; have hi' : (i : ℕ) ≠ l := fun e => hi (Fin.ext e)
      rw [show Vmat k i l = 0 by simp only [Vmat, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c1 : k - 1 - (l : ℕ) = 1
  · rw [if_neg c0, if_pos c1, Fintype.sum_eq_single l]
    · rw [show Vmat k l l = 1 by simp only [Vmat]; split_ifs <;> omega, c1, mul_one]
    · intro i hi; have hi' : (i : ℕ) ≠ l := fun e => hi (Fin.ext e)
      rw [show Vmat k i l = 0 by simp only [Vmat, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c2 : k - 1 - (l : ℕ) = 2
  · rw [if_neg c0, if_neg c1, if_pos c2, Fintype.sum_eq_single l]
    · rw [show Vmat k l l = -2 by simp only [Vmat]; split_ifs <;> omega, c2]; ring
    · intro i hi; have hi' : (i : ℕ) ≠ l := fun e => hi (Fin.ext e)
      rw [show Vmat k i l = 0 by simp only [Vmat, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c3 : k - 1 - (l : ℕ) = 3
  · rw [if_neg c0, if_neg c1, if_neg c2, if_pos c3,
      Fintype.sum_eq_add l ⟨(l : ℕ) + 1, by omega⟩ (fun e => by simp [Fin.ext_iff] at e)]
    · rw [show Vmat k l l = 4 by simp only [Vmat]; split_ifs <;> omega,
        show Vmat k ⟨(l : ℕ) + 1, by omega⟩ l = -2 by simp only [Vmat]; split_ifs <;> omega,
        c3, show k - 1 - ((l : ℕ) + 1) = 2 by omega]
      ring
    · intro i ⟨hi1, hi2⟩
      have hi1' : (i : ℕ) ≠ l := fun e => hi1 (Fin.ext e)
      have hi2' : (i : ℕ) ≠ (l : ℕ) + 1 := fun e => hi2 (Fin.ext e)
      rw [show Vmat k i l = 0 by simp only [Vmat, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  · rw [if_neg c0, if_neg c1, if_neg c2, if_neg c3,
      Fintype.sum_eq_add l ⟨k - 4, by omega⟩ (fun e => by simp [Fin.ext_iff] at e; omega)]
    · rw [show Vmat k l l = 1 by simp only [Vmat]; split_ifs <;> omega,
        show Vmat k ⟨k - 4, by omega⟩ l = -1 by simp only [Vmat]; split_ifs <;> omega,
        show k - 1 - (k - 4) = 3 by omega]
      ring
    · intro i ⟨hi1, hi2⟩
      have hi1' : (i : ℕ) ≠ l := fun e => hi1 (Fin.ext e)
      have hi2' : (i : ℕ) ≠ k - 4 := fun e => hi2 (Fin.ext e)
      rw [show Vmat k i l = 0 by simp only [Vmat, Fin.ext_iff]; split_ifs <;> omega, mul_zero]

/-! ## `cor:rows`: rows `0, 1` of the blocks of `𝒬_{k,p}` -/

lemma Rmat_mul_row0 (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (2 * k)) (Fin k) ℤ) (j : Fin k) :
    (Rmat k * B) ⟨0, by omega⟩ j = B ⟨0, by omega⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single ⟨0, by omega⟩]
  · simp [Rmat]
  · intro i hi
    have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
    simp only [Rmat, Fin.ext_iff]; split_ifs <;> first | omega | simp

lemma Rmat_mul_row1 (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (2 * k)) (Fin k) ℤ) (j : Fin k) :
    (Rmat k * B) ⟨1, by omega⟩ j = B ⟨1, by omega⟩ j + ((k : ℤ) - 1) * B ⟨0, by omega⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add ⟨1, by omega⟩ ⟨0, by omega⟩ (by simp [Fin.ext_iff])]
  · simp [Rmat]
  · intro i ⟨hi1, hi0⟩
    have h1 : (i : ℕ) ≠ 1 := fun e => hi1 (Fin.ext e)
    have h0 : (i : ℕ) ≠ 0 := fun e => hi0 (Fin.ext e)
    simp only [Rmat, Fin.ext_iff]; split_ifs <;> first | omega | simp

/-- A row whose reverse-level generating function is `F`, after the gauge `U_* = U_0 V`. -/
lemma gauge_row (k : ℕ) (hk : 1 ≤ k) (M : Matrix (Fin (2 * k)) (Fin k) ℤ) (r : Fin (2 * k))
    (F : PowerSeries ℤ) (hM : ∀ j : Fin k, M r j = PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * F))
    (l : Fin k) :
    (M * Ustar k) r l = Vrow (fun c => PowerSeries.coeff c (F * (1 - PowerSeries.X) ^ (k + 1)))
      (k - 1 - l) := by
  rw [Ustar, ← Matrix.mul_assoc, Matrix.mul_apply, ← sum_mul_Vmat]
  refine sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, ← sum_mul_U0 k hk F i]
  simp only [hM]

lemma PS_coeff_one_sub_X (c : ℕ) :
    PowerSeries.coeff c (1 - PowerSeries.X : PowerSeries ℤ) =
      if c = 0 then 1 else if c = 1 then -1 else 0 := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X]
  split_ifs <;> simp_all

lemma E1_pow_mul_one_sub_pow (k : ℕ) :
    E1 ^ k * (1 - PowerSeries.X) ^ k = 1 := by
  rw [← mul_pow, E1_mul_one_sub, one_pow]

/-- Table of `cor:rows` (index `c = k-1-l`, the distance from the last level). -/
def tabB0 (c : ℕ) : ℤ := if c ≤ 1 then -1 else 0
def tabB1 (c : ℕ) : ℤ := if c = 1 then -1 else if c = 2 ∨ c = 3 then -2 else 0
def tabC0 (c : ℕ) : ℤ := if c = 0 then -1 else 0
def tabC1 (c : ℕ) : ℤ :=
  if c = 0 then 1 else if c = 1 then -1 else if c = 2 then 2 else if c = 3 then -2 else 0

lemma QB_row0 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    (Rmat k * frameB k * Ustar k) ⟨0, by omega⟩ l = tabB0 (k - 1 - l) := by
  rw [gauge_row k (by omega) _ _ (E1 ^ k) (fun j => by
    rw [Rmat_mul_row0 k (by omega), frameB_row0 k hk])]
  rw [pow_succ (1 - PowerSeries.X), ← mul_assoc, E1_pow_mul_one_sub_pow, one_mul]
  simp only [PS_coeff_one_sub_X, Vrow, tabB0]
  split_ifs <;> first | contradiction | omega | simp

lemma QB_row1 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    (Rmat k * frameB k * Ustar k) ⟨1, by omega⟩ l = tabB1 (k - 1 - l) := by
  rw [gauge_row k (by omega) _ _ (-(PowerSeries.X * E1 ^ k)) (fun j => by
    rw [Rmat_mul_row1 k (by omega), frameB_row1' k hk])]
  rw [show -(PowerSeries.X * E1 ^ k) * (1 - PowerSeries.X) ^ (k + 1) =
      -(PowerSeries.X * (1 - PowerSeries.X)) * (E1 ^ k * (1 - PowerSeries.X) ^ k) by ring,
    E1_pow_mul_one_sub_pow, mul_one]
  have hc : ∀ c : ℕ, PowerSeries.coeff c (-(PowerSeries.X * (1 - PowerSeries.X)) : PowerSeries ℤ) =
      if c = 1 then -1 else if c = 2 then 1 else 0 := by
    intro c
    rcases c with _ | c
    · simp
    · rw [map_neg, PowerSeries.coeff_succ_X_mul, PS_coeff_one_sub_X]
      split_ifs <;> simp_all
  simp only [hc, Vrow, tabB1]
  split_ifs <;> first | contradiction | omega | simp

lemma QC_row0 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    (-(Rmat k * frameC k * Ustar k)) ⟨0, by omega⟩ l = tabC0 (k - 1 - l) := by
  rw [Matrix.neg_apply, gauge_row k (by omega) _ _ (-(E1 ^ (k + 1))) (fun j => by
    rw [Rmat_mul_row0 k (by omega), frameC_row0 k hk])]
  rw [neg_mul, ← mul_pow, E1_mul_one_sub, one_pow]
  simp only [map_neg, PowerSeries.coeff_one, Vrow, tabC0]
  split_ifs <;> first | contradiction | omega | simp

lemma QC_row1 (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    (-(Rmat k * frameC k * Ustar k)) ⟨1, by omega⟩ l = tabC1 (k - 1 - l) := by
  rw [Matrix.neg_apply, gauge_row k (by omega) _ _ (E1 ^ (k + 2)) (fun j => by
    rw [Rmat_mul_row1 k (by omega), frameC_row1' k hk])]
  rw [show E1 ^ (k + 2) * (1 - PowerSeries.X) ^ (k + 1) = E1 * (E1 * (1 - PowerSeries.X)) ^ (k + 1) by
    rw [mul_pow]; ring, E1_mul_one_sub, one_pow, mul_one]
  simp only [E1, PowerSeries.coeff_mk, Pi.one_apply, Vrow, tabC1]
  split_ifs <;> first | contradiction | omega | simp

/-- Relative position `d - c` of block `Φ_cd` in the circulant graph form. -/
lemma QPhiOf_self (k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c : Fin 3) :
    QPhiOf k B C c c = Astar k := by simp [QPhiOf]

lemma QPhiOf_succ (k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c : Fin 3) :
    QPhiOf k B C c (c + 1) = Rmat k * B * Ustar k := by
  fin_cases c <;> simp [QPhiOf]

lemma QPhiOf_succ2 (k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c : Fin 3) :
    QPhiOf k B C c (c + 2) = -(Rmat k * C * Ustar k) := by
  fin_cases c <;> simp [QPhiOf] <;> decide

/-- First-offset-digit table of `cor:rows` by relative position `d - c`. -/
def tab0 (rel : Fin 3) (c : ℕ) : ℤ := if rel = 1 then tabB0 c else tabC0 c

/-- Second-offset-digit table of `cor:rows` by relative position `d - c`. -/
def tab1 (rel : Fin 3) (c : ℕ) : ℤ := if rel = 0 then 0 else if rel = 1 then tabB1 c else tabC1 c

lemma tab0_zero (c : ℕ) : tab0 0 c = tabC0 c := rfl
lemma tab0_one (c : ℕ) : tab0 1 c = tabB0 c := rfl
lemma tab0_two (c : ℕ) : tab0 2 c = tabC0 c := rfl
lemma tab1_zero (c : ℕ) : tab1 0 c = 0 := rfl
lemma tab1_one (c : ℕ) : tab1 1 c = tabB1 c := rfl
lemma tab1_two (c : ℕ) : tab1 2 c = tabC1 c := rfl

/-- **`cor:rows`, row 0.** -/
theorem QPhi_row0 (k : ℕ) (hk : 2 ≤ k) (c d : Fin 3) (l : Fin k) :
    QPhiOf k (frameB k) (frameC k) c d ⟨0, by omega⟩ l = tab0 (d - c) (k - 1 - l) := by
  have hl := l.isLt
  obtain ⟨i, rfl⟩ : ∃ i : Fin 3, d = c + i := ⟨d - c, by abel⟩
  rw [show c + i - c = i by abel]
  fin_cases i
  · simp only [Fin.zero_eta, add_zero, QPhiOf_self, Astar, tab0_zero, tabC0]
    simp only [true_and]; split_ifs <;> omega
  · simp only [Fin.mk_one, QPhiOf_succ, tab0_one]; exact QB_row0 k hk l
  · simp only [Fin.reduceFinMk, QPhiOf_succ2, tab0_two]; exact QC_row0 k hk l

/-- **`cor:rows`, row 1.** -/
theorem QPhi_row1 (k : ℕ) (hk : 2 ≤ k) (c d : Fin 3) (l : Fin k) :
    QPhiOf k (frameB k) (frameC k) c d ⟨1, by omega⟩ l = tab1 (d - c) (k - 1 - l) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 3, d = c + i := ⟨d - c, by abel⟩
  rw [show c + i - c = i by abel]
  fin_cases i
  · simp [QPhiOf_self, Astar, tab1_zero]
  · simp only [Fin.mk_one, QPhiOf_succ, tab1_one]; exact QB_row1 k hk l
  · simp only [Fin.reduceFinMk, QPhiOf_succ2, tab1_two]; exact QC_row1 k hk l

/-- The own blocks `Φ_cc = A_*` vanish below row `0`. -/
theorem QPhi_self_row (k : ℕ) (c : Fin 3) (r : Fin (2 * k)) (hr : (r : ℕ) ≠ 0) (l : Fin k) :
    QPhiOf k (frameB k) (frameC k) c c r l = 0 := by
  simp [QPhiOf_self, Astar, hr]

end

end Z3Net.Two
