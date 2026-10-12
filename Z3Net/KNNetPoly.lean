module
public import Z3Net.KNNetPhi

@[expose] public section

/-!
# Coefficient toolkit for the frame's window columns (KN entry)

Small lemmas on the coefficients of `t^a (t-1)^b Q(t)` with `Q` of degree `≤ 2`, and of its shift
`t ↦ t + 1` (the reading at the place `1`).
-/

namespace Z3NetKN.Win

open Polynomial

variable {F : Type*} [Field F]

lemma cXm1 (n j : ℕ) : ((X - 1 : F[X]) ^ n).coeff j = (-1) ^ (n - j) * (n.choose j : F) := by
  have : (X - 1 : F[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [this, coeff_X_add_C_pow]

lemma cXm1_zero (n : ℕ) : ((X - 1 : F[X]) ^ n).coeff 0 = (-1) ^ n := by
  rw [cXm1]; simp

lemma cXm1_one (n : ℕ) : ((X - 1 : F[X]) ^ (n + 1)).coeff 1 = (-1) ^ n * ((n : F) + 1) := by
  rw [cXm1]; simp

lemma cXm1_top (n : ℕ) : ((X - 1 : F[X]) ^ n).coeff n = 1 := by
  rw [cXm1]; simp

lemma cXm1_top1 (n : ℕ) : ((X - 1 : F[X]) ^ (n + 1)).coeff n = -((n : F) + 1) := by
  rw [cXm1, show n + 1 - n = 1 by omega, Nat.choose_succ_self_right]; push_cast; ring

lemma choose_two_cast (n : ℕ) :
    (((n + 2).choose n : ℕ) : F) * 2 = ((n : F) + 2) * ((n : F) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.choose_succ_succ,
      show n + 2 = (n + 1) + 1 by ring, Nat.choose_succ_self_right]
    push_cast
    rw [show n + 1 + 1 = n + 2 by ring] at *
    linear_combination ih

lemma cXm1_top2 (n : ℕ) :
    ((X - 1 : F[X]) ^ (n + 2)).coeff n * 2 = ((n : F) + 2) * ((n : F) + 1) := by
  rw [cXm1, show n + 2 - n = 2 by omega, mul_assoc, choose_two_cast]; ring

lemma cXp1 (n j : ℕ) : ((X + 1 : F[X]) ^ n).coeff j = (n.choose j : F) := coeff_X_add_one_pow F n j

lemma cXpow_lt (a j : ℕ) (P : F[X]) (h : j < a) : (X ^ a * P).coeff j = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma cXpow_add (a j : ℕ) (P : F[X]) : (X ^ a * P).coeff (a + j) = P.coeff j := by
  rw [coeff_X_pow_mul', if_pos (by omega)]; congr 1; omega

lemma cLin_succ (P : F[X]) (a : F) (j : ℕ) :
    (P * (X + C a)).coeff (j + 1) = P.coeff j + a * P.coeff (j + 1) := by
  rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C]; ring

lemma cLin_zero (P : F[X]) (a : F) : (P * (X + C a)).coeff 0 = a * P.coeff 0 := by
  rw [mul_add, coeff_add, coeff_mul_C]; simp; ring

lemma cLin'_succ (P : F[X]) (a : F) (j : ℕ) :
    (P * (1 + C a * X)).coeff (j + 1) = P.coeff (j + 1) + a * P.coeff j := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, mul_comm P (C a), mul_assoc, coeff_C_mul,
    coeff_mul_X]

lemma cLin'_zero (P : F[X]) (a : F) : (P * (1 + C a * X)).coeff 0 = P.coeff 0 := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, mul_comm P (C a), mul_assoc, coeff_C_mul]
  simp

lemma comp_shift_Xpow (a : ℕ) : ((X : F[X]) ^ a).comp (X + 1) = (X + 1) ^ a := by simp

lemma comp_shift_Xm1pow (b : ℕ) : ((X - 1 : F[X]) ^ b).comp (X + 1) = X ^ b := by simp

lemma comp_shift_lin (a : F) : (X + C a).comp (X + 1) = X + C (a + 1) := by
  simp; ring

lemma cXpow_at (a N j : ℕ) (P : F[X]) (h : N = a + j) : (X ^ a * P).coeff N = P.coeff j := by
  subst h; exact cXpow_add a j P

lemma cXpow_lt' (a N : ℕ) (P : F[X]) (h : N < a) : (X ^ a * P).coeff N = 0 := cXpow_lt a N P h

lemma cLin_at (P : F[X]) (a : F) (N j : ℕ) (h : N = j + 1) :
    (P * (X + C a)).coeff N = P.coeff j + a * P.coeff N := by
  subst h; exact cLin_succ P a j

lemma cLin'_at (P : F[X]) (a : F) (N j : ℕ) (h : N = j + 1) :
    (P * (1 + C a * X)).coeff N = P.coeff N + a * P.coeff j := by
  subst h; exact cLin'_succ P a j

lemma cXm1_top_at (n N : ℕ) (h : N = n) : ((X - 1 : F[X]) ^ n).coeff N = 1 := by
  subst h; exact cXm1_top N

lemma cXm1_top1_at (n N : ℕ) (h : n = N + 1) : ((X - 1 : F[X]) ^ n).coeff N = -((N : F) + 1) := by
  subst h; exact cXm1_top1 N

lemma cXm1_one' (n : ℕ) : ((X - 1 : F[X]) ^ n).coeff 1 = -((-1) ^ n * (n : F)) := by
  rcases n with _ | n
  · simp [coeff_one]
  · rw [cXm1_one]; push_cast; ring

lemma cXm1_hi (n N : ℕ) (h : n < N) : ((X - 1 : F[X]) ^ n).coeff N = 0 := by
  rw [cXm1, Nat.choose_eq_zero_of_lt h]; simp

lemma cXp1_zero (n : ℕ) : ((X + 1 : F[X]) ^ n).coeff 0 = 1 := by rw [cXp1]; simp

lemma cXp1_one (n : ℕ) : ((X + 1 : F[X]) ^ n).coeff 1 = n := by rw [cXp1]; simp

lemma neg_one_pow_pred (k : ℕ) (hk : 1 ≤ k) : (-1 : F) ^ (k - 1) = -(-1) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, pow_succ]; ring

lemma comp_shift_lin' (a : F) : (1 + C a * X).comp (X + 1) = C (1 + a) + C a * X := by
  simp; ring

lemma cAff_zero (P : F[X]) (c a : F) : (P * (C c + C a * X)).coeff 0 = c * P.coeff 0 := by
  rw [mul_add, coeff_add, coeff_mul_C, ← mul_assoc, mul_comm P (C a), mul_assoc, coeff_C_mul]
  simp; ring

lemma cAff_at (P : F[X]) (c a : F) (N j : ℕ) (h : N = j + 1) :
    (P * (C c + C a * X)).coeff N = c * P.coeff N + a * P.coeff j := by
  subst h
  rw [mul_add, coeff_add, coeff_mul_C, ← mul_assoc, mul_comm P (C a), mul_assoc, coeff_C_mul,
    coeff_mul_X]; ring

lemma neg_one_pow_sq (k : ℕ) : (-1 : F) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

lemma comp_shift_aff (c a : F) : (C c + C a * X).comp (X + 1) = C (c + a) + C a * X := by
  simp; ring

lemma cQuad_zero (P : F[X]) (a c : F) : (P * (X ^ 2 + C a * X + C c)).coeff 0 = c * P.coeff 0 := by
  rw [mul_add, mul_add, coeff_add, coeff_add, coeff_mul_C, ← mul_assoc, mul_comm P (C a), mul_assoc,
    coeff_C_mul, coeff_mul_X_pow']
  simp; ring

lemma cQuad_one (P : F[X]) (a c : F) :
    (P * (X ^ 2 + C a * X + C c)).coeff 1 = a * P.coeff 0 + c * P.coeff 1 := by
  rw [mul_add, mul_add, coeff_add, coeff_add, coeff_mul_C, ← mul_assoc, mul_comm P (C a), mul_assoc,
    coeff_C_mul, coeff_mul_X_pow', show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X]
  simp; ring

lemma cQuad_at (P : F[X]) (a c : F) (N j : ℕ) (h : N = j + 2) :
    (P * (X ^ 2 + C a * X + C c)).coeff N = P.coeff j + a * P.coeff (j + 1) + c * P.coeff N := by
  subst h
  rw [mul_add, mul_add, coeff_add, coeff_add, coeff_mul_C, ← mul_assoc, mul_comm P (C a), mul_assoc,
    coeff_C_mul, coeff_mul_X_pow', if_pos (by omega), show j + 2 = (j + 1) + 1 by ring, coeff_mul_X,
    show j + 1 + 1 - 2 = j by omega]
  ring

lemma comp_shift_quad (a c : F) :
    (X ^ 2 + C a * X + C c).comp (X + 1) = X ^ 2 + C (2 + a) * X + C (1 + a + c) := by
  simp only [add_comp, pow_comp, X_comp, mul_comp, C_comp]
  simp only [map_add, map_ofNat, map_one]
  ring

end Z3NetKN.Win
