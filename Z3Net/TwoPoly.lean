module
public import Mathlib
public import Z3Net.Defs

@[expose] public section

/-!
# Theorem 2 (`thm:two`), part 1: the Möbius map `τ` as a polynomial map

`tauL N P = ∑_{l ≤ N} P_l (1 - X)^(N - l)` is `τ` on `ℤ[t]_{≤ N}` (`(τV)(t) = (1-t)^N V(1/(1-t))`).
Key facts: multiplicativity `τ_{a+b}(PQ) = τ_a(P) τ_b(Q)` (degree bounds `a`, `b`), hence
`τ³ = (-1)^N`; the matrix `tau m` is `tauL (m-1)` on coefficient vectors.
-/

namespace Z3Net.Two

open Polynomial Finset Matrix

noncomputable section

lemma coeff_one_sub_X_pow (j n : ℕ) :
    ((1 - X : ℤ[X]) ^ j).coeff n = (-1) ^ n * (j.choose n : ℤ) := by
  have h : (1 - X : ℤ[X]) = (-1 : ℤ[X]) * (X + C (-1)) := by simp; ring
  rw [h, mul_pow, show ((-1 : ℤ[X]) ^ j) = C ((-1) ^ j) by simp, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt n j with hnj | hnj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnj
    rw [Nat.add_sub_cancel_left, pow_add]
    have : ((-1 : ℤ) ^ d) * (-1) ^ d = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination ((-1 : ℤ) ^ n * ((n + d).choose n : ℤ)) * this
  · simp [Nat.choose_eq_zero_of_lt hnj]

/-- `τ_N` as a `ℤ`-linear map on `ℤ[X]`. -/
def tauL (N : ℕ) : ℤ[X] →ₗ[ℤ] ℤ[X] where
  toFun P := ∑ l ∈ range (N + 1), C (P.coeff l) * (1 - X) ^ (N - l)
  map_add' P Q := by simp [add_mul, sum_add_distrib]
  map_smul' c P := by simp [mul_sum, smul_eq_C_mul, mul_assoc]

lemma tauL_apply (N : ℕ) (P : ℤ[X]) :
    tauL N P = ∑ l ∈ range (N + 1), C (P.coeff l) * (1 - X) ^ (N - l) := rfl

lemma tauL_monomial (N n : ℕ) (c : ℤ) :
    tauL N (monomial n c) = if n ≤ N then C c * (1 - X) ^ (N - n) else 0 := by
  rw [tauL_apply]
  simp only [coeff_monomial]
  by_cases hn : n ≤ N
  · rw [Finset.sum_eq_single n, if_pos hn]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; simp [Nat.lt_succ_iff] at h; omega
  · rw [if_neg hn]
    refine Finset.sum_eq_zero fun l hl => ?_
    simp only [mem_range] at hl
    rw [if_neg (by omega)]; simp

lemma tauL_X_pow {N i : ℕ} (h : i ≤ N) : tauL N (X ^ i) = (1 - X) ^ (N - i) := by
  rw [← monomial_one_right_eq_X_pow, tauL_monomial, if_pos h]; simp

lemma tauL_one (N : ℕ) : tauL N 1 = (1 - X) ^ N := by
  simpa using tauL_X_pow (N := N) (Nat.zero_le N)

lemma tauL_X_pow_self (N : ℕ) : tauL N (X ^ N) = 1 := by
  simpa using tauL_X_pow (le_refl N)

lemma tauL_mul (a b : ℕ) (P Q : ℤ[X]) (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b) :
    tauL (a + b) (P * Q) = tauL a P * tauL b Q := by
  conv_lhs => rw [as_sum_range' P (a + 1) (by omega), as_sum_range' Q (b + 1) (by omega),
    sum_mul_sum]
  conv_rhs => rw [as_sum_range' P (a + 1) (by omega), as_sum_range' Q (b + 1) (by omega)]
  simp only [map_sum, sum_mul_sum, monomial_mul_monomial, tauL_monomial]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  simp only [mem_range] at hi hj
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), C_mul,
    show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]
  ring

lemma natDegree_one_sub_X_le : (1 - X : ℤ[X]).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (by simp)

lemma natDegree_one_sub_X_pow_le (n : ℕ) : ((1 - X : ℤ[X]) ^ n).natDegree ≤ n :=
  (natDegree_pow_le_of_le n natDegree_one_sub_X_le).trans (by simp)

lemma natDegree_neg_X_pow_le (n : ℕ) : ((-X : ℤ[X]) ^ n).natDegree ≤ n :=
  (natDegree_pow_le_of_le (m := 1) n (by simp)).trans (by simp)

lemma tauL_one_sub_X : tauL 1 (1 - X) = -X := by
  rw [map_sub, tauL_one, show (X : ℤ[X]) = X ^ 1 by simp, tauL_X_pow_self]; ring

lemma tauL_one_sub_X_pow (n : ℕ) : tauL n ((1 - X) ^ n) = (-X) ^ n := by
  induction n with
  | zero => simpa using tauL_one 0
  | succ n ih =>
    rw [pow_succ, tauL_mul n 1 _ _ (natDegree_one_sub_X_pow_le n) natDegree_one_sub_X_le, ih,
      tauL_one_sub_X, pow_succ]

lemma natDegree_tauL_le (N : ℕ) (P : ℤ[X]) : (tauL N P).natDegree ≤ N := by
  rw [tauL_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_one_sub_X_pow_le _).trans (Nat.sub_le _ _)

lemma tauL_cube_X_pow {N i : ℕ} (h : i ≤ N) :
    tauL N (tauL N (tauL N (X ^ i))) = (-1) ^ N * X ^ i := by
  rw [tauL_X_pow h]
  have h1 : tauL N ((1 - X) ^ (N - i)) = (-X) ^ (N - i) * (1 - X) ^ i := by
    have := tauL_mul (N - i) i ((1 - X) ^ (N - i)) 1 (natDegree_one_sub_X_pow_le _) (by simp)
    rw [mul_one, show N - i + i = N by omega] at this
    rw [this, tauL_one_sub_X_pow, tauL_one]
  rw [h1]
  have h2 := tauL_mul (N - i) i ((-X) ^ (N - i)) ((1 - X) ^ i) (natDegree_neg_X_pow_le _)
    (natDegree_one_sub_X_pow_le _)
  rw [show N - i + i = N by omega] at h2
  have h3 : ((-X : ℤ[X]) ^ (N - i)) = ((-1 : ℤ) ^ (N - i)) • X ^ (N - i) := by
    rw [neg_pow, smul_eq_C_mul]; simp
  rw [h2, tauL_one_sub_X_pow, h3, LinearMap.map_smul, tauL_X_pow_self, smul_eq_C_mul,
    neg_pow (X : ℤ[X]) i]
  simp only [map_pow, map_neg, map_one]
  rw [mul_one, ← mul_assoc, ← pow_add, show N - i + i = N by omega]

lemma tauL_C_mul (N : ℕ) (c : ℤ) (P : ℤ[X]) : tauL N (C c * P) = C c * tauL N P := by
  rw [← smul_eq_C_mul, LinearMap.map_smul, smul_eq_C_mul]

lemma tauL_cube (N : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ N) :
    tauL N (tauL N (tauL N P)) = (-1) ^ N * P := by
  conv_lhs => rw [as_sum_range' P (N + 1) (by omega)]
  conv_rhs => rw [as_sum_range' P (N + 1) (by omega)]
  simp only [map_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  rw [← C_mul_X_pow_eq_monomial, tauL_C_mul, tauL_C_mul, tauL_C_mul,
    tauL_cube_X_pow (by omega)]
  ring

/-! ## Coefficient vectors -/

/-- The polynomial `∑ v_i t^i` of a coefficient vector. -/
def pv {m : ℕ} (v : Fin m → ℤ) : ℤ[X] := ∑ i : Fin m, monomial (i : ℕ) (v i)

lemma coeff_pv {m : ℕ} (v : Fin m → ℤ) (n : ℕ) :
    (pv v).coeff n = if h : n < m then v ⟨n, h⟩ else 0 := by
  unfold pv
  rw [finset_sum_coeff]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro e; exact hb (Fin.ext e)
    · simp
  · refine sum_eq_zero fun i _ => ?_
    rw [if_neg]; intro e; exact h (e ▸ i.isLt)

lemma pv_injective {m : ℕ} {u v : Fin m → ℤ} (h : pv u = pv v) : u = v := by
  funext i
  have := congrArg (fun P => P.coeff i) h
  simpa [coeff_pv] using this

lemma natDegree_pv_le {m : ℕ} (v : Fin m → ℤ) : (pv v).natDegree ≤ m - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_pv, dif_neg (by omega)]

lemma pv_smul {m : ℕ} (c : ℤ) (v : Fin m → ℤ) : pv (c • v) = C c * pv v := by
  ext n; simp [coeff_pv, coeff_C_mul]

/-- The matrix `tau m` acts on coefficient vectors as `τ_{m-1}`. -/
lemma pv_tau_mulVec {m : ℕ} (hm : 1 ≤ m) (v : Fin m → ℤ) :
    pv (tau m *ᵥ v) = tauL (m - 1) (pv v) := by
  ext n
  rw [coeff_pv, tauL_apply, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_one_sub_X_pow, coeff_pv]
  rw [show m - 1 + 1 = m by omega, Finset.sum_range (fun l =>
    (if h : l < m then v ⟨l, h⟩ else 0) * ((-1) ^ n * ((m - 1 - l).choose n : ℤ)))]
  split_ifs with h
  · simp only [Matrix.mulVec, dotProduct, tau, Fin.is_lt, dif_pos]
    refine sum_congr rfl fun l _ => ?_
    ring
  · symm
    refine sum_eq_zero fun l _ => ?_
    have hl := l.isLt
    rw [Nat.choose_eq_zero_of_lt (show m - 1 - (l : ℕ) < n by omega)]; simp

lemma pv_T_mulVec (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ℤ) :
    pv (T k *ᵥ v) = C ((-1) ^ (k + 1)) * tauL (3 * k - 1) (pv v) := by
  rw [T, Matrix.smul_mulVec, pv_smul, pv_tau_mulVec (by omega)]

lemma T_cube (k : ℕ) (hk : 1 ≤ k) : T k ^ 3 = 1 := by
  have key : ∀ v : Fin (3 * k) → ℤ, (T k ^ 3) *ᵥ v = v := by
    intro v
    rw [show T k ^ 3 = T k * (T k * T k) by rw [pow_succ', pow_two], ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    apply pv_injective
    simp only [pv_T_mulVec k hk, tauL_C_mul]
    rw [tauL_cube _ _ (natDegree_pv_le v)]
    have : ((-1 : ℤ) ^ (k + 1)) * ((-1) ^ (k + 1) * ((-1) ^ (k + 1) * (-1) ^ (3 * k - 1))) = 1 := by
      rw [← pow_add, ← pow_add, ← pow_add]
      exact Even.neg_one_pow ⟨3 * k + 1, by omega⟩
    have e2 : ∀ P : ℤ[X], C ((-1 : ℤ) ^ (k + 1)) * (C ((-1) ^ (k + 1)) * (C ((-1) ^ (k + 1)) *
        ((-1) ^ (3 * k - 1) * P))) = C (((-1 : ℤ) ^ (k + 1)) * ((-1) ^ (k + 1) * ((-1) ^ (k + 1) *
        (-1) ^ (3 * k - 1)))) * P := by intro P; simp; ring
    rw [e2, this, C_1, one_mul]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this


/-! ## The `y`-columns of the inverse of the `(k,k,k)` box matrix of the frame

The column of `B_kkk⁻¹` for the `y`-cell `e_j` is the coefficient vector of
`Y_j = (t-1)^k A_j`, `A_j = (t^j (t-1)^(-k) mod t^k)`; the `x`- and `z`-columns are `T Y_j` and
`T² Y_j` (cyclic symmetry, `T³ = 1`). -/

/-- `E1 = 1 + t + t² + ⋯ = (1-t)⁻¹`. -/
def E1 : PowerSeries ℤ := PowerSeries.mk 1

lemma E1_mul_one_sub : E1 * (1 - PowerSeries.X) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one ℤ

/-- `G_k = (t-1)^(-k) = (-1)^k E1^k`. -/
def Gk (k : ℕ) : PowerSeries ℤ := (-1) ^ k * E1 ^ k

lemma X_sub_one_pow_mul_Gk (k : ℕ) : (PowerSeries.X - 1) ^ k * Gk k = 1 := by
  rw [show (PowerSeries.X - 1 : PowerSeries ℤ) = -(1 - PowerSeries.X) by ring, neg_pow, Gk]
  calc (-1) ^ k * (1 - PowerSeries.X) ^ k * ((-1) ^ k * E1 ^ k)
      = ((-1 : PowerSeries ℤ) * (-1)) ^ k * (E1 * (1 - PowerSeries.X)) ^ k := by
        rw [mul_pow, mul_pow]; ring
    _ = 1 := by rw [E1_mul_one_sub]; simp

/-- `A_j = t^j G_k mod t^k`. -/
def Apoly (k j : ℕ) : ℤ[X] := PowerSeries.trunc k (PowerSeries.X ^ j * Gk k)

/-- `Y_j = (t-1)^k A_j`. -/
def Ypoly (k j : ℕ) : ℤ[X] := (X - 1) ^ k * Apoly k j

lemma natDegree_Apoly_le (k j : ℕ) (hk : 1 ≤ k) : (Apoly k j).natDegree ≤ k - 1 := by
  have := PowerSeries.natDegree_trunc_lt (PowerSeries.X ^ j * Gk k) (k - 1)
  rw [show k - 1 + 1 = k by omega] at this
  unfold Apoly; omega

lemma natDegree_X_sub_one_pow_le (k : ℕ) : ((X - 1 : ℤ[X]) ^ k).natDegree ≤ k :=
  (natDegree_pow_le_of_le (m := 1) k ((natDegree_sub_le _ _).trans (by simp))).trans (by simp)

lemma natDegree_Ypoly_le (k j : ℕ) (hk : 1 ≤ k) : (Ypoly k j).natDegree ≤ 3 * k - 1 :=
  (natDegree_mul_le).trans (by
    have := natDegree_X_sub_one_pow_le k; have := natDegree_Apoly_le k j hk; omega)

/-- Truncation does not change low coefficients of a product. -/
lemma coeff_mul_trunc (φ ψ : PowerSeries ℤ) {n r : ℕ} (h : r < n) :
    PowerSeries.coeff r (φ * (PowerSeries.trunc n ψ : PowerSeries ℤ)) =
      PowerSeries.coeff r (φ * ψ) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos]
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega

/-- The `y`-cell of `Y_j` is `e_j`. -/
lemma coeff_Ypoly_lt (k j r : ℕ) (hr : r < k) :
    (Ypoly k j).coeff r = if r = j then 1 else 0 := by
  rw [← Polynomial.coeff_coe, Ypoly, Polynomial.coe_mul, Apoly, coeff_mul_trunc _ _ hr]
  have : ((((X - 1 : ℤ[X]) ^ k : ℤ[X]) : PowerSeries ℤ)) * (PowerSeries.X ^ j * Gk k)
      = PowerSeries.X ^ j := by
    rw [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one,
      mul_left_comm, X_sub_one_pow_mul_Gk, mul_one]
  rw [this, PowerSeries.coeff_X_pow]

/-- `Ã_j = τ_{k-1} A_j`. -/
def Atil (k j : ℕ) : ℤ[X] := tauL (k - 1) (Apoly k j)

lemma X_sub_one_pow_eq (k : ℕ) : (X - 1 : ℤ[X]) ^ k = C ((-1) ^ k) * (1 - X) ^ k := by
  rw [show (X - 1 : ℤ[X]) = C (-1) * (1 - X) by simp, mul_pow, ← C_pow]

/-- `τ Y_j = t^k (1-t)^k Ã_j`. -/
lemma tauL_Ypoly (k j : ℕ) (hk : 1 ≤ k) :
    tauL (3 * k - 1) (Ypoly k j) = X ^ k * (1 - X) ^ k * Atil k j := by
  have h1 := tauL_mul k (2 * k - 1) ((X - 1) ^ k) (Apoly k j) (natDegree_X_sub_one_pow_le k)
    ((natDegree_Apoly_le k j hk).trans (by omega))
  rw [show k + (2 * k - 1) = 3 * k - 1 by omega] at h1
  rw [Ypoly, h1]
  have h2 := tauL_mul k (k - 1) 1 (Apoly k j) (by simp) (natDegree_Apoly_le k j hk)
  rw [show k + (k - 1) = 2 * k - 1 by omega, one_mul] at h2
  rw [h2, tauL_one, X_sub_one_pow_eq, tauL_C_mul, tauL_one_sub_X_pow, Atil, neg_pow (X : ℤ[X]) k]
  have hc : C ((-1 : ℤ) ^ k) * (-1 : ℤ[X]) ^ k = 1 := by
    rw [show (-1 : ℤ[X]) = C (-1) by simp, ← C_pow, ← C_mul, ← mul_pow]; simp
  linear_combination (X ^ k * (1 - X) ^ k * tauL (k - 1) (Apoly k j)) * hc

/-- `τ² Y_j = (-t)^k τ_{k-1}(Ã_j)`. -/
lemma tauL_tauL_Ypoly (k j : ℕ) (hk : 1 ≤ k) :
    tauL (3 * k - 1) (X ^ k * (1 - X) ^ k * Atil k j) = (-X) ^ k * tauL (k - 1) (Atil k j) := by
  have hA : (Atil k j).natDegree ≤ k - 1 := natDegree_tauL_le _ _
  have h1 := tauL_mul k (2 * k - 1) (X ^ k) ((1 - X) ^ k * Atil k j) (by simp)
    ((natDegree_mul_le).trans (by have := natDegree_one_sub_X_pow_le k; omega))
  rw [show k + (2 * k - 1) = 3 * k - 1 by omega, ← mul_assoc] at h1
  rw [h1, tauL_X_pow_self, one_mul]
  have h2 := tauL_mul k (k - 1) ((1 - X) ^ k) (Atil k j) (natDegree_one_sub_X_pow_le k) hA
  rw [show k + (k - 1) = 2 * k - 1 by omega] at h2
  rw [h2, tauL_one_sub_X_pow]

/-- The coefficient vector of `Y_j` (as a vector of length `3k`). -/
def Yv (k j : ℕ) : Fin (3 * k) → ℤ := fun i => (Ypoly k j).coeff i

lemma pv_Yv (k j : ℕ) (hk : 1 ≤ k) : pv (Yv k j) = Ypoly k j := by
  ext n
  rw [coeff_pv]
  split_ifs with h
  · rfl
  · symm; apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_Ypoly_le k j hk; omega

lemma pv_T_Yv (k j : ℕ) (hk : 1 ≤ k) :
    pv (T k *ᵥ Yv k j) = C ((-1) ^ (k + 1)) * (X ^ k * (1 - X) ^ k * Atil k j) := by
  rw [pv_T_mulVec k hk, pv_Yv k j hk, tauL_Ypoly k j hk]

lemma pv_T2_Yv (k j : ℕ) (hk : 1 ≤ k) :
    pv (T k ^ 2 *ᵥ Yv k j) = (-X) ^ k * tauL (k - 1) (Atil k j) := by
  rw [pow_two, ← mulVec_mulVec, pv_T_mulVec k hk, pv_T_Yv k j hk, tauL_C_mul,
    tauL_tauL_Ypoly k j hk, ← mul_assoc, ← C_mul, ← pow_add]
  rw [Even.neg_one_pow ⟨k + 1, rfl⟩]; simp

lemma vec_eq_coeff_pv {m : ℕ} (v : Fin m → ℤ) (i : Fin m) : v i = (pv v).coeff i := by
  rw [coeff_pv, dif_pos i.isLt]


lemma Yv_lt (k j : ℕ) (i : Fin (3 * k)) (hr : (i : ℕ) < k) :
    Yv k j i = if (i : ℕ) = j then 1 else 0 := coeff_Ypoly_lt k j i hr

lemma TYv_lt (k j : ℕ) (hk : 1 ≤ k) (i : Fin (3 * k)) (hr : (i : ℕ) < k) :
    (T k *ᵥ Yv k j) i = 0 := by
  rw [vec_eq_coeff_pv (T k *ᵥ Yv k j), pv_T_Yv k j hk, coeff_C_mul, mul_assoc, coeff_X_pow_mul',
    if_neg (by omega)]
  simp

lemma T2Yv_lt (k j : ℕ) (hk : 1 ≤ k) (i : Fin (3 * k)) (hr : (i : ℕ) < k) :
    (T k ^ 2 *ᵥ Yv k j) i = 0 := by
  rw [vec_eq_coeff_pv (T k ^ 2 *ᵥ Yv k j), pv_T2_Yv k j hk, neg_pow, mul_assoc,
    show ((-1 : ℤ[X]) ^ k) = C ((-1) ^ k) by simp, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega)]
  simp

/-- Explicit inverse of the `(k,k,k)` box matrix of the frame. -/
def Wmat (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ := fun i col =>
  if (col : ℕ) < k then (T k *ᵥ Yv k col) i
  else if (col : ℕ) < 2 * k then Yv k (col - k) i
  else (T k ^ 2 *ᵥ Yv k (col - 2 * k)) i

lemma frameGen_box_mulVec (k : ℕ) (w : Fin (3 * k) → ℤ) (r : Fin (3 * k)) :
    (boxMatrix (frameGen k) (fun _ => k) *ᵥ w) r =
      if (r : ℕ) < k then (T k ^ 2 *ᵥ w) r
      else if h : (r : ℕ) < k + k then w ⟨(r : ℕ) - k, by omega⟩
      else (T k *ᵥ w) ⟨(r : ℕ) - k - k, by omega⟩ := by
  simp only [mulVec, dotProduct, boxMatrix]
  split_ifs with h1 h2
  · simp [frameGen]
  · simp only [frameGen, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨(r : ℕ) - k, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb h.symm)]; simp
    · simp
  · simp [frameGen]

lemma T_T_mulVec (k : ℕ) (v : Fin (3 * k) → ℤ) : T k *ᵥ (T k *ᵥ v) = T k ^ 2 *ᵥ v := by
  rw [mulVec_mulVec, pow_two]

lemma T2_T_mulVec (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ℤ) : T k ^ 2 *ᵥ (T k *ᵥ v) = v := by
  rw [mulVec_mulVec, ← pow_succ, T_cube k hk, one_mulVec]

lemma T_T2_mulVec (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ℤ) : T k *ᵥ (T k ^ 2 *ᵥ v) = v := by
  rw [mulVec_mulVec, ← pow_succ', T_cube k hk, one_mulVec]

lemma T2_T2_mulVec (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ℤ) :
    T k ^ 2 *ᵥ (T k ^ 2 *ᵥ v) = T k *ᵥ v := by
  rw [mulVec_mulVec, ← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, T_cube k hk, one_mul]

lemma box_mul_Wmat (k : ℕ) (hk : 1 ≤ k) : boxMatrix (frameGen k) (fun _ => k) * Wmat k = 1 := by
  ext r col
  have hcol : (boxMatrix (frameGen k) (fun _ => k) * Wmat k) r col =
      (boxMatrix (frameGen k) (fun _ => k) *ᵥ (fun i => Wmat k i col)) r := rfl
  have hw : (fun i => Wmat k i col) = if (col : ℕ) < k then T k *ᵥ Yv k col
      else if (col : ℕ) < 2 * k then Yv k (col - k) else T k ^ 2 *ᵥ Yv k (col - 2 * k) := by
    funext i; simp only [Wmat]; split_ifs <;> rfl
  rw [hcol, hw, frameGen_box_mulVec, Matrix.one_apply]
  have hr := r.isLt; have hc := col.isLt
  by_cases c1 : (col : ℕ) < k
  · rw [if_pos c1]
    by_cases r1 : (r : ℕ) < k
    · rw [if_pos r1, T2_T_mulVec k hk, Yv_lt k _ _ r1]
      by_cases e : r = col
      · subst e; simp
      · rw [if_neg (fun h => e (Fin.ext h)), if_neg e]
    · rw [if_neg r1, if_neg (show ¬ r = col from fun h => by subst h; exact r1 c1)]
      by_cases r2 : (r : ℕ) < k + k
      · rw [dif_pos r2, TYv_lt k _ hk _ (by simp; omega)]
      · rw [dif_neg r2, T_T_mulVec, T2Yv_lt k _ hk _ (by simp; omega)]
  · by_cases c2 : (col : ℕ) < 2 * k
    · rw [if_neg c1, if_pos c2]
      by_cases r1 : (r : ℕ) < k
      · rw [if_pos r1, T2Yv_lt k _ hk _ r1, if_neg (show ¬ r = col from fun h => by subst h; exact c1 r1)]
      · rw [if_neg r1]
        by_cases r2 : (r : ℕ) < k + k
        · rw [dif_pos r2, Yv_lt k _ _ (by simp; omega)]
          by_cases e : r = col
          · subst e; simp
          · rw [if_neg e, if_neg]; intro h; apply e; apply Fin.ext; simp at h; omega
        · rw [dif_neg r2, TYv_lt k _ hk _ (by simp; omega), if_neg]
          intro h; subst h; omega
    · rw [if_neg c1, if_neg c2]
      by_cases r1 : (r : ℕ) < k
      · rw [if_pos r1, T2_T2_mulVec k hk, TYv_lt k _ hk _ r1, if_neg]; intro h; subst h; omega
      · rw [if_neg r1]
        by_cases r2 : (r : ℕ) < k + k
        · rw [dif_pos r2, T2Yv_lt k _ hk _ (by simp; omega), if_neg]; intro h; subst h; omega
        · rw [dif_neg r2, T_T2_mulVec k hk, Yv_lt k _ _ (by simp; omega)]
          by_cases e : r = col
          · subst e; simp; omega
          · rw [if_neg e, if_neg]; intro h; apply e; apply Fin.ext; simp at h; omega

lemma box_inv (k : ℕ) (hk : 1 ≤ k) : (boxMatrix (frameGen k) (fun _ => k))⁻¹ = Wmat k :=
  Matrix.inv_eq_right_inv (box_mul_Wmat k hk)

/-- Row `r`, level `l` of `B = Φ^F_{x,y}`: digit `k + r` of `T² Y_l`. -/
lemma frameB_eq (k : ℕ) (hk : 1 ≤ k) (r : Fin (2 * k)) (l : Fin k) :
    frameB k r l = (T k ^ 2 *ᵥ Yv k l) ⟨k + r, by omega⟩ := by
  unfold frameB graphBlock
  rw [box_inv k hk, ent, dif_pos ⟨by omega, by simp; omega⟩]
  simp only [frameGen, Matrix.cons_val_zero, Matrix.mul_apply, mulVec, dotProduct, Wmat]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.val_one, one_mul]
  rw [if_neg (by omega), if_pos (by omega), show k + (l : ℕ) - k = l by omega]

/-- Row `r`, level `l` of `C = Φ^F_{x,z}`: digit `k + r` of `T Y_l`. -/
lemma frameC_eq (k : ℕ) (hk : 1 ≤ k) (r : Fin (2 * k)) (l : Fin k) :
    frameC k r l = (T k *ᵥ Yv k l) ⟨k + r, by omega⟩ := by
  unfold frameC graphBlock
  rw [box_inv k hk, ent, dif_pos ⟨by omega, by simp; omega⟩, ← T2_T2_mulVec k hk]
  simp only [frameGen, Matrix.cons_val_zero, Matrix.mul_apply, mulVec, dotProduct, Wmat]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.val_two, show ((2 : Fin 3) : ℕ) = 2 from rfl]
  rw [if_neg (by omega), if_neg (by omega), show 2 * k + (l : ℕ) - 2 * k = l by omega]


end

end Z3Net.Two
