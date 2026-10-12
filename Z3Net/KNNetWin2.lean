module
public import Z3Net.KNNetPoly

@[expose] public section

/-!
# Window entries of the frame's graph form, `m = 3k + 2` (KN entry, `KN2_net`)

Depths `K = (k+1, k+1, k)`, offsets `0, k+1, 2k+2`.  The needed window columns of the graph form
of the frame `(φ_∞, φ_0, φ_1)` are the polynomials (`S = (-1)^k`, `a = k`)

* `x_k : t^(k+1) (t-1)^k`, `x_{k-1} : t^(k+1) (t-1)^k (t + a)`,
* `y_k : S t^k (t-1)^k`, `y_{k-1} : S t^(k-1) (t-1)^k (1 + a t)`,
* `z_{k-1} : t^(k+1) (t-1)^(k-1)`

(`lem:ppinv`(b) of the paper): their coarse digits are unit vectors, and their offset digits are
the window entries.
-/

namespace Z3NetKN.Win

open Polynomial Z3NetKN.Phi Z3NetKN.Realize Z3NetKN.Frame

variable {F : Type*} [Field F]

lemma natDeg_Xm1_pow (b : ℕ) : ((X - 1 : F[X]) ^ b).natDegree ≤ b :=
  calc ((X - 1 : F[X]) ^ b).natDegree ≤ b * (X - 1 : F[X]).natDegree := natDegree_pow_le
    _ ≤ b * 1 := by gcongr; exact natDegree_sub_le_of_le natDegree_X_le natDegree_one.le
    _ = b := mul_one b

lemma natDeg_shape (a b : ℕ) (Q : F[X]) :
    (X ^ a * ((X - 1) ^ b * Q)).natDegree ≤ a + b + Q.natDegree := by
  calc (X ^ a * ((X - 1) ^ b * Q)).natDegree
      ≤ (X ^ a : F[X]).natDegree + ((X - 1) ^ b * Q).natDegree := natDegree_mul_le
    _ ≤ a + (((X - 1 : F[X]) ^ b).natDegree + Q.natDegree) := by
        gcongr
        · exact natDegree_X_pow_le a
        · exact natDegree_mul_le
    _ ≤ a + (b + Q.natDegree) := by gcongr; exact natDeg_Xm1_pow b
    _ = a + b + Q.natDegree := by ring

lemma natDeg_C_mul_le (s : F) (P : F[X]) : (C s * P).natDegree ≤ P.natDegree :=
  natDegree_C_mul_le s P

lemma shape_comp (a b : ℕ) (Q : F[X]) :
    (X ^ a * ((X - 1) ^ b * Q)).comp (X + 1) = X ^ b * ((X + 1) ^ a * Q.comp (X + 1)) := by
  simp only [mul_comp, pow_comp, X_comp, sub_comp, one_comp, add_sub_cancel_right]
  ring

lemma coeff_hi (W : F[X]) (N j : ℕ) (hW : W.natDegree ≤ N) (hj : N < j) : W.coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by omega)

lemma natDeg_lin (a : F) : (X + C a).natDegree ≤ 1 := by rw [natDegree_X_add_C]

lemma natDeg_lin' (a : F) : (1 + C a * X).natDegree ≤ 1 := by
  calc (1 + C a * X).natDegree ≤ max (1 : F[X]).natDegree (C a * X).natDegree := natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · exact (natDegree_C_mul_le a X).trans natDegree_X_le

section R2

variable (k : ℕ)

lemma d2_0 : depth 2 k 0 = k + 1 := by simp [depth]
lemma d2_1 : depth 2 k 1 = k + 1 := by simp [depth]
lemma d2_2 : depth 2 k 2 = k := by simp [depth]
lemma o2_0 : offK (depth 2 k) 0 = 0 := by simp [offK]
lemma o2_1 : offK (depth 2 k) 1 = k + 1 := by simp [offK, depth]
lemma o2_2 : offK (depth 2 k) 2 = 2 * k + 2 := by simp [offK, depth]; ring

lemma hK2 : depth 2 k 0 + depth 2 k 1 + depth 2 k 2 = 3 * k + 2 := depth_sum 2 k (by norm_num)

local notation "G2" kk:max c:max => (G0 (F := F) (m := 3 * kk + 2) (depth 2 kk) c)

/-- Column `x_k`: `t^(k+1) (t-1)^k`. -/
lemma win2_xk :
    ent (G2 k 1) (k + 1) k = (-1) ^ k ∧ ent (G2 k 2) k k = 1 ∧ ent (G2 k 2) (k + 1) k = (k : F) + 1 := by
  set W : F[X] := X ^ (k + 1) * ((X - 1) ^ k * 1) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 1 := by
    rw [hWd]; have := natDeg_shape (k + 1) k (1 : F[X]); simp only [natDegree_one] at this; omega
  have hc := phi_col' (depth 2 k) (hK2 k) W (by omega) k (by omega)
    (by
      intro j hj; rw [d2_0] at hj; rw [o2_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at (k + 1) _ k _ (by omega), mul_one, cXm1_top]
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d2_1] at hj; rw [o2_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d2_2] at hj
      rw [o2_2, if_neg (by omega), hWd, shape_comp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.2.1 (k + 1) (by omega), hWd, cXpow_at (k + 1) (k + 1) 0 _ (by omega), mul_one,
      cXm1_zero]
  · rw [hc.2.2 k (by omega), hWd, shape_comp, cXpow_at k k 0 _ (by omega), one_comp, mul_one,
      cXp1_zero]
  · rw [hc.2.2 (k + 1) (by omega), hWd, shape_comp, cXpow_at k (k + 1) 1 _ (by omega), one_comp,
      mul_one, cXp1_one]
    push_cast; ring

/-- Column `x_{k-1}`: `t^(k+1) (t-1)^k (t + k)`. -/
lemma win2_xk1 (k : ℕ) :
    ent (G2 (k + 1) 1) (k + 2) k = (-1) ^ (k + 1) * ((k : F) + 1) ∧
    ent (G2 (k + 1) 2) (k + 1) k = (k : F) + 2 ∧
    ent (G2 (k + 1) 2) (k + 2) k = ((k : F) + 1) ^ 2 + 2 * ((k : F) + 1) + 2 := by
  set a : F := ((k + 1 : ℕ) : F) with ha
  set W : F[X] := X ^ (k + 2) * ((X - 1) ^ (k + 1) * (X + C a)) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 4 := by
    rw [hWd]; have := natDeg_shape (k + 2) (k + 1) (X + C a); have := natDeg_lin a; omega
  have hc := phi_col' (depth 2 (k + 1)) (hK2 (k + 1)) W (by omega) k (by omega)
    (by
      intro j hj; rw [d2_0] at hj; rw [o2_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at (k + 2) _ (k + 2) _ (by omega),
          cLin_at _ _ (k + 2) (k + 1) rfl, cXm1_top, cXm1_hi _ _ (by omega)]
        ring
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, cXpow_at (k + 2) _ (k + 1) _ (by omega),
          cLin_at _ _ (k + 1) k rfl, cXm1_top1_at _ _ rfl, cXm1_top, ha]
        push_cast; ring
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d2_1] at hj; rw [o2_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d2_2] at hj
      rw [o2_2, if_neg (by omega), hWd, shape_comp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cLin_zero,
      cXm1_zero, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 1) (by omega), hWd, shape_comp, cXpow_at (k + 1) (k + 1) 0 _ (by omega),
      comp_shift_lin, cLin_zero, cXp1_zero, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hWd, shape_comp, cXpow_at (k + 1) (k + 2) 1 _ (by omega),
      comp_shift_lin, cLin_at _ _ 1 0 rfl, cXp1_zero, cXp1_one, ha]
    push_cast; ring

/-- Column `y_k`: `S t^k (t-1)^k`. -/
lemma win2_yk :
    ent (G2 k 0) (k + 1) (2 * k + 1) = (-1) ^ k ∧ ent (G2 k 2) k (2 * k + 1) = (-1) ^ k ∧
    ent (G2 k 2) (k + 1) (2 * k + 1) = (-1) ^ k * (k : F) := by
  set S : F := (-1) ^ k with hS
  set W : F[X] := C S * (X ^ k * ((X - 1) ^ k * 1)) with hWd
  have hdeg : W.natDegree ≤ 2 * k := by
    rw [hWd]; have := natDeg_shape k k (1 : F[X]); simp only [natDegree_one] at this
    have := natDeg_C_mul_le S (X ^ k * ((X - 1) ^ k * 1)); omega
  have hcomp : W.comp (X + 1) = C S * (X ^ k * ((X + 1) ^ k * 1)) := by
    rw [hWd, mul_comp, C_comp, shape_comp, one_comp]
  have hc := phi_col' (depth 2 k) (hK2 k) W (by omega) (2 * k + 1) (by omega)
    (by
      intro j hj; rw [d2_0] at hj; rw [o2_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d2_1] at hj; rw [o2_1]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, coeff_C_mul, cXpow_at k j 0 _ (by omega), mul_one, cXm1_zero,
          hS, neg_one_pow_sq]
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_lt' _ _ _ (by omega), mul_zero])
    (by
      intro j hj; rw [d2_2] at hj
      rw [o2_2, if_neg (by omega), hcomp, coeff_C_mul, cXpow_lt' _ _ _ hj, mul_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 1) (by omega), show 3 * k + 2 - 1 - (k + 1) = k + k by omega, hWd, coeff_C_mul,
      cXpow_at k (k + k) k _ rfl, mul_one, cXm1_top, mul_one]
  · rw [hc.2.2 k (by omega), hcomp, coeff_C_mul, cXpow_at k k 0 _ (by omega), mul_one, cXp1_zero,
      mul_one]
  · rw [hc.2.2 (k + 1) (by omega), hcomp, coeff_C_mul, cXpow_at k (k + 1) 1 _ (by omega), mul_one,
      cXp1_one]

/-- Column `y_{k-1}`: `S t^(k-1) (t-1)^k (1 + k t)`. -/
lemma win2_yk1 (k : ℕ) :
    ent (G2 (k + 1) 0) (k + 2) (2 * k + 2) = (-1) ^ (k + 1) * ((k : F) + 1) ∧
    ent (G2 (k + 1) 2) (k + 1) (2 * k + 2) = (-1) ^ (k + 1) * ((k : F) + 2) ∧
    ent (G2 (k + 1) 2) (k + 2) (2 * k + 2) =
      (-1) ^ (k + 1) * (((k : F) + 1) ^ 2 + ((k : F) + 1) - 1) := by
  set S : F := (-1) ^ (k + 1) with hS
  set a : F := ((k + 1 : ℕ) : F) with ha
  set W : F[X] := C S * (X ^ k * ((X - 1) ^ (k + 1) * (1 + C a * X))) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 2 := by
    rw [hWd]; have := natDeg_shape k (k + 1) (1 + C a * X); have := natDeg_lin' a
    have := natDeg_C_mul_le S (X ^ k * ((X - 1) ^ (k + 1) * (1 + C a * X))); omega
  have hcomp : W.comp (X + 1) = C S * (X ^ (k + 1) * ((X + 1) ^ k * (C (1 + a) + C a * X))) := by
    rw [hWd, mul_comp, C_comp, shape_comp, comp_shift_lin']
  have hc := phi_col' (depth 2 (k + 1)) (hK2 (k + 1)) W (by omega) (2 * k + 2) (by omega)
    (by
      intro j hj; rw [d2_0] at hj; rw [o2_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d2_1] at hj; rw [o2_1]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, coeff_C_mul, cXpow_at k j 0 _ (by omega), cLin'_zero,
          cXm1_zero, hS, neg_one_pow_sq]
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_at k j 1 _ (by omega),
          cLin'_at _ _ 1 0 rfl, cXm1_zero, cXm1_one', ha]
        push_cast; ring
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_lt' _ _ _ (by omega), mul_zero])
    (by
      intro j hj; rw [d2_2] at hj
      rw [o2_2, if_neg (by omega), hcomp, coeff_C_mul, cXpow_lt' _ _ _ hj, mul_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 2) (by omega), show 3 * (k + 1) + 2 - 1 - (k + 2) = k + (k + 2) by omega, hWd,
      coeff_C_mul, cXpow_at k _ (k + 2) _ rfl, cLin'_at _ _ (k + 2) (k + 1) rfl, cXm1_top,
      cXm1_hi _ _ (by omega), ha]
    push_cast; ring
  · rw [hc.2.2 (k + 1) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 1) (k + 1) 0 _ (by omega),
      cAff_zero, cXp1_zero, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 1) (k + 2) 1 _ (by omega),
      cAff_at _ _ _ 1 0 rfl, cXp1_zero, cXp1_one, ha]
    push_cast; ring

/-- Column `z_{k-1}`: `t^(k+1) (t-1)^(k-1)`. -/
lemma win2_zk1 (k : ℕ) :
    ent (G2 (k + 1) 0) (k + 2) (3 * k + 4) = 1 ∧
    ent (G2 (k + 1) 1) (k + 2) (3 * k + 4) = -(-1) ^ (k + 1) := by
  set W : F[X] := X ^ (k + 2) * ((X - 1) ^ k * 1) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 2 := by
    rw [hWd]; have := natDeg_shape (k + 2) k (1 : F[X]); simp only [natDegree_one] at this; omega
  have hcomp : W.comp (X + 1) = X ^ k * ((X + 1) ^ (k + 2) * 1) := by
    rw [hWd, shape_comp, one_comp]
  have hc := phi_col' (depth 2 (k + 1)) (hK2 (k + 1)) W (by omega) (3 * k + 4) (by omega)
    (by
      intro j hj; rw [d2_0] at hj; rw [o2_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d2_1] at hj; rw [o2_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ (by omega)])
    (by
      intro j hj; rw [d2_2] at hj; rw [o2_2]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hcomp, cXpow_at k j 0 _ (by omega), mul_one, cXp1_zero]
      · rw [if_neg (by omega), hcomp, cXpow_lt' _ _ _ (by omega)])
  refine ⟨?_, ?_⟩
  · rw [hc.1 (k + 2) (by omega), show 3 * (k + 1) + 2 - 1 - (k + 2) = (k + 2) + k by omega, hWd,
      cXpow_at (k + 2) _ k _ rfl, mul_one, cXm1_top]
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 2) (k + 2) 0 _ (by omega), mul_one,
      cXm1_zero, pow_succ]
    ring

end R2

end Z3NetKN.Win
