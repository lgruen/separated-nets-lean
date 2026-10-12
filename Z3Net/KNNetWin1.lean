module
public import Z3Net.KNNetWin2

@[expose] public section

/-!
# Window entries of the frame's graph form, `m = 3k + 1` (KN entry, `KN1_net`)

Depths `K = (k+1, k, k)`, offsets `0, k+1, 2k+1`.  Window columns (`S = (-1)^k`, `a = k`,
`c₂ = a(a+1)/2`), cf. `lem:ppinv`(b):

* `ξ₀ = x_k : t^k (t-1)^k`, `ξ₁ = x_{k-1} : t^k (t-1)^k (t + a)`,
  `ξ₂ = x_{k-2} : t^k (t-1)^k (t² + a t + c₂)`;
* `η₀ = y_{k-1} : S t^(k-1) (t-1)^k`, `η₁ = y_{k-2} : S t^(k-2) (t-1)^k (1 + a t)`;
* `ζ₀ = z_{k-1} : t^k (t-1)^(k-1)`, `ζ₁ = z_{k-2} : t^k (t-1)^(k-2) (1 + a - a t)`.

Each lemma is stated at a shifted `k` so that no natural subtraction occurs.
-/

namespace Z3NetKN.Win

open Polynomial Z3NetKN.Phi Z3NetKN.Realize Z3NetKN.Frame

variable {F : Type*} [Field F]

section R1

lemma d1_0 (k : ℕ) : depth 1 k 0 = k + 1 := by simp [depth]
lemma d1_1 (k : ℕ) : depth 1 k 1 = k := by simp [depth]
lemma d1_2 (k : ℕ) : depth 1 k 2 = k := by simp [depth]
lemma o1_0 (k : ℕ) : offK (depth 1 k) 0 = 0 := by simp [offK]
lemma o1_1 (k : ℕ) : offK (depth 1 k) 1 = k + 1 := by simp [offK, depth]
lemma o1_2 (k : ℕ) : offK (depth 1 k) 2 = 2 * k + 1 := by simp [offK, depth]; ring

lemma hK1 (k : ℕ) : depth 1 k 0 + depth 1 k 1 + depth 1 k 2 = 3 * k + 1 :=
  depth_sum 1 k (by norm_num)

local notation "G1" kk:max c:max => (G0 (F := F) (m := 3 * kk + 1) (depth 1 kk) c)

/-- `ξ₀ = x_k : t^k (t-1)^k`. -/
lemma win1_xi0 (k : ℕ) (hk : 1 ≤ k) :
    ent (G1 k 1) k k = (-1) ^ k ∧ ent (G1 k 1) (k + 1) k = -((-1) ^ k * (k : F)) ∧
    ent (G1 k 2) k k = 1 ∧ ent (G1 k 2) (k + 1) k = (k : F) := by
  set W : F[X] := X ^ k * ((X - 1) ^ k * 1) with hWd
  have hdeg : W.natDegree ≤ 2 * k := by
    rw [hWd]; have := natDeg_shape k k (1 : F[X]); simp only [natDegree_one] at this; omega
  have hcomp : W.comp (X + 1) = X ^ k * ((X + 1) ^ k * 1) := by rw [hWd, shape_comp, one_comp]
  have hc := phi_col' (depth 1 k) (hK1 k) W (by omega) k (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at k _ k _ (by omega), mul_one, cXm1_top]
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.2.1 k (by omega), hWd, cXpow_at k k 0 _ (by omega), mul_one, cXm1_zero]
  · rw [hc.2.1 (k + 1) (by omega), hWd, cXpow_at k (k + 1) 1 _ (by omega), mul_one, cXm1_one']
  · rw [hc.2.2 k (by omega), hcomp, cXpow_at k k 0 _ (by omega), mul_one, cXp1_zero]
  · rw [hc.2.2 (k + 1) (by omega), hcomp, cXpow_at k (k + 1) 1 _ (by omega), mul_one, cXp1_one]

/-- `ξ₁ = x_{k-1} : t^k (t-1)^k (t + a)`, at `k + 1`. -/
lemma win1_xi1 (k : ℕ) :
    ent (G1 (k + 1) 1) (k + 1) k = (-1) ^ (k + 1) * ((k : F) + 1) ∧
    ent (G1 (k + 1) 1) (k + 2) k = (-1) ^ (k + 1) * (1 - ((k : F) + 1) ^ 2) ∧
    ent (G1 (k + 1) 2) (k + 1) k = (k : F) + 2 ∧
    ent (G1 (k + 1) 2) (k + 2) k = ((k : F) + 1) ^ 2 + ((k : F) + 1) + 1 := by
  set a : F := ((k + 1 : ℕ) : F) with ha
  set W : F[X] := X ^ (k + 1) * ((X - 1) ^ (k + 1) * (X + C a)) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 3 := by
    rw [hWd]; have := natDeg_shape (k + 1) (k + 1) (X + C a); have := natDeg_lin a; omega
  have hcomp : W.comp (X + 1) = X ^ (k + 1) * ((X + 1) ^ (k + 1) * (X + C (a + 1))) := by
    rw [hWd, shape_comp, comp_shift_lin]
  have hc := phi_col' (depth 1 (k + 1)) (hK1 (k + 1)) W (by omega) k (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at (k + 1) _ (k + 2) _ (by omega),
          cLin_at _ _ (k + 2) (k + 1) rfl, cXm1_top, cXm1_hi _ _ (by omega)]
        ring
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, cXpow_at (k + 1) _ (k + 1) _ (by omega),
          cLin_at _ _ (k + 1) k rfl, cXm1_top1_at _ _ rfl, cXm1_top, ha]
        push_cast; ring
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.2.1 (k + 1) (by omega), hWd, cXpow_at (k + 1) (k + 1) 0 _ (by omega), cLin_zero,
      cXm1_zero, ha]
    push_cast; ring
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 1) (k + 2) 1 _ (by omega),
      cLin_at _ _ 1 0 rfl, cXm1_zero, cXm1_one', ha]
    push_cast; ring
  · rw [hc.2.2 (k + 1) (by omega), hcomp, cXpow_at (k + 1) (k + 1) 0 _ (by omega), cLin_zero,
      cXp1_zero, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hcomp, cXpow_at (k + 1) (k + 2) 1 _ (by omega),
      cLin_at _ _ 1 0 rfl, cXp1_zero, cXp1_one, ha]
    push_cast; ring

/-- `ξ₂ = x_{k-2} : t^k (t-1)^k (t² + a t + a(a+1)/2)`, at `k + 2`. -/
lemma win1_xi2 (k : ℕ) (h2 : (2 : F) ≠ 0) :
    ent (G1 (k + 2) 1) (k + 2) k =
      (-1) ^ (k + 2) * (((k : F) + 2) * ((k : F) + 3) / 2) ∧
    ent (G1 (k + 2) 1) (k + 3) k =
      (-1) ^ (k + 2) * (((k : F) + 2) * (1 - ((k : F) + 2) * ((k : F) + 3) / 2)) ∧
    ent (G1 (k + 2) 2) (k + 2) k = 1 + ((k : F) + 2) + ((k : F) + 2) * ((k : F) + 3) / 2 ∧
    ent (G1 (k + 2) 2) (k + 3) k = (2 + ((k : F) + 2)) +
      (1 + ((k : F) + 2) + ((k : F) + 2) * ((k : F) + 3) / 2) * ((k : F) + 2) := by
  set a : F := ((k + 2 : ℕ) : F) with ha
  set c : F := a * (a + 1) / 2 with hcd
  set W : F[X] := X ^ (k + 2) * ((X - 1) ^ (k + 2) * (X ^ 2 + C a * X + C c)) with hWd
  have hQ : (X ^ 2 + C a * X + C c : F[X]).natDegree ≤ 2 := by
    calc (X ^ 2 + C a * X + C c : F[X]).natDegree
        ≤ max (X ^ 2 + C a * X : F[X]).natDegree (C c).natDegree := natDegree_add_le _ _
      _ ≤ 2 := by
          apply max_le _ (by simp)
          calc (X ^ 2 + C a * X : F[X]).natDegree
              ≤ max (X ^ 2 : F[X]).natDegree (C a * X).natDegree := natDegree_add_le _ _
            _ ≤ 2 := by
                apply max_le (natDegree_X_pow_le 2)
                exact (natDegree_C_mul_le a X).trans (natDegree_X_le.trans (by norm_num))
  have hdeg : W.natDegree ≤ 2 * k + 6 := by
    rw [hWd]; have := natDeg_shape (k + 2) (k + 2) (X ^ 2 + C a * X + C c); omega
  have hcomp : W.comp (X + 1) =
      X ^ (k + 2) * ((X + 1) ^ (k + 2) * (X ^ 2 + C (2 + a) * X + C (1 + a + c))) := by
    rw [hWd, shape_comp, comp_shift_quad]
  have hc := phi_col' (depth 1 (k + 2)) (hK1 (k + 2)) W (by omega) k (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at (k + 2) _ (k + 4) _ (by omega),
          cQuad_at _ _ _ (k + 4) (k + 2) rfl, cXm1_top, cXm1_hi _ _ (by omega),
          cXm1_hi _ _ (by omega)]
        ring
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, cXpow_at (k + 2) _ (k + 3) _ (by omega),
          cQuad_at _ _ _ (k + 3) (k + 1) rfl, cXm1_top1_at _ _ rfl, cXm1_top,
          cXm1_hi _ _ (by omega), ha]
        push_cast; ring
      by_cases hjk2 : j = k + 2
      · rw [if_neg (by omega), hWd, cXpow_at (k + 2) _ (k + 2) _ (by omega),
          cQuad_at _ _ _ (k + 2) k rfl, cXm1_top1_at _ _ rfl, cXm1_top]
        have h3 := cXm1_top2 (F := F) k
        have : ((X - 1 : F[X]) ^ (k + 2)).coeff k = ((k : F) + 2) * ((k : F) + 1) / 2 := by
          field_simp; linear_combination h3
        rw [this, hcd, ha]
        push_cast
        field_simp
        ring
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cQuad_zero,
      cXm1_zero, hcd, ha]
    push_cast; ring
  · rw [hc.2.1 (k + 3) (by omega), hWd, cXpow_at (k + 2) (k + 3) 1 _ (by omega), cQuad_one,
      cXm1_zero, cXm1_one', hcd, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hcomp, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cQuad_zero,
      cXp1_zero, hcd, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 3) (by omega), hcomp, cXpow_at (k + 2) (k + 3) 1 _ (by omega), cQuad_one,
      cXp1_zero, cXp1_one, hcd, ha]
    push_cast; ring

/-- `η₀ = y_{k-1} : S t^(k-1) (t-1)^k`, at `k + 1`. -/
lemma win1_eta0 (k : ℕ) :
    ent (G1 (k + 1) 0) (k + 2) (2 * k + 2) = (-1) ^ (k + 1) ∧
    ent (G1 (k + 1) 2) (k + 1) (2 * k + 2) = (-1) ^ (k + 1) ∧
    ent (G1 (k + 1) 2) (k + 2) (2 * k + 2) = (-1) ^ (k + 1) * (k : F) := by
  set S : F := (-1) ^ (k + 1) with hS
  set W : F[X] := C S * (X ^ k * ((X - 1) ^ (k + 1) * 1)) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 1 := by
    rw [hWd]; have := natDeg_shape k (k + 1) (1 : F[X]); simp only [natDegree_one] at this
    have := natDeg_C_mul_le S (X ^ k * ((X - 1) ^ (k + 1) * 1)); omega
  have hcomp : W.comp (X + 1) = C S * (X ^ (k + 1) * ((X + 1) ^ k * 1)) := by
    rw [hWd, mul_comp, C_comp, shape_comp, one_comp]
  have hc := phi_col' (depth 1 (k + 1)) (hK1 (k + 1)) W (by omega) (2 * k + 2) (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, coeff_C_mul, cXpow_at k j 0 _ (by omega), mul_one, cXm1_zero,
          hS, neg_one_pow_sq]
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_lt' _ _ _ (by omega), mul_zero])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, coeff_C_mul, cXpow_lt' _ _ _ hj, mul_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 2) (by omega), show 3 * (k + 1) + 1 - 1 - (k + 2) = k + (k + 1) by omega, hWd,
      coeff_C_mul, cXpow_at k _ (k + 1) _ rfl, mul_one, cXm1_top, mul_one]
  · rw [hc.2.2 (k + 1) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 1) (k + 1) 0 _ (by omega),
      mul_one, cXp1_zero, mul_one]
  · rw [hc.2.2 (k + 2) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 1) (k + 2) 1 _ (by omega),
      mul_one, cXp1_one]

/-- `η₁ = y_{k-2} : S t^(k-2) (t-1)^k (1 + a t)`, at `k + 2`. -/
lemma win1_eta1 (k : ℕ) :
    ent (G1 (k + 2) 0) (k + 3) (2 * k + 3) = (-1) ^ (k + 2) * ((k : F) + 2) ∧
    ent (G1 (k + 2) 2) (k + 2) (2 * k + 3) = (-1) ^ (k + 2) * ((k : F) + 3) ∧
    ent (G1 (k + 2) 2) (k + 3) (2 * k + 3) =
      (-1) ^ (k + 2) * (((k : F) + 3) * k + ((k : F) + 2)) := by
  set S : F := (-1) ^ (k + 2) with hS
  set a : F := ((k + 2 : ℕ) : F) with ha
  set W : F[X] := C S * (X ^ k * ((X - 1) ^ (k + 2) * (1 + C a * X))) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 3 := by
    rw [hWd]; have := natDeg_shape k (k + 2) (1 + C a * X); have := natDeg_lin' a
    have := natDeg_C_mul_le S (X ^ k * ((X - 1) ^ (k + 2) * (1 + C a * X))); omega
  have hcomp : W.comp (X + 1) = C S * (X ^ (k + 2) * ((X + 1) ^ k * (C (1 + a) + C a * X))) := by
    rw [hWd, mul_comp, C_comp, shape_comp, comp_shift_lin']
  have hc := phi_col' (depth 1 (k + 2)) (hK1 (k + 2)) W (by omega) (2 * k + 3) (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, coeff_C_mul, cXpow_at k j 0 _ (by omega), cLin'_zero,
          cXm1_zero, hS, neg_one_pow_sq]
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_at k j 1 _ (by omega),
          cLin'_at _ _ 1 0 rfl, cXm1_zero, cXm1_one', ha]
        push_cast; ring
      · rw [if_neg (by omega), hWd, coeff_C_mul, cXpow_lt' _ _ _ (by omega), mul_zero])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, coeff_C_mul, cXpow_lt' _ _ _ hj, mul_zero])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 3) (by omega), show 3 * (k + 2) + 1 - 1 - (k + 3) = k + (k + 3) by omega, hWd,
      coeff_C_mul, cXpow_at k _ (k + 3) _ rfl, cLin'_at _ _ (k + 3) (k + 2) rfl,
      cXm1_hi _ _ (by omega), cXm1_top, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 2) (k + 2) 0 _ (by omega),
      cAff_zero, cXp1_zero, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 3) (by omega), hcomp, coeff_C_mul, cXpow_at (k + 2) (k + 3) 1 _ (by omega),
      cAff_at _ _ _ 1 0 rfl, cXp1_zero, cXp1_one, ha]
    push_cast; ring

/-- `ζ₀ = z_{k-1} : t^k (t-1)^(k-1)`, at `k + 1`. -/
lemma win1_zeta0 (k : ℕ) :
    ent (G1 (k + 1) 0) (k + 2) (3 * k + 3) = 1 ∧
    ent (G1 (k + 1) 1) (k + 1) (3 * k + 3) = (-1) ^ k ∧
    ent (G1 (k + 1) 1) (k + 2) (3 * k + 3) = -((-1) ^ k * (k : F)) := by
  set W : F[X] := X ^ (k + 1) * ((X - 1) ^ k * 1) with hWd
  have hdeg : W.natDegree ≤ 2 * k + 1 := by
    rw [hWd]; have := natDeg_shape (k + 1) k (1 : F[X]); simp only [natDegree_one] at this; omega
  have hcomp : W.comp (X + 1) = X ^ k * ((X + 1) ^ (k + 1) * 1) := by
    rw [hWd, shape_comp, one_comp]
  have hc := phi_col' (depth 1 (k + 1)) (hK1 (k + 1)) W (by omega) (3 * k + 3) (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ (by omega)])
    (by
      intro j hj; rw [d1_2] at hj; rw [o1_2]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hcomp, cXpow_at k j 0 _ (by omega), mul_one, cXp1_zero]
      · rw [if_neg (by omega), hcomp, cXpow_lt' _ _ _ (by omega)])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 2) (by omega), show 3 * (k + 1) + 1 - 1 - (k + 2) = (k + 1) + k by omega, hWd,
      cXpow_at (k + 1) _ k _ rfl, mul_one, cXm1_top]
  · rw [hc.2.1 (k + 1) (by omega), hWd, cXpow_at (k + 1) (k + 1) 0 _ (by omega), mul_one,
      cXm1_zero]
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 1) (k + 2) 1 _ (by omega), mul_one,
      cXm1_one']

/-- `ζ₁ = z_{k-2} : t^k (t-1)^(k-2) (1 + a - a t)`, at `k + 2`. -/
lemma win1_zeta1 (k : ℕ) :
    ent (G1 (k + 2) 0) (k + 3) (3 * k + 5) = -((k : F) + 2) ∧
    ent (G1 (k + 2) 1) (k + 2) (3 * k + 5) = ((k : F) + 3) * (-1) ^ k ∧
    ent (G1 (k + 2) 1) (k + 3) (3 * k + 5) =
      -(((k : F) + 3) * ((-1) ^ k * (k : F))) - ((k : F) + 2) * (-1) ^ k := by
  set a : F := ((k + 2 : ℕ) : F) with ha
  set W : F[X] := X ^ (k + 2) * ((X - 1) ^ k * (C (1 + a) + C (-a) * X)) with hWd
  have hQ : (C (1 + a) + C (-a) * X : F[X]).natDegree ≤ 1 := by
    calc (C (1 + a) + C (-a) * X : F[X]).natDegree
        ≤ max (C (1 + a)).natDegree (C (-a) * X).natDegree := natDegree_add_le _ _
      _ ≤ 1 := max_le (by simp) ((natDegree_C_mul_le _ X).trans natDegree_X_le)
  have hdeg : W.natDegree ≤ 2 * k + 3 := by
    rw [hWd]; have := natDeg_shape (k + 2) k (C (1 + a) + C (-a) * X); omega
  have hcomp : W.comp (X + 1) = X ^ k * ((X + 1) ^ (k + 2) * (C (1 + a + -a) + C (-a) * X)) := by
    rw [hWd, shape_comp, comp_shift_aff]
  have hc := phi_col' (depth 1 (k + 2)) (hK1 (k + 2)) W (by omega) (3 * k + 5) (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0, if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ (by omega)])
    (by
      intro j hj; rw [d1_2] at hj; rw [o1_2]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hcomp, cXpow_at k j 0 _ (by omega), cAff_zero, cXp1_zero]
        ring
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hcomp, cXpow_at k j 1 _ (by omega), cAff_at _ _ _ 1 0 rfl,
          cXp1_zero, cXp1_one, ha]
        push_cast; ring
      · rw [if_neg (by omega), hcomp, cXpow_lt' _ _ _ (by omega)])
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 (k + 3) (by omega), show 3 * (k + 2) + 1 - 1 - (k + 3) = (k + 2) + (k + 1) by omega,
      hWd, cXpow_at (k + 2) _ (k + 1) _ rfl, cAff_at _ _ _ (k + 1) k rfl, cXm1_top,
      cXm1_hi _ _ (by omega), ha]
    push_cast; ring
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cAff_zero,
      cXm1_zero, ha]
    push_cast; ring
  · rw [hc.2.1 (k + 3) (by omega), hWd, cXpow_at (k + 2) (k + 3) 1 _ (by omega),
      cAff_at _ _ _ 1 0 rfl, cXm1_zero, cXm1_one', ha]
    push_cast; ring

end R1

end Z3NetKN.Win
