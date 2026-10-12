module
public import Mathlib
public import Z3Net.D4Thm1
public import Z3Net.D4Rows

@[expose] public section

/-!
# 4D entry, part 11: the `E`-basis description is Definition N, literally

`G E = B`: the `(k,k,k,k)` box matrix `G` of the frame maps the basis vector `E_{d,j}` to the
block-diagonal matrix `B = diag(U0_d)` (cells of `E_{d,j}` vanish off `d`). `G` is invertible over
`ℚ` (Lemma T), so `Φ^F_cd U0_d = (O_c G⁻¹ B)_{block d} = (O_c E)_{block d} = Ψ_cd`, and
`U0_d = Q_d^k Toep(g_d)` is a polynomial identity (Taylor expansion of `P_d` at `a_d`; at `∞` a
reflection of `(1 - x²)^k`).
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

/-- The `(k,k,k,k)` box matrix of the frame over `ℚ`. -/
abbrev Gq (k : ℕ) : Matrix (Fin (4 * k)) (Fin (4 * k)) ℚ := boxMatrix (frameQ k) (fun _ => k)

lemma ix_surj (k : ℕ) (ρ : Fin (4 * k)) :
    ρ = ix k ⟨(ρ : ℕ) / k, Nat.div_lt_of_lt_mul (by have := ρ.isLt; omega)⟩
      ⟨(ρ : ℕ) % k, Nat.mod_lt _ (by have := ρ.isLt; omega)⟩ := by
  ext; simp [ix]; exact (Nat.div_add_mod' (ρ : ℕ) k).symm

lemma Gq_mulVec_ix (k : ℕ) (w : Fin (4 * k) → ℚ) (c : Fin 4) (i : Fin k) :
    (Gq k *ᵥ w) (ix k c i) = (frameQ k c *ᵥ w) ⟨i, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  rw [boxMatrix_mulVec4]
  fin_cases c
  · rw [if_pos (by simp [ix] <;> omega)]; congr 1; ext; simp [ix]
  · rw [if_neg (by simp [ix] <;> omega), if_pos (by simp [ix] <;> omega)]; congr 1; ext; simp [ix]
  · rw [if_neg (by simp [ix] <;> omega), if_neg (by simp [ix] <;> omega), if_pos (by simp [ix] <;> omega)]
    congr 1; ext; simp [ix]; omega
  · rw [if_neg (by simp [ix] <;> omega), if_neg (by simp [ix] <;> omega), if_neg (by simp [ix] <;> omega)]
    congr 1; ext; simp [ix]; omega

lemma Gq_ker (k : ℕ) (w : Fin (4 * k) → ℚ) (h : Gq k *ᵥ w = 0) : w = 0 := by
  have hz := box_zero_imp (frameQ k) (fun _ => k) (by ring) w h
  have h2 : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  have hfin : ∀ (c : Fin 4), c ≠ 2 → ∀ i < k,
      (taylor ((place c : ℤ) : ℚ) (pv w)).coeff i = 0 := by
    intro c hc i hi
    have := frame_fin (4 * k) c hc w ⟨i, by omega⟩
    rw [← this]
    exact hz c ⟨i, by omega⟩ hi
  apply pv_eq_zero
  refine lemmaT h2 (4 * k) _ (degree_pv_lt _) (fun _ => k) (by ring) (hfin 0 (by decide))
    (hfin 1 (by decide)) (hfin 3 (by decide)) ?_
  intro i hi
  have := frame_inf (4 * k) w ⟨i, by omega⟩
  rw [← this]
  exact hz 2 ⟨i, by omega⟩ hi

lemma Gq_unit (k : ℕ) : IsUnit (Gq k).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  exact hv0 (Gq_ker k v hv)

/-- The basis matrix: column `ix d j` is `E_{d,j}`. -/
def Emat (k : ℕ) : Matrix (Fin (4 * k)) (Fin (4 * k)) ℚ :=
  fun ρ col => EvecR (R := ℚ) k ⟨(col : ℕ) / k, Nat.div_lt_of_lt_mul (by have := col.isLt; omega)⟩
    ((col : ℕ) % k) ρ

/-- `B = diag(U0_d)`. -/
def Bmat (k : ℕ) : Matrix (Fin (4 * k)) (Fin (4 * k)) ℚ :=
  fun ρ col => if (ρ : ℕ) / k = (col : ℕ) / k then
    U0 ℚ k ⟨(col : ℕ) / k, Nat.div_lt_of_lt_mul (by have := col.isLt; omega)⟩
      ⟨(ρ : ℕ) % k, Nat.mod_lt _ (by have := ρ.isLt; omega)⟩
      ⟨(col : ℕ) % k, Nat.mod_lt _ (by have := col.isLt; omega)⟩ else 0

lemma Emat_ix (k : ℕ) (ρ : Fin (4 * k)) (d : Fin 4) (j : Fin k) :
    Emat k ρ (ix k d j) = EvecR (R := ℚ) k d j ρ := by
  simp only [Emat]
  rw [show (⟨(ix k d j : ℕ) / k, Nat.div_lt_of_lt_mul (by have := (ix k d j).isLt; omega)⟩ : Fin 4) = d
    from Fin.ext (ix_div k d j), ix_mod k d j]

lemma Bmat_ix (k : ℕ) (c d : Fin 4) (i j : Fin k) :
    Bmat k (ix k c i) (ix k d j) = if c = d then U0 ℚ k d i j else 0 := by
  simp only [Bmat, ix_div, ix_mod]
  by_cases h : c = d
  · subst h; simp
  · rw [if_neg (by intro h'; exact h (Fin.ext h')), if_neg h]

lemma G_Emat (k : ℕ) : Gq k * Emat k = Bmat k := by
  ext ρ col
  rw [ix_surj k ρ, ix_surj k col]
  set c : Fin 4 := ⟨(ρ : ℕ) / k, _⟩
  set i : Fin k := ⟨(ρ : ℕ) % k, _⟩
  set d : Fin 4 := ⟨(col : ℕ) / k, _⟩
  set j : Fin k := ⟨(col : ℕ) % k, _⟩
  rw [Bmat_ix]
  have e1 : (Gq k * Emat k) (ix k c i) (ix k d j) = (Gq k *ᵥ EvecR (R := ℚ) k d j) (ix k c i) := by
    simp only [mul_apply, mulVec, dotProduct]
    refine sum_congr rfl fun t _ => ?_
    rw [Emat_ix]
  rw [e1, Gq_mulVec_ix]
  by_cases hcd : c = d
  · rw [if_pos hcd, ← hcd]; rfl
  · rw [if_neg hcd]
    exact Fr_E_cell_ne k c d hcd j j.isLt i i.isLt

lemma Ginv_Bmat (k : ℕ) : (Gq k)⁻¹ * Bmat k = Emat k := by
  rw [← G_Emat, ← Matrix.mul_assoc, nonsing_inv_mul _ (Gq_unit k), Matrix.one_mul]

/-- `Φ^F_cd · U0_d = Ψ_cd`. -/
lemma frameGraph_U0 (k : ℕ) (c d : Fin 4) :
    frameGraph k c d * U0 ℚ k d = (Psi k c d).map (Int.cast : ℤ → ℚ) := by
  ext r j
  have key : (frameQ k c * (Gq k)⁻¹ * Bmat k) ⟨k + (r : ℕ), by omega⟩ (ix k d j) =
      (frameQ k c * Emat k) ⟨k + (r : ℕ), by omega⟩ (ix k d j) := by
    rw [Matrix.mul_assoc, Ginv_Bmat]
  have lhs : (frameQ k c * (Gq k)⁻¹ * Bmat k) ⟨k + (r : ℕ), by omega⟩ (ix k d j) =
      (frameGraph k c d * U0 ℚ k d) r j := by
    rw [mul_apply, sum_fin4k, Finset.sum_eq_single d]
    · simp only [mul_apply, frameGraph]
      refine sum_congr rfl fun l _ => ?_
      rw [Bmat_ix, if_pos rfl]; rfl
    · intro d' _ hd'
      apply sum_eq_zero; intro l _
      rw [Bmat_ix, if_neg hd', mul_zero]
    · simp
  have rhs : (frameQ k c * Emat k) ⟨k + (r : ℕ), by omega⟩ (ix k d j) = (Psi k c d r j : ℚ) := by
    rw [← Fr_E_off k c d j r]
    simp only [mul_apply, Fr, mulVec, dotProduct, frameQ]
    refine sum_congr rfl fun t _ => ?_
    rw [Emat_ix]
  rw [← lhs, key, rhs]; rfl

/-! ## `U0_d = Q_d^k Toep(g_d)` -/

lemma taylor_Hself (k : ℕ) (d : Fin 4) (hd : d ≠ 2) :
    taylor ((place d : ℤ) : ℚ) (Hself ℚ k d) = C (Qval d ^ k) * gpoly k d := by
  have hC : (C (2 : ℚ)) * C 2⁻¹ = 1 := by rw [← C_mul]; norm_num
  have hC2 : (C (2 : ℚ)) = 2 := map_ofNat C 2
  fin_cases d
  · simp [Hself, gpoly, place, Qval, taylor_mul, taylor_pow]
    rw [show (X - 1 : ℚ[X]) = (-1) * (1 - X) by ring, mul_pow]; ring
  · simp [Hself, gpoly, place, Qval, taylor_mul, taylor_pow]
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    linear_combination (X - 1) * hC2 + X * (1 - X) * hC
  · exact absurd rfl hd
  · simp [Hself, gpoly, place, Qval, taylor_mul, taylor_pow]
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    linear_combination (-(1 + X)) * hC2 - X * (1 + X) * hC

lemma reflect_one_sub_X_sq_pow (k : ℕ) : reflect (2 * k) ((1 - X ^ 2 : ℚ[X]) ^ k) = (X ^ 2 - 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdeg : ((1 - X ^ 2 : ℚ[X]) ^ k).natDegree ≤ 2 * k := by
      refine (natDegree_pow_le).trans ?_
      have : (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 :=
        (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
      nlinarith
    have hdeg1 : (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
    rw [pow_succ (1 - X ^ 2 : ℚ[X]) k, show 2 * (k + 1) = 2 * k + 2 by ring, reflect_mul _ _ hdeg hdeg1,
      ih, pow_succ (X ^ 2 - 1 : ℚ[X]) k]
    congr 1
    rw [reflect_sub, show (1 : ℚ[X]) = C 1 by simp, reflect_C, reflect_monomial,
      revAt_le (le_refl 2)]
    simp

lemma coeff_X_sq_sub_one_pow (k s : ℕ) :
    ((X ^ 2 - 1 : ℚ[X]) ^ k).coeff s = if s ≤ 2 * k then ((1 - X ^ 2 : ℚ[X]) ^ k).coeff (2 * k - s) else 0 := by
  rw [← reflect_one_sub_X_sq_pow, coeff_reflect]
  split_ifs with h
  · rw [revAt_le h]
  · rw [revAt_eq_self_of_lt (by omega)]
    apply coeff_eq_zero_of_natDegree_lt
    have : (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
    have := natDegree_pow_le_of_le k this
    omega

lemma U0_eq_toep (k : ℕ) (d : Fin 4) : U0 ℚ k d = (Qval d ^ k) • toep k (gpoly k d) := by
  ext i j
  have hi := i.isLt; have hj := j.isLt
  simp only [U0, Matrix.smul_apply, smul_eq_mul, toep]
  by_cases hd : d = 2
  · subst hd
    rw [Fr_E_inf k 2 j hj]
    simp only
    have e : EPoly ℚ k 2 j = X ^ (2 * k - 1 - j) * (X ^ 2 - 1) ^ k := by
      simp only [EPoly, exT, exP, exM]
      simp
      rw [mul_assoc, ← mul_pow]; ring
    rw [e, coeff_X_pow_mul', if_pos (by omega), coeff_X_sq_sub_one_pow]
    have hQ : Qval 2 = 1 := rfl
    simp only [hQ, one_pow, one_mul, gpoly, show ¬ ((2 : Fin 4) = 0) by decide,
      show ¬ ((2 : Fin 4) = 1) by decide, if_true, if_false]
    by_cases hji : j ≤ i
    · have : (j : ℕ) ≤ i := hji
      rw [if_pos hji, if_pos (show 4 * k - 1 - (i : ℕ) - (2 * k - 1 - j) ≤ 2 * k by omega)]
      congr 1; omega
    · have : (i : ℕ) < j := lt_of_not_ge hji
      rw [if_neg hji, if_neg (show ¬ (4 * k - 1 - (i : ℕ) - (2 * k - 1 - j) ≤ 2 * k) by omega)]

  · rw [Fr_E_fin k d d j hj hd, taylor_E_self k d j hd, taylor_Hself k d hd, coeff_C_mul]
    by_cases hji : j ≤ i
    · have : (j : ℕ) ≤ i := hji
      rw [if_pos this, if_pos hji]
    · have : ¬ (j : ℕ) ≤ i := hji
      rw [if_neg this, if_neg hji, mul_zero]

lemma Qinv_half (k : ℕ) (c : Fin 4) : Qinv (1 / 2 : ℚ) k c = (Qval c ^ k)⁻¹ := by
  fin_cases c <;> simp [Qinv, Qval] <;> rw [← inv_pow, inv_neg, inv_one]

lemma wtab_half (c d : Fin 4) (hcd : c ≠ d) : wtab (1 / 2 : ℚ) c d = wN c d := by
  fin_cases c <;> fin_cases d <;> simp at hcd <;> simp [wtab, wN, place] <;> norm_num

lemma ytab_half (c d : Fin 4) (hcd : c ≠ d) : ytab (1 / 2 : ℚ) c d = yN c d := by
  fin_cases c <;> fin_cases d <;> simp at hcd <;> simp [ytab, yN, place] <;> norm_num

/-- **Definition N, literally.** -/
theorem D4_defN (k : ℕ) (hk : 1 ≤ k) (c d : Fin 4) (hcd : c ≠ d) (r : Fin (3 * k)) (l : Fin k) :
    D4Phi ℚ (1 / 2) k c d r l =
      (if (r : ℕ) = 0 then (lamRes c : ℚ) * (Qval c ^ k)⁻¹ else 1) * (frameGraph k c d * Ulit k d) r l := by
  rw [Ulit, ← U0_eq_toep, ← Matrix.mul_assoc, frameGraph_U0]
  simp only [D4Phi, if_neg hcd, Qinv_half, mul_apply, map_apply]

/-- **Proposition N.** -/
theorem D4_propN (k : ℕ) (hk : 1 ≤ k) (c d : Fin 4) (hcd : c ≠ d) (j : Fin k) :
    (Qval c ^ k)⁻¹ * (frameGraph k c d * ((Qval d ^ k) • toep k (gpoly k d)))
        ⟨0, Nat.mul_pos (Nat.succ_pos 2) hk⟩ j = wN c d * yN c d ^ (k - 1 - (j : ℕ)) := by
  rw [← U0_eq_toep, frameGraph_U0, map_apply, ← Qinv_half, ← wtab_half c d hcd, ← ytab_half c d hcd]
  exact Qinv_Psi (1 / 2 : ℚ) (by norm_num) k c d hcd j

/-- **Proposition G.** -/
theorem D4_propG (c d : Fin 4) (hcd : c ≠ d) (n : ℕ) (hn : 3 ≤ n) :
    wN c d * yN c d ^ n =
      alpha (1 / 2 : ℚ) d n * (wN c d * yN c d) + beta (1 / 2 : ℚ) d n * (wN c d * yN c d ^ 2) := by
  have := resid_ge (1 / 2 : ℚ) (by norm_num) c d hcd n hn
  rw [wtab_half c d hcd, ytab_half c d hcd, pow_one] at this
  linear_combination this

end

end Z3NetD4.Proofs
