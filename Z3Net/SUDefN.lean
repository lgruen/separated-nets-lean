module
public import Mathlib
public import Z3Net.SURows
public import Z3Net.SUBoxMinor

@[expose] public section

/-!
# Entry U, part 12: the `E`-basis description is Definition N_s, literally

`G E = B`: the `(k,…,k)` box matrix `G` of the frame maps the basis vector `E_{d,j}` to the
block-diagonal matrix `B = diag(U0_d)` (cells of `E_{d,j}` vanish off `d`). `G` is invertible over
`ℚ` (Lemma T_s), so `Φ^F_cd U0_d = (O_c G⁻¹ B)_{block d} = (O_c E)_{block d} = Ψ_cd`, and
`U0_d = Q_d^k Toep(g_d)` is a polynomial identity (Taylor expansion of `P_d` at `a_d`; at `∞` the
reverse of `∏_b (t - a_b)^k`). Adapted from the 4D entry.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

variable {s : ℕ}

/-- The `(k,…,k)` box matrix of the frame over `ℚ`. -/
abbrev Gq (s k : ℕ) : Matrix (Fin (s * k)) (Fin (s * k)) ℚ := boxMatrix (frameQ (s := s) k) (fun _ => k)

lemma take_const_sum (k c : ℕ) (hc : c ≤ s) :
    ((List.ofFn (fun _ : Fin s => k)).take c).sum = c * k := by
  rw [List.ofFn_const, List.take_replicate, List.sum_replicate, smul_eq_mul, min_eq_left hc]

lemma Gq_row (k : ℕ) (c : Fin s) (i : Fin k) :
    Gq s k (ix k c i) = frameQ k c ⟨i, lt_of_lt_of_le i.isLt (k_le_sk k c)⟩ := by
  have hloc := boxLoc_spec (List.ofFn (fun _ : Fin s => k)) 0 c i (by simp) (by simp)
  rw [take_const_sum k c (by have := c.isLt; omega)] at hloc
  funext l
  have hloc' : boxLoc (List.replicate s k) 0 (ix k c i : ℕ) = ((c : ℕ), (i : ℕ)) := by
    have hix : ((ix k c i : Fin (s * k)) : ℕ) = (c : ℕ) * k + i := rfl
    rw [hix, ← List.ofFn_const]; simpa using hloc
  simp [Gq, boxMatrix, hloc']
  rw [dif_pos (lt_of_lt_of_le i.isLt (k_le_sk k c))]

lemma Gq_mulVec_ix (k : ℕ) (w : Fin (s * k) → ℚ) (c : Fin s) (i : Fin k) :
    (Gq s k *ᵥ w) (ix k c i) = (frameQ k c *ᵥ w) ⟨i, lt_of_lt_of_le i.isLt (k_le_sk k c)⟩ := by
  simp only [mulVec, dotProduct]
  rw [Gq_row]

lemma Gq_ker (hs : 3 ≤ s) (k : ℕ) (w : Fin (s * k) → ℚ) (h : Gq s k *ᵥ w = 0) : w = 0 := by
  have hs0 : 0 < s := by omega
  have hz : ∀ c (i : Fin k), (frameQ k c *ᵥ w) ⟨i, lt_of_lt_of_le i.isLt (k_le_sk k c)⟩ = 0 := by
    intro c i; rw [← Gq_mulVec_ix, h]; rfl
  apply pv_eq_zero
  refine lemmaT hs0 (fun c => ((place c : ℤ) : ℚ)) ?_ (s * k) _ (degree_pv_lt _) (fun _ => k)
    (by simp [mul_comm]) ?_ ?_
  · intro c c' hc hc' hne
    obtain ⟨h1, _⟩ := diff_small c c' hc hc' hne
    rw [isUnit_iff_ne_zero]
    have : (((c : ℤ) - c' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h1
    simpa [place] using this
  · intro c hc i hi
    have := frame_fin (s * k) c hc w ⟨i, lt_of_lt_of_le hi (k_le_sk k c)⟩
    rw [← this]
    exact hz c ⟨i, hi⟩
  · intro i hi
    have := frame_inf (s * k) (c0 hs0) rfl w ⟨i, lt_of_lt_of_le hi (k_le_sk k (c0 hs0))⟩
    rw [← this]
    exact hz (c0 hs0) ⟨i, hi⟩

lemma Gq_unit (hs : 3 ≤ s) (k : ℕ) : IsUnit (Gq s k).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  exact hv0 (Gq_ker hs k v hv)

/-- The basis matrix: column `ix d j` is `E_{d,j}`. -/
def Emat (s k : ℕ) : Matrix (Fin (s * k)) (Fin (s * k)) ℚ :=
  fun ρ col => EvecR (R := ℚ) k (⟨(col : ℕ) / k, Nat.div_lt_of_lt_mul
    (Nat.lt_of_lt_of_eq col.isLt (Nat.mul_comm s k))⟩ : Fin s) ((col : ℕ) % k) ρ

/-- `B = diag(U0_d)`. -/
def Bmat (s k : ℕ) : Matrix (Fin (s * k)) (Fin (s * k)) ℚ :=
  fun ρ col => if (ρ : ℕ) / k = (col : ℕ) / k then
    U0 ℚ k (⟨(col : ℕ) / k, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq col.isLt (Nat.mul_comm s k))⟩ : Fin s)
      ⟨(ρ : ℕ) % k, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos ρ))⟩
      ⟨(col : ℕ) % k, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Fin.pos col))⟩ else 0

lemma Emat_ix (k : ℕ) (ρ : Fin (s * k)) (d : Fin s) (j : Fin k) :
    Emat s k ρ (ix k d j) = EvecR (R := ℚ) k d j ρ := by
  simp only [Emat]
  rw [show (⟨(ix k d j : ℕ) / k, Nat.div_lt_of_lt_mul
      (Nat.lt_of_lt_of_eq (ix k d j).isLt (Nat.mul_comm s k))⟩ : Fin s) = d
    from Fin.ext (ix_div k d j), ix_mod k d j]

lemma Bmat_ix (k : ℕ) (c d : Fin s) (i j : Fin k) :
    Bmat s k (ix k c i) (ix k d j) = if c = d then U0 ℚ k d i j else 0 := by
  simp only [Bmat, ix_div, ix_mod]
  by_cases h : c = d
  · subst h; simp
  · rw [if_neg (by intro h'; exact h (Fin.ext h')), if_neg h]

lemma G_Emat (hs : 3 ≤ s) (k : ℕ) : Gq s k * Emat s k = Bmat s k := by
  ext ρ col
  obtain ⟨c, i, rfl⟩ := ix_surj k ρ
  obtain ⟨d, j, rfl⟩ := ix_surj k col
  rw [Bmat_ix]
  have e1 : (Gq s k * Emat s k) (ix k c i) (ix k d j) = (Gq s k *ᵥ EvecR (R := ℚ) k d j) (ix k c i) := by
    simp only [mul_apply, mulVec, dotProduct]
    refine sum_congr rfl fun t _ => ?_
    rw [Emat_ix]
  rw [e1, Gq_mulVec_ix]
  by_cases hcd : c = d
  · rw [if_pos hcd, ← hcd]; rfl
  · rw [if_neg hcd]
    exact Fr_E_cell_ne (by omega) k c d hcd j j.isLt i i.isLt

lemma Ginv_Bmat (hs : 3 ≤ s) (k : ℕ) : (Gq s k)⁻¹ * Bmat s k = Emat s k := by
  rw [← G_Emat hs, ← Matrix.mul_assoc, nonsing_inv_mul _ (Gq_unit hs k), Matrix.one_mul]

/-- `Φ^F_cd · U0_d = Ψ_cd`. -/
lemma frameGraph_U0 (hs : 3 ≤ s) (k : ℕ) (c d : Fin s) :
    frameGraph k c d * U0 ℚ k d = (Psi k c d).map (Int.cast : ℤ → ℚ) := by
  ext r j
  have key : (frameQ k c * (Gq s k)⁻¹ * Bmat s k) ⟨k + (r : ℕ), sk_sub_add r⟩ (ix k d j) =
      (frameQ k c * Emat s k) ⟨k + (r : ℕ), sk_sub_add r⟩ (ix k d j) := by
    rw [Matrix.mul_assoc, Ginv_Bmat hs]
  have lhs : (frameQ k c * (Gq s k)⁻¹ * Bmat s k) ⟨k + (r : ℕ), sk_sub_add r⟩ (ix k d j) =
      (frameGraph k c d * U0 ℚ k d) r j := by
    rw [mul_apply, sum_fin_sk, Finset.sum_eq_single d]
    · simp only [mul_apply, frameGraph]
      refine sum_congr rfl fun l _ => ?_
      rw [Bmat_ix, if_pos rfl]; rfl
    · intro d' _ hd'
      apply sum_eq_zero; intro l _
      rw [Bmat_ix, if_neg hd', mul_zero]
    · simp
  have rhs : (frameQ k c * Emat s k) ⟨k + (r : ℕ), sk_sub_add r⟩ (ix k d j) = (Psi k c d r j : ℚ) := by
    rw [← Fr_E_off k c d j r]
    simp only [mul_apply, Fr, mulVec, dotProduct, frameQ]
    refine sum_congr rfl fun t _ => ?_
    rw [Emat_ix]
  rw [← lhs, key, rhs]; rfl

/-! ## `U0_d = Q_d^k Toep(g_d)` -/

lemma reflect_one_X : reflect 1 (X : ℚ[X]) = 1 := by
  have := reflect_C_mul_X_pow (R := ℚ) 1 1 (c := 1)
  simpa using this

lemma reverse_X_sub_C' (a : ℚ) : (X - C a).reverse = 1 - C a * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C, reflect_one_X, pow_one]

lemma reverse_pow' (p : ℚ[X]) : ∀ k : ℕ, (p ^ k).reverse = p.reverse ^ k
  | 0 => by simp only [pow_zero]; rw [← C_1, reverse_C]
  | k + 1 => by rw [pow_succ, reverse_mul_of_domain, reverse_pow' p k, pow_succ]

lemma reverse_prod' {ι : Type*} (S : Finset ι) (f : ι → ℚ[X]) :
    (∏ i ∈ S, f i).reverse = ∏ i ∈ S, (f i).reverse := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty]; rw [← C_1, reverse_C]
  | insert a S ha ih => rw [Finset.prod_insert ha, reverse_mul_of_domain, ih, Finset.prod_insert ha]

/-- `∏_{b finite} (X - a_b)^k`. -/
def PinfQ (s k : ℕ) : ℚ[X] :=
  ∏ b ∈ univ.filter (fun b : Fin s => (b : ℕ) ≠ 0), (X - C ((b : ℚ) - 1)) ^ k

lemma gpoly_inf (k : ℕ) (d : Fin s) (hd : (d : ℕ) = 0) : gpoly k d = (PinfQ s k).reverse := by
  rw [gpoly, if_pos hd, PinfQ, reverse_prod']
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [reverse_pow', reverse_X_sub_C']

lemma natDegree_PinfQ (hs : 1 ≤ s) (k : ℕ) : (PinfQ s k).natDegree = (s - 1) * k := by
  rw [PinfQ, natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _)]
  rw [Finset.sum_congr rfl (fun b _ => by
    rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]), sum_const, smul_eq_mul]
  congr 1
  have : univ.filter (fun b : Fin s => (b : ℕ) ≠ 0) = univ.erase (c0 (by omega)) := by
    ext b; simp [c0, Fin.ext_iff]
  rw [this, card_erase_c0]

lemma EPoly_inf (k : ℕ) (d : Fin s) (hd : (d : ℕ) = 0) (j : ℕ) (hs : 0 < s) :
    EPoly ℚ k d j = X ^ (k - 1 - j) * PinfQ s k := by
  rw [EPoly, ← Finset.mul_prod_erase _ _ (mem_univ (c0 hs))]
  congr 1
  · simp [Eroot, Eexp, c0, hd]
  · rw [PinfQ]
    apply Finset.prod_congr
    · ext b; simp [c0, Fin.ext_iff]
    · intro b hb
      have hb0 : (b : ℕ) ≠ 0 := by simpa using hb
      have hbd : b ≠ d := fun h => hb0 (by rw [h]; exact hd)
      rw [Eroot_fin b hb0, Eexp_fin k d b j hb0, if_neg hbd]
      simp [place]

lemma Rest_self_taylor (k : ℕ) (d : Fin s) (hd : (d : ℕ) ≠ 0) (j : ℕ) :
    taylor ((place d : ℤ) : ℚ) (Rest ℚ k d d j) = C (Qval d ^ k) * gpoly k d := by
  rw [taylor_apply, Rest, Polynomial.prod_comp, gpoly, if_neg hd, Qval, if_neg hd]
  have hs0 : 0 < s := by have := d.isLt; omega
  have hset : univ.erase d = insert (c0 hs0) (univ.filter (fun b : Fin s => (b : ℕ) ≠ 0 ∧ b ≠ d)) := by
    ext b; simp only [mem_erase, mem_insert, mem_filter, mem_univ, true_and, c0, Fin.ext_iff]
    constructor
    · intro h; by_cases hb : (b : ℕ) = 0
      · left; exact hb
      · right; exact ⟨hb, fun h' => h.1 (Fin.ext (by rw [h']))⟩
    · rintro (h | h)
      · exact ⟨fun h' => hd (by rw [← h', h]), trivial⟩
      · exact ⟨fun h' => h.2 (Fin.ext (by rw [h'])), trivial⟩
  rw [hset, Finset.prod_insert (by simp [c0])]
  have e0 : ((X - C ((Eroot (c0 hs0) : ℤ) : ℚ)) ^ Eexp k d (c0 hs0) j).comp (X + C ((place d : ℤ) : ℚ)) = 1 := by
    simp [Eexp, c0, hd]
  rw [e0, one_mul, ← Finset.prod_pow, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [mem_filter] at hb
  rw [Eroot_fin b hb.2.1, Eexp_fin k d b j hb.2.1, if_neg hb.2.2, pow_comp, sub_comp, X_comp, C_comp]
  have hne : ((d : ℚ) - b) ≠ 0 := by
    have : (d : ℕ) ≠ b := fun h => hb.2.2 (Fin.ext h).symm
    have : ((d : ℕ) : ℚ) ≠ (b : ℕ) := by exact_mod_cast this
    intro h; apply this; linarith
  rw [map_pow, ← mul_pow]
  congr 1
  simp only [place]
  push_cast
  rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, one_mul, C_sub]
  ring_nf
  simp [C_sub]
  ring

lemma U0_eq_toep (hs : 3 ≤ s) (k : ℕ) (d : Fin s) : U0 ℚ k d = (Qval d ^ k) • toep k (gpoly k d) := by
  ext i j
  have hi := i.isLt; have hj := j.isLt
  have hs0 : 0 < s := by omega
  simp only [U0, Matrix.smul_apply, smul_eq_mul, toep]
  by_cases hd : (d : ℕ) = 0
  · rw [Fr_E_inf (by omega) k d d j hj hd]
    simp only
    rw [EPoly_inf k d hd j hs0, coeff_X_pow_mul', gpoly_inf k d hd, Qval, if_pos hd, one_pow, one_mul]
    have hN := natDegree_PinfQ (show 1 ≤ s by omega) k
    have hsk := sk_eq (show 2 ≤ s by omega) k
    have h2k : k ≤ (s - 1) * k := Nat.le_mul_of_pos_left k (by omega)
    by_cases hji : j ≤ i
    · have : (j : ℕ) ≤ i := hji
      rw [if_pos (by omega), if_pos hji, coeff_reverse, hN, revAt_le (by omega)]
      congr 1; omega
    · have : (i : ℕ) < j := lt_of_not_ge hji
      rw [if_pos (by omega), if_neg hji]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hN]; omega
  · rw [Fr_E_fin (by omega) k d d j hj hd, taylor_EPoly_fin k d d j hd, Eexp_self k d j hd,
      Rest_self_taylor k d hd, coeff_C_mul]
    by_cases hji : j ≤ i
    · have : (j : ℕ) ≤ i := hji
      rw [if_pos this, if_pos hji]
    · have : ¬ (j : ℕ) ≤ i := hji
      rw [if_neg this, if_neg hji, mul_zero]

lemma ivz_rat (z : ℤ) : ivz (fun i => ((i : ℕ) : ℚ)⁻¹) z = (z : ℚ)⁻¹ := by
  unfold ivz
  split_ifs with h
  · congr 1; rw [show (z : ℚ) = ((z.toNat : ℤ) : ℚ) by rw [Int.toNat_of_nonneg h]]; rfl
  · rw [← inv_neg]; congr 1
    rw [show (z : ℚ) = -(((-z).toNat : ℤ) : ℚ) by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring]
    push_cast; ring

lemma Qinv_rat (k : ℕ) (c : Fin s) : Qinv (fun i => ((i : ℕ) : ℚ)⁻¹) k c = (Qval c ^ k)⁻¹ := by
  unfold Qinv Qval
  split_ifs with hc
  · simp
  · rw [← inv_pow, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [ivz_rat]; push_cast; rfl

/-- **Definition N_s, literally.** -/
theorem U_defN (s k : ℕ) (hs : 3 ≤ s) (hk : 1 ≤ k) (c d : Fin s) (hcd : c ≠ d)
    (r : Fin (s * k - k)) (l : Fin k) :
    UPhi ℚ (fun i => ((i : ℕ) : ℚ)⁻¹) k c d r l =
      (if (r : ℕ) = 0 then (lamRes c : ℚ) * (Qval c ^ k)⁻¹ else 1) * (frameGraph k c d * Ulit k d) r l := by
  rw [Ulit, ← U0_eq_toep hs, ← Matrix.mul_assoc, frameGraph_U0 hs]
  simp only [UPhi, if_neg hcd, Qinv_rat, mul_apply, map_apply]

end

end Z3NetU.Proofs
