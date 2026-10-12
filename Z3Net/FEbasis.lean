module
public import Z3Net.FFrame

@[expose] public section

/-!
# Entry F, part 7: the `E`-basis of the frame and `prop:Ns`
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)

/-- `Π_d = ∏_{b finite, b ≠ d} (X - x_b)^k` (all finite places for `d = ∞`). -/
def Ppoly (d : Fin s) : R[X] := ∏ b ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d), (X - C (x b)) ^ k

/-- The basis polynomial `E_{d,j}`. -/
def Epoly (d : Fin s) (j : ℕ) : R[X] :=
  if d = inf then Ppoly k inf x d * X ^ (k - 1 - j) else Ppoly k inf x d * (X - C (x d)) ^ j

/-- Coefficient vector of `E_{d,j}` in `R[t]_{<sk}`. -/
def Evec (d : Fin s) (j : ℕ) : Fin (s * k) → R := fun l => (Epoly k inf x d j).coeff l

lemma card_fin_places : (univ.filter (fun b : Fin s => b ≠ inf)).card = s - 1 := by
  rw [Finset.filter_ne' univ inf, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

lemma card_fin_places_ne (d : Fin s) (hd : d ≠ inf) :
    (univ.filter (fun b : Fin s => b ≠ inf ∧ b ≠ d)).card = s - 2 := by
  have : univ.filter (fun b : Fin s => b ≠ inf ∧ b ≠ d) = (univ.erase inf).erase d := by
    ext b; simp [and_comm]
  rw [this, card_erase_of_mem (by simp [hd]), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]
  omega

lemma Ppoly_inf : Ppoly k inf x inf = ∏ b ∈ univ.filter (fun b => b ≠ inf), (X - C (x b)) ^ k := by
  unfold Ppoly; congr 1; ext b; simp

lemma Ppoly_inf_card : (univ.filter (fun b : Fin s => b ≠ inf ∧ b ≠ inf)).card = s - 1 := by
  rw [← card_fin_places inf]; congr 1; ext b; simp

lemma monic_Ppoly (d : Fin s) : (Ppoly k inf x d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma natDegree_Ppoly [Nontrivial R] (d : Fin s) :
    (Ppoly k inf x d).natDegree = (univ.filter (fun b => b ≠ inf ∧ b ≠ d)).card * k := by
  rw [Ppoly, natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _)]
  rw [Finset.sum_congr rfl (fun b _ => by
    rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]), sum_const, smul_eq_mul]

lemma natDegree_Epoly_fin [Nontrivial R] (d : Fin s) (hd : d ≠ inf) (j : ℕ) :
    (Epoly k inf x d j).natDegree = (s - 2) * k + j := by
  rw [Epoly, if_neg hd, (monic_Ppoly k inf x d).natDegree_mul ((monic_X_sub_C _).pow _),
    natDegree_Ppoly, card_fin_places_ne inf d hd, (monic_X_sub_C _).natDegree_pow,
    natDegree_X_sub_C, mul_one]

lemma natDegree_Epoly_inf [Nontrivial R] (j : ℕ) :
    (Epoly k inf x inf j).natDegree = (s - 1) * k + (k - 1 - j) := by
  rw [Epoly, if_pos rfl, (monic_Ppoly k inf x inf).natDegree_mul (monic_X_pow _),
    natDegree_Ppoly, natDegree_X_pow]
  congr 2
  rw [← card_fin_places inf]; congr 1; ext b; simp

lemma natDegree_Epoly_lt [Nontrivial R] (d : Fin s) (j : ℕ) (hj : j < k) :
    (Epoly k inf x d j).natDegree < s * k := by
  have hs : 1 ≤ s := by have := inf.isLt; omega
  by_cases hd : d = inf
  · subst hd; rw [natDegree_Epoly_inf]
    have : (s - 1) * k + k = s * k := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hs]
    omega
  · rw [natDegree_Epoly_fin k inf x d hd]
    have hs2 : 2 ≤ s := by
      by_contra h; push_neg at h
      exact hd (Fin.ext (by have := d.isLt; have := inf.isLt; omega))
    have : (s - 2) * k + k + k = s * k := by
      rw [← Nat.succ_mul, ← Nat.succ_mul]
      congr 1; omega
    omega

/-! ## Readings of the basis -/

lemma read_Evec [Nontrivial R] (c d : Fin s) (j : ℕ) (hj : j < k) (i : Fin (s * k)) :
    (Z3NetF.frameRead (s * k) inf x c *ᵥ Evec k inf x d j) i =
      if c = inf then (Epoly k inf x d j).coeff (s * k - 1 - i)
      else (taylor (x c) (Epoly k inf x d j)).coeff i := by
  simp only [mulVec, dotProduct, Z3NetF.frameRead, Evec]
  split_ifs
  · exact readInf_mul _ _ _
  · exact readAt_mul _ _ _ (natDegree_Epoly_lt k inf x d j hj) _

/-! ## Cells of the basis -/

lemma taylor_Ppoly (d : Fin s) (hd : d ≠ inf) :
    taylor (x d) (Ppoly k inf x d) = Z3NetF.uN k inf x d := by
  rw [Z3NetF.uN, if_neg hd, Ppoly, taylor_apply, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [pow_comp, sub_comp, X_comp, C_comp, C_sub]
  ring

lemma natDegree_lin_pow (a : R) (n : ℕ) : ((X - C a) ^ n).natDegree ≤ n :=
  (natDegree_pow_le_of_le n (natDegree_X_sub_C_le a)).trans (by simp)

lemma reflect_lin_pow (a : R) : ∀ n : ℕ, reflect n ((X - C a) ^ n) = (1 - C a * X) ^ n
  | 0 => by simp [reflect_one]
  | n + 1 => by
    have hX : reflect 1 (X : R[X]) = 1 := by
      simpa using reflect_C_mul_X_pow (R := R) 1 1 (c := 1)
    rw [pow_succ, reflect_mul _ _ (natDegree_lin_pow a n) (natDegree_X_sub_C_le a),
      reflect_lin_pow a n, reflect_sub, reflect_C, hX, pow_one, pow_succ]

lemma reflect_prod_lin (S : Finset (Fin s)) :
    reflect (S.card * k) (∏ b ∈ S, (X - C (x b)) ^ k) = ∏ b ∈ S, (1 - C (x b) * X) ^ k := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reflect_one]
  | insert a S ha ih =>
    have h2 : (∏ b ∈ S, (X - C (x b)) ^ k).natDegree ≤ S.card * k := by
      refine (natDegree_prod_le _ _).trans ?_
      exact (Finset.sum_le_sum (fun b _ => natDegree_lin_pow (x b) k)).trans
        (by rw [sum_const, smul_eq_mul])
    rw [Finset.prod_insert ha, Finset.prod_insert ha, card_insert_of_notMem ha,
      show (S.card + 1) * k = k + S.card * k by ring,
      reflect_mul ((X - C (x a)) ^ k) (∏ b ∈ S, (X - C (x b)) ^ k) (natDegree_lin_pow _ k) h2,
      reflect_lin_pow, ih]

lemma uN_inf_reflect :
    Z3NetF.uN k inf x inf = reflect ((s - 1) * k) (Ppoly k inf x inf) := by
  rw [Z3NetF.uN, if_pos rfl, Ppoly_inf, ← card_fin_places inf, reflect_prod_lin]

lemma cell_Evec [Nontrivial R] (hs : 2 ≤ s) (c d : Fin s) (j : ℕ) (hj : j < k) (i : ℕ) (hi : i < k) :
    (Z3NetF.frameRead (s * k) inf x c *ᵥ Evec k inf x d j) ⟨i, by nlinarith⟩ =
      if c = d then Z3NetF.toep k (Z3NetF.uN k inf x d) ⟨i, hi⟩ ⟨j, hj⟩ else 0 := by
  have hsk : k ≤ (s - 1) * k := Nat.le_mul_of_pos_left k (by omega)
  have hsk2 : (s - 1) * k + k = s * k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hsk3 : (s - 2) * k + k = (s - 1) * k := by
    rw [← Nat.succ_mul]; congr 1; omega
  rw [read_Evec k inf x c d j hj]
  by_cases hcd : c = d
  · subst hcd
    rw [if_pos rfl]
    simp only [Z3NetF.toep]
    by_cases hc : c = inf
    · subst hc
      have hN : (Ppoly k c x c).natDegree = (s - 1) * k := by
        rw [natDegree_Ppoly, Ppoly_inf_card]
      rw [if_pos rfl, Epoly, if_pos rfl, coeff_mul_X_pow', uN_inf_reflect]
      by_cases hji : j ≤ i
      · have h1 : k - 1 - j ≤ s * k - 1 - i := by omega
        have h2 : (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
        rw [if_pos h1, if_pos h2, coeff_reflect, revAt_le (show i - j ≤ (s - 1) * k by omega)]
        congr 1; omega
      · have h2 : ¬ (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
        rw [if_neg h2]
        split_ifs with h1
        · apply coeff_eq_zero_of_natDegree_lt; rw [hN]; omega
        · rfl
    · rw [if_neg hc, Epoly, if_neg hc, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
        taylor_Ppoly k inf x c hc]
      by_cases hji : j ≤ i
      · have h2 : (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
        rw [if_pos hji, if_pos h2]
      · have h2 : ¬ (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
        rw [if_neg hji, if_neg h2]
  · rw [if_neg hcd]
    by_cases hc : c = inf
    · rw [if_pos hc]
      have hd : d ≠ inf := fun h => hcd (hc.trans h.symm)
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_Epoly_fin k inf x d hd]
      show (s - 2) * k + j < s * k - 1 - i
      omega
    · rw [if_neg hc]
      have hmem : c ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d) := by simp [hc, hcd]
      unfold Epoly Ppoly
      rw [← Finset.mul_prod_erase _ _ hmem]
      split_ifs <;>
        rw [mul_assoc, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_neg (by simp only [Fin.val_mk]; omega)]

/-! ## The first offset digit of the basis -/

lemma pow_inv_cancel (D u : R) (h : D * u = 1) (j k : ℕ) (hj : j < k) :
    D ^ k * (u * u ^ (k - 1 - j)) = D ^ j := by
  have e1 : u * u ^ (k - 1 - j) = u ^ (k - j) := by
    rw [← pow_succ']; congr 1; omega
  have e2 : D ^ k = D ^ j * D ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [e1, e2, mul_assoc, ← mul_pow, h, one_pow, mul_one]

lemma Qf_unit (hx : Z3NetF.PlacesOK inf x) (c : Fin s) : IsUnit (Z3NetF.Qf inf x c) := by
  unfold Z3NetF.Qf
  split_ifs with hc
  · exact isUnit_one
  · rw [IsUnit.prod_iff]
    intro b hb
    obtain ⟨-, hb1, hb2⟩ := mem_filter.mp hb
    exact hx c b hc hb1 (Ne.symm hb2)

lemma off_Evec [Nontrivial R] (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d)
    (j : ℕ) (hj : j < k) :
    (Z3NetF.frameRead (s * k) inf x c *ᵥ Evec k inf x d j) ⟨k, by nlinarith⟩ =
      Z3NetF.Qf inf x c ^ k * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (k - 1 - j)) := by
  have hsk3 : (s - 2) * k + k = (s - 1) * k := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hsk2 : (s - 1) * k + k = s * k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  rw [read_Evec k inf x c d j hj]
  by_cases hc : c = inf
  · have hd : d ≠ inf := fun h => hcd (hc.trans h.symm)
    rw [if_pos hc]
    have hw : Z3NetF.wN inf x c d = 1 := by simp [Z3NetF.wN, hc]
    have hy : Z3NetF.yN inf x c d = 0 := by simp [Z3NetF.yN, hc]
    have hQ : Z3NetF.Qf inf x c = 1 := by simp [Z3NetF.Qf, hc]
    rw [hw, hy, hQ, one_pow, one_mul, one_mul]
    by_cases hjk : j = k - 1
    · rw [show k - 1 - j = 0 by omega, pow_zero]
      have hdeg := natDegree_Epoly_fin k inf x d hd j
      rw [show s * k - 1 - k = (Epoly k inf x d j).natDegree by rw [hdeg]; omega]
      unfold Epoly; rw [if_neg hd]
      exact ((monic_Ppoly k inf x d).mul ((monic_X_sub_C _).pow _)).coeff_natDegree
    · rw [zero_pow (by omega)]
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_Epoly_fin k inf x d hd]
      show (s - 2) * k + j < s * k - 1 - k
      omega
  · rw [if_neg hc]
    have hmem : c ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d) := by simp [hc, hcd]
    by_cases hd : d = inf
    · subst hd
      unfold Epoly Ppoly
      rw [if_pos rfl, ← Finset.mul_prod_erase _ _ hmem, mul_assoc,
        Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
      simp only [Z3NetF.Qf, Z3NetF.wN, Z3NetF.yN, if_neg hc, or_true, if_true, if_pos rfl, one_mul,
        eval_mul, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      rw [← Finset.prod_pow]
      congr 1
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext b; simp [and_comm]
    · unfold Epoly Ppoly
      rw [if_neg hd, ← Finset.mul_prod_erase _ _ hmem, mul_assoc,
        Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
      have hw : Z3NetF.wN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.wN, hc, hd]
      have hy : Z3NetF.yN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.yN, hc, hd]
      rw [hw, hy]
      simp only [Z3NetF.Qf, if_neg hc, eval_mul, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      have hmem2 : d ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ c) := by simp [hd, Ne.symm hcd]
      rw [← Finset.mul_prod_erase _ _ hmem2]
      have hS : (univ.filter (fun b => b ≠ inf ∧ b ≠ d)).erase c =
          (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d := by
        ext b; simp only [mem_erase, mem_filter, mem_univ, true_and]; tauto
      rw [hS, mul_pow, Finset.prod_pow]
      have hD := Ring.mul_inverse_cancel (x c - x d) (hx c d hc hd hcd)
      rw [show (x c - x d) ^ k * (∏ b ∈ (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d, (x c - x b)) ^ k *
          (Ring.inverse (x c - x d) * Ring.inverse (x c - x d) ^ (k - 1 - j)) =
          (∏ b ∈ (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d, (x c - x b)) ^ k *
          ((x c - x d) ^ k * (Ring.inverse (x c - x d) * Ring.inverse (x c - x d) ^ (k - 1 - j))) by ring,
        pow_inv_cancel _ _ hD j k hj]


/-! ## `Φ^F_cd · Toep(uN_d) = Ψ_cd` and `prop:Ns` -/

lemma key_Psi [Nontrivial R] (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (j : Fin k)
    (r : Fin (s * k - k)) :
    (Z3NetF.frameGraph R k inf x c d * Z3NetF.toep k (Z3NetF.uN k inf x d)) r j =
      (Z3NetF.frameRead (s * k) inf x c *ᵥ Evec k inf x d j) ⟨k + r, by omega⟩ := by
  have hspec := (frameGraph_spec_core k inf x hx).2 c
  rw [← hspec, ← mulVec_mulVec]
  have := graphGenK_mulVec_off (m := s * k) (fun _ => k) (sum_const_k k) (Z3NetF.frameGraph R k inf x) c
    (Gk k inf x *ᵥ Evec k inf x d j) r
  refine Eq.trans ?_ this.symm
  rw [Finset.sum_eq_single d, mul_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [box_mulVec_pre _ _ (sum_const_k k) _ d l l.isLt]
    rw [cell_Evec k inf x hs d d j j.isLt l l.isLt, if_pos rfl]
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [box_mulVec_pre _ _ (sum_const_k k) _ d' l l.isLt]
    rw [cell_Evec k inf x hs d' d j j.isLt l l.isLt, if_neg hd', mul_zero]
  · simp

theorem Ns_row0_core (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) (j : Fin k) :
    (Z3NetF.Lgauge (s * k - k) (Ring.inverse (Z3NetF.Qf inf x c ^ k)) * Z3NetF.frameGraph R k inf x c d *
        Z3NetF.toep k (Z3NetF.uN k inf x d)) r j =
      Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (k - 1 - (j : ℕ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hs : 2 ≤ s := by
    by_contra h; push_neg at h
    exact hcd (Fin.ext (by have := c.isLt; have := d.isLt; omega))
  rw [Matrix.mul_assoc, Z3NetF.Lgauge, diagonal_mul, if_pos hr, key_Psi k inf x hs hx c d j r]
  have hidx : (⟨k + (r : ℕ), by omega⟩ : Fin (s * k)) = ⟨k, by have := r.isLt; omega⟩ :=
    Fin.ext (by simp [hr])
  rw [hidx, off_Evec k inf x hs hx c d hcd j j.isLt, ← mul_assoc,
    Ring.inverse_mul_cancel _ ((Qf_unit inf x hx c).pow k), one_mul]


end

end Z3NetF.Proofs
