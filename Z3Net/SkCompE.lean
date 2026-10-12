/-
Proof module of entry Skel (`prop:skelcomp`(i): the frame's graph form and normal form for
arbitrary depths `K`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkelDefs
public import Z3Net.FMain

@[expose] public section

/-!
# Entry Skel: the frame with arbitrary depths `K`, `E`-basis, normal form

The proofs of entry F (`FFrame`, `FEbasis`) with the constant depths `(k, …, k)` replaced by
arbitrary depths `K` (`∑ K = m`):

* `frameGraphK_spec`: the `K`-box of the frame is invertible and `frameGraphK` is its graph form.
* The `E`-basis `E_{d,j} = Π_d (t - a_d)^j` (finite `d`), `E_{∞,j} = Π_∞ t^(K_∞-1-j)`, with
  `Π_d = ∏_{b finite, b ≠ d} (t - a_b)^(K_b)`: its cells vanish off `d` and are `Toep(uNK_d)` at
  `d`, and its first offset digit at `c ≠ d` is `Q^K_c w_cd y_cd^(K_d-1-j)`.
* `skelcomp_normal`: hence row `0` of `L_c Φ^F_cd Toep(uNK_d)` is `w_cd y_cd^n` at `x`-index `n`.
-/

namespace Z3NetF.Proofs

namespace SkComp

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s m : ℕ}

/-! ## Offsets and sums of the depths -/

lemma pre_eq_offL (K : Fin s → ℕ) (d : Fin s) : pre K d = Z3NetF.offL K d := by
  rw [pre, Z3NetU.Proofs.pre_eq_sum]
  rfl

lemma two_le_sum (K : Fin s → ℕ) (c d : Fin s) (hcd : c ≠ d) : K c + K d ≤ ∑ e, K e := by
  rw [← Finset.add_sum_erase univ K (mem_univ c),
    ← Finset.add_sum_erase (univ.erase c) K (a := d) (by simp [Ne.symm hcd])]
  omega

/-- `∑_{b finite, b ≠ d} K_b`. -/
def Sf (K : Fin s → ℕ) (inf d : Fin s) : ℕ := ∑ b ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d), K b

lemma filter_fin (inf d : Fin s) :
    univ.filter (fun b : Fin s => b ≠ inf ∧ b ≠ d) = (univ.erase inf).erase d := by
  ext b; simp [and_comm]

lemma Sf_fin (K : Fin s → ℕ) (hK : ∑ c, K c = m) (inf d : Fin s) (hd : d ≠ inf) :
    Sf K inf d + K d + K inf = m := by
  rw [← hK, Sf, filter_fin, ← Finset.add_sum_erase univ K (mem_univ inf),
    ← Finset.add_sum_erase (univ.erase inf) K (a := d) (by simp [hd])]
  omega

lemma Sf_inf (K : Fin s → ℕ) (hK : ∑ c, K c = m) (inf : Fin s) : Sf K inf inf + K inf = m := by
  rw [← hK, Sf, filter_fin, ← Finset.add_sum_erase univ K (mem_univ inf)]
  have : (univ.erase inf).erase inf = univ.erase inf := by
    ext b; simp
  rw [this]; omega

/-! ## The frame's graph form -/

lemma frameGraphK_eq_invPhi (K : Fin s → ℕ) (hK : ∑ c, K c = m) (inf : Fin s) (x : Fin s → R) :
    Z3NetF.frameGraphK R m K inf x = invPhi K hK (Z3NetF.frameRead m inf x) := by
  funext c d r l
  simp only [Z3NetF.frameGraphK, invPhi, Z3NetF.ent]
  have h1 : K c + (r : ℕ) < m := by have := r.isLt; omega
  have h2 : Z3NetF.offL K d + (l : ℕ) < m := by
    rw [← pre_eq_offL]; exact pre_add_lt K hK d l l.isLt
  rw [dif_pos ⟨h1, h2⟩]
  exact mat_congr2 _ _ _ _ _ _ _ _ _ rfl (by rw [pre_eq_offL])

lemma GK_unit (K : Fin s → ℕ) (hK : ∑ c, K c = m) (inf : Fin s) (x : Fin s → R)
    (hx : Z3NetF.PlacesOK inf x) : IsUnit (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K).det := by
  have hprod : IsUnit (∏ c : Fin s, ∏ c' : Fin s,
      (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (K c' * K c) else 1)) := by
    rw [IsUnit.prod_univ_iff]; intro c
    rw [IsUnit.prod_univ_iff]; intro c'
    split_ifs with h
    · exact (hx c c' h.2.1 h.2.2 (ne_of_gt h.1)).pow _
    · exact isUnit_one
  rcases frame_minor_core inf x (d := K) hK with h | h <;> rw [h]
  · exact hprod
  · exact hprod.neg

theorem frameGraphK_spec_core (K : Fin s → ℕ) (hK : ∑ c, K c = m) (inf : Fin s) (x : Fin s → R)
    (hx : Z3NetF.PlacesOK inf x) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K).det ∧
      ∀ c, Z3NetF.graphGenK (m := m) K (Z3NetF.frameGraphK R m K inf x) c *
        Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K = Z3NetF.frameRead m inf x c := by
  refine ⟨GK_unit K hK inf x hx, fun c => ?_⟩
  rw [frameGraphK_eq_invPhi K hK, graphGenK_inv K hK _ (GK_unit K hK inf x hx) c,
    Matrix.mul_assoc, nonsing_inv_mul _ (GK_unit K hK inf x hx), Matrix.mul_one]

/-! ## The `E`-basis -/

variable (K : Fin s → ℕ) (inf : Fin s) (x : Fin s → R)

/-- `Π_d = ∏_{b finite, b ≠ d} (X - a_b)^(K_b)`. -/
def PK (d : Fin s) : R[X] := ∏ b ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d), (X - C (x b)) ^ (K b)

/-- The basis polynomial `E_{d,j}`. -/
def EK (d : Fin s) (j : ℕ) : R[X] :=
  if d = inf then PK K inf x d * X ^ (K inf - 1 - j) else PK K inf x d * (X - C (x d)) ^ j

/-- Coefficient vector of `E_{d,j}`. -/
def EvK (m : ℕ) (d : Fin s) (j : ℕ) : Fin m → R := fun l => (EK K inf x d j).coeff l

lemma monic_PK (d : Fin s) : (PK K inf x d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma natDegree_PK [Nontrivial R] (d : Fin s) : (PK K inf x d).natDegree = Sf K inf d := by
  rw [PK, natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _), Sf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma natDegree_EK_fin [Nontrivial R] (d : Fin s) (hd : d ≠ inf) (j : ℕ) :
    (EK K inf x d j).natDegree = Sf K inf d + j := by
  rw [EK, if_neg hd, (monic_PK K inf x d).natDegree_mul ((monic_X_sub_C _).pow _),
    natDegree_PK, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma natDegree_EK_inf [Nontrivial R] (j : ℕ) :
    (EK K inf x inf j).natDegree = Sf K inf inf + (K inf - 1 - j) := by
  rw [EK, if_pos rfl, (monic_PK K inf x inf).natDegree_mul (monic_X_pow _), natDegree_PK,
    natDegree_X_pow]

lemma natDegree_EK_lt [Nontrivial R] (hK : ∑ c, K c = m) (d : Fin s) (j : ℕ) (hj : j < K d) :
    (EK K inf x d j).natDegree < m := by
  by_cases hd : d = inf
  · subst hd; rw [natDegree_EK_inf]; have := Sf_inf K hK d; omega
  · rw [natDegree_EK_fin K inf x d hd]; have := Sf_fin K hK inf d hd; omega

lemma read_EK [Nontrivial R] (hK : ∑ c, K c = m) (c d : Fin s) (j : ℕ) (hj : j < K d)
    (i : Fin m) :
    (Z3NetF.frameRead m inf x c *ᵥ EvK K inf x m d j) i =
      if c = inf then (EK K inf x d j).coeff (m - 1 - i)
      else (taylor (x c) (EK K inf x d j)).coeff i := by
  simp only [mulVec, dotProduct, Z3NetF.frameRead, EvK]
  split_ifs
  · exact readInf_mul _ _ _
  · exact readAt_mul _ _ _ (natDegree_EK_lt K inf x hK d j hj) _

lemma taylor_PK (d : Fin s) (hd : d ≠ inf) : taylor (x d) (PK K inf x d) = Z3NetF.uNK K inf x d := by
  rw [Z3NetF.uNK, if_neg hd, PK, taylor_apply, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [pow_comp, sub_comp, X_comp, C_comp, C_sub]
  ring

lemma reflect_prod_linK (S : Finset (Fin s)) :
    reflect (∑ b ∈ S, K b) (∏ b ∈ S, (X - C (x b)) ^ (K b)) = ∏ b ∈ S, (1 - C (x b) * X) ^ (K b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reflect_one]
  | insert a S ha ih =>
    have h2 : (∏ b ∈ S, (X - C (x b)) ^ (K b)).natDegree ≤ ∑ b ∈ S, K b := by
      refine (natDegree_prod_le _ _).trans ?_
      exact Finset.sum_le_sum (fun b _ => natDegree_lin_pow (x b) (K b))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      reflect_mul ((X - C (x a)) ^ (K a)) (∏ b ∈ S, (X - C (x b)) ^ (K b))
        (natDegree_lin_pow _ (K a)) h2, reflect_lin_pow, ih]

lemma uNK_inf_reflect : Z3NetF.uNK K inf x inf = reflect (Sf K inf inf) (PK K inf x inf) := by
  have e : univ.filter (fun b : Fin s => b ≠ inf ∧ b ≠ inf) = univ.filter (fun b => b ≠ inf) := by
    ext b; simp
  rw [Z3NetF.uNK, if_pos rfl, PK, Sf, e, reflect_prod_linK]

/-! ## Cells of the basis -/

lemma cell_EK_same [Nontrivial R] (hK : ∑ c, K c = m) (d : Fin s) (j : ℕ) (hj : j < K d) (i : ℕ)
    (hi : i < K d) :
    (Z3NetF.frameRead m inf x d *ᵥ EvK K inf x m d j) ⟨i, lt_of_lt_of_le hi (le_of_sum K hK d)⟩ =
      Z3NetF.toep (K d) (Z3NetF.uNK K inf x d) ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [read_EK K inf x hK d d j hj]
  simp only [Z3NetF.toep]
  by_cases hc : d = inf
  · subst hc
    have hN : (PK K d x d).natDegree = Sf K d d := natDegree_PK K d x d
    have hS := Sf_inf K hK d
    rw [if_pos rfl, EK, if_pos rfl, coeff_mul_X_pow', uNK_inf_reflect]
    by_cases hji : j ≤ i
    · have h2 : (⟨j, hj⟩ : Fin (K d)) ≤ ⟨i, hi⟩ := hji
      rw [if_pos h2]
      by_cases h1 : K d - 1 - j ≤ m - 1 - i
      · rw [if_pos h1, coeff_reflect, revAt_le (show i - j ≤ Sf K d d by omega)]
        congr 1; omega
      · rw [if_neg h1, coeff_reflect]
        rw [revAt_eq_self_of_lt (show Sf K d d < i - j by omega)]
        exact (coeff_eq_zero_of_natDegree_lt (by rw [hN]; omega)).symm
    · have h2 : ¬ (⟨j, hj⟩ : Fin (K d)) ≤ ⟨i, hi⟩ := hji
      rw [if_neg h2]
      split_ifs with h1
      · apply coeff_eq_zero_of_natDegree_lt; rw [hN]; omega
      · rfl
  · rw [if_neg hc, EK, if_neg hc, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
      taylor_PK K inf x d hc]
    by_cases hji : j ≤ i
    · have h2 : (⟨j, hj⟩ : Fin (K d)) ≤ ⟨i, hi⟩ := hji
      rw [if_pos hji, if_pos h2]
    · have h2 : ¬ (⟨j, hj⟩ : Fin (K d)) ≤ ⟨i, hi⟩ := hji
      rw [if_neg hji, if_neg h2]

lemma cell_EK_ne [Nontrivial R] (hK : ∑ c, K c = m) (c d : Fin s) (hcd : c ≠ d) (j : ℕ)
    (hj : j < K d) (i : ℕ) (hi : i < K c) :
    (Z3NetF.frameRead m inf x c *ᵥ EvK K inf x m d j) ⟨i, lt_of_lt_of_le hi (le_of_sum K hK c)⟩ =
      0 := by
  rw [read_EK K inf x hK c d j hj]
  by_cases hc : c = inf
  · rw [if_pos hc]
    have hd : d ≠ inf := fun h => hcd (hc.trans h.symm)
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_EK_fin K inf x d hd]
    have := Sf_fin K hK inf d hd
    subst hc
    simp only [Fin.val_mk]
    omega
  · rw [if_neg hc]
    have hmem : c ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d) := by simp [hc, hcd]
    unfold EK PK
    rw [← Finset.mul_prod_erase _ _ hmem]
    split_ifs <;>
      rw [mul_assoc, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
        if_neg (by simp only [Fin.val_mk]; omega)]

/-! ## The first offset digit of the basis -/

lemma QfK_unit (hx : Z3NetF.PlacesOK inf x) (c : Fin s) : IsUnit (Z3NetF.QfK K inf x c) := by
  unfold Z3NetF.QfK
  split_ifs with hc
  · exact isUnit_one
  · rw [IsUnit.prod_iff]
    intro b hb
    obtain ⟨-, hb1, hb2⟩ := mem_filter.mp hb
    exact (hx c b hc hb1 (Ne.symm hb2)).pow _

lemma Kc_lt (hK : ∑ c, K c = m) (c d : Fin s) (hcd : c ≠ d) (hd : 1 ≤ K d) : K c < m := by
  have := two_le_sum K c d hcd; omega

lemma off_EK [Nontrivial R] (hK : ∑ c, K c = m) (hx : Z3NetF.PlacesOK inf x) (c d : Fin s)
    (hcd : c ≠ d) (j : ℕ) (hj : j < K d) :
    (Z3NetF.frameRead m inf x c *ᵥ EvK K inf x m d j) ⟨K c, Kc_lt K hK c d hcd (by omega)⟩ =
      Z3NetF.QfK K inf x c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (K d - 1 - j)) := by
  rw [read_EK K inf x hK c d j hj]
  by_cases hc : c = inf
  · have hd : d ≠ inf := fun h => hcd (hc.trans h.symm)
    rw [if_pos hc]
    have hw : Z3NetF.wN inf x c d = 1 := by simp [Z3NetF.wN, hc]
    have hy : Z3NetF.yN inf x c d = 0 := by simp [Z3NetF.yN, hc]
    have hQ : Z3NetF.QfK K inf x c = 1 := by simp [Z3NetF.QfK, hc]
    rw [hw, hy, hQ, one_mul, one_mul]
    have hS := Sf_fin K hK inf d hd
    have hdeg := natDegree_EK_fin K inf x d hd j
    subst hc
    by_cases hjk : j = K d - 1
    · rw [show K d - 1 - j = 0 by omega, pow_zero]
      rw [show m - 1 - K c = (EK K c x d j).natDegree by omega]
      unfold EK; rw [if_neg hd]
      exact ((monic_PK K c x d).mul ((monic_X_sub_C _).pow _)).coeff_natDegree
    · rw [zero_pow (by omega)]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hdeg]
      simp only [Fin.val_mk]
      omega
  · rw [if_neg hc]
    have hmem : c ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d) := by simp [hc, hcd]
    by_cases hd : d = inf
    · subst hd
      unfold EK PK
      rw [if_pos rfl, ← Finset.mul_prod_erase _ _ hmem, mul_assoc,
        Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
      simp only [Z3NetF.QfK, Z3NetF.wN, Z3NetF.yN, if_neg hc, or_true, if_true, if_pos rfl, one_mul,
        eval_mul, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      congr 1
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext b; simp only [mem_erase, mem_filter, mem_univ, true_and]; tauto
    · unfold EK PK
      rw [if_neg hd, ← Finset.mul_prod_erase _ _ hmem, mul_assoc,
        Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
      have hw : Z3NetF.wN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.wN, hc, hd]
      have hy : Z3NetF.yN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.yN, hc, hd]
      rw [hw, hy]
      simp only [Z3NetF.QfK, if_neg hc, eval_mul, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      have hmem2 : d ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ c) := by simp [hd, Ne.symm hcd]
      rw [← Finset.mul_prod_erase _ _ hmem2]
      have hS : (univ.filter (fun b => b ≠ inf ∧ b ≠ d)).erase c =
          (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d := by
        ext b; simp only [mem_erase, mem_filter, mem_univ, true_and]; tauto
      rw [hS]
      have hD := Ring.mul_inverse_cancel (x c - x d) (hx c d hc hd hcd)
      rw [show (x c - x d) ^ K d * (∏ b ∈ (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d,
            (x c - x b) ^ K b) * (Ring.inverse (x c - x d) * Ring.inverse (x c - x d) ^ (K d - 1 - j)) =
          (∏ b ∈ (univ.filter (fun b => b ≠ inf ∧ b ≠ c)).erase d, (x c - x b) ^ K b) *
          ((x c - x d) ^ K d * (Ring.inverse (x c - x d) * Ring.inverse (x c - x d) ^ (K d - 1 - j)))
          by ring, pow_inv_cancel _ _ hD j (K d) hj]

/-! ## `Φ^F_cd · Toep(uNK_d) = Ψ_cd` and the normal form -/

lemma key_PsiK [Nontrivial R] (hK : ∑ c, K c = m) (hx : Z3NetF.PlacesOK inf x) (c d : Fin s)
    (j : Fin (K d)) (r : Fin (m - K c)) :
    (Z3NetF.frameGraphK R m K inf x c d * Z3NetF.toep (K d) (Z3NetF.uNK K inf x d)) r j =
      (Z3NetF.frameRead m inf x c *ᵥ EvK K inf x m d j) ⟨K c + r, by omega⟩ := by
  have hspec := (frameGraphK_spec_core K hK inf x hx).2 c
  rw [← hspec, ← mulVec_mulVec]
  have := graphGenK_mulVec_off K hK (Z3NetF.frameGraphK R m K inf x) c
    (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K *ᵥ EvK K inf x m d j) r
  refine Eq.trans ?_ this.symm
  rw [Finset.sum_eq_single d, mul_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [box_mulVec_pre _ _ hK _ d l l.isLt, cell_EK_same K inf x hK d j j.isLt l l.isLt]
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [box_mulVec_pre _ _ hK _ d' l l.isLt, cell_EK_ne K inf x hK d' d hd' j j.isLt l l.isLt,
      mul_zero]
  · simp

end

end SkComp

open SkComp in
/-- **`prop:skelcomp`**: the frame's `K`-box is invertible and `frameGraphK` is its graph form. -/
theorem frameGraphK_spec {R : Type*} [CommRing R] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x) :
    IsUnit (boxMatrix (frameRead m inf x) K).det ∧
      ∀ c, graphGenK (m := m) K (frameGraphK R m K inf x) c * boxMatrix (frameRead m inf x) K =
        frameRead m inf x c :=
  frameGraphK_spec_core K hK inf x hx

open SkComp in
/-- **`prop:skelcomp`(i)** (normal form for arbitrary depths `K`). -/
theorem skelcomp_normal {R : Type*} [CommRing R] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d)
    (j : Fin (K d)) :
    ent (Lgauge (m - K c) (Ring.inverse (QfK K inf x c)) * frameGraphK R m K inf x c d *
        toep (K d) (uNK K inf x d)) 0 j = wN inf x c d * yN inf x c d ^ (K d - 1 - (j : ℕ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hlt := Kc_lt K hK c d hcd (by have := j.isLt; omega)
  have h0 : 0 < m - K c := by omega
  unfold ent
  rw [dif_pos ⟨h0, j.isLt⟩, Matrix.mul_assoc, Lgauge, Matrix.diagonal_mul, if_pos rfl,
    key_PsiK K inf x hK hx c d j ⟨0, h0⟩]
  have hidx : (⟨K c + ((⟨0, h0⟩ : Fin (m - K c)) : ℕ), by omega⟩ : Fin m) = ⟨K c, hlt⟩ :=
    Fin.ext (by simp)
  rw [hidx, off_EK K inf x hK hx c d hcd j j.isLt, ← mul_assoc,
    Ring.inverse_mul_cancel _ (QfK_unit K inf x hx c), one_mul]

end Z3NetF.Proofs
