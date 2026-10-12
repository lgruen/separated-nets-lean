module
public import Z3Net.FGs

@[expose] public section

/-!
# Entry F, part 10: `prop:Gs` (existence of `β`), `cor:tsk`, `def:Ns` over `ℤ/qℤ`
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)

lemma inv_sub_inv (a b : R) (ha : IsUnit a) (hb : IsUnit b) :
    Ring.inverse a - Ring.inverse b = Ring.inverse a * Ring.inverse b * (b - a) := by
  have h1 := Ring.inverse_mul_cancel a ha
  have h2 := Ring.mul_inverse_cancel b hb
  linear_combination (Ring.inverse b) * h1 - (Ring.inverse a) * h2

lemma yN_sub_unit (hx : Z3NetF.PlacesOK inf x) (d c c' : Fin s) (hc : c ≠ d) (hc' : c' ≠ d)
    (hcc' : c ≠ c') : IsUnit (Z3NetF.yN inf x c d - Z3NetF.yN inf x c' d) := by
  by_cases hd : d = inf
  · have hci : c ≠ inf := hd ▸ hc
    have hci' : c' ≠ inf := hd ▸ hc'
    simp only [Z3NetF.yN, if_neg hci, if_neg hci', if_pos hd]
    exact hx c c' hci hci' hcc'
  · by_cases hci : c = inf
    · have hci' : c' ≠ inf := fun h => hcc' (hci.trans h.symm)
      simp only [Z3NetF.yN, if_pos hci, if_neg hci', if_neg hd, zero_sub]
      exact (hx c' d hci' hd hc').ringInverse.neg
    · by_cases hci' : c' = inf
      · simp only [Z3NetF.yN, if_pos hci', if_neg hci, if_neg hd, sub_zero]
        exact (hx c d hci hd hc).ringInverse
      · simp only [Z3NetF.yN, if_neg hci, if_neg hci', if_neg hd]
        rw [inv_sub_inv _ _ (hx c d hci hd hc) (hx c' d hci' hd hc')]
        refine ((hx c d hci hd hc).ringInverse.mul (hx c' d hci' hd hc').ringInverse).mul ?_
        rw [show x c' - x d - (x c - x d) = x c' - x c by ring]
        exact hx c' c hci' hci (Ne.symm hcc')

lemma wN_unit (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d) : IsUnit (Z3NetF.wN inf x c d) := by
  unfold Z3NetF.wN
  split_ifs with h
  · exact isUnit_one
  · push_neg at h
    exact (hx c d h.1 h.2 hcd).ringInverse

/-! ## `β` exists and is unique -/

theorem Gs_beta_core (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur) (d : Fin s)
    (n : ℕ) :
    ∃! b : Fin (s - 1) → R, ∀ c, c ≠ d →
      lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n) = ∑ i : Fin (s - 1), b i * F i c d := by
  classical
  have hcard : Fintype.card {c : Fin s // c ≠ d} = s - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  let e : Fin (s - 1) ≃ {c : Fin s // c ≠ d} := (Fintype.equivFinOfCardEq hcard).symm
  set A : Matrix (Fin (s - 1)) (Fin (s - 1)) R := fun r i => F i (e r).1 d with hA
  set rhs : Fin (s - 1) → R := fun r =>
    lam (e r).1 * (Z3NetF.wN inf x (e r).1 d * Z3NetF.yN inf x (e r).1 d ^ n)
  -- factorization of `A`
  set V : Matrix (Fin (s - 1)) (Fin (s - 1)) R := vandermonde (fun r => Z3NetF.yN inf x (e r).1 d)
  set Um : Matrix (Fin (s - 1)) (Fin (s - 1)) R := fun n' i => Ur d n' i
  have hfac : A = diagonal (fun r => lam (e r).1) * (diagonal (fun r => Z3NetF.wN inf x (e r).1 d) * V) * Um := by
    ext r i
    rw [Matrix.mul_apply]
    simp only [diagonal_mul, V, vandermonde_apply, Um, hA]
    rw [hres.2.2.2 _ d (e r).2 i i.isLt, Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun n' : ℕ => lam (e r).1 * (Z3NetF.wN inf x (e r).1 d *
        Z3NetF.yN inf x (e r).1 d ^ n') * Ur d n' i) (s - 1)]
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by have := i.isLt; omega))
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      rw [hres.2.1 d n' i (by omega) hn'.1, mul_zero]
    · intro n' _; ring
  have hdet : IsUnit A.det := by
    rw [hfac, det_mul, det_mul, det_mul, det_diagonal, det_diagonal, det_vandermonde]
    refine ((IsUnit.prod_univ_iff.mpr fun r => hres.1 _).mul ((IsUnit.prod_univ_iff.mpr fun r =>
      wN_unit inf x hx _ d (e r).2).mul ?_)).mul ?_
    · rw [IsUnit.prod_univ_iff]; intro r
      rw [IsUnit.prod_iff]; intro r' hr'
      have hne : (e r').1 ≠ (e r).1 := by
        intro h; have := e.injective (Subtype.ext h); rw [this] at hr'; simp at hr'
      exact yN_sub_unit inf x hx d _ _ (e r').2 (e r).2 hne
    · rw [det_of_isUpperTriangular]
      · rw [IsUnit.prod_univ_iff]; intro i; exact hres.2.2.1 d i i.isLt
      · intro i j hij; exact hres.2.1 d i j hij i.isLt
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hdet)
  have hinj : Function.Injective A.mulVec := Z3Net.Proofs.mulVec_injective_of_isUnit_det A hdet
  have hiff : ∀ b : Fin (s - 1) → R, (∀ c, c ≠ d → lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n) =
      ∑ i : Fin (s - 1), b i * F i c d) ↔ A *ᵥ b = rhs := by
    intro b
    constructor
    · intro h; funext r
      show (A *ᵥ b) r = lam (e r).1 * (Z3NetF.wN inf x (e r).1 d * Z3NetF.yN inf x (e r).1 d ^ n)
      rw [h _ (e r).2]
      simp only [mulVec, dotProduct, hA]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro h c hc
      have := congrFun h (e.symm ⟨c, hc⟩)
      simp only [mulVec, dotProduct, hA, rhs, Equiv.apply_symm_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨b, hb⟩ := hsurj rhs
  refine ⟨b, (hiff b).mpr hb, fun b' hb' => hinj (((hiff b').mp hb').trans hb.symm)⟩

/-! ## `cor:tsk` -/

theorem tsk_unit_core (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur)
    (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.PGen k inf x F lam Ur β) d).det := by
  obtain ⟨hL, hLu, hU, hUu⟩ := Gs_gauge_core k inf x F lam Ur β hx hres
  obtain ⟨u, hu, H⟩ := gauge_LU (m := s * k) (fun _ => k) (sum_const_k k)
    (Z3NetF.Lmat k inf x lam) (Z3NetF.Ugauge k inf x Ur β) hL hLu hU hUu d hd
  rw [Z3NetF.PGen, H (Z3NetF.frameGraph R k inf x) (Z3NetF.PPhi k inf x F lam Ur β)
    (fun c d hcd => by simp [Z3NetF.PPhi, hcd])]
  refine hu.mul ?_
  have hG := Gk_unit k inf x hx
  rw [frameGraph_eq_invPhi]
  have e1 : Z3NetF.graphGenK (m := s * k) (fun _ => k)
      (invPhi (fun _ => k) (sum_const_k k) (Z3NetF.frameRead (s * k) inf x)) =
      fun c => Z3NetF.frameRead (s * k) inf x c * (Gk k inf x)⁻¹ := by
    funext c; exact graphGenK_inv _ (sum_const_k k) _ hG c
  rw [e1, box_mul_right, det_mul, det_nonsing_inv]
  refine IsUnit.mul ?_ hG.ringInverse
  have hprod : IsUnit (∏ c : Fin s, ∏ c' : Fin s,
      (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (d c' * d c) else 1)) := by
    rw [IsUnit.prod_univ_iff]; intro c
    rw [IsUnit.prod_univ_iff]; intro c'
    split_ifs with h
    · exact (hx c c' h.2.1 h.2.2 (ne_of_gt h.1)).pow _
    · exact isUnit_one
  rcases frame_minor_core inf x (d := d) hd with h | h <;> rw [h]
  · exact hprod
  · exact hprod.neg

theorem tsk_net_core {q : ℕ} [NeZero q] (ψ : R →+* ZMod q) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.Residual inf x F lam Ur) :
    Z3NetF.IsNet0 s q (s * k) (Z3NetF.digPoint q (s * k) fun c => (Z3NetF.PGen k inf x F lam Ur β c).map ψ) := by
  rw [nie_zmod]
  intro d hd
  rw [box_map ψ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (tsk_unit_core k inf x hx F lam Ur β hres d hd).map ψ

theorem away_hom_core (q D : ℕ) (h : Nat.Coprime q D) :
    Nonempty (Localization.Away (D : ℤ) →+* ZMod q) := by
  have hu : IsUnit ((Int.castRingHom (ZMod q)) (D : ℤ)) := by
    rw [map_natCast]
    exact (ZMod.unitOfCoprime D h.symm).isUnit
  exact ⟨IsLocalization.Away.lift (D : ℤ) hu⟩

end

end Z3NetF.Proofs
