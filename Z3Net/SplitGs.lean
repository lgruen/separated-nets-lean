module
public import Z3Net.SplitRs
public import Z3Net.FTsk

@[expose] public section

/-!
# Entry Split, part 3: `prop:Gsplit` (`prop:Gs`, `def:Ns`, `cor:tsk` on the split frame)

The proofs of entry F (`FGs`, `FTsk`) with the frame replaced by the split frame: they use only
that the `w_cd = y_cd` are units and that the `y_cd` of a column have unit differences
(`Gsplit_nodes`), the normal form (`Gsplit_normal`), and unit box minors (`lem:Tsplit`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ}

/-! ## The gauge -/

lemma sUxm_lower {u v : Fin s → R} {F : ℕ → Fin s → Fin s → R} {lam : Fin s → R}
    {Ur : Fin s → ℕ → ℕ → R} (k : ℕ) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.ResidualS u v F lam Ur) (d : Fin s) :
    ∀ i j : Fin k, i < j → Z3NetF.Ux Ur β d (k - 1 - (i : ℕ)) (k - 1 - (j : ℕ)) = 0 := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  have hjk := j.isLt
  simp only [Z3NetF.Ux]
  split_ifs with h1 h2 h3 h4
  · exact hres.2.1 d _ _ (by omega) h2
  · rfl
  · omega
  · omega
  · rfl

lemma sUxm_diag {u v : Fin s → R} {F : ℕ → Fin s → Fin s → R} {lam : Fin s → R}
    {Ur : Fin s → ℕ → ℕ → R} (k : ℕ) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.ResidualS u v F lam Ur) (d : Fin s) (i : Fin k) :
    IsUnit (Z3NetF.Ux Ur β d (k - 1 - (i : ℕ)) (k - 1 - (i : ℕ))) := by
  simp only [Z3NetF.Ux]
  by_cases h1 : k - 1 - (i : ℕ) < s - 1
  · rw [if_pos h1, if_pos h1]; exact hres.2.2.1 d _ h1
  · rw [if_neg h1]; simp

theorem Gsplit_gauge (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.ResidualS u v F lam Ur) :
    (∀ c i j, i < j → Z3NetF.LmatS k u v lam c i j = 0) ∧
      (∀ c i, IsUnit (Z3NetF.LmatS k u v lam c i i)) ∧
      (∀ d i j, i < j → Z3NetF.UgaugeS k v Ur β d i j = 0) ∧
      (∀ d i, IsUnit (Z3NetF.UgaugeS k v Ur β d i i)) := by
  refine ⟨fun c i j hij => ?_, fun c i => ?_, fun d i j hij => ?_, fun d i => ?_⟩
  · simp only [Z3NetF.LmatS, Z3NetF.Lgauge]
    rw [diagonal_apply_ne _ (ne_of_lt hij)]
  · simp only [Z3NetF.LmatS, Z3NetF.Lgauge, diagonal_apply_eq]
    split_ifs
    · exact (hres.1 c).mul ((Psplit_unit huv c).pow k).ringInverse
    · exact isUnit_one
  · exact lower_mul _ _ (toep_lower k _) (fun i j h => by
      simp only [of_apply]; exact sUxm_lower k β hres d i j h) i j hij
  · rw [Z3NetF.UgaugeS, diag_mul _ _ (toep_lower k _) (fun i j h => by
      simp only [of_apply]; exact sUxm_lower k β hres d i j h)]
    refine IsUnit.mul ?_ ?_
    · simp only [Z3NetF.toep, le_refl, if_true, Nat.sub_self]
      exact piSplit_unit k u v huv d
    · simp only [of_apply]; exact sUxm_diag k β hres d i

/-! ## Row `0` of the gauged block -/

lemma srow0_LPT (k : ℕ) (u v : Fin s → R) (lam : Fin s → R) (huv : Z3NetF.SplitOK u v)
    (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (l : Fin k) :
    (Z3NetF.LmatS k u v lam c * Z3NetF.splitGraph R k u v c d *
        Z3NetF.toep k (Z3NetF.piSplit k v d)) r l =
      lam c * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ (k - 1 - (l : ℕ))) := by
  have h := Gsplit_normal k u v huv c d hcd r hr l
  rw [Matrix.mul_assoc, Z3NetF.Lgauge, diagonal_mul, if_pos hr] at h
  rw [Matrix.mul_assoc, Z3NetF.LmatS, Z3NetF.Lgauge, diagonal_mul, if_pos hr, mul_assoc, h]

/-- The sum `∑_{n' < k} λ' w y^(n') Ux[n', n]` is the design (`n < s-1`) or `0`. -/
lemma ssum_Ux (k : ℕ) (u v : Fin s → R) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.ResidualS u v F lam Ur) (hβ : Z3NetF.BetaRelS u v F lam β)
    (c d : Fin s) (hcd : c ≠ d) (n : ℕ) (hn : n < k) :
    ∑ n' ∈ range k, lam c * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n') *
        Z3NetF.Ux Ur β d n' n =
      if n < s - 1 then F n c d else 0 := by
  set g : ℕ → R := fun n' => lam c * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n') with hg
  have hF0 : ∀ i, i < s - 1 → ∑ n' ∈ range (i + 1), g n' * Ur d n' i = F i c d := by
    intro i hi
    rw [hres.2.2.2 c d hcd i hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [hg]; ring
  have hFN : ∀ i N, i < s - 1 → i + 1 ≤ N →
      ∑ n' ∈ range N, g n' * (if n' < s - 1 then Ur d n' i else 0) = F i c d := by
    intro i N hi hN
    rw [← hF0 i hi]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr hN)
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      split_ifs with h
      · rw [hres.2.1 d n' i (by omega) h, mul_zero]
      · rw [mul_zero]
    · intro n' hn'
      simp only [mem_range] at hn'
      rw [if_pos (by omega)]
  by_cases hns : n < s - 1
  · rw [if_pos hns, ← hFN n k hns (by omega)]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [Z3NetF.Ux, if_pos hns, hg]
  · rw [if_neg hns]
    have hsplit : ∀ n', Z3NetF.Ux Ur β d n' n = (if n' = n then 1 else 0) +
        (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) := by
      intro n'
      simp only [Z3NetF.Ux, if_neg hns]
      by_cases h1 : n' = n
      · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
      · rw [if_neg h1, if_neg h1, zero_add]
    simp only [hsplit, mul_add, Finset.sum_add_distrib]
    have e1 : ∑ n' ∈ range k, g n' * (if n' = n then 1 else 0) = g n := by
      rw [Finset.sum_eq_single n]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb; rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_range.mpr hn) h
    have e2 : ∑ n' ∈ range k, g n' *
        (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) =
        -∑ i ∈ range (s - 1), β d n i * F i c d := by
      have : ∀ n', g n' * (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) =
          -∑ i ∈ range (s - 1), β d n i * (g n' * (if n' < s - 1 then Ur d n' i else 0)) := by
        intro n'
        split_ifs
        · rw [mul_neg, Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        · simp
      simp only [this, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.mul_sum, hFN i k (mem_range.mp hi) (by have := mem_range.mp hi; omega)]
    rw [e1, e2, ← hβ d n (by omega) c hcd]
    simp only [hg]; ring

theorem Gsplit_row0 (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.ResidualS u v F lam Ur)
    (hβ : Z3NetF.BetaRelS u v F lam β) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) (j : Fin k) :
    (Z3NetF.LmatS k u v lam c * Z3NetF.splitGraph R k u v c d * Z3NetF.UgaugeS k v Ur β d) r j =
      if k - 1 - (j : ℕ) < s - 1 then F (k - 1 - (j : ℕ)) c d else 0 := by
  rw [Z3NetF.UgaugeS, ← Matrix.mul_assoc, mul_apply]
  simp only [srow0_LPT k u v lam huv c d hcd r hr, of_apply]
  rw [← ssum_Ux k u v F lam Ur β hres hβ c d hcd (k - 1 - j) (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun l => lam c * (Z3NetF.ySplit u v c d *
    Z3NetF.ySplit u v c d ^ (k - 1 - l)) * Z3NetF.Ux Ur β d (k - 1 - l) (k - 1 - (j : ℕ))) k]
  exact Finset.sum_range_reflect (fun n' => lam c * (Z3NetF.ySplit u v c d *
    Z3NetF.ySplit u v c d ^ n') * Z3NetF.Ux Ur β d n' (k - 1 - (j : ℕ))) k

/-! ## `β` exists and is unique -/

theorem Gsplit_beta (hs : 2 ≤ s) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (hres : Z3NetF.ResidualS u v F lam Ur) (d : Fin s) (n : ℕ) :
    ∃! b : Fin (s - 1) → R, ∀ c, c ≠ d →
      lam c * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n) =
        ∑ i : Fin (s - 1), b i * F i c d := by
  classical
  have hcard : Fintype.card {c : Fin s // c ≠ d} = s - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  let e : Fin (s - 1) ≃ {c : Fin s // c ≠ d} := (Fintype.equivFinOfCardEq hcard).symm
  set A : Matrix (Fin (s - 1)) (Fin (s - 1)) R := fun r i => F i (e r).1 d with hA
  set rhs : Fin (s - 1) → R := fun r =>
    lam (e r).1 * (Z3NetF.ySplit u v (e r).1 d * Z3NetF.ySplit u v (e r).1 d ^ n)
  set V : Matrix (Fin (s - 1)) (Fin (s - 1)) R := vandermonde (fun r => Z3NetF.ySplit u v (e r).1 d)
  set Um : Matrix (Fin (s - 1)) (Fin (s - 1)) R := fun n' i => Ur d n' i
  have hfac : A = diagonal (fun r => lam (e r).1) *
      (diagonal (fun r => Z3NetF.ySplit u v (e r).1 d) * V) * Um := by
    ext r i
    rw [Matrix.mul_apply]
    simp only [diagonal_mul, V, vandermonde_apply, Um, hA]
    rw [hres.2.2.2 _ d (e r).2 i i.isLt, Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun n' : ℕ => lam (e r).1 * (Z3NetF.ySplit u v (e r).1 d *
        Z3NetF.ySplit u v (e r).1 d ^ n') * Ur d n' i) (s - 1)]
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by have := i.isLt; omega))
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      rw [hres.2.1 d n' i (by omega) hn'.1, mul_zero]
    · intro n' _; ring
  have hdet : IsUnit A.det := by
    rw [hfac, det_mul, det_mul, det_mul, det_diagonal, det_diagonal, det_vandermonde]
    refine ((IsUnit.prod_univ_iff.mpr fun r => hres.1 _).mul ((IsUnit.prod_univ_iff.mpr fun r =>
      ySplit_unit huv _ d).mul ?_)).mul ?_
    · rw [IsUnit.prod_univ_iff]; intro r
      rw [IsUnit.prod_iff]; intro r' hr'
      have hne : (e r').1 ≠ (e r).1 := by
        intro h; have := e.injective (Subtype.ext h); rw [this] at hr'; simp at hr'
      exact (Gsplit_nodes u v huv _ _ d (e r').2 (e r).2).2.2 hne
    · rw [det_of_isUpperTriangular]
      · rw [IsUnit.prod_univ_iff]; intro i; exact hres.2.2.1 d i i.isLt
      · intro i j hij; exact hres.2.1 d i j hij i.isLt
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hdet)
  have hinj : Function.Injective A.mulVec := Z3Net.Proofs.mulVec_injective_of_isUnit_det A hdet
  have hiff : ∀ b : Fin (s - 1) → R, (∀ c, c ≠ d →
      lam c * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n) =
        ∑ i : Fin (s - 1), b i * F i c d) ↔ A *ᵥ b = rhs := by
    intro b
    constructor
    · intro h; funext r
      show (A *ᵥ b) r = lam (e r).1 * (Z3NetF.ySplit u v (e r).1 d * Z3NetF.ySplit u v (e r).1 d ^ n)
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

theorem Gsplit_tsk_unit (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.ResidualS u v F lam Ur)
    (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.PGenS k u v F lam Ur β) d).det := by
  obtain ⟨hL, hLu, hU, hUu⟩ := Gsplit_gauge k u v huv F lam Ur β hres
  obtain ⟨w, hw, H⟩ := gauge_LU (m := s * k) (fun _ => k) (sum_const_k k)
    (Z3NetF.LmatS k u v lam) (Z3NetF.UgaugeS k v Ur β) hL hLu hU hUu d hd
  rw [Z3NetF.PGenS, H (Z3NetF.splitGraph R k u v) (Z3NetF.PPhiS k u v F lam Ur β)
    (fun c d hcd => by simp [Z3NetF.PPhiS, hcd])]
  refine hw.mul ?_
  rw [graphGenK_splitGraph k u v huv, box_mul_right, det_mul, det_nonsing_inv]
  exact (split_box_unit k huv d hd).mul (GkS_unit k u v huv).ringInverse

theorem Gsplit_tsk_net {q : ℕ} [NeZero q] (ψ : R →+* ZMod q) (k : ℕ)
    (u v : Fin s → R) (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.ResidualS u v F lam Ur) :
    Z3NetF.IsNet0 s q (s * k)
      (Z3NetF.digPoint q (s * k) fun c => (Z3NetF.PGenS k u v F lam Ur β c).map ψ) := by
  rw [nie_zmod]
  intro d hd
  rw [box_map ψ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Gsplit_tsk_unit k u v huv F lam Ur β hres d hd).map ψ

end

end Z3NetF.Proofs
