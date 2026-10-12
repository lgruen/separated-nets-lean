/-
Proof module of entry Skel (`prop:skelcomp`(i), consequences: `prop:Gs` and `prop:F` on a set of
rows, for arbitrary depths `K`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkCompE

@[expose] public section

/-!
# Entry Skel: `prop:Gs` and `prop:F` on the rows `S`

* `SkComp.col_beta`, `SkComp.col_gauge`: the column argument of `prop:Gs` for one column with an
  abstract set `T` of rows (`ℓ = #T`), values `a_c y_c^n` with units `a_c` and `y_c` of unit
  differences: the residual data `U'` extend to a lower-triangular unit-diagonal level gauge for
  every number `k` of levels.
* `skel_Gs`, `skel_reach_iff`: the Challenge statements (rows `S`, `ℓ_d = #(S \ {d})`).
-/

namespace Z3NetF.Proofs

namespace SkComp

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## The column argument -/

section Column

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma col_beta (ℓ : ℕ) (T : Finset ι) (hT : T.card = ℓ) (a y : ι → R)
    (ha : ∀ c ∈ T, IsUnit (a c)) (hy : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → IsUnit (y c - y c'))
    (Ur : ℕ → ℕ → R) (hUl : ∀ n' n, n < n' → n' < ℓ → Ur n' n = 0)
    (hUu : ∀ n, n < ℓ → IsUnit (Ur n n)) (G : ℕ → ι → R)
    (hG : ∀ c ∈ T, ∀ n, n < ℓ → G n c = a c * ∑ n' ∈ range (n + 1), y c ^ n' * Ur n' n)
    (n : ℕ) : ∃ b : ℕ → R, ∀ c ∈ T, a c * y c ^ n = ∑ i ∈ range ℓ, b i * G i c := by
  classical
  let e : Fin ℓ ≃ {c // c ∈ T} := (T.equivFinOfCardEq hT).symm
  set A : Matrix (Fin ℓ) (Fin ℓ) R := fun r i => G i (e r).1 with hA
  set rhs : Fin ℓ → R := fun r => a (e r).1 * y (e r).1 ^ n
  set V : Matrix (Fin ℓ) (Fin ℓ) R := vandermonde (fun r => y (e r).1)
  set Um : Matrix (Fin ℓ) (Fin ℓ) R := fun n' i => Ur n' i
  have hfac : A = diagonal (fun r => a (e r).1) * V * Um := by
    ext r i
    rw [Matrix.mul_apply]
    simp only [diagonal_mul, V, vandermonde_apply, Um, hA]
    rw [hG _ (e r).2 i i.isLt, Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun n' : ℕ => a (e r).1 * y (e r).1 ^ n' * Ur n' i) ℓ]
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by have := i.isLt; omega))
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      rw [hUl n' i (by omega) hn'.1, mul_zero]
    · intro n' _; ring
  have hdet : IsUnit A.det := by
    rw [hfac, det_mul, det_mul, det_diagonal, det_vandermonde]
    refine ((IsUnit.prod_univ_iff.mpr fun r => ha _ (e r).2).mul ?_).mul ?_
    · rw [IsUnit.prod_univ_iff]; intro r
      rw [IsUnit.prod_iff]; intro r' hr'
      have hne : (e r').1 ≠ (e r).1 := by
        intro h; have := e.injective (Subtype.ext h); rw [this] at hr'; simp at hr'
      exact hy _ (e r').2 _ (e r).2 hne
    · rw [det_of_isUpperTriangular]
      · rw [IsUnit.prod_univ_iff]; intro i; exact hUu i i.isLt
      · intro i j hij; exact hUl i j hij i.isLt
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hdet)
  obtain ⟨b0, hb0⟩ := hsurj rhs
  refine ⟨fun i => if h : i < ℓ then b0 ⟨i, h⟩ else 0, fun c hc => ?_⟩
  have := congrFun hb0 (e.symm ⟨c, hc⟩)
  simp only [mulVec, dotProduct, hA, rhs, Equiv.apply_symm_apply] at this
  rw [← this, ← Fin.sum_univ_eq_sum_range (fun i => (if h : i < ℓ then b0 ⟨i, h⟩ else 0) * G i c) ℓ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, mul_comm]

/-- The all-`k` gauge in the `x`-index (`prop:Gs`): `U'` on the indices `< ℓ`, and for `n ≥ ℓ`
the column `e_n - ∑_{i < ℓ} β_{n,i} (column i of U')`. -/
def Vx (ℓ : ℕ) (Ur β : ℕ → ℕ → R) (n' n : ℕ) : R :=
  if n < ℓ then (if n' < ℓ then Ur n' n else 0)
  else if n' = n then 1
  else if n' < ℓ then -∑ i ∈ range ℓ, β n i * Ur n' i else 0

omit [DecidableEq ι] in
lemma sum_Vx (ℓ k : ℕ) (T : Finset ι) (a y : ι → R) (Ur β : ℕ → ℕ → R)
    (hUl : ∀ n' n, n < n' → n' < ℓ → Ur n' n = 0) (G : ℕ → ι → R)
    (hG : ∀ c ∈ T, ∀ n, n < ℓ → G n c = a c * ∑ n' ∈ range (n + 1), y c ^ n' * Ur n' n)
    (hβ : ∀ n, ∀ c ∈ T, a c * y c ^ n = ∑ i ∈ range ℓ, β n i * G i c)
    (c : ι) (hc : c ∈ T) (n : ℕ) (hn : n < k) :
    ∑ n' ∈ range k, a c * y c ^ n' * Vx ℓ Ur β n' n = if n < ℓ then G n c else 0 := by
  set g : ℕ → R := fun n' => a c * y c ^ n' with hg
  have hF0 : ∀ i, i < ℓ → ∑ n' ∈ range (i + 1), g n' * Ur n' i = G i c := by
    intro i hi
    rw [hG c hc i hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [hg]; ring
  have hFN : ∀ i N, i < ℓ → i + 1 ≤ N →
      ∑ n' ∈ range N, g n' * (if n' < ℓ then Ur n' i else 0) = G i c := by
    intro i N hi hN
    rw [← hF0 i hi]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr hN)
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      split_ifs with h
      · rw [hUl n' i (by omega) h, mul_zero]
      · rw [mul_zero]
    · intro n' hn'
      simp only [mem_range] at hn'
      rw [if_pos (by omega)]
  by_cases hns : n < ℓ
  · rw [if_pos hns, ← hFN n k hns (by omega)]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [Vx, if_pos hns, hg]
  · rw [if_neg hns]
    have hsplit : ∀ n', Vx ℓ Ur β n' n = (if n' = n then 1 else 0) +
        (if n' < ℓ then -∑ i ∈ range ℓ, β n i * Ur n' i else 0) := by
      intro n'
      simp only [Vx, if_neg hns]
      by_cases h1 : n' = n
      · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
      · rw [if_neg h1, if_neg h1, zero_add]
    simp only [hsplit, mul_add, Finset.sum_add_distrib]
    have e1 : ∑ n' ∈ range k, a c * y c ^ n' * (if n' = n then 1 else 0) = g n := by
      rw [Finset.sum_eq_single n]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb; rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_range.mpr hn) h
    have e2 : ∑ n' ∈ range k, a c * y c ^ n' * (if n' < ℓ then -∑ i ∈ range ℓ, β n i * Ur n' i else 0) =
        -∑ i ∈ range ℓ, β n i * G i c := by
      have : ∀ n', a c * y c ^ n' * (if n' < ℓ then -∑ i ∈ range ℓ, β n i * Ur n' i else 0) =
          -∑ i ∈ range ℓ, β n i * (g n' * (if n' < ℓ then Ur n' i else 0)) := by
        intro n'
        split_ifs
        · rw [mul_neg, Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl fun i _ => by simp only [hg]; ring
        · simp
      simp only [this, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.mul_sum, hFN i k (mem_range.mp hi) (by have := mem_range.mp hi; omega)]
    rw [e1, e2, ← hβ n c hc]
    simp only [hg]; ring

omit [DecidableEq ι] in
/-- **The column argument of `prop:Gs`** with an abstract set `T` of rows. -/
lemma col_gauge (ℓ k : ℕ) (T : Finset ι) (hT : T.card = ℓ) (a y : ι → R)
    (ha : ∀ c ∈ T, IsUnit (a c)) (hy : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → IsUnit (y c - y c'))
    (Ur : ℕ → ℕ → R) (hUl : ∀ n' n, n < n' → n' < ℓ → Ur n' n = 0)
    (hUu : ∀ n, n < ℓ → IsUnit (Ur n n)) (G : ℕ → ι → R)
    (hG : ∀ c ∈ T, ∀ n, n < ℓ → G n c = a c * ∑ n' ∈ range (n + 1), y c ^ n' * Ur n' n) :
    ∃ V : Matrix (Fin k) (Fin k) R, Z3NetF.IsLTU V ∧ ∀ c ∈ T, ∀ j : Fin k,
      ∑ l : Fin k, a c * y c ^ (k - 1 - (l : ℕ)) * V l j =
        if k - 1 - (j : ℕ) < ℓ then G (k - 1 - (j : ℕ)) c else 0 := by
  choose β hβ using fun n => col_beta ℓ T hT a y ha hy Ur hUl hUu G hG n
  refine ⟨Matrix.of fun i j : Fin k => Vx ℓ Ur β (k - 1 - (i : ℕ)) (k - 1 - (j : ℕ)), ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hjk := j.isLt
    simp only [of_apply, Vx]
    split_ifs with h1 h2 h3 h4
    · exact hUl _ _ (by omega) h2
    · rfl
    · omega
    · omega
    · rfl
  · intro i
    simp only [of_apply, Vx]
    by_cases h1 : k - 1 - (i : ℕ) < ℓ
    · rw [if_pos h1, if_pos h1]; exact hUu _ h1
    · rw [if_neg h1]; simp
  · intro c hc j
    simp only [of_apply]
    rw [← sum_Vx ℓ k T a y Ur β hUl G hG (fun n c hc => hβ n c hc) c hc (k - 1 - j) (by omega)]
    rw [Fin.sum_univ_eq_sum_range (fun l => a c * y c ^ (k - 1 - l) *
      Vx ℓ Ur β (k - 1 - l) (k - 1 - (j : ℕ))) k]
    exact Finset.sum_range_reflect (fun n' => a c * y c ^ n' * Vx ℓ Ur β n' (k - 1 - (j : ℕ))) k

end Column

/-! ## Row `0` of the gauged frame block -/

variable {s m : ℕ} (K : Fin s → ℕ) (inf : Fin s) (x : Fin s → R)

lemma uNK_unit (hx : Z3NetF.PlacesOK inf x) (d : Fin s) :
    IsUnit ((Z3NetF.uNK K inf x d).coeff 0) := by
  rw [coeff_zero_eq_eval_zero, Z3NetF.uNK]
  split_ifs with hd
  · simp [eval_prod]
  · simp only [eval_prod, eval_pow, eval_add, eval_C, eval_X, add_zero]
    rw [IsUnit.prod_iff]
    intro b hb
    obtain ⟨-, hb1, hb2⟩ := mem_filter.mp hb
    exact (hx d b hd hb1 (Ne.symm hb2)).pow _

lemma row0_mul (hK : ∑ c, K c = m) (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d)
    (sc : R) (W : Matrix (Fin (K d)) (Fin (K d)) R) (j : Fin (K d)) :
    Z3NetF.ent (Z3NetF.Lgauge (m - K c) (sc * Ring.inverse (Z3NetF.QfK K inf x c)) *
        Z3NetF.frameGraphK R m K inf x c d * (Z3NetF.toep (K d) (Z3NetF.uNK K inf x d) * W)) 0 j =
      ∑ l : Fin (K d), sc * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (K d - 1 - (l : ℕ))) *
        W l j := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hlt := Kc_lt K hK c d hcd (by have := j.isLt; omega)
  have h0 : 0 < m - K c := by omega
  unfold Z3NetF.ent
  rw [dif_pos ⟨h0, j.isLt⟩, ← Matrix.mul_assoc, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Matrix.mul_assoc, Z3NetF.Lgauge, Matrix.diagonal_mul, if_pos rfl,
    key_PsiK K inf x hK hx c d l ⟨0, h0⟩]
  have hidx : (⟨K c + ((⟨0, h0⟩ : Fin (m - K c)) : ℕ), by omega⟩ : Fin m) = ⟨K c, hlt⟩ :=
    Fin.ext (by simp)
  rw [hidx, off_EK K inf x hK hx c d hcd l l.isLt]
  have hQ := Ring.inverse_mul_cancel _ (QfK_unit K inf x hx c)
  rw [show sc * Ring.inverse (Z3NetF.QfK K inf x c) * (Z3NetF.QfK K inf x c *
      (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (K d - 1 - (l : ℕ)))) =
      sc * (Ring.inverse (Z3NetF.QfK K inf x c) * Z3NetF.QfK K inf x c) *
      (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (K d - 1 - (l : ℕ))) by ring, hQ, mul_one]

lemma toep_lowerK (k : ℕ) (u : R[X]) : ∀ i j : Fin k, i < j → Z3NetF.toep k u i j = 0 := by
  intro i j hij
  simp only [Z3NetF.toep]
  rw [if_neg (not_le.mpr hij)]

lemma toep_mul_LTU (hx : Z3NetF.PlacesOK inf x) (d : Fin s) (V : Matrix (Fin (K d)) (Fin (K d)) R)
    (hV : Z3NetF.IsLTU V) : Z3NetF.IsLTU (Z3NetF.toep (K d) (Z3NetF.uNK K inf x d) * V) := by
  refine ⟨lower_mul _ _ (toep_lowerK _ _) hV.1, fun i => ?_⟩
  rw [diag_mul _ _ (toep_lowerK _ _) hV.1]
  refine IsUnit.mul ?_ (hV.2 i)
  simp only [Z3NetF.toep, le_refl, if_true, Nat.sub_self]
  exact uNK_unit K inf x hx d

end

end SkComp

open SkComp Finset Matrix in
/-- **`prop:skelcomp`(i), consequence: `prop:Gs` on the rows `S`.** -/
theorem skel_Gs {R : Type*} [CommRing R] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x) (S : Finset (Fin s))
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (hres : ResidualSk inf x S F lam Ur) :
    ∃ U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R, (∀ d, IsLTU (U d)) ∧
      ∀ c ∈ S, ∀ d, c ≠ d → ∀ j : Fin (K d),
        ent (Lgauge (m - K c) (lam c * Ring.inverse (QfK K inf x c)) * frameGraphK R m K inf x c d *
          U d) 0 j = if K d - 1 - (j : ℕ) < (S.erase d).card then F (K d - 1 - (j : ℕ)) c d else 0 := by
  classical
  have hcol : ∀ d : Fin s, ∃ V : Matrix (Fin (K d)) (Fin (K d)) R, IsLTU V ∧
      ∀ c ∈ S.erase d, ∀ j : Fin (K d),
        ∑ l : Fin (K d), lam c * wN inf x c d * yN inf x c d ^ (K d - 1 - (l : ℕ)) * V l j =
          if K d - 1 - (j : ℕ) < (S.erase d).card then F (K d - 1 - (j : ℕ)) c d else 0 := by
    intro d
    refine col_gauge (S.erase d).card (K d) (S.erase d) rfl (fun c => lam c * wN inf x c d)
      (fun c => yN inf x c d) ?_ ?_ (Ur d) (fun n' n h1 h2 => hres.2.1 d n' n h1 h2)
      (fun n hn => hres.2.2.1 d n hn) (fun n c => F n c d) ?_
    · intro c hc
      obtain ⟨hcd, hcS⟩ := mem_erase.mp hc
      exact (hres.1 c hcS).mul (wN_unit inf x hx c d hcd)
    · intro c hc c' hc' hne
      exact yN_sub_unit inf x hx d c c' (mem_erase.mp hc).1 (mem_erase.mp hc').1 hne
    · intro c hc n hn
      obtain ⟨hcd, hcS⟩ := mem_erase.mp hc
      rw [hres.2.2.2 c hcS d hcd n hn, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n' _ => by ring
  choose V hV hVrow using hcol
  refine ⟨fun d => toep (K d) (uNK K inf x d) * V d, fun d => toep_mul_LTU K inf x hx d _ (hV d),
    fun c hc d hcd j => ?_⟩
  rw [row0_mul K inf x hK hx c d hcd, ← hVrow d c (mem_erase.mpr ⟨hcd, hc⟩) j]
  refine Finset.sum_congr rfl fun l _ => by ring

open SkComp Finset Matrix in
/-- **`prop:skelcomp`(i), consequence: `prop:F` on the rows `S`.** -/
theorem skel_reach_iff {R : Type*} [CommRing R] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x) (S : Finset (Fin s))
    (hKS : ∀ d, (S.erase d).card ≤ K d) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (hlam : ∀ c ∈ S, IsUnit (lam c)) :
    (∃ U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R, (∀ d, IsLTU (U d)) ∧
      ∀ c ∈ S, ∀ d, c ≠ d → ∀ j : Fin (K d),
        ent (Lgauge (m - K c) (lam c * Ring.inverse (QfK K inf x c)) * frameGraphK R m K inf x c d *
          U d) 0 j = if K d - 1 - (j : ℕ) < (S.erase d).card then F (K d - 1 - (j : ℕ)) c d else 0) ↔
      ∃ Ur : Fin s → ℕ → ℕ → R, ResidualSk inf x S F lam Ur := by
  classical
  constructor
  · rintro ⟨U, hU, hrow⟩
    have hTdet : ∀ d, IsUnit (toep (K d) (uNK K inf x d)).det := by
      intro d
      rw [det_of_isLowerTriangular _ (fun i j hij => toep_lowerK _ _ i j hij)]
      rw [IsUnit.prod_univ_iff]; intro i
      simp only [toep, le_refl, if_true, Nat.sub_self]
      exact uNK_unit K inf x hx d
    set V : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R :=
      fun d => (toep (K d) (uNK K inf x d))⁻¹ * U d with hVdef
    have hTinv_lower : ∀ d, ∀ i j : Fin (K d), i < j → (toep (K d) (uNK K inf x d))⁻¹ i j = 0 := by
      intro d i j hij
      let _ := invertibleOfIsUnitDet _ (hTdet d)
      have hbt : (toep (K d) (uNK K inf x d)).BlockTriangular OrderDual.toDual :=
        fun i j hij => toep_lowerK _ _ i j hij
      exact blockTriangular_inv_of_blockTriangular hbt hij
    have hVl : ∀ d i j, i < j → V d i j = 0 := fun d =>
      lower_mul _ _ (hTinv_lower d) (hU d).1
    have hVu : ∀ d i, IsUnit (V d i i) := by
      intro d i
      show IsUnit (((toep (K d) (uNK K inf x d))⁻¹ * U d) i i)
      rw [diag_mul _ _ (hTinv_lower d) (hU d).1]
      refine IsUnit.mul ?_ ((hU d).2 i)
      have h1 : ((toep (K d) (uNK K inf x d))⁻¹ * toep (K d) (uNK K inf x d)) i i = 1 := by
        rw [nonsing_inv_mul _ (hTdet d), one_apply_eq]
      rw [diag_mul _ _ (hTinv_lower d) (fun i j hij => toep_lowerK _ _ i j hij)] at h1
      exact IsUnit.of_mul_eq_one _ h1
    have hUV : ∀ d, U d = toep (K d) (uNK K inf x d) * V d := by
      intro d; rw [hVdef, ← Matrix.mul_assoc, mul_nonsing_inv _ (hTdet d), Matrix.one_mul]
    refine ⟨fun d n' n => if h : n' < K d ∧ n < K d then
      V d ⟨K d - 1 - n', by omega⟩ ⟨K d - 1 - n, by omega⟩ else 0, hlam, ?_, ?_, ?_⟩
    · intro d n' n hnn' hn's
      have := hKS d
      simp only
      rw [dif_pos ⟨by omega, by omega⟩]
      exact hVl d _ _ (by show K d - 1 - n' < K d - 1 - n; omega)
    · intro d n hn
      have := hKS d
      simp only
      rw [dif_pos ⟨by omega, by omega⟩]
      exact hVu d _
    · intro c hc d hcd n hn
      have hKd := hKS d
      have h := hrow c hc d hcd ⟨K d - 1 - n, by omega⟩
      simp only [show K d - 1 - (K d - 1 - n) = n by omega, if_pos hn] at h
      have h2 := row0_mul K inf x hK hx c d hcd (lam c) (V d) ⟨K d - 1 - n, by omega⟩
      rw [← h, hUV d]
      refine h2.trans ?_
      set w := wN inf x c d
      set y := yN inf x c d
      have hA : ∑ l : Fin (K d), lam c * (w * y ^ (K d - 1 - (l : ℕ))) *
            V d l ⟨K d - 1 - n, by omega⟩ =
          ∑ l ∈ range (K d), (if h : l < K d then lam c * (w * y ^ (K d - 1 - l)) *
            V d ⟨l, h⟩ ⟨K d - 1 - n, by omega⟩ else 0) := by
        rw [← Fin.sum_univ_eq_sum_range (fun l => if h : l < K d then lam c * (w * y ^ (K d - 1 - l)) *
          V d ⟨l, h⟩ ⟨K d - 1 - n, by omega⟩ else 0) (K d)]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [dif_pos l.isLt]
      rw [hA, ← Finset.sum_range_reflect, Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
      · intro n' hn'
        simp only [mem_sdiff, mem_range] at hn'
        rw [dif_pos (by omega)]
        have := hVl d ⟨K d - 1 - n', by omega⟩ ⟨K d - 1 - n, by omega⟩
          (by show K d - 1 - n' < K d - 1 - n; omega)
        rw [this, mul_zero]
      · intro n' hn'
        simp only [mem_range] at hn'
        have c1 : n' < K d ∧ n < K d := ⟨by omega, by omega⟩
        have c2 : K d - 1 - n' < K d := by omega
        dsimp only
        rw [dif_pos c1, dif_pos c2]
        have e : K d - 1 - (K d - 1 - n') = n' := by omega
        simp only [e]
        ring
  · rintro ⟨Ur, hres⟩
    exact skel_Gs K hK inf x hx S F lam Ur hres

end Z3NetF.Proofs
