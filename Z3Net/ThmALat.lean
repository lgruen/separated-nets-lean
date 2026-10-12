/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmALatDefs
public import Z3Net.ThmAUstar

@[expose] public section

/-!
# Theorem A, part 3: the real geometry of the flag (`lem:adelic`, archimedean part)

V14 stage S4.

* Vectors of real polynomials (`polyVecR`, linear in the polynomial) and the subspaces
  `Vlt d J` (`V_{J-1} ⊗ ℝ`): membership is "vector of a real polynomial of degree `< J`" (`mem_Vlt`),
  and for a flag `B_i ∈ Λ_i`, `κ_i(B_i) = γ_i` it is the real span of `B_0, …, B_{J-1}`
  (`Vlt_le_span`).
* The rational projection coefficients of `def:Ustar` (`ProjCoef`) are those of Mathlib's
  orthogonal projection onto `V_{j-1} ⊗ ℝ` (`proj_of_projCoef`, `projCoef_of_proj`).
* The Gram–Schmidt vector `u = B_j − P_{V_{j-1}} B_j` of a flag: it lies on the line
  `V_j ∩ V_{j-1}^⊥`, `⟨u, (w_c g(y_c))_c⟩ = g_j ‖u‖² / γ_j` for every real `g` of degree `≤ j`
  (`inner_u_poly`), `u ≠ 0`, and `π_j((w_c g(y_c))_c) = (g_j / γ_j) u` (`pi_poly`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

/-! ## Vectors of real polynomials -/

lemma polyVecR_apply (d : Fin s) (g : Polynomial ℝ) (c : Fin s) :
    polyVecR d g c = if c = d then 0 else (wQ c d : ℝ) * g.eval (yQ c d : ℝ) := rfl

lemma colE_apply (E : Fin s → ℤ) (c : Fin s) : colE E c = (E c : ℝ) := rfl

/-- `g ↦ (w_c g(y_c))_c` as a linear map. -/
def pvL (d : Fin s) : Polynomial ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin s) where
  toFun := polyVecR d
  map_add' g h := by
    ext c; simp only [polyVecR_apply, PiLp.add_apply, eval_add]; split_ifs <;> ring
  map_smul' a g := by
    ext c; simp only [polyVecR_apply, PiLp.smul_apply, eval_smul, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma pvL_apply (d : Fin s) (g : Polynomial ℝ) : pvL d g = polyVecR d g := rfl

lemma polyVecR_add (d : Fin s) (g h : Polynomial ℝ) :
    polyVecR d (g + h) = polyVecR d g + polyVecR d h := (pvL d).map_add g h

lemma polyVecR_sub (d : Fin s) (g h : Polynomial ℝ) :
    polyVecR d (g - h) = polyVecR d g - polyVecR d h := (pvL d).map_sub g h

lemma polyVecR_smul (d : Fin s) (a : ℝ) (g : Polynomial ℝ) :
    polyVecR d (a • g) = a • polyVecR d g := (pvL d).map_smul a g

lemma polyVecR_zero (d : Fin s) : polyVecR d 0 = 0 := (pvL d).map_zero

/-- An integer column of `Λ_i` is the vector of its (real) polynomial. -/
lemma colE_eq_poly (hs : 3 ≤ s) (d : Fin s) (E : Fin s → ℤ) (hE0 : E d = 0) :
    colE E = polyVecR d ((colPoly d fun c => (E c : ℚ)).map (algebraMap ℚ ℝ)) := by
  ext c
  rw [colE_apply, polyVecR_apply]
  split_ifs with h
  · rw [h, hE0]; simp
  · have := colPoly_rep (by omega) d (fun c => (E c : ℚ)) c h
    rw [eval_map, ← eq_ratCast (algebraMap ℚ ℝ) (yQ c d), eval₂_at_apply, eq_ratCast]
    have h2 := congrArg (fun x : ℚ => (x : ℝ)) this
    push_cast at h2
    exact h2

lemma degree_lt_of (g : Polynomial ℝ) (j : ℕ) (hg : g.natDegree ≤ j) (hc : g.coeff j = 0) :
    g.degree < j := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rcases Nat.lt_or_ge j m with h | h
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [show m = j by omega]; exact hc

/-! ## The subspaces `Vlt d J` -/

/-- `{(w_c g(y_c))_c : deg g < J}` is already a subspace. -/
def VltSub (d : Fin s) (J : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin s)) where
  carrier := {x | ∃ g : Polynomial ℝ, g.degree < J ∧ x = polyVecR d g}
  add_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨g + h, (degree_add_le _ _).trans_lt (max_lt hg hh), (polyVecR_add d g h).symm⟩
  zero_mem' := ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe _, (polyVecR_zero d).symm⟩
  smul_mem' := by
    rintro a _ ⟨g, hg, rfl⟩
    exact ⟨a • g, (degree_smul_le _ _).trans_lt hg, (polyVecR_smul d a g).symm⟩

lemma Vlt_eq (d : Fin s) (J : ℕ) : Vlt d J = VltSub d J :=
  Submodule.span_eq (VltSub d J)

lemma mem_Vlt (d : Fin s) (J : ℕ) (x : EuclideanSpace ℝ (Fin s)) :
    x ∈ Vlt d J ↔ ∃ g : Polynomial ℝ, g.degree < J ∧ x = polyVecR d g := by
  rw [Vlt_eq]; rfl

lemma polyVecR_mem (d : Fin s) {J : ℕ} (g : Polynomial ℝ) (hg : g.degree < J) :
    polyVecR d g ∈ Vlt d J := (mem_Vlt d J _).2 ⟨g, hg, rfl⟩

lemma Vlt_mono (d : Fin s) {J J' : ℕ} (h : J ≤ J') : Vlt d J ≤ Vlt d J' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_Vlt d J x).1 hx
  exact polyVecR_mem d g (hg.trans_le (by exact_mod_cast h))

lemma map_natDegree_le (g : Polynomial ℚ) : (g.map (algebraMap ℚ ℝ)).natDegree = g.natDegree :=
  natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective g

lemma colE_mem_Vlt (hs : 3 ≤ s) (d : Fin s) {i J : ℕ} (hiJ : i < J) (hi : i ≤ s - 2)
    (E : Fin s → ℤ) (hE : InLam d i E) : colE E ∈ Vlt d J := by
  rw [colE_eq_poly hs d E hE.1]
  refine polyVecR_mem d _ ?_
  have h := ((inLam_iff hs hi E).1 hE).2
  refine (degree_le_natDegree).trans_lt ?_
  rw [map_natDegree_le]
  exact_mod_cast (show _ < J by omega)

/-- Real polynomials with the same vector and degree `≤ s - 2` are equal. -/
lemma polyVecR_inj (hs : 3 ≤ s) (d : Fin s) (g h : Polynomial ℝ) (hg : g.natDegree ≤ s - 2)
    (hh : h.natDegree ≤ s - 2) (he : polyVecR d g = polyVecR d h) : g = h := by
  set T := (univ.filter fun c : Fin s => c ≠ d).image fun c => (yQ c d : ℝ)
  have hinj : Set.InjOn (fun c => (yQ c d : ℝ)) ↑(univ.filter fun c : Fin s => c ≠ d) := by
    intro c hc c' hc' hcc
    exact yQ_injOn (by omega) d hc hc' (Rat.cast_injective hcc)
  have hT : T.card = s - 1 := by
    rw [card_image_of_injOn hinj, card_rows]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq T ?_ ?_
  · rw [hT]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_) <;>
      refine (degree_le_natDegree).trans_lt ?_ <;> exact_mod_cast (show _ < s - 1 by omega)
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    have hcd : c ≠ d := by simpa using hc
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin s) => v c) he
    simp only [polyVecR_apply, hcd, ite_false] at h1
    have hw : (wQ c d : ℝ) ≠ 0 := by exact_mod_cast (wQ_unit_RS (by omega) c d hcd).2.2
    exact mul_left_cancel₀ hw h1

/-! ## A flag spans `Vlt` -/

/-- A flag `B_i ∈ Λ_i`, `κ_i(B_i) = γ_i` for `i ≤ j`. -/
def Flag (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i

/-- The real span of `B_0, …, B_{J-1}`. -/
def spanB (B : ℕ → Fin s → ℤ) (J : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin s)) :=
  Submodule.span ℝ ((fun i => colE (B i)) '' ↑(range J))

lemma colE_mem_spanB (B : ℕ → Fin s → ℤ) {i J : ℕ} (h : i < J) : colE (B i) ∈ spanB B J :=
  Submodule.subset_span ⟨i, by simpa using h, rfl⟩

lemma spanB_mono (B : ℕ → Fin s → ℤ) {J J' : ℕ} (h : J ≤ J') : spanB B J ≤ spanB B J' :=
  Submodule.span_mono (Set.image_mono (by intro i hi; simp at hi ⊢; omega))

lemma sum_mem_spanB (B : ℕ → Fin s → ℤ) (J : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ range J, a i • colE (B i) ∈ spanB B J :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (colE_mem_spanB B (by simpa using hi))

lemma colE_sum (B : ℕ → Fin s → ℤ) (T : Finset ℕ) (t : ℕ → ℤ) :
    colE (∑ i ∈ T, t i • B i) = ∑ i ∈ T, (t i : ℝ) • colE (B i) := by
  ext c
  simp [colE_apply, Finset.sum_apply, WithLp.ofLp_sum]

lemma colE_sub (E F : Fin s → ℤ) : colE (E - F) = colE E - colE F := by
  ext c; simp [colE_apply]

lemma colE_zsmul (z : ℤ) (E : Fin s → ℤ) : colE (z • E) = (z : ℝ) • colE E := by
  ext c; simp [colE_apply]

/-- The vector of `X^k` lies in the real span of `B_0, …, B_k`. -/
lemma vecX_mem (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (k : ℕ) (hk : k ≤ s - 2)
    (hB : Flag d B k) : polyVecR d (X ^ k) ∈ spanB B (k + 1) := by
  set E : Fin s → ℚ := polyVecQ d (X ^ k)
  have hE0 : E d = 0 := by simp [E, polyVecQ]
  have hrep : ∀ c, c ≠ d → E c = wQ c d * (X ^ k : Polynomial ℚ).eval (yQ c d) := by
    intro c hc; simp [E, polyVecQ, hc]
  obtain ⟨D, hD, F, hF, hFE⟩ := rat_mul_inLam d k E hE0 (X ^ k) (by simp) hrep
  obtain ⟨t, ht⟩ := ((sat_basis_core hs d k hk B hB).1 F).1 hF
  have hcol : polyVecR d (X ^ k) = (1 / (D : ℝ)) • colE F := by
    ext c
    have h2 := congrArg (fun x : ℚ => (x : ℝ)) (hFE c)
    push_cast at h2
    rw [polyVecR_apply, PiLp.smul_apply, colE_apply, h2]
    have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    split_ifs with h
    · rw [h, hE0]; simp
    · simp only [E, polyVecQ, h, ite_false, eval_pow, eval_X]
      push_cast
      rw [smul_eq_mul]; field_simp
  rw [hcol, ht, colE_sum]
  exact Submodule.smul_mem _ _ (sum_mem_spanB B _ _)

/-- `V_{J-1} ⊗ ℝ` is contained in the real span of a flag `B_0, …, B_{J-1}`. -/
lemma Vlt_le_span (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (J : ℕ) (hJ : J ≤ s - 1)
    (hB : ∀ i < J, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) : Vlt d J ≤ spanB B J := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_Vlt d J x).1 hx
  by_cases hg0 : g = 0
  · rw [hg0, polyVecR_zero]; exact Submodule.zero_mem _
  have hnd : g.natDegree < J := (natDegree_lt_iff_degree_lt hg0).2 hg
  rw [as_sum_range' g J hnd, ← pvL_apply, map_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hkJ : k < J := by simpa using hk
  rw [← smul_X_eq_monomial, map_smul, pvL_apply]
  refine Submodule.smul_mem _ _ (spanB_mono B (show k + 1 ≤ J by omega) ?_)
  exact vecX_mem hs d B k (by omega) fun i hi => hB i (by omega)

lemma span_le_Vlt (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (J : ℕ) (hJ : J ≤ s - 1)
    (hB : ∀ i < J, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) : spanB B J ≤ Vlt d J := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < J := by simpa using hi
  exact colE_mem_Vlt hs d hi' (by omega) _ (hB i hi').1

/-- Orthogonality to `B_0, …, B_{J-1}` is orthogonality to `V_{J-1} ⊗ ℝ`. -/
lemma orth_of_flag (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (J : ℕ) (hJ : J ≤ s - 1)
    (hB : ∀ i < J, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) (x : EuclideanSpace ℝ (Fin s))
    (hx : ∀ i < J, inner ℝ (colE (B i)) x = 0) : x ∈ (Vlt d J)ᗮ := by
  have key : ∀ w ∈ spanB B J, inner ℝ w x = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact hx i (by simpa using hi)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [real_inner_smul_left, hy, mul_zero]
  rw [Submodule.mem_orthogonal]
  exact fun w hw => key w (Vlt_le_span hs d B J hJ hB hw)

/-! ## `ProjCoef` is Mathlib's orthogonal projection onto `V_{j-1} ⊗ ℝ` -/

lemma inner_colE (E F : Fin s → ℤ) : inner ℝ (colE E) (colE F) = ∑ c, (E c : ℝ) * F c := by
  simp only [PiLp.inner_apply, colE_apply, RCLike.inner_apply, conj_trivial]
  exact sum_congr rfl fun c _ => mul_comm _ _

lemma proj_of_projCoef (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 1)
    (hB : ∀ i < j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) (E : Fin s → ℤ) (cf : ℕ → ℚ)
    (h : ProjCoef B j E cf) :
    (Vlt d j).starProjection (colE E) = ∑ i ∈ range j, (cf i : ℝ) • colE (B i) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · exact span_le_Vlt hs d B j hj hB (sum_mem_spanB B j _)
  · refine orth_of_flag hs d B j hj hB _ fun i hi => ?_
    rw [inner_sub_right, inner_sum]
    simp only [real_inner_smul_right, inner_colE]
    have h1 := h i hi
    have h2 : ((∑ c, ((E c : ℚ) - ∑ l ∈ range j, cf l * (B l c : ℚ)) * (B i c : ℚ) : ℚ) : ℝ) = 0 := by
      rw [h1]; simp
    push_cast at h2
    rw [← h2]
    simp only [sub_mul, sum_sub_distrib, sum_mul, mul_sum]
    congr 1
    · exact sum_congr rfl fun c _ => mul_comm _ _
    · rw [sum_comm]; exact sum_congr rfl fun l _ => sum_congr rfl fun c _ => by ring

lemma projCoef_of_proj (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 1)
    (hB : ∀ i < j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) (E : Fin s → ℤ) (cf : ℕ → ℚ)
    (h : (Vlt d j).starProjection (colE E) = ∑ i ∈ range j, (cf i : ℝ) • colE (B i)) :
    ProjCoef B j E cf := by
  intro i hi
  have hmem : colE (B i) ∈ Vlt d j := colE_mem_Vlt hs d hi (by omega) _ (hB i hi).1
  have h0 := Submodule.starProjection_inner_eq_zero (K := Vlt d j) (colE E) _ hmem
  rw [h, inner_sub_left, sum_inner] at h0
  simp only [real_inner_smul_left, inner_colE] at h0
  have h2 : ((∑ c, ((E c : ℚ) - ∑ l ∈ range j, cf l * (B l c : ℚ)) * (B i c : ℚ) : ℚ) : ℝ) = 0 := by
    push_cast
    rw [← h0]
    simp only [sub_mul, sum_sub_distrib, sum_mul, mul_sum]
    congr 1
    rw [sum_comm]; exact sum_congr rfl fun l _ => sum_congr rfl fun c _ => by ring
  exact_mod_cast h2

/-! ## The Gram–Schmidt vector of a flag -/

/-- `u = B_j − P_{V_{j-1}}(B_j)`. -/
def uvec (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : EuclideanSpace ℝ (Fin s) :=
  colE (B j) - (Vlt d j).starProjection (colE (B j))

lemma uvec_orth (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : uvec d B j ∈ (Vlt d j)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- The polynomial of `B_j`, over `ℝ`. -/
def Gpoly (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : Polynomial ℝ :=
  (colPoly d fun c => (B j c : ℚ)).map (algebraMap ℚ ℝ)

lemma Gpoly_spec (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) :
    colE (B j) = polyVecR d (Gpoly d B j) ∧ (Gpoly d B j).natDegree ≤ j ∧
      (Gpoly d B j).coeff j = (gamS d j : ℝ) := by
  obtain ⟨hl, hk⟩ := hB j le_rfl
  refine ⟨colE_eq_poly hs d _ hl.1, ?_, ?_⟩
  · rw [Gpoly, map_natDegree_le]; exact ((inLam_iff hs hj _).1 hl).2
  · rw [Gpoly, coeff_map]; unfold kappa at hk; rw [hk]; rfl

lemma gam_pos (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) : (0 : ℝ) < gamS d j := by
  exact_mod_cast (gamS_spec hs d j hj).1

/-- For `g` of degree `≤ j`: `(w g(y)) − (g_j/γ_j) B_j ∈ V_{j-1} ⊗ ℝ`. -/
lemma poly_sub_mem (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) (g : Polynomial ℝ) (hg : g.natDegree ≤ j) :
    polyVecR d g - (g.coeff j / gamS d j) • colE (B j) ∈ Vlt d j := by
  obtain ⟨hcol, hdeg, hco⟩ := Gpoly_spec hs d B j hj hB
  have hγ := (gam_pos hs d j hj).ne'
  rw [hcol, ← polyVecR_smul, ← polyVecR_sub]
  refine polyVecR_mem d _ (degree_lt_of _ j ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le hg ?_)
    exact (natDegree_smul_le _ _).trans hdeg
  · rw [coeff_sub, coeff_smul, hco, smul_eq_mul, div_mul_cancel₀ _ hγ, sub_self]

lemma inner_u_self (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) :
    inner ℝ (uvec d B j) (colE (B j)) = ‖uvec d B j‖ ^ 2 := by
  have h0 : inner ℝ (uvec d B j) ((Vlt d j).starProjection (colE (B j))) = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (uvec_orth d B j) _ (Submodule.starProjection_apply_mem _ _)
  have : colE (B j) = uvec d B j + (Vlt d j).starProjection (colE (B j)) := by
    simp [uvec]
  rw [this, inner_add_right, h0, add_zero, real_inner_self_eq_norm_sq]

lemma inner_u_poly (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) (g : Polynomial ℝ) (hg : g.natDegree ≤ j) :
    inner ℝ (uvec d B j) (polyVecR d g) = g.coeff j / gamS d j * ‖uvec d B j‖ ^ 2 := by
  have hm := poly_sub_mem hs d B j hj hB g hg
  have h0 : inner ℝ (uvec d B j) (polyVecR d g - (g.coeff j / gamS d j) • colE (B j)) = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (uvec_orth d B j) _ hm
  rw [inner_sub_right, real_inner_smul_right, inner_u_self] at h0
  linarith

lemma uvec_mem (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) : uvec d B j ∈ lineA d j := by
  refine ⟨Submodule.sub_mem _ ?_ (Vlt_mono d (Nat.le_succ j) (Submodule.starProjection_apply_mem _ _)),
    uvec_orth d B j⟩
  exact colE_mem_Vlt hs d (Nat.lt_succ_self j) hj _ (hB j le_rfl).1

lemma uvec_ne_zero (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) : uvec d B j ≠ 0 := by
  intro hu
  obtain ⟨hcol, hdeg, hco⟩ := Gpoly_spec hs d B j hj hB
  have hmem : colE (B j) ∈ Vlt d j := by
    have : colE (B j) = (Vlt d j).starProjection (colE (B j)) := by
      have := hu; unfold uvec at this; exact sub_eq_zero.1 this
    rw [this]; exact Submodule.starProjection_apply_mem _ _
  obtain ⟨g, hg, hge⟩ := (mem_Vlt d j _).1 hmem
  have hgn : g.natDegree ≤ s - 2 := by
    by_cases h0 : g = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).2 hg; omega
  have := polyVecR_inj hs d _ _ (hdeg.trans hj) hgn (hcol.symm.trans hge)
  have hc0 : g.coeff j = 0 := coeff_eq_zero_of_degree_lt hg
  rw [← this, hco] at hc0
  exact (gam_pos hs d j hj).ne' hc0

lemma lineA_le (d : Fin s) (j : ℕ) : Vlt d j ≤ (lineA d j)ᗮ :=
  (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le inf_le_right)

/-- `π_j((w_c g(y_c))_c) = (g_j/γ_j) u` for every real `g` of degree `≤ j`. -/
lemma pi_poly (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) (g : Polynomial ℝ) (hg : g.natDegree ≤ j) :
    piA d j (polyVecR d g) = (g.coeff j / gamS d j) • uvec d B j := by
  set t := g.coeff j / gamS d j
  have hm := poly_sub_mem hs d B j hj hB g hg
  refine Submodule.eq_starProjection_of_mem_orthogonal'
    (Submodule.smul_mem _ t (uvec_mem hs d B j hj hB))
    (lineA_le d j (Submodule.add_mem _ hm
      (Submodule.smul_mem _ t (Submodule.starProjection_apply_mem (Vlt d j) (colE (B j)))))) ?_
  simp only [uvec, smul_sub]
  abel

end

end Z3NetA.Proofs
