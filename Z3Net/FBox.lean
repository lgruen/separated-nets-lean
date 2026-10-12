module
public import Z3Net.FNie

@[expose] public section

/-!
# Entry F, part 3: graph forms with depths `K`, `lem:box` and the gauge moves

* `graphGenK_apply`: the entries of a graph-form generator matrix at column `pre K e + l`.
* `graphForm_of_box` (paper, `sec:prelim`): an invertible `K`-box makes any digital point set a
  graph form.
* `box_minor_self`: the `K`-box of a graph form is the identity.
* `box_minor` (`lem:box`): after reindexing rows and columns (unit rows/selected columns first),
  the box matrix is `[[1, 0], [*, D]]` with `D` the reduced box matrix; the sign is that of a
  permutation that depends only on `K`, `d` and the squaring bijection.
* `gauge_diag`, `gauge_LU`, `gauge_scale3` and the net consequences `gauge_net`, `gauge_net3`.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

variable {R : Type*} {s m : ℕ}

lemma K_congr (K : Fin s → ℕ) (b : ℕ) (hb : b < s) (e : Fin s) (h : b = e) :
    K ⟨b, hb⟩ = K e := by subst h; rfl

lemma Φ_congr {n : ℕ} (K : Fin s → ℕ) (Φ : (d : Fin s) → Matrix (Fin n) (Fin (K d)) R)
    (b : ℕ) (hb : b < s) (e : Fin s) (h : b = e) (r : Fin n) (l' l : ℕ) (hl' : l' < K ⟨b, hb⟩)
    (hl : l < K e) (h' : l' = l) : Φ ⟨b, hb⟩ r ⟨l', hl'⟩ = Φ e r ⟨l, hl⟩ := by
  subst h; subst h'; rfl

lemma graphGenK_apply [Zero R] [One R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) (i : Fin m)
    (e : Fin s) (l : ℕ) (hl : l < K e) :
    Z3NetF.graphGenK K Φ c i ⟨pre K e + l, pre_add_lt K hK e l hl⟩ =
      if hi : (i : ℕ) < K c then (if e = c ∧ l = (i : ℕ) then 1 else 0)
      else Φ c e ⟨(i : ℕ) - K c, by omega⟩ ⟨l, hl⟩ := by
  have hloc := boxLoc_pre K e l hl
  have h1 : (Z3NetF.boxLoc (List.ofFn K) 0 (pre K e + l)).1 = e := by rw [hloc]
  have h2 : (Z3NetF.boxLoc (List.ofFn K) 0 (pre K e + l)).2 = l := by rw [hloc]
  have hb : (Z3NetF.boxLoc (List.ofFn K) 0 (pre K e + l)).1 < s := by rw [h1]; exact e.isLt
  have hb2 : (Z3NetF.boxLoc (List.ofFn K) 0 (pre K e + l)).2 < K ⟨_, hb⟩ := by
    rw [K_congr K _ hb e h1, h2]; exact hl
  unfold Z3NetF.graphGenK
  dsimp only
  rw [dif_pos hb, dif_pos hb2]
  by_cases hi : (i : ℕ) < K c
  · rw [dif_pos hi, dif_pos hi, h1, h2]
    congr 1
    simp only [Fin.ext_iff]
  · rw [dif_neg hi, dif_neg hi]
    exact Φ_congr K (Φ c) _ hb e h1 _ _ _ hb2 hl h2

/-- Every column is `pre K e + l` with `l < K e`. -/
lemma col_cover (K : Fin s → ℕ) (hK : ∑ c, K c = m) (j : Fin m) :
    ∃ e : Fin s, ∃ l : ℕ, ∃ hl : l < K e, j = ⟨pre K e + l, pre_add_lt K hK e l hl⟩ := by
  obtain ⟨e, l, hl, hj, -⟩ := box_row_cover K hK j
  exact ⟨e, l, hl, Fin.ext hj⟩

lemma pos_inj (K : Fin s → ℕ) (c e : Fin s) (i l : ℕ) (hi : i < K c) (hl : l < K e)
    (h : pre K c + i = pre K e + l) : c = e ∧ i = l := by
  have h1 := boxLoc_pre K c i hi
  have h2 := boxLoc_pre K e l hl
  rw [h, h2] at h1
  simp only [Prod.mk.injEq] at h1
  exact ⟨Fin.ext h1.1.symm, h1.2.symm⟩

/-! ## `graphForm_of_box` -/

/-- The graph form of a point set with invertible `K`-box `G`: offset rows of `C_c G⁻¹`. -/
def invPhi [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m) (C : Fin s → Matrix (Fin m) (Fin m) R) :
    (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R :=
  fun c d (r : Fin (m - K c)) (l : Fin (K d)) =>
    (C c * (Z3NetF.boxMatrix C K)⁻¹ : Matrix (Fin m) (Fin m) R) ⟨K c + (r : ℕ), by omega⟩
      ⟨pre K d + l, pre_add_lt K hK d l l.isLt⟩

lemma graphGenK_inv [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (C : Fin s → Matrix (Fin m) (Fin m) R) (hG : IsUnit (Z3NetF.boxMatrix C K).det) (c : Fin s) :
    Z3NetF.graphGenK K (invPhi K hK C) c = C c * (Z3NetF.boxMatrix C K)⁻¹ := by
  set G := Z3NetF.boxMatrix C K
  ext i j
  obtain ⟨e, l, hl, rfl⟩ := col_cover K hK j
  rw [graphGenK_apply K hK _ c i e l hl]
  by_cases hi : (i : ℕ) < K c
  · rw [dif_pos hi]
    have hrow : C c i = G ⟨pre K c + i, pre_add_lt K hK c i hi⟩ := by
      change C c i = Z3NetF.boxMatrix C K _
      rw [box_row_pre C K hK c i hi]
    have : (C c * G⁻¹) i ⟨pre K e + l, pre_add_lt K hK e l hl⟩ =
        (G * G⁻¹) ⟨pre K c + i, pre_add_lt K hK c i hi⟩ ⟨pre K e + l, pre_add_lt K hK e l hl⟩ := by
      simp only [mul_apply, hrow]
    rw [this, mul_nonsing_inv G hG, one_apply]
    by_cases h : e = c ∧ l = (i : ℕ)
    · rw [if_pos h, if_pos]; obtain ⟨rfl, rfl⟩ := h; rfl
    · rw [if_neg h, if_neg]
      intro h'
      have := pos_inj K c e i l hi hl (by simpa using congrArg Fin.val h')
      exact h ⟨this.1.symm, this.2.symm⟩
  · rw [dif_neg hi]
    have hii : (⟨K c + ((i : ℕ) - K c), by omega⟩ : Fin m) = i := Fin.ext (by simp; omega)
    exact congrFun (congrArg (C c * G⁻¹ : Matrix (Fin m) (Fin m) R) hii) _

theorem graphForm_of_box [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (C : Fin s → Matrix (Fin m) (Fin m) R) (hG : IsUnit (Z3NetF.boxMatrix C K).det) :
    ∃ Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R,
      ∀ c, Z3NetF.graphGenK K Φ c * Z3NetF.boxMatrix C K = C c :=
  ⟨invPhi K hK C, fun c => by
    rw [graphGenK_inv K hK C hG c, Matrix.mul_assoc, nonsing_inv_mul _ hG, Matrix.mul_one]⟩

/-! ## The `K`-box of a graph form -/

theorem box_minor_self [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) :
    (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) K).det = 1 := by
  have : Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) K = 1 := by
    ext r j
    obtain ⟨c, i, hi, hr, -⟩ := box_row_cover K hK r
    have hr' : r = ⟨pre K c + i, pre_add_lt K hK c i hi⟩ := Fin.ext hr
    obtain ⟨e, l, hl, rfl⟩ := col_cover K hK j
    rw [hr', box_row_pre _ K hK c i hi, graphGenK_apply K hK Φ c _ e l hl, dif_pos hi, one_apply]
    by_cases h : e = c ∧ l = i
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg (by simpa using h), if_neg]
      intro h'
      have := pos_inj K c e i l hi hl (by simpa using congrArg Fin.val h')
      exact h ⟨this.1.symm, this.2.symm⟩
  rw [this, det_one]


lemma mat_congr {p r : ℕ} (M : Matrix (Fin p) (Fin r) R) (a a' b : ℕ) (h1 : a < p) (h1' : a' < p)
    (h2 : b < r) (h2' : b < r) (h : a = a') : M ⟨a, h1⟩ ⟨b, h2⟩ = M ⟨a', h1'⟩ ⟨b, h2'⟩ := by
  subst h; rfl

/-! ## `lem:box`: the reduction -/

section reduce

variable (K d : Fin s → ℕ)

/-- Unit rows / selected columns: level `i < min(d_c, K_c)` of coordinate `c`. -/
abbrev Xs : Type := Σ c : Fin s, Fin (min (d c) (K c))

/-- Row positions: unit rows `pre d c + i`, offset rows `pre d c + K c + r`. -/
def rowF (hd : ∑ c, d c = m) : Xs K d ⊕ Z3NetF.OverRows K d → Fin m
  | Sum.inl x => ⟨pre d x.1 + x.2, pre_add_lt d hd x.1 x.2 (lt_of_lt_of_le x.2.isLt (min_le_left _ _))⟩
  | Sum.inr y => ⟨pre d y.1.1 + (K y.1.1 + y.2), pre_add_lt d hd y.1.1 _ (by have := y.2.isLt; omega)⟩

/-- Column positions: selected columns `pre K e + l`, free columns `pre K e + d e + l`. -/
def colF (hK : ∑ c, K c = m) : Xs K d ⊕ Z3NetF.UnderCols K d → Fin m
  | Sum.inl x => ⟨pre K x.1 + x.2, pre_add_lt K hK x.1 x.2 (lt_of_lt_of_le x.2.isLt (min_le_right _ _))⟩
  | Sum.inr y => ⟨pre K y.1.1 + (d y.1.1 + y.2), pre_add_lt K hK y.1.1 _ (by have := y.2.isLt; have := y.1.2; omega)⟩

lemma sigma_eq_of {X : Fin s → ℕ} (c e : Fin s) (i : Fin (X c)) (l : Fin (X e)) (h1 : c = e)
    (h2 : (i : ℕ) = l) : (⟨c, i⟩ : Σ c : Fin s, Fin (X c)) = ⟨e, l⟩ := by
  subst h1; congr 1; exact Fin.ext h2

lemma sigma_eq_of' {X : Fin s → ℕ} {P : Fin s → Prop} (c e : {c // P c}) (i : Fin (X c.1))
    (l : Fin (X e.1)) (h1 : c.1 = e.1) (h2 : (i : ℕ) = l) :
    (⟨c, i⟩ : Σ c : {c // P c}, Fin (X c.1)) = ⟨e, l⟩ := by
  obtain ⟨c, hc⟩ := c; obtain ⟨e, he⟩ := e
  simp only at h1; subst h1; congr 1; exact Fin.ext h2

lemma rowF_bij (hd : ∑ c, d c = m) : Function.Bijective (rowF K d hd) := by
  constructor
  · rintro (⟨c, i⟩ | ⟨⟨c, hc⟩, r⟩) (⟨e, l⟩ | ⟨⟨e, he⟩, r'⟩) h <;>
      have h' := congrArg Fin.val h <;> simp only [rowF] at h'
    · have := pos_inj d c e i l (lt_of_lt_of_le i.isLt (min_le_left _ _))
        (lt_of_lt_of_le l.isLt (min_le_left _ _)) h'
      exact congrArg Sum.inl (sigma_eq_of (X := fun c => min (d c) (K c)) c e i l this.1 this.2)
    · obtain ⟨h1, h2⟩ := pos_inj d c e i _ (lt_of_lt_of_le i.isLt (min_le_left _ _))
        (by have : (r' : ℕ) < d e - K e := r'.isLt; omega) h'
      subst h1
      have := i.isLt; have := min_le_right (d c) (K c); omega
    · obtain ⟨h1, h2⟩ := pos_inj d c e _ l (by have : (r : ℕ) < d c - K c := r.isLt; omega)
        (lt_of_lt_of_le l.isLt (min_le_left _ _)) h'
      subst h1
      have := l.isLt; have := min_le_right (d c) (K c); omega
    · have := pos_inj d c e (K c + r) (K e + r') (by have : (r : ℕ) < d c - K c := r.isLt; omega)
        (by have : (r' : ℕ) < d e - K e := r'.isLt; omega) h'
      have h1 := this.1; subst h1
      exact congrArg Sum.inr (sigma_eq_of' (X := fun c => d c - K c) (P := fun c => K c < d c) ⟨c, hc⟩ ⟨c, he⟩ r r' rfl (by have := this.2; omega))
  · intro r
    obtain ⟨c, i, hi, hr, -⟩ := box_row_cover d hd r
    by_cases hik : i < K c
    · exact ⟨Sum.inl ⟨c, ⟨i, lt_min hi hik⟩⟩, Fin.ext (by simp [rowF, hr])⟩
    · exact ⟨Sum.inr ⟨⟨c, by omega⟩, ⟨i - K c, by show i - K c < d c - K c; omega⟩⟩,
        Fin.ext (by simp [rowF, hr]; omega)⟩

lemma colF_bij (hK : ∑ c, K c = m) : Function.Bijective (colF K d hK) := by
  constructor
  · rintro (⟨c, i⟩ | ⟨⟨c, hc⟩, r⟩) (⟨e, l⟩ | ⟨⟨e, he⟩, r'⟩) h <;>
      have h' := congrArg Fin.val h <;> simp only [colF] at h'
    · have := pos_inj K c e i l (lt_of_lt_of_le i.isLt (min_le_right _ _))
        (lt_of_lt_of_le l.isLt (min_le_right _ _)) h'
      exact congrArg Sum.inl (sigma_eq_of (X := fun c => min (d c) (K c)) c e i l this.1 this.2)
    · obtain ⟨h1, h2⟩ := pos_inj K c e i _ (lt_of_lt_of_le i.isLt (min_le_right _ _))
        (by have : (r' : ℕ) < K e - d e := r'.isLt; omega) h'
      subst h1
      have := i.isLt; have := min_le_left (d c) (K c); omega
    · obtain ⟨h1, h2⟩ := pos_inj K c e _ l (by have : (r : ℕ) < K c - d c := r.isLt; omega)
        (lt_of_lt_of_le l.isLt (min_le_right _ _)) h'
      subst h1
      have := l.isLt; have := min_le_left (d c) (K c); omega
    · have := pos_inj K c e (d c + r) (d e + r') (by have : (r : ℕ) < K c - d c := r.isLt; omega)
        (by have : (r' : ℕ) < K e - d e := r'.isLt; omega) h'
      have h1 := this.1; subst h1
      exact congrArg Sum.inr (sigma_eq_of' (X := fun e => K e - d e) (P := fun e => d e < K e) ⟨c, hc⟩ ⟨c, he⟩ r r' rfl (by have := this.2; omega))
  · intro j
    obtain ⟨e, l, hl, rfl⟩ := col_cover K hK j
    by_cases hld : l < d e
    · exact ⟨Sum.inl ⟨e, ⟨l, lt_min hld hl⟩⟩, rfl⟩
    · exact ⟨Sum.inr ⟨⟨e, by omega⟩, ⟨l - d e, by show l - d e < K e - d e; omega⟩⟩,
        Fin.ext (by simp [colF]; omega)⟩

/-- The row bijection. -/
def rowE (hd : ∑ c, d c = m) : Xs K d ⊕ Z3NetF.OverRows K d ≃ Fin m :=
  Equiv.ofBijective _ (rowF_bij K d hd)

/-- The column bijection. -/
def colE (hK : ∑ c, K c = m) : Xs K d ⊕ Z3NetF.UnderCols K d ≃ Fin m :=
  Equiv.ofBijective _ (colF_bij K d hK)

lemma card_over_under (hK : ∑ c, K c = m) (hd : ∑ c, d c = m) :
    Fintype.card (Z3NetF.UnderCols K d) = Fintype.card (Z3NetF.OverRows K d) := by
  have h1 := Fintype.card_congr (rowE K d hd)
  have h2 := Fintype.card_congr (colE K d hK)
  rw [Fintype.card_sum] at h1 h2
  omega

end reduce

theorem box_minor [CommRing R] (K d : Fin s → ℕ) (hK : ∑ c, K c = m) (hd : ∑ c, d c = m) :
    Nonempty (Z3NetF.UnderCols K d ≃ Z3NetF.OverRows K d) ∧
      ∀ σ : Z3NetF.UnderCols K d ≃ Z3NetF.OverRows K d, ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
        ∀ Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R,
          (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) d).det = ε * (Z3NetF.redBox K d Φ σ).det := by
  classical
  refine ⟨⟨Fintype.equivOfCardEq (card_over_under K d hK hd)⟩, fun σ => ?_⟩
  set ρ := rowE K d hd
  set κ' : Xs K d ⊕ Z3NetF.OverRows K d ≃ Fin m :=
    (Equiv.sumCongr (Equiv.refl _) σ.symm).trans (colE K d hK)
  set π : Equiv.Perm (Fin m) := ρ.symm.trans κ'
  have hsign : ((Equiv.Perm.sign π : ℤ) : R) * ((Equiv.Perm.sign π : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  refine ⟨((Equiv.Perm.sign π : ℤ) : R), ?_, fun Φ => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  set B := Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) d
  -- reindexed box matrix
  set B' := B.submatrix ρ κ'
  have hB'det : B'.det = ((Equiv.Perm.sign π : ℤ) : R) * B.det := by
    have e1 : B' = (B.submatrix id π).submatrix ρ ρ := by
      ext a b; simp [B', π]
    rw [e1, det_submatrix_equiv_self, det_permute']
  -- entries
  have hrow_in : ∀ (c : Fin s) (i : Fin (min (d c) (K c))),
      B (ρ (Sum.inl ⟨c, i⟩)) = Z3NetF.graphGenK K Φ c ⟨i, lt_of_lt_of_le
        (lt_of_lt_of_le i.isLt (min_le_left _ _)) (le_of_sum d hd c)⟩ := by
    intro c i
    exact box_row_pre _ d hd c i (lt_of_lt_of_le i.isLt (min_le_left _ _))
  have hrow_out : ∀ (y : Z3NetF.OverRows K d),
      B (ρ (Sum.inr y)) = Z3NetF.graphGenK K Φ y.1.1 ⟨K y.1.1 + y.2, lt_of_lt_of_le
        (by have := y.2.isLt; omega) (le_of_sum d hd y.1.1)⟩ := by
    intro y
    exact box_row_pre _ d hd y.1.1 _ (by have := y.2.isLt; omega)
  have h11 : B'.toBlocks₁₁ = 1 := by
    ext ⟨c, i⟩ ⟨e, l⟩
    simp only [toBlocks₁₁, of_apply, B', submatrix_apply]
    rw [hrow_in]
    have hl : (l : ℕ) < K e := lt_of_lt_of_le l.isLt (min_le_right _ _)
    have hcol : κ' (Sum.inl ⟨e, l⟩) = ⟨pre K e + l, pre_add_lt K hK e l hl⟩ := rfl
    rw [hcol, graphGenK_apply K hK Φ c _ e l hl,
      dif_pos (lt_of_lt_of_le i.isLt (min_le_right _ _)), one_apply]
    by_cases h : e = c ∧ (l : ℕ) = i
    · rw [if_pos h, if_pos]
      exact (sigma_eq_of (X := fun c => min (d c) (K c)) e c l i h.1 h.2).symm
    · rw [if_neg h, if_neg]
      intro h'
      rw [Sigma.mk.inj_iff] at h'
      obtain ⟨h1, h2⟩ := h'
      subst h1
      exact h ⟨rfl, (Fin.heq_ext_iff rfl).mp h2 |>.symm⟩
  have h12 : B'.toBlocks₁₂ = 0 := by
    ext ⟨c, i⟩ y
    simp only [toBlocks₁₂, of_apply, B', submatrix_apply, Matrix.zero_apply]
    rw [hrow_in]
    set y' := σ.symm y
    have hl : d y'.1.1 + (y'.2 : ℕ) < K y'.1.1 := by have := y'.2.isLt; have := y'.1.2; omega
    have hcol : κ' (Sum.inr y) = ⟨pre K y'.1.1 + (d y'.1.1 + y'.2), pre_add_lt K hK y'.1.1 _ hl⟩ := rfl
    rw [hcol, graphGenK_apply K hK Φ c _ y'.1.1 _ hl,
      dif_pos (lt_of_lt_of_le i.isLt (min_le_right _ _)), if_neg]
    rintro ⟨h1, h2⟩
    have : (i : ℕ) < d c := lt_of_lt_of_le i.isLt (min_le_left _ _)
    have h3 : d y'.1.1 = d c := by rw [h1]
    simp only at h2
    omega
  have h22 : (B'.toBlocks₂₂).submatrix σ σ = Z3NetF.redBox K d Φ σ := by
    ext x' y'
    simp only [submatrix_apply, toBlocks₂₂, of_apply, B']
    rw [hrow_out]
    have hl : d y'.1.1 + (y'.2 : ℕ) < K y'.1.1 := by have := y'.2.isLt; have := y'.1.2; omega
    have hcol : κ' (Sum.inr (σ y')) = ⟨pre K y'.1.1 + (d y'.1.1 + y'.2), pre_add_lt K hK y'.1.1 _ hl⟩ := by
      simp [κ', colE, colF]
    have hx : ((σ x').2 : ℕ) < m - K (σ x').1.1 := by
      have := (σ x').2.isLt; have := le_of_sum d hd (σ x').1.1; omega
    rw [hcol, graphGenK_apply K hK Φ (σ x').1.1 _ y'.1.1 _ hl, dif_neg (by simp)]
    unfold Z3NetF.redBox
    rw [dif_pos hx]
    exact mat_congr _ _ _ _ _ _ _ _ (by simp)
  have hdet : B'.det = (Z3NetF.redBox K d Φ σ).det := by
    rw [← fromBlocks_toBlocks B', h11, h12, det_fromBlocks_zero₁₂, det_one, one_mul, ← h22,
      det_submatrix_equiv_self]
  rw [hdet] at hB'det
  rw [hB'det, ← mul_assoc, hsign, one_mul]


/-! ## Gauge moves -/

section gauge

variable [CommRing R] (K d : Fin s → ℕ)

/-- The rectangular reduced matrix (over rows × under columns). -/
def Dm (hd : ∑ c, d c = m) (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) :
    Matrix (Z3NetF.OverRows K d) (Z3NetF.UnderCols K d) R :=
  fun x y => Φ x.1.1 y.1.1 ⟨x.2, by have := x.2.isLt; have := le_of_sum d hd x.1.1; omega⟩
    ⟨d y.1.1 + (y.2 : ℕ), by have := y.2.isLt; have := y.1.2; omega⟩

lemma redBox_eq (hd : ∑ c, d c = m) (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (σ : Z3NetF.UnderCols K d ≃ Z3NetF.OverRows K d) :
    Z3NetF.redBox K d Φ σ = (Dm K d hd Φ).submatrix σ id := by
  ext x y
  have hx : ((σ x).2 : ℕ) < m - K (σ x).1.1 := by
    have := (σ x).2.isLt; have := le_of_sum d hd (σ x).1.1; omega
  simp only [Z3NetF.redBox, dif_pos hx, submatrix_apply, Dm, id]

lemma over_ne_under (x : Z3NetF.OverRows K d) (y : Z3NetF.UnderCols K d) : x.1.1 ≠ y.1.1 := by
  intro h
  have h1 := x.1.2; have h2 := y.1.2
  rw [h] at h1; omega

lemma sum_fin_restrict {n n' : ℕ} (h : n' ≤ n) (g : Fin n → R) (hz : ∀ i : Fin n, n' ≤ i → g i = 0) :
    ∑ i, g i = ∑ i : Fin n', g ⟨i, lt_of_lt_of_le i.isLt h⟩ := by
  have e : ∑ i : Fin n', g ⟨i, lt_of_lt_of_le i.isLt h⟩ =
      ∑ i ∈ (univ : Finset (Fin n')).map (Fin.castLEEmb h), g i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  symm
  apply Finset.sum_subset (subset_univ _)
  intro i _ hi
  apply hz
  by_contra hlt
  push_neg at hlt
  exact hi (Finset.mem_map.mpr ⟨⟨i, hlt⟩, mem_univ _, Fin.ext rfl⟩)

lemma sum_fin_shift {n a : ℕ} (h : a ≤ n) (g : Fin n → R) (hz : ∀ i : Fin n, (i : ℕ) < a → g i = 0) :
    ∑ i, g i = ∑ i : Fin (n - a), g ⟨a + i, by have := i.isLt; omega⟩ := by
  let emb : Fin (n - a) ↪ Fin n := ⟨fun i => ⟨a + i, by have := i.isLt; omega⟩, by
    intro i j hij; simp only [Fin.mk.injEq] at hij; exact Fin.ext (by omega)⟩
  have e : ∑ i : Fin (n - a), g ⟨a + i, by have := i.isLt; omega⟩ =
      ∑ i ∈ (univ : Finset (Fin (n - a))).map emb, g i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  symm
  apply Finset.sum_subset (subset_univ _)
  intro i _ hi
  apply hz
  by_contra hlt
  push_neg at hlt
  exact hi (Finset.mem_map.mpr ⟨⟨i - a, by have := i.isLt; omega⟩, mem_univ _,
    Fin.ext (by show a + ((i : ℕ) - a) = i; omega)⟩)

/-- The row factor of move (c) on the over rows. -/
def Ablk (hd : ∑ c, d c = m) (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R) :
    Matrix (Z3NetF.OverRows K d) (Z3NetF.OverRows K d) R :=
  fun x x' => if h : x.1.1 = x'.1.1 then
      L x.1.1 ⟨x.2, by have := x.2.isLt; have := le_of_sum d hd x.1.1; omega⟩
        ⟨x'.2, by have := x'.2.isLt; have := le_of_sum d hd x'.1.1; rw [h]; omega⟩
    else 0

/-- The column factor of move (c) on the under columns. -/
def Bblk (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R) :
    Matrix (Z3NetF.UnderCols K d) (Z3NetF.UnderCols K d) R :=
  fun y' y => if h : y'.1.1 = y.1.1 then
      U y.1.1 ⟨d y.1.1 + (y'.2 : ℕ), by have := y'.2.isLt; have := y.1.2; rw [← h]; omega⟩
        ⟨d y.1.1 + (y.2 : ℕ), by have := y.2.isLt; have := y.1.2; omega⟩
    else 0

lemma Dm_LU (hd : ∑ c, d c = m)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R)
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R)
    (hL : ∀ c i j, i < j → L c i j = 0) (hU : ∀ d i j, i < j → U d i j = 0)
    (Φ Φ' : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (h : ∀ c d, c ≠ d → Φ' c d = L c * Φ c d * U d) :
    Dm K d hd Φ' = Ablk K d hd L * Dm K d hd Φ * Bblk K d U := by
  ext x y
  obtain ⟨⟨c, hc⟩, r⟩ := x
  obtain ⟨⟨e, he⟩, l⟩ := y
  have hce : c ≠ e := by intro h'; subst h'; omega
  have hr0 : (r : ℕ) < d c - K c := r.isLt
  have hl0 : (l : ℕ) < K e - d e := l.isLt
  have hr : (r : ℕ) < m - K c := by have := le_of_sum d hd c; omega
  have hl : d e + (l : ℕ) < K e := by omega
  have hde : d e ≤ K e := by omega
  have hdc : d c - K c ≤ m - K c := by have := le_of_sum d hd c; omega
  -- left side: only the levels `≥ d e` contribute
  have hL1 : (L c * Φ c e * U e) ⟨r, hr⟩ ⟨d e + l, hl⟩ = ∑ l' : Fin (K e - d e),
      (L c * Φ c e) ⟨r, hr⟩ ⟨d e + l', by omega⟩ * U e ⟨d e + l', by omega⟩ ⟨d e + l, hl⟩ := by
    rw [mul_apply, sum_fin_shift hde]
    intro i hi
    rw [hU e i ⟨d e + l, hl⟩ (by show (i : ℕ) < d e + l; omega), mul_zero]
  -- right side, outer sum
  have hR1 : (Ablk K d hd L * Dm K d hd Φ * Bblk K d U) ⟨⟨c, hc⟩, r⟩ ⟨⟨e, he⟩, l⟩ =
      ∑ l' : Fin (K e - d e), (Ablk K d hd L * Dm K d hd Φ) ⟨⟨c, hc⟩, r⟩ ⟨⟨e, he⟩, l'⟩ *
        U e ⟨d e + l', by omega⟩ ⟨d e + l, hl⟩ := by
    rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single ⟨e, he⟩]
    · refine Finset.sum_congr rfl fun l' _ => ?_
      congr 1
      simp [Bblk]
    · intro b _ hb
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp only [Bblk]
      rw [dif_neg (by intro h'; exact hb (Subtype.ext h')), mul_zero]
    · simp
  -- right side, inner sum
  have hR2 : ∀ l' : Fin (K e - d e), (Ablk K d hd L * Dm K d hd Φ) ⟨⟨c, hc⟩, r⟩ ⟨⟨e, he⟩, l'⟩ =
      (L c * Φ c e) ⟨r, hr⟩ ⟨d e + l', by omega⟩ := by
    intro l'
    rw [mul_apply, mul_apply, Fintype.sum_sigma, Finset.sum_eq_single ⟨c, hc⟩,
      sum_fin_restrict hdc]
    · refine Finset.sum_congr rfl fun r' _ => ?_
      simp [Ablk, Dm]
    · intro i hi
      rw [hL c ⟨r, hr⟩ i (by show (r : ℕ) < i; omega), zero_mul]
    · intro b _ hb
      refine Finset.sum_eq_zero fun r' _ => ?_
      simp only [Ablk]
      rw [dif_neg (by intro h'; exact hb (Subtype.ext h'.symm)), zero_mul]
    · simp
  show Φ' c e ⟨r, hr⟩ ⟨d e + l, hl⟩ = _
  rw [h c e hce, hL1, hR1]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [hR2]

lemma posR_inj (hd : ∑ c, d c = m) :
    Function.Injective (fun y : Z3NetF.OverRows K d => ((rowF K d hd (Sum.inr y) : Fin m) : ℕ)) :=
  fun a b h => Sum.inr_injective ((rowF_bij K d hd).1 (Fin.ext h))

lemma posC_inj (hK : ∑ c, K c = m) :
    Function.Injective (fun y : Z3NetF.UnderCols K d => ((colF K d hK (Sum.inr y) : Fin m) : ℕ)) :=
  fun a b h => Sum.inr_injective ((colF_bij K d hK).1 (Fin.ext h))

lemma det_Ablk (hd : ∑ c, d c = m)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R)
    (hL : ∀ c i j, i < j → L c i j = 0) (hLu : ∀ c i, IsUnit (L c i i)) :
    IsUnit (Ablk K d hd L).det := by
  letI : LinearOrder (Z3NetF.OverRows K d) := LinearOrder.lift' _ (posR_inj K d hd)
  rw [det_of_isLowerTriangular]
  · rw [IsUnit.prod_univ_iff]
    intro x
    simp only [Ablk, dif_pos rfl]
    exact hLu _ _
  · intro x x' hxx'
    simp only [Ablk]
    split_ifs with h
    · obtain ⟨⟨c, hc⟩, r⟩ := x
      obtain ⟨⟨c', hc'⟩, r'⟩ := x'
      simp only at h
      subst h
      apply hL
      have : ((rowF K d hd (Sum.inr ⟨⟨c, hc⟩, r⟩) : Fin m) : ℕ) <
          ((rowF K d hd (Sum.inr ⟨⟨c, hc'⟩, r'⟩) : Fin m) : ℕ) := hxx'
      simp only [rowF] at this
      show (r : ℕ) < r'
      omega
    · rfl

lemma det_Bblk (hK : ∑ c, K c = m)
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R)
    (hU : ∀ d i j, i < j → U d i j = 0) (hUu : ∀ d i, IsUnit (U d i i)) :
    IsUnit (Bblk K d U).det := by
  letI : LinearOrder (Z3NetF.UnderCols K d) := LinearOrder.lift' _ (posC_inj K d hK)
  rw [det_of_isLowerTriangular]
  · rw [IsUnit.prod_univ_iff]
    intro y
    simp only [Bblk, dif_pos rfl]
    exact hUu _ _
  · intro y' y hyy
    simp only [Bblk]
    split_ifs with h
    · obtain ⟨⟨e, he⟩, l⟩ := y
      obtain ⟨⟨e', he'⟩, l'⟩ := y'
      simp only at h
      subst h
      apply hU
      have : ((colF K d hK (Sum.inr ⟨⟨e', he'⟩, l'⟩) : Fin m) : ℕ) <
          ((colF K d hK (Sum.inr ⟨⟨e', he⟩, l⟩) : Fin m) : ℕ) := hyy
      simp only [colF] at this
      show d e' + (l' : ℕ) < d e' + l
      omega
    · rfl

end gauge

theorem gauge_diag [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ Φ' : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (h : ∀ c d, c ≠ d → Φ' c d = Φ c d) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ') d).det = (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) d).det := by
  obtain ⟨⟨σ⟩, H⟩ := box_minor (R := R) K d hK hd
  obtain ⟨ε, -, hε⟩ := H σ
  rw [hε Φ', hε Φ, redBox_eq K d hd, redBox_eq K d hd]
  congr 3
  ext x y
  simp only [Dm]
  rw [h _ _ (over_ne_under K d x y)]

theorem gauge_LU [CommRing R] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R)
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R)
    (hL : ∀ c i j, i < j → L c i j = 0) (hLu : ∀ c i, IsUnit (L c i i))
    (hU : ∀ d i j, i < j → U d i j = 0) (hUu : ∀ d i, IsUnit (U d i i))
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    ∃ u : R, IsUnit u ∧ ∀ Φ Φ' : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R,
      (∀ c d, c ≠ d → Φ' c d = L c * Φ c d * U d) →
        (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ') d).det = u * (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) d).det := by
  obtain ⟨⟨σ⟩, H⟩ := box_minor (R := R) K d hK hd
  obtain ⟨ε, -, hε⟩ := H σ
  refine ⟨(Ablk K d hd L).det * (Bblk K d U).det,
    (det_Ablk K d hd L hL hLu).mul (det_Bblk K d hK U hU hUu), fun Φ Φ' h => ?_⟩
  rw [hε Φ', hε Φ, redBox_eq K d hd, redBox_eq K d hd, Dm_LU K d hd L U hL hU Φ Φ' h]
  have : (Ablk K d hd L * Dm K d hd Φ * Bblk K d U).submatrix σ id =
      (Ablk K d hd L).submatrix σ σ * (Dm K d hd Φ).submatrix σ id * Bblk K d U := by
    ext x y
    simp only [submatrix_apply, mul_apply, id]
    refine Finset.sum_congr rfl fun y' _ => ?_
    congr 1
    exact (Equiv.sum_comp σ (fun x' => Ablk K d hd L (σ x) x' * Dm K d hd Φ x' y')).symm
  rw [this, det_mul, det_mul, det_submatrix_equiv_self]
  ring

/-- For `s = 3` either all over rows or all under columns share their coordinate. -/
lemma three_single (K d : Fin 3 → ℕ) :
    (∀ x x' : Z3NetF.OverRows K d, x.1.1 = x'.1.1) ∨
      (∀ y y' : Z3NetF.UnderCols K d, y.1.1 = y'.1.1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x, x', hx⟩, ⟨y, y', hy⟩⟩ := hcon
  have h1 := over_ne_under K d x y
  have h2 := over_ne_under K d x y'
  have h3 := over_ne_under K d x' y
  have h4 := over_ne_under K d x' y'
  have key : ∀ a b c e : Fin 3, a ≠ b → c ≠ e → a ≠ c → a ≠ e → b ≠ c → b ≠ e → False := by
    intro a b c e h1 h2 h3 h4 h5 h6
    have := a.isLt; have := b.isLt; have := c.isLt; have := e.isLt
    have := Fin.val_ne_of_ne h1; have := Fin.val_ne_of_ne h2; have := Fin.val_ne_of_ne h3
    have := Fin.val_ne_of_ne h4; have := Fin.val_ne_of_ne h5; have := Fin.val_ne_of_ne h6
    omega
  exact key _ _ _ _ hx hy h1 h2 h3 h4

theorem gauge_scale3 [CommRing R] {m : ℕ} (K : Fin 3 → ℕ) (hK : ∑ c, K c = m)
    (μ : Fin 3 → Fin 3 → R) (hμ : ∀ c d, c ≠ d → IsUnit (μ c d))
    (d : Fin 3 → ℕ) (hd : ∑ c, d c = m) :
    ∃ u : R, IsUnit u ∧ ∀ Φ Φ' : (c d : Fin 3) → Matrix (Fin (m - K c)) (Fin (K d)) R,
      (∀ c d, c ≠ d → Φ' c d = μ c d • Φ c d) →
        (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ') d).det = u * (Z3NetF.boxMatrix (Z3NetF.graphGenK K Φ) d).det := by
  obtain ⟨⟨σ⟩, H⟩ := box_minor (R := R) K d hK hd
  obtain ⟨ε, -, hε⟩ := H σ
  rcases three_single K d with hO | hU
  · refine ⟨∏ y, μ (σ y).1.1 y.1.1, IsUnit.prod_univ_iff.mpr fun y =>
      hμ _ _ (over_ne_under K d (σ y) y), fun Φ Φ' h => ?_⟩
    have e : (Dm K d hd Φ').submatrix σ id =
        (Dm K d hd Φ).submatrix σ id * diagonal (fun y => μ (σ y).1.1 y.1.1) := by
      ext x y
      rw [mul_diagonal]
      simp only [submatrix_apply, id, Dm]
      have hμeq : μ (σ x).1.1 y.1.1 = μ (σ y).1.1 y.1.1 := by rw [hO (σ x) (σ y)]
      rw [h _ _ (over_ne_under K d (σ x) y), Matrix.smul_apply, smul_eq_mul, hμeq]
      ring
    rw [hε Φ', hε Φ, redBox_eq K d hd, redBox_eq K d hd, e, det_mul, det_diagonal]
    ring
  · refine ⟨∏ x, μ (σ x).1.1 x.1.1, IsUnit.prod_univ_iff.mpr fun x =>
      hμ _ _ (over_ne_under K d (σ x) x), fun Φ Φ' h => ?_⟩
    have e : (Dm K d hd Φ').submatrix σ id =
        diagonal (fun x => μ (σ x).1.1 x.1.1) * (Dm K d hd Φ).submatrix σ id := by
      ext x y
      rw [diagonal_mul]
      simp only [submatrix_apply, id, Dm]
      have hμeq : μ (σ x).1.1 y.1.1 = μ (σ x).1.1 x.1.1 := by rw [hU x y]
      rw [h _ _ (over_ne_under K d (σ x) y), Matrix.smul_apply, smul_eq_mul, hμeq]
    rw [hε Φ', hε Φ, redBox_eq K d hd, redBox_eq K d hd, e, det_mul, det_diagonal]
    ring

theorem gauge_net [CommRing R] {q : ℕ} (e : R ≃ Fin q) (K : Fin s → ℕ)
    (hK : ∑ c, K c = m)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R)
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R)
    (hL : ∀ c i j, i < j → L c i j = 0) (hLu : ∀ c i, IsUnit (L c i i))
    (hU : ∀ d i j, i < j → U d i j = 0) (hUu : ∀ d i, IsUnit (U d i i))
    (Φ Φ' : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (h : ∀ c d, c ≠ d → Φ' c d = L c * Φ c d * U d) :
    Z3NetF.IsNet0E e (Z3NetF.graphGenK K Φ) → Z3NetF.IsNet0E e (Z3NetF.graphGenK K Φ') := by
  rw [nie_net, nie_net]
  intro hn d hd
  obtain ⟨u, hu, H⟩ := gauge_LU K hK L U hL hLu hU hUu d hd
  rw [H Φ Φ' h]
  exact hu.mul (hn d hd)

theorem gauge_net3 [CommRing R] {q m : ℕ} (e : R ≃ Fin q) (K : Fin 3 → ℕ)
    (hK : ∑ c, K c = m) (μ : Fin 3 → Fin 3 → R) (hμ : ∀ c d, c ≠ d → IsUnit (μ c d))
    (Φ Φ' : (c d : Fin 3) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (h : ∀ c d, c ≠ d → Φ' c d = μ c d • Φ c d) :
    Z3NetF.IsNet0E e (Z3NetF.graphGenK K Φ) → Z3NetF.IsNet0E e (Z3NetF.graphGenK K Φ') := by
  rw [nie_net, nie_net]
  intro hn d hd
  obtain ⟨u, hu, H⟩ := gauge_scale3 K hK μ hμ d hd
  rw [H Φ Φ' h]
  exact hu.mul (hn d hd)


end

end Z3NetF.Proofs
