module
public import Z3Net.HalfBox

@[expose] public section

/-!
# Entry Half, part 2: `prop:half`(2) (generic deeper rows; existence of the layer)

* `box_det_ne_zero_spec` (paper proof of `prop:half`(2)): for every composition `d` of `s`
  there are integer deeper rows making the integer box determinant of `halfIntGen` nonzero:
  with `Z = {d_c = 0}` the rows of the box past the unit rows are indexed by
  `Σ c, Fin (d_c - 1)`, a set of size `|Z|`; a bijection `φ` onto `Z` sends the `M`-rows
  (index `0`) to `Z'` and the deeper rows to unit vectors `e_z`, `z ∈ Z \ Z'`. A kernel vector
  vanishes off `Z` (unit rows), on `Z \ Z'` (deeper rows) and on `Z'` (the disjoint minor
  `M_{T,Z'}` is nonsingular).
* `half_net_generic`: the box determinants with indeterminate deeper rows are nonzero integer
  polynomials; a common nonvanishing integer point exists (`MvPolynomial.funext`); the net
  property then holds for every prime larger than the product of the box determinants.
* `half_M_exists`: the disjoint minors of `(2Y_cd + 1)` are nonzero polynomials (evaluate over `ℚ`
  at `Y = (I - J)/2` on the minor's positions); a common nonvanishing integer point gives odd
  off-diagonal entries; the diagonal `-∑_{d≠c}|O_cd|` (rounded down to an odd integer) makes the
  layer weakly dominant.
-/

namespace Z3NetHL.Proofs

open Matrix Finset

noncomputable section

variable {s : ℕ}

/-! ## The kernel argument -/

lemma box_rows_of_mulVec {R : Type*} [CommRing R] (C : Fin s → Matrix (Fin s) (Fin s) R)
    (d : Fin s → ℕ) (hd : ∑ c, d c = s) (v : Fin s → R) (h : boxMatrix C d *ᵥ v = 0)
    (c : Fin s) (i : ℕ) (hi : i < d c) :
    C c ⟨i, lt_of_lt_of_le hi (Z3NetF.Proofs.le_of_sum d hd c)⟩ ⬝ᵥ v = 0 := by
  rw [boxMatrix_eqF] at h
  have h1 := congrFun h ⟨Z3NetF.Proofs.pre d c + i, Z3NetF.Proofs.pre_add_lt d hd c i hi⟩
  rw [Pi.zero_apply] at h1
  rw [← h1]
  change _ = Z3NetF.boxMatrix C d _ ⬝ᵥ v
  rw [Z3NetF.Proofs.box_row_pre C d hd c i hi]

lemma card_rows_eq (d : Fin s → ℕ) (hd : ∑ c, d c = s) :
    Fintype.card (Σ c : Fin s, Fin (d c - 1)) = Fintype.card {z : Fin s // d z = 0} := by
  rw [Fintype.card_sigma, Fintype.card_subtype]
  simp only [Fintype.card_fin]
  rw [Finset.card_filter]
  have h1 : ∑ c, (d c - 1) + ∑ c : Fin s, (if d c = 0 then 0 else 1) = s := by
    have : ∑ c, (d c - 1 + (if d c = 0 then 0 else 1)) = ∑ c, d c :=
      sum_congr rfl fun c _ => by split_ifs <;> omega
    rw [← sum_add_distrib, this, hd]
  have h2 : ∑ c : Fin s, (if d c = 0 then 1 else 0) + ∑ c : Fin s, (if d c = 0 then 0 else 1)
      = s := by
    rw [← sum_add_distrib]
    have : ∀ c : Fin s, ((if d c = 0 then 1 else 0) + (if d c = 0 then 0 else 1)) = 1 := by
      intro c; split_ifs <;> rfl
    simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- **The paper's completion argument**: for each composition `d`, some integer deeper rows
give a nonzero integer box determinant. -/
theorem box_det_ne_zero_spec (M2 : Fin s → Fin s → ℤ) (hM : DisjMinors M2) (d : Fin s → ℕ)
    (hd : ∑ c, d c = s) :
    ∃ x : Fin s × ℕ × Fin s → ℤ,
      (boxMatrix (halfIntGen M2 (fun c r j => x (c, r, j))) d).det ≠ 0 := by
  classical
  let φ : (Σ c : Fin s, Fin (d c - 1)) ≃ {z : Fin s // d z = 0} :=
    Fintype.equivOfCardEq (card_rows_eq d hd)
  let x : Fin s × ℕ × Fin s → ℤ := fun t =>
    if h : 1 ≤ t.2.1 ∧ t.2.1 < d t.1 - 1 then
      (if t.2.2 = (φ ⟨t.1, ⟨t.2.1, h.2⟩⟩).1 then 1 else 0) else 0
  refine ⟨x, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  apply hv0
  have hrow := box_rows_of_mulVec _ d hd v hv
  -- unit rows
  have ha : ∀ c, 1 ≤ d c → v c = 0 := by
    intro c hc
    have h := hrow c 0 hc
    have e : (halfIntGen M2 (fun c r j => x (c, r, j)) c
        ⟨0, lt_of_lt_of_le hc (Z3NetF.Proofs.le_of_sum d hd c)⟩ : Fin s → ℤ) =
        fun j => if j = c then 1 else 0 := by
      funext j; simp [halfIntGen]
    rw [e] at h
    simpa [dotProduct] using h
  -- deeper rows
  have hb : ∀ (c : Fin s) (r : Fin (d c - 1)), 1 ≤ (r : ℕ) → v (φ ⟨c, r⟩).1 = 0 := by
    intro c r hr
    have h := hrow c ((r : ℕ) + 1) (by have := r.isLt; omega)
    have e : (halfIntGen M2 (fun c r j => x (c, r, j)) c ⟨(r : ℕ) + 1, by
        have := r.isLt; have := Z3NetF.Proofs.le_of_sum d hd c; omega⟩ : Fin s → ℤ) =
        fun j => if j = (φ ⟨c, r⟩).1 then 1 else 0 := by
      funext j
      have hr2 : (r : ℕ) + 1 ≠ 1 := by omega
      simp only [halfIntGen, Nat.add_one_ne_zero, if_false, hr2, Nat.add_sub_cancel, x]
      rw [dif_pos ⟨hr, r.isLt⟩]
    rw [e] at h
    simpa [dotProduct] using h
  -- the `M`-rows
  have hc : ∀ c, 2 ≤ d c → ∑ j, M2 c j * v j = 0 := by
    intro c hc
    have h := hrow c 1 (by omega)
    simpa [halfIntGen, dotProduct] using h
  -- the disjoint minor
  let T := {c : Fin s // 2 ≤ d c}
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let cc' : T → Fin s := fun t => (φ ⟨t.1, ⟨0, by have := t.2; omega⟩⟩).1
  let rr : Fin (Fintype.card T) → Fin s := fun i => (e i).1
  let cc : Fin (Fintype.card T) → Fin s := fun i => cc' (e i)
  have hrr : Function.Injective rr := Subtype.val_injective.comp e.injective
  have hcc' : Function.Injective cc' := by
    intro t t' h
    have h1 := φ.injective (Subtype.ext h)
    exact Subtype.ext (Sigma.mk.inj_iff.mp h1).1
  have hcc : Function.Injective cc := hcc'.comp e.injective
  have hdisj : ∀ i j, rr i ≠ cc j := by
    intro i j h
    have h1 : 2 ≤ d (rr i) := (e i).2
    have h2 : d (cc j) = 0 := (φ _).2
    rw [h] at h1; omega
  have hA := hM _ rr cc hrr hcc hdisj
  -- `v` vanishes off the image of `cc`
  have hvan : ∀ z, z ∉ Set.range cc → v z = 0 := by
    intro z hz
    by_cases hz0 : d z = 0
    · obtain ⟨⟨c, r⟩, hy⟩ := φ.surjective ⟨z, hz0⟩
      by_cases hr : 1 ≤ (r : ℕ)
      · have := hb c r hr
        rw [hy] at this; exact this
      · exfalso
        have hr0 : (r : ℕ) = 0 := by omega
        have h2 : 2 ≤ d c := by have := r.isLt; omega
        apply hz
        refine ⟨e.symm ⟨c, h2⟩, ?_⟩
        show cc' (e (e.symm ⟨c, h2⟩)) = z
        rw [Equiv.apply_symm_apply]
        show (φ ⟨c, ⟨0, by omega⟩⟩).1 = z
        have : (⟨c, ⟨0, by omega⟩⟩ : Σ c : Fin s, Fin (d c - 1)) = ⟨c, r⟩ :=
          Sigma.ext rfl (heq_of_eq (Fin.ext hr0.symm))
        rw [this, hy]
    · exact ha z (by omega)
  have hw : (Matrix.of fun i j => M2 (rr i) (cc j)) *ᵥ (fun j => v (cc j)) = 0 := by
    funext i
    simp only [mulVec, dotProduct, of_apply, Pi.zero_apply]
    rw [← hc (rr i) (e i).2]
    symm
    rw [← Finset.sum_image (f := fun z => M2 (rr i) z * v z)
      (fun a _ b _ h => hcc h)]
    refine (Finset.sum_subset (subset_univ _) fun z _ hz => ?_).symm
    have : z ∉ Set.range cc := by
      rintro ⟨j, rfl⟩; exact hz (mem_image_of_mem _ (mem_univ j))
    rw [hvan z this, mul_zero]
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hA hw
  funext z
  by_cases hz : z ∈ Set.range cc
  · obtain ⟨j, rfl⟩ := hz
    exact congrFun hw0 j
  · exact hvan z hz

/-! ## Indeterminate deeper rows -/

/-- `halfIntGen` with indeterminate deeper rows `X (c, r, j)`. -/
def GX (M2 : Fin s → Fin s → ℤ) (c : Fin s) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Fin s × ℕ × Fin s) ℤ) :=
  fun i j => if (i : ℕ) = 0 then (if j = c then 1 else 0)
    else if (i : ℕ) = 1 then MvPolynomial.C (M2 c j) else MvPolynomial.X (c, (i : ℕ) - 1, j)

lemma GX_eval (M2 : Fin s → Fin s → ℤ) (x : Fin s × ℕ × Fin s → ℤ) (c : Fin s) :
    (GX M2 c).map (MvPolynomial.eval x) = halfIntGen M2 (fun c r j => x (c, r, j)) c := by
  ext i j
  simp only [GX, halfIntGen, map_apply]
  split_ifs <;> simp

lemma GX_box_eval (M2 : Fin s → Fin s → ℤ) (x : Fin s × ℕ × Fin s → ℤ) (d : Fin s → ℕ) :
    MvPolynomial.eval x (boxMatrix (GX M2) d).det =
      (boxMatrix (halfIntGen M2 (fun c r j => x (c, r, j))) d).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, boxMatrix_eqF, boxMatrix_eqF,
    ← Z3NetF.Proofs.box_map]
  simp_rw [GX_eval]

/-- The compositions of `s` into `s` parts. -/
def comps (s : ℕ) : Finset (Fin s → ℕ) :=
  (Fintype.piFinset fun _ : Fin s => range (s + 1)).filter fun d => ∑ c, d c = s

lemma mem_comps (d : Fin s → ℕ) (hd : ∑ c, d c = s) : d ∈ comps s := by
  refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun c => mem_range.mpr ?_, hd⟩
  have := Z3NetF.Proofs.le_of_sum d hd c
  omega

/-- **`prop:half`(2)**, generic deeper rows. -/
theorem half_net_generic (s : ℕ) (M2 : Fin s → Fin s → ℤ) (hM : DisjMinors M2) :
    ∃ D : Fin s → ℕ → Fin s → ℤ, ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      IsNet0 s p (s * 1) (GFpoint s p 1 (halfPhi s p M2 D)) := by
  classical
  set Q := ∏ d ∈ comps s, (boxMatrix (GX M2) d).det with hQdef
  have hQ : Q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun d hd => ?_
    have hd' : ∑ c, d c = s := (mem_filter.mp hd).2
    obtain ⟨x, hx⟩ := box_det_ne_zero_spec M2 hM d hd'
    intro h0
    apply hx
    rw [← GX_box_eval, h0, map_zero]
  obtain ⟨x, hx⟩ : ∃ x : Fin s × ℕ × Fin s → ℤ, MvPolynomial.eval x Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  refine ⟨fun c r j => x (c, r, j), range ((MvPolynomial.eval x Q).natAbs + 3),
    fun p hp hpS => ?_⟩
  rw [mem_range, not_lt] at hpS
  refine halfPhi_net_of_int s p hp (by omega) M2 _ fun d hd hdvd => ?_
  have hdiv : (boxMatrix (halfIntGen M2 (fun c r j => x (c, r, j))) d).det ∣
      MvPolynomial.eval x Q := by
    rw [hQdef, map_prod, ← GX_box_eval]
    exact Finset.dvd_prod_of_mem _ (mem_comps d hd)
  have h2 := Int.natAbs_dvd_natAbs.mpr (hdvd.trans hdiv)
  rw [Int.natAbs_natCast] at h2
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hx) h2
  omega

/-! ## Existence of the layer -/

/-- The disjoint minor with entries `2 Y + 1` (indeterminates `Y`). -/
def PY (n : ℕ) (r c : Fin n → Fin s) : MvPolynomial (Fin s × Fin s) ℤ :=
  (Matrix.of fun i j => 2 * MvPolynomial.X (r i, c j) + 1).det

lemma PY_ne_zero (n : ℕ) (r c : Fin n → Fin s) (hr : Function.Injective r)
    (hc : Function.Injective c) : PY n r c ≠ 0 := by
  classical
  let y : Fin s × Fin s → ℚ := fun t => if ∃ k, r k = t.1 ∧ c k = t.2 then 0 else -1 / 2
  intro h0
  have h1 : MvPolynomial.aeval y (PY n r c) = 1 := by
    rw [PY, ← AlgHom.coe_toRingHom, RingHom.map_det]
    rw [← det_one (R := ℚ) (n := Fin n)]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply, of_apply, AlgHom.coe_toRingHom, map_add,
      map_mul, map_ofNat, MvPolynomial.aeval_X, map_one, one_apply, y]
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl, rfl⟩, if_pos rfl]; norm_num
    · rw [if_neg, if_neg hij]
      · norm_num
      · rintro ⟨k, hk1, hk2⟩
        exact hij ((hr hk1).symm.trans (hc hk2))
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/-- **`prop:half`(2)**, existence of the layer. -/
theorem half_M_exists (s : ℕ) :
    (∃ O : Fin s → Fin s → ℤ, (∀ c d, c ≠ d → Odd (O c d)) ∧
      ∀ M2 : Fin s → Fin s → ℤ, (∀ c d, c ≠ d → M2 c d = O c d) → DisjMinors M2) ∧
    ∃ M2 : Fin s → Fin s → ℤ, (∀ c d, Odd (M2 c d)) ∧
      (∀ c, M2 c c ≤ -∑ d ∈ univ.erase c, |M2 c d|) ∧ DisjMinors M2 := by
  classical
  set Q : MvPolynomial (Fin s × Fin s) ℤ := ∏ n ∈ range (s + 1),
    ∏ rc ∈ (univ : Finset ((Fin n → Fin s) × (Fin n → Fin s))).filter
      (fun rc => Function.Injective rc.1 ∧ Function.Injective rc.2), PY n rc.1 rc.2 with hQdef
  have hQ : Q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun n _ => Finset.prod_ne_zero_iff.mpr fun rc hrc => ?_
    have := (mem_filter.mp hrc).2
    exact PY_ne_zero n rc.1 rc.2 this.1 this.2
  obtain ⟨y, hy⟩ : ∃ y : Fin s × Fin s → ℤ, MvPolynomial.eval y Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  set O : Fin s → Fin s → ℤ := fun c d => 2 * y (c, d) + 1 with hOdef
  have hOodd : ∀ c d, Odd (O c d) := fun c d => ⟨y (c, d), rfl⟩
  have hdisj : ∀ M2 : Fin s → Fin s → ℤ, (∀ c d, c ≠ d → M2 c d = O c d) → DisjMinors M2 := by
    intro M2 hM2 n r c hr hc hrc
    have hn : n ≤ s := by simpa using Fintype.card_le_of_injective r hr
    have hev : MvPolynomial.eval y (PY n r c) ≠ 0 := by
      intro h0
      apply hy
      rw [hQdef, map_prod]
      refine Finset.prod_eq_zero (i := n) (mem_range.mpr (by omega)) ?_
      rw [map_prod]
      exact Finset.prod_eq_zero (i := (r, c)) (mem_filter.mpr ⟨mem_univ _, hr, hc⟩) h0
    have e : (Matrix.of fun i j => M2 (r i) (c j)) =
        (Matrix.of fun i j => (2 * MvPolynomial.X (r i, c j) + 1 :
          MvPolynomial (Fin s × Fin s) ℤ)).map (MvPolynomial.eval y) := by
      ext i j
      simp only [of_apply, map_apply, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, map_one]
      rw [hM2 _ _ (hrc i j)]
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hev
  refine ⟨⟨O, fun c d _ => hOodd c d, hdisj⟩, ?_⟩
  let S : Fin s → ℤ := fun c => ∑ d ∈ univ.erase c, |O c d|
  let M2 : Fin s → Fin s → ℤ := fun c d =>
    if c = d then -S c - (if Even (S c) then 1 else 0) else O c d
  have hM2off : ∀ c d, c ≠ d → M2 c d = O c d := fun c d h => by simp [M2, h]
  refine ⟨M2, fun c d => ?_, fun c => ?_, hdisj M2 hM2off⟩
  · by_cases h : c = d
    · subst h
      simp only [M2, if_true]
      by_cases hS : Even (S c)
      · rw [if_pos hS]
        exact (hS.neg).sub_odd odd_one
      · rw [if_neg hS, sub_zero]
        exact (Int.not_even_iff_odd.mp hS).neg
    · rw [hM2off c d h]; exact hOodd c d
  · have hsum : ∑ d ∈ univ.erase c, |M2 c d| = S c :=
      sum_congr rfl fun d hd => by rw [hM2off c d (Ne.symm (ne_of_mem_erase hd))]
    rw [hsum]
    simp only [M2, if_true]
    split_ifs <;> omega

end

end Z3NetHL.Proofs
