/-
`rem:projlines`: the middle digits of two coordinates of the frame, of `𝒫^F_{k,q}` and of `𝒫_{k,q}` agree up to a sign
and more significant digits; rescaling one row keeps `t = 0`. V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ProjDefs
public import Z3Net.FTsk
public import Z3Net.Net

@[expose] public section

/-!
# `rem:projlines` (V14 stage S13′)

* The span machinery: `Sp fa fb r` is the span of the functionals `fa l`, `fb l` (`l < r`); `RowRel` is membership of
  `dig B · r - g · dig A · r` in it (`rowRel_iff_Sp`).
* `rowRel_of_box`, `rowRel_unique_of_box` (the general lemma): if the box with depths `r + 1` at `a`, `r` at `b` is
  invertible (`m = 2r + 1`), a relation exists; if the box with depths `r` at `a`, `r + 1` at `b` is invertible, its
  coefficient `g` is a unit and unique.
* `frame_rowRel_iff`: for the frame the coefficient is `projSign` (evaluation at `(t-a)^r (t-b)^r`, resp. `(t-a)^r`).
* `PGen_rowRel_iff`: the same for `𝒫^F_k` when `r ≥ k + 1` (the gauge of `def:Ns` is triangular with unit diagonal
  `1` in the rows below the first offset row).
* `P_rowRel`: for `𝒫_{k,q}` (`def:net`, `k` odd) some integer sign `±1`, the same for every base.
* `rowScale_box`, `rowScale_net`: rescaling row `r` multiplies each box minor by the product of the `ρ_c` with
  `r < d_c`; units keep `t = 0`. `rowScale_rowRel`: the rescaled relation has the coefficient `ρ_b g ρ_a⁻¹`.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

/-! ## Spans of digit functionals -/

section span

variable {R : Type*} [CommRing R] {W : Type*}

/-- The span of the functionals `fa l`, `fb l`, `l < r`. -/
def Sp (fa fb : ℕ → W → R) (r : ℕ) : Submodule R (W → R) :=
  Submodule.span R (Set.range (fun l : Fin r => fa l) ∪ Set.range (fun l : Fin r => fb l))

/-- The span of the functionals `f l`, `l < r`. -/
def Sp1 (f : ℕ → W → R) (r : ℕ) : Submodule R (W → R) :=
  Submodule.span R (Set.range (fun l : Fin r => f l))

lemma Sp1_le_left (fa fb : ℕ → W → R) (r : ℕ) : Sp1 fa r ≤ Sp fa fb r :=
  Submodule.span_mono Set.subset_union_left

lemma Sp1_le_right (fa fb : ℕ → W → R) (r : ℕ) : Sp1 fb r ≤ Sp fa fb r :=
  Submodule.span_mono Set.subset_union_right

lemma mem_Sp1 (f : ℕ → W → R) {r l : ℕ} (hl : l < r) : f l ∈ Sp1 f r :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

lemma mem_Sp_iff (fa fb : ℕ → W → R) (r : ℕ) (f : W → R) :
    f ∈ Sp fa fb r ↔ ∃ α β : ℕ → R, ∀ v, f v = ∑ l ∈ range r, (α l * fa l v + β l * fb l v) := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · refine ⟨fun j => if j = l then 1 else 0, fun _ => 0, fun v => ?_⟩
        simp [ite_mul, Finset.sum_ite_eq', l.isLt]
      · refine ⟨fun _ => 0, fun j => if j = l then 1 else 0, fun v => ?_⟩
        simp [ite_mul, Finset.sum_ite_eq', l.isLt]
    | zero => exact ⟨fun _ => 0, fun _ => 0, fun v => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨α, β, hx⟩ := hx
      obtain ⟨α', β', hy⟩ := hy
      refine ⟨α + α', β + β', fun v => ?_⟩
      rw [Pi.add_apply, hx v, hy v, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Pi.add_apply]; ring
    | smul a x _ hx =>
      obtain ⟨α, β, hx⟩ := hx
      refine ⟨a • α, a • β, fun v => ?_⟩
      rw [Pi.smul_apply, hx v, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rintro ⟨α, β, h⟩
    have e : f = ∑ l ∈ range r, (α l • fa l + β l • fb l) := by
      funext v; rw [h v, Finset.sum_apply]; simp
    rw [e]
    refine Submodule.sum_mem _ fun l hl => ?_
    have hl' : l < r := Finset.mem_range.mp hl
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨⟨l, hl'⟩, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨⟨l, hl'⟩, rfl⟩)))

/-- The transfer step: if the `y`-digits below `r` are combinations of the `f`-digits below `r` of the same
coordinate, and the `y`-digit `r` is the `f`-digit `r` plus such a combination, a relation for the `y`-digits gives
one for the `f`-digits with the same coefficient. -/
lemma Sp_transfer (fa fb ya yb : ℕ → W → R) (r : ℕ) (g : R)
    (hya : ∀ l < r, ya l ∈ Sp1 fa r) (hyb : ∀ l < r, yb l ∈ Sp1 fb r)
    (hra : ya r - fa r ∈ Sp1 fa r) (hrb : yb r - fb r ∈ Sp1 fb r)
    (h : yb r - g • ya r ∈ Sp ya yb r) : fb r - g • fa r ∈ Sp fa fb r := by
  have hle : Sp ya yb r ≤ Sp fa fb r := by
    refine Submodule.span_le.mpr ?_
    rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
    · exact Sp1_le_left fa fb r (hya l l.isLt)
    · exact Sp1_le_right fa fb r (hyb l l.isLt)
  have e : fb r - g • fa r = (yb r - g • ya r) - (yb r - fb r) + g • (ya r - fa r) := by
    rw [smul_sub]; abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.sub_mem _ (hle h) (Sp1_le_right fa fb r hrb))
    (Submodule.smul_mem _ _ (Sp1_le_left fa fb r hra))

end span

section rows

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The digit functionals of a generator matrix. -/
def digF (C : Matrix (Fin m) (Fin m) R) : ℕ → (Fin m → R) → R := fun l v => Z3NetF.dig C v l

lemma rowRel_iff_Sp (A B : Matrix (Fin m) (Fin m) R) (r : ℕ) (g : R) :
    Z3NetF.RowRel A B r g ↔ (digF B r - g • digF A r) ∈ Sp (digF A) (digF B) r := by
  rw [mem_Sp_iff]
  constructor
  · rintro ⟨α, β, h⟩
    exact ⟨α, β, fun v => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, digF]; rw [h v]; ring⟩
  · rintro ⟨α, β, h⟩
    refine ⟨α, β, fun v => ?_⟩
    have := h v
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, digF] at this
    rw [← this]; ring

/-- Evaluating a relation at an index whose more significant digits vanish in both coordinates. -/
lemma rowRel_eval {A B : Matrix (Fin m) (Fin m) R} {r : ℕ} {g : R} (h : Z3NetF.RowRel A B r g)
    (v : Fin m → R) (ha : ∀ l < r, Z3NetF.dig A v l = 0) (hb : ∀ l < r, Z3NetF.dig B v l = 0) :
    Z3NetF.dig B v r = g * Z3NetF.dig A v r := by
  obtain ⟨α, β, h⟩ := h
  rw [h v, Finset.sum_eq_zero fun l hl => by
    rw [ha l (Finset.mem_range.mp hl), hb l (Finset.mem_range.mp hl)]; ring, add_zero]

lemma dig_eq (C : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (l : ℕ) (hl : l < m) :
    Z3NetF.dig C v l = (C *ᵥ v) ⟨l, hl⟩ := dif_pos hl

/-- The entries of row `l` (`0` for `l ≥ m`). -/
def rowEnt (C : Matrix (Fin m) (Fin m) R) (l : ℕ) (j : Fin m) : R :=
  if h : l < m then C ⟨l, h⟩ j else 0

lemma dig_rowEnt (C : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (l : ℕ) :
    Z3NetF.dig C v l = ∑ j, rowEnt C l j * v j := by
  unfold Z3NetF.dig rowEnt
  split_ifs with h
  · rfl
  · simp

lemma rowEnt_map {S : Type*} [CommRing S] (f : R →+* S) (C : Matrix (Fin m) (Fin m) R) (l : ℕ) (j : Fin m) :
    rowEnt (C.map f) l j = f (rowEnt C l j) := by
  unfold rowEnt; split_ifs <;> simp

/-- A relation maps along a ring homomorphism. -/
lemma rowRel_map {S : Type*} [CommRing S] (f : R →+* S) {A B : Matrix (Fin m) (Fin m) R} {r : ℕ} {g : R}
    (h : Z3NetF.RowRel A B r g) : Z3NetF.RowRel (A.map f) (B.map f) r (f g) := by
  obtain ⟨α, β, h⟩ := h
  have hrow : ∀ j : Fin m, rowEnt B r j = g * rowEnt A r j +
      ∑ l ∈ range r, (α l * rowEnt A l j + β l * rowEnt B l j) := by
    intro j
    have := h (Pi.single j (1 : R))
    simpa only [dig_rowEnt, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using this
  refine ⟨fun l => f (α l), fun l => f (β l), fun v => ?_⟩
  simp only [dig_rowEnt, rowEnt_map, hrow, map_add, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul,
    add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j l => f (α l) * f (rowEnt A l j) * v j),
    Finset.sum_comm (f := fun j l => f (β l) * f (rowEnt B l j) * v j)]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => by ring
  · congr 1
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

end rows

/-! ## The general lemma: relations from two box minors -/

section boxes

variable {R : Type*} [CommRing R] {s m : ℕ}

lemma box_span (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) (hd : ∑ c, d c = m)
    (hG : IsUnit (Z3NetF.boxMatrix C d).det) (w : Fin m → R) :
    ∃ κ : Fin s → ℕ → R, ∀ v, w ⬝ᵥ v = ∑ c, ∑ i ∈ range (d c), κ c i * Z3NetF.dig (C c) v i := by
  set G := Z3NetF.boxMatrix C d
  set y := w ᵥ* G⁻¹
  refine ⟨fun c i => if h : i < d c then y ⟨pre d c + i, pre_add_lt d hd c i h⟩ else 0, fun v => ?_⟩
  have hw : w = y ᵥ* G := by rw [vecMul_vecMul, nonsing_inv_mul _ hG, vecMul_one]
  rw [hw, ← dotProduct_mulVec]
  unfold dotProduct
  rw [sum_cols d hd]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < d c then y ⟨pre d c + i, pre_add_lt d hd c i h⟩
    else 0) * Z3NetF.dig (C c) v i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt, box_mulVec_pre C d hd v c i i.isLt,
    dig_eq _ _ _ (lt_of_lt_of_le i.isLt (le_of_sum d hd c))]

lemma pairDepth_sum {a b : Fin s} (hab : a ≠ b) (r : ℕ) : ∑ c, Z3NetF.pairDepth a b r c = 2 * r + 1 := by
  rw [Fintype.sum_eq_add a b hab (fun c hc => by simp [Z3NetF.pairDepth, hc.1, hc.2])]
  simp [Z3NetF.pairDepth, hab.symm]; ring

/-- **The general lemma, existence**: if the box with depths `r + 1` at `a`, `r` at `b` is invertible (`m = 2r+1`),
digit `r` of `C_b` is a multiple of digit `r` of `C_a` plus more significant digits of both. -/
lemma rowRel_of_box (C : Fin s → Matrix (Fin m) (Fin m) R) {a b : Fin s} (hab : a ≠ b) {r : ℕ}
    (hm : m = 2 * r + 1) (hG : IsUnit (Z3NetF.boxMatrix C (Z3NetF.pairDepth a b r)).det) :
    ∃ g, Z3NetF.RowRel (C a) (C b) r g := by
  have hd : ∑ c, Z3NetF.pairDepth a b r c = m := by rw [pairDepth_sum hab, hm]
  have hr : r < m := by omega
  obtain ⟨κ, hκ⟩ := box_span C _ hd hG (C b ⟨r, hr⟩)
  refine ⟨κ a r, κ a, κ b, fun v => ?_⟩
  have h1 : Z3NetF.dig (C b) v r = C b ⟨r, hr⟩ ⬝ᵥ v := dig_eq _ _ _ hr
  rw [h1, hκ v, Fintype.sum_eq_add a b hab (fun c hc => by simp [Z3NetF.pairDepth, hc.1, hc.2]),
    show Z3NetF.pairDepth a b r a = r + 1 by simp [Z3NetF.pairDepth],
    show Z3NetF.pairDepth a b r b = r by simp [Z3NetF.pairDepth, hab.symm]]
  rw [Finset.sum_range_succ, Finset.sum_add_distrib]; ring

/-- **The general lemma, uniqueness**: if the box with depths `r` at `a`, `r + 1` at `b` is invertible, the
coefficient of a relation is a unit and unique. -/
lemma rowRel_unique_of_box (C : Fin s → Matrix (Fin m) (Fin m) R) {a b : Fin s} (hab : a ≠ b) {r : ℕ}
    (hm : m = 2 * r + 1) (hG : IsUnit (Z3NetF.boxMatrix C (Z3NetF.pairDepth b a r)).det) {g g' : R}
    (h : Z3NetF.RowRel (C a) (C b) r g) (h' : Z3NetF.RowRel (C a) (C b) r g') : IsUnit g ∧ g = g' := by
  set d := Z3NetF.pairDepth b a r
  have hd : ∑ c, d c = m := by rw [pairDepth_sum hab.symm, hm]
  have hda : d a = r := by simp [d, Z3NetF.pairDepth, hab]
  have hdb : d b = r + 1 := by simp [d, Z3NetF.pairDepth]
  set G := Z3NetF.boxMatrix C d
  have hbr : r < d b := by omega
  set n0 : Fin m := ⟨pre d b + r, pre_add_lt d hd b r hbr⟩
  set P : Fin m → R := G⁻¹ *ᵥ Pi.single n0 1
  have hGP : G *ᵥ P = Pi.single n0 1 := by
    simp only [P, mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]
  have hval : ∀ c (i : ℕ) (hi : i < d c), Z3NetF.dig (C c) P i =
      if pre d c + i = pre d b + r then 1 else 0 := by
    intro c i hi
    rw [dig_eq _ _ _ (lt_of_lt_of_le hi (le_of_sum d hd c)), ← box_mulVec_pre C d hd P c i hi, hGP,
      Pi.single_apply]
    simp only [n0, Fin.ext_iff]
  have ha : ∀ l < r, Z3NetF.dig (C a) P l = 0 := by
    intro l hl
    rw [hval a l (by omega), if_neg]
    intro he
    exact hab (pos_inj d a b l r (by omega) hbr he).1
  have hb : ∀ l < r, Z3NetF.dig (C b) P l = 0 := by
    intro l hl
    rw [hval b l (by omega), if_neg]
    intro he
    have := (pos_inj d b b l r (by omega) hbr he).2
    omega
  have hb1 : Z3NetF.dig (C b) P r = 1 := by rw [hval b r hbr, if_pos rfl]
  have e := rowRel_eval h P ha hb
  have e' := rowRel_eval h' P ha hb
  rw [hb1] at e e'
  refine ⟨IsUnit.of_mul_eq_one _ e.symm, ?_⟩
  calc g = g * (g' * Z3NetF.dig (C a) P r) := by rw [← e', mul_one]
    _ = g' * (g * Z3NetF.dig (C a) P r) := by ring
    _ = g' := by rw [← e, mul_one]

end boxes

/-! ## The frame -/

section frame

variable {R : Type*} [CommRing R] {s m : ℕ} (inf : Fin s) (x : Fin s → R)

open Polynomial in
lemma dig_readAt (V : R[X]) (hV : V.natDegree < m) (y : R) (i : ℕ) (hi : i < m) :
    Z3NetF.dig (Z3NetF.readAt m y) (fun l : Fin m => V.coeff l) i = (taylor y V).coeff i := by
  rw [dig_eq _ _ _ hi]
  simp only [mulVec, dotProduct, Z3NetF.readAt]
  conv_rhs => rw [V.as_sum_range' m hV]
  rw [map_sum, finsetSum_coeff, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]; ring

open Polynomial in
lemma dig_readInf (V : R[X]) (i : ℕ) (hi : i < m) :
    Z3NetF.dig (Z3NetF.readInf m) (fun l : Fin m => V.coeff l) i = V.coeff (m - 1 - i) := by
  rw [dig_eq _ _ _ hi]
  simp only [mulVec, dotProduct, Z3NetF.readInf, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro l _ hl
    rw [if_neg]; intro h; exact hl (Fin.ext (by simp; omega))
  · simp

lemma frame_box_unit (hx : Z3NetF.PlacesOK inf x) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d).det := by
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

open Polynomial in
lemma natDegree_XC_pow (c : R) (r : ℕ) : ((X + C c) ^ r).natDegree ≤ r := by
  refine le_trans natDegree_pow_le ?_
  rw [natDegree_add_C]
  have := natDegree_X_le (R := R)
  nlinarith

open Polynomial in
/-- The coefficient of a relation between two readings of the frame is `projSign`. -/
lemma frame_coeff (hx : Z3NetF.PlacesOK inf x) {r : ℕ} (hm : m = 2 * r + 1) {a b : Fin s} (hab : a ≠ b)
    {g : R} (h : Z3NetF.RowRel (Z3NetF.frameRead m inf x a) (Z3NetF.frameRead m inf x b) r g) :
    g = (Z3NetF.projSign inf a b r : R) := by
  have hrm : r < m := by omega
  -- the readings at a finite place `y` of `(t - y)^r · W`
  have tay : ∀ (y z : R) (i : ℕ), (taylor y ((X + C (-y)) ^ r * (X + C (-z)) ^ r)).coeff i =
      if r ≤ i then ((X + C (y - z)) ^ r).coeff (i - r) else 0 := by
    intro y z i
    rw [taylor_mul, taylor_pow, taylor_pow, map_add, map_add, taylor_X, taylor_C, taylor_C,
      add_assoc X (C y) (C (-y)), ← C_add, add_neg_cancel, C_0, add_zero, add_assoc X (C y) (C (-z)),
      ← C_add, ← sub_eq_add_neg, coeff_X_pow_mul']
  have tay1 : ∀ (y : R) (i : ℕ), (taylor y ((X + C (-y)) ^ r)).coeff i = if i = r then 1 else 0 := by
    intro y i
    rw [taylor_pow, map_add, taylor_X, taylor_C, add_assoc, ← C_add, add_neg_cancel, C_0, add_zero,
      coeff_X_pow]
  by_cases hinf : a = inf ∨ b = inf
  · rw [Z3NetF.projSign, if_pos hinf, Int.cast_one]
    -- one place is `∞`: evaluate at `(t - y)^r`, `y` the finite place
    have key : ∀ (y : R) (V : R[X]), V = (X + C (-y)) ^ r →
        (∀ l < r, Z3NetF.dig (Z3NetF.readInf m) (fun l : Fin m => V.coeff l) l = 0) ∧
        (∀ l < r, Z3NetF.dig (Z3NetF.readAt m y) (fun l : Fin m => V.coeff l) l = 0) ∧
        Z3NetF.dig (Z3NetF.readInf m) (fun l : Fin m => V.coeff l) r = 1 ∧
        Z3NetF.dig (Z3NetF.readAt m y) (fun l : Fin m => V.coeff l) r = 1 := by
      intro y V hV
      have hdeg : V.natDegree < m := by rw [hV]; have := natDegree_XC_pow (-y) r; omega
      refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, ?_⟩
      · rw [dig_readInf V l (by omega), hV, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · rw [dig_readAt V hdeg y l (by omega), hV, tay1, if_neg (by omega)]
      · rw [dig_readInf V r hrm, hV, coeff_X_add_C_pow, show m - 1 - r = r by omega]; simp
      · rw [dig_readAt V hdeg y r hrm, hV, tay1, if_pos rfl]
    rcases hinf with ha | hb
    · have hb : b ≠ inf := fun hb => hab (ha.trans hb.symm)
      obtain ⟨k1, k2, k3, k4⟩ := key (x b) _ rfl
      have fa : Z3NetF.frameRead m inf x a = Z3NetF.readInf m := by simp [Z3NetF.frameRead, ha]
      have fb : Z3NetF.frameRead m inf x b = Z3NetF.readAt m (x b) := by simp [Z3NetF.frameRead, hb]
      rw [fa, fb] at h
      have e := rowRel_eval h _ k1 k2
      rw [k3, k4, mul_one] at e
      exact e.symm
    · have ha : a ≠ inf := fun ha => hab (ha.trans hb.symm)
      obtain ⟨k1, k2, k3, k4⟩ := key (x a) _ rfl
      have fa : Z3NetF.frameRead m inf x a = Z3NetF.readAt m (x a) := by simp [Z3NetF.frameRead, ha]
      have fb : Z3NetF.frameRead m inf x b = Z3NetF.readInf m := by simp [Z3NetF.frameRead, hb]
      rw [fa, fb] at h
      have e := rowRel_eval h _ k2 k1
      rw [k3, k4, mul_one] at e
      exact e.symm
  · rw [Z3NetF.projSign, if_neg hinf]
    push Not at hinf
    obtain ⟨ha, hb⟩ := hinf
    set V : R[X] := (X + C (-x a)) ^ r * (X + C (-x b)) ^ r with hV
    have hV' : V = (X + C (-x b)) ^ r * (X + C (-x a)) ^ r := by rw [hV, mul_comm]
    have hdeg : V.natDegree < m := by
      have := natDegree_mul_le (p := (X + C (-x a)) ^ r) (q := (X + C (-x b)) ^ r)
      have h1 := natDegree_XC_pow (-x a) r
      have h2 := natDegree_XC_pow (-x b) r
      rw [← hV] at this; omega
    have dA : ∀ l, Z3NetF.dig (Z3NetF.readAt m (x a)) (fun l : Fin m => V.coeff l) l =
        if l < m then (if r ≤ l then ((X + C (x a - x b)) ^ r).coeff (l - r) else 0) else 0 := by
      intro l
      split_ifs with h1
      · rw [dig_readAt V hdeg _ l h1, hV, tay, if_pos ‹r ≤ l›]
      · rw [dig_readAt V hdeg _ l h1, hV, tay, if_neg ‹¬ r ≤ l›]
      · simp [Z3NetF.dig, h1]
    have dB : ∀ l, Z3NetF.dig (Z3NetF.readAt m (x b)) (fun l : Fin m => V.coeff l) l =
        if l < m then (if r ≤ l then ((X + C (x b - x a)) ^ r).coeff (l - r) else 0) else 0 := by
      intro l
      split_ifs with h1
      · rw [dig_readAt V hdeg _ l h1, hV', tay, if_pos ‹r ≤ l›]
      · rw [dig_readAt V hdeg _ l h1, hV', tay, if_neg ‹¬ r ≤ l›]
      · simp [Z3NetF.dig, h1]
    have fa : Z3NetF.frameRead m inf x a = Z3NetF.readAt m (x a) := by simp [Z3NetF.frameRead, ha]
    have fb : Z3NetF.frameRead m inf x b = Z3NetF.readAt m (x b) := by simp [Z3NetF.frameRead, hb]
    rw [fa, fb] at h
    have e := rowRel_eval h (fun l : Fin m => V.coeff l)
      (fun l hl => by rw [dA, if_pos (by omega), if_neg (by omega)])
      (fun l hl => by rw [dB, if_pos (by omega), if_neg (by omega)])
    rw [dA, dB, if_pos hrm, if_pos le_rfl, if_pos hrm, if_pos le_rfl, Nat.sub_self, coeff_X_add_C_pow,
      coeff_X_add_C_pow, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, mul_one, mul_one] at e
    -- `(b - a)^r = g (a - b)^r = g (-1)^r (b - a)^r`
    have hu : IsUnit ((x b - x a) ^ r) := (hx b a hb ha (Ne.symm hab)).pow r
    have e2 : (x b - x a) ^ r * 1 = (x b - x a) ^ r * (g * (-1) ^ r) := by
      have hab' : (x a - x b) ^ r = (-1) ^ r * (x b - x a) ^ r := by rw [← mul_pow]; congr 1; ring
      linear_combination e + g * hab'
    have e3 := hu.mul_left_cancel e2
    have hsq : ((-1 : R) ^ r) * (-1) ^ r = 1 := by rw [← mul_pow]; simp
    push_cast
    calc g = g * ((-1) ^ r * (-1) ^ r) := by rw [hsq, mul_one]
      _ = (g * (-1) ^ r) * (-1) ^ r := by ring
      _ = (-1) ^ r := by rw [← e3, one_mul]

/-- **The frame** (`rem:projlines`, the Möbius-transported reversal symmetry): for `m = 2r + 1` and two coordinates
`a ≠ b`, the coefficient of a relation between digit `r` of the readings `b` and `a` exists and is `projSign`. -/
theorem frame_rowRel_iff (hx : Z3NetF.PlacesOK inf x) {r : ℕ} (hm : m = 2 * r + 1) {a b : Fin s}
    (hab : a ≠ b) (g : R) :
    Z3NetF.RowRel (Z3NetF.frameRead m inf x a) (Z3NetF.frameRead m inf x b) r g ↔
      g = (Z3NetF.projSign inf a b r : R) := by
  constructor
  · exact frame_coeff inf x hx hm hab
  · rintro rfl
    have hd : ∑ c, Z3NetF.pairDepth a b r c = m := by rw [pairDepth_sum hab, hm]
    obtain ⟨g0, h0⟩ := rowRel_of_box (Z3NetF.frameRead m inf x) hab hm (frame_box_unit inf x hx _ hd)
    rwa [frame_coeff inf x hx hm hab h0] at h0

end frame

/-! ## Transfer to `𝒫^F_k` (`def:Ns`) -/

section pgen

variable {R : Type*} [CommRing R] {s k : ℕ}

/-- The cells re-gauged by the column gauges `U_d`: the index `u` with `u_{d, l} = ∑_j (U_d)_{l j} v_{d, j}`. -/
def Umap (U : Fin s → Matrix (Fin k) (Fin k) R) (v : Fin (s * k) → R) (n : Fin (s * k)) : R :=
  ∑ d : Fin s, ∑ l : Fin k, if (n : ℕ) = pre (fun _ : Fin s => k) d + l then
    ∑ j : Fin k, U d l j * v ⟨pre (fun _ : Fin s => k) d + j,
      pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d j j.isLt⟩ else 0

lemma Umap_pre (U : Fin s → Matrix (Fin k) (Fin k) R) (v : Fin (s * k) → R) (d : Fin s) (l : ℕ) (hl : l < k) :
    Umap U v ⟨pre (fun _ : Fin s => k) d + l, pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d l hl⟩ =
      ∑ j : Fin k, U d ⟨l, hl⟩ j * v ⟨pre (fun _ : Fin s => k) d + j,
        pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d j j.isLt⟩ := by
  unfold Umap
  rw [Finset.sum_eq_single d, Finset.sum_eq_single (⟨l, hl⟩ : Fin k), if_pos rfl]
  · intro l' _ hl'
    rw [if_neg]
    intro h
    exact hl' (Fin.ext (pos_inj (fun _ : Fin s => k) d d l l' hl l'.isLt h).2.symm)
  · simp
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun l' _ => if_neg ?_
    intro h
    exact hd' (pos_inj (fun _ : Fin s => k) d d' l l' hl l'.isLt h).1.symm
  · simp

variable (inf : Fin s) (x : Fin s → R) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
  (Ur β : Fin s → ℕ → ℕ → R)

lemma graphF_eq (hx : Z3NetF.PlacesOK inf x) (c : Fin s) :
    Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.frameGraph R k inf x) c =
      Z3NetF.frameRead (s * k) inf x c * (Gk k inf x)⁻¹ := by
  rw [frameGraph_eq_invPhi, graphGenK_inv _ (sum_const_k k) _ (Gk_unit k inf x hx) c]

/-- The digit functionals of the frame's graph form at the re-gauged cells. -/
def Yf (c : Fin s) : ℕ → (Fin (s * k) → R) → R := fun l v =>
  Z3NetF.dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.frameGraph R k inf x) c)
    (Umap (Z3NetF.Ugauge k inf x Ur β) v) l

/-- The digit functionals of `𝒫^F_k`. -/
def Pf (c : Fin s) : ℕ → (Fin (s * k) → R) → R := digF (Z3NetF.PGen k inf x F lam Ur β c)

lemma P_cell (c : Fin s) (j : ℕ) (hj : j < k) (v : Fin (s * k) → R) :
    Pf inf x F lam Ur β c j v =
      v ⟨pre (fun _ : Fin s => k) c + j, pre_add_lt (fun _ : Fin s => k) (sum_const_k k) c j hj⟩ := by
  have hjm : j < s * k := lt_of_lt_of_le hj (le_of_sum (fun _ : Fin s => k) (sum_const_k k) c)
  simp only [Pf, digF]
  rw [dig_eq _ _ _ hjm]
  exact graphGenK_mulVec_cell (fun _ : Fin s => k) (sum_const_k k) _ c v j hj

lemma Y_cell (c : Fin s) (i : ℕ) (hi : i < k) (v : Fin (s * k) → R) :
    Yf (k := k) inf x Ur β c i v =
      ∑ j : Fin k, Z3NetF.Ugauge k inf x Ur β c ⟨i, hi⟩ j * Pf inf x F lam Ur β c j v := by
  have him : i < s * k := lt_of_lt_of_le hi (le_of_sum (fun _ : Fin s => k) (sum_const_k k) c)
  simp only [Yf]
  rw [dig_eq _ _ _ him]
  rw [graphGenK_mulVec_cell (fun _ : Fin s => k) (sum_const_k k) _ c _ i hi, Umap_pre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P_cell inf x F lam Ur β c j j.isLt]

lemma Y_off (c : Fin s) (r' : Fin (s * k - k)) (v : Fin (s * k) → R) :
    Yf (k := k) inf x Ur β c (k + r') v = ∑ d : Fin s, ∑ j : Fin k,
      (Z3NetF.frameGraph R k inf x c d * Z3NetF.Ugauge k inf x Ur β d) r' j *
        v ⟨pre (fun _ : Fin s => k) d + j, pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d j j.isLt⟩ := by
  simp only [Yf]
  rw [dig_eq _ _ _ (by omega)]
  have := graphGenK_mulVec_off (fun _ : Fin s => k) (sum_const_k k) (Z3NetF.frameGraph R k inf x) c
    (Umap (Z3NetF.Ugauge k inf x Ur β) v) r'
  refine this.trans ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Umap_pre _ _ d _ (Fin.isLt _), Finset.mul_sum, mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma P_off (c : Fin s) (r' : Fin (s * k - k)) (v : Fin (s * k) → R) :
    Pf inf x F lam Ur β c (k + r') v = ∑ d : Fin s, ∑ j : Fin k,
      Z3NetF.PPhi k inf x F lam Ur β c d r' j *
        v ⟨pre (fun _ : Fin s => k) d + j, pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d j j.isLt⟩ := by
  simp only [Pf, digF]
  rw [dig_eq _ _ _ (by omega)]
  exact graphGenK_mulVec_off (fun _ : Fin s => k) (sum_const_k k) _ c v r'

/-- The row scalar of the gauge `L_c` in offset row `r'`. -/
def ellR (c : Fin s) (r' : ℕ) : R := if r' = 0 then lam c * Ring.inverse (Z3NetF.Qf inf x c ^ k) else 1

lemma ellR_unit (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur) (c : Fin s) (r' : ℕ) :
    IsUnit (ellR (k := k) inf x lam c r') := by
  unfold ellR
  split_ifs
  · exact (hres.1 c).mul ((Qf_unit inf x hx c).pow k).ringInverse
  · exact isUnit_one

/-- The offset digits of `𝒫^F_k` against those of the re-gauged frame graph form: they differ by the row scalar of
`L_c` and a combination of the own cell digits (the diagonal block). -/
lemma key_off (c : Fin s) (r' : Fin (s * k - k)) (v : Fin (s * k) → R) :
    Pf inf x F lam Ur β c (k + r') v = ellR (k := k) inf x lam c r' * Yf (k := k) inf x Ur β c (k + r') v +
      ∑ j : Fin k, (Z3NetF.PPhi k inf x F lam Ur β c c r' j - ellR (k := k) inf x lam c r' *
        (Z3NetF.frameGraph R k inf x c c * Z3NetF.Ugauge k inf x Ur β c) r' j) * Pf inf x F lam Ur β c j v := by
  have hd : ∀ d, d ≠ c → ∀ j, Z3NetF.PPhi k inf x F lam Ur β c d r' j = ellR (k := k) inf x lam c r' *
      (Z3NetF.frameGraph R k inf x c d * Z3NetF.Ugauge k inf x Ur β d) r' j := by
    intro d hdc j
    have e1 : Z3NetF.PPhi k inf x F lam Ur β c d = Z3NetF.Lmat k inf x lam c * Z3NetF.frameGraph R k inf x c d *
        Z3NetF.Ugauge k inf x Ur β d := by simp [Z3NetF.PPhi, Ne.symm hdc]
    rw [e1, Matrix.mul_assoc, Z3NetF.Lmat, Z3NetF.Lgauge, diagonal_mul]
    rfl
  rw [P_off, Y_off, ← sub_eq_iff_eq_add', Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single c]
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [P_cell inf x F lam Ur β c j j.isLt]; ring
  · intro d _ hdc
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hd d hdc j]; ring
  · simp

/-- The digits of the re-gauged frame graph form in terms of those of `𝒫^F_k`, below and at digit `r ≥ k + 1`. -/
lemma Y_mem (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur) {r : ℕ} (hr : k + 1 ≤ r)
    (hrm : r < s * k) (c : Fin s) :
    (∀ l < r, Yf (k := k) inf x Ur β c l ∈ Sp1 (Pf inf x F lam Ur β c) r) ∧
      Yf (k := k) inf x Ur β c r - Pf inf x F lam Ur β c r ∈ Sp1 (Pf inf x F lam Ur β c) r := by
  set P := Pf inf x F lam Ur β c
  have hcell : ∀ j : Fin k, P j ∈ Sp1 P r := fun j => mem_Sp1 P (by omega)
  constructor
  · intro l hl
    by_cases hlk : l < k
    · have e : Yf (k := k) inf x Ur β c l = ∑ j : Fin k, Z3NetF.Ugauge k inf x Ur β c ⟨l, hlk⟩ j • P j := by
        funext v; rw [Y_cell inf x F lam Ur β c l hlk v, Finset.sum_apply]; simp [P]
      rw [e]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcell j)
    · set r' : Fin (s * k - k) := ⟨l - k, by omega⟩
      have hl' : k + (r' : ℕ) = l := by simp [r']; omega
      obtain ⟨t, ht⟩ := (ellR_unit (k := k) inf x F lam Ur hx hres c r').exists_left_inv
      have e : Yf (k := k) inf x Ur β c l = t • P l - ∑ j : Fin k, (t * (Z3NetF.PPhi k inf x F lam Ur β c c r' j -
          ellR (k := k) inf x lam c r' * (Z3NetF.frameGraph R k inf x c c * Z3NetF.Ugauge k inf x Ur β c) r' j)) •
            P j := by
        funext v
        have := key_off inf x F lam Ur β c r' v
        rw [hl'] at this
        simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, P, this, mul_add,
          Finset.mul_sum, ← mul_assoc, ht, one_mul]
        ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mem_Sp1 P hl))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcell j))
  · set r' : Fin (s * k - k) := ⟨r - k, by omega⟩
    have hl' : k + (r' : ℕ) = r := by simp [r']; omega
    have h1 : ellR (k := k) inf x lam c r' = 1 := by simp [ellR, r']; omega
    have e : Yf (k := k) inf x Ur β c r - P r = -∑ j : Fin k, (Z3NetF.PPhi k inf x F lam Ur β c c r' j -
        (Z3NetF.frameGraph R k inf x c c * Z3NetF.Ugauge k inf x Ur β c) r' j) • P j := by
      funext v
      have := key_off inf x F lam Ur β c r' v
      rw [hl', h1] at this
      simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, P, this, one_mul]
      ring
    rw [e]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcell j))

/-- **`rem:projlines` for `𝒫^F_k` over `R`**: for `s k = 2r + 1` with `r ≥ k + 1`, the coefficient of the relation
between digit `r` of coordinates `b` and `a` exists and is `projSign` (the gauge of `def:Ns` keeps the frame's). -/
theorem PGen_rowRel_iff (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur) {r : ℕ}
    (hm : s * k = 2 * r + 1) (hr : k + 1 ≤ r) {a b : Fin s} (hab : a ≠ b) (g : R) :
    Z3NetF.RowRel (Z3NetF.PGen k inf x F lam Ur β a) (Z3NetF.PGen k inf x F lam Ur β b) r g ↔
      g = (Z3NetF.projSign inf a b r : R) := by
  have hrm : r < s * k := by omega
  have hsign : Z3NetF.RowRel (Z3NetF.PGen k inf x F lam Ur β a) (Z3NetF.PGen k inf x F lam Ur β b) r
      (Z3NetF.projSign inf a b r : R) := by
    have hF := (frame_rowRel_iff (m := s * k) inf x hx hm hab (Z3NetF.projSign inf a b r : R)).mpr rfl
    obtain ⟨α, β', hF⟩ := hF
    have hY : Yf (k := k) inf x Ur β b r - (Z3NetF.projSign inf a b r : R) • Yf (k := k) inf x Ur β a r ∈
        Sp (Yf (k := k) inf x Ur β a) (Yf (k := k) inf x Ur β b) r := by
      rw [mem_Sp_iff]
      refine ⟨α, β', fun v => ?_⟩
      have e : ∀ c l, Yf (k := k) inf x Ur β c l v = Z3NetF.dig (Z3NetF.frameRead (s * k) inf x c)
          ((Gk k inf x)⁻¹ *ᵥ Umap (Z3NetF.Ugauge k inf x Ur β) v) l := by
        intro c l
        simp only [Yf, graphF_eq inf x hx c, Z3NetF.dig, mulVec_mulVec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
      rw [hF]; ring
    obtain ⟨ha1, ha2⟩ := Y_mem inf x F lam Ur β hx hres hr hrm a
    obtain ⟨hb1, hb2⟩ := Y_mem inf x F lam Ur β hx hres hr hrm b
    rw [rowRel_iff_Sp]
    exact Sp_transfer _ _ _ _ r _ ha1 hb1 ha2 hb2 hY
  constructor
  · intro h
    have hd : ∑ c, Z3NetF.pairDepth b a r c = s * k := by rw [pairDepth_sum (Ne.symm hab), hm]
    exact (rowRel_unique_of_box _ hab hm (tsk_unit_core k inf x hx F lam Ur β hres _ hd) h hsign).2
  · rintro rfl; exact hsign

/-- The same over any ring receiving `R` (the net `𝒫^F_{k,q}` over `ℤ/qℤ` for `ψ : R → ℤ/qℤ`). -/
theorem PGen_rowRel_iff_map {S : Type*} [CommRing S] (ψ : R →+* S) (hx : Z3NetF.PlacesOK inf x)
    (hres : Z3NetF.Residual inf x F lam Ur) {r : ℕ} (hm : s * k = 2 * r + 1) (hr : k + 1 ≤ r) {a b : Fin s}
    (hab : a ≠ b) (g : S) :
    Z3NetF.RowRel ((Z3NetF.PGen k inf x F lam Ur β a).map ψ) ((Z3NetF.PGen k inf x F lam Ur β b).map ψ) r g ↔
      g = (Z3NetF.projSign inf a b r : S) := by
  have hsign := rowRel_map ψ ((PGen_rowRel_iff inf x F lam Ur β hx hres hm hr hab _).mpr rfl)
  rw [map_intCast] at hsign
  constructor
  · intro h
    have hd : ∑ c, Z3NetF.pairDepth b a r c = s * k := by rw [pairDepth_sum (Ne.symm hab), hm]
    have hG : IsUnit (Z3NetF.boxMatrix (fun c => (Z3NetF.PGen k inf x F lam Ur β c).map ψ)
        (Z3NetF.pairDepth b a r)).det := by
      rw [box_map ψ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (tsk_unit_core k inf x hx F lam Ur β hres _ hd).map ψ
    exact (rowRel_unique_of_box (fun c => (Z3NetF.PGen k inf x F lam Ur β c).map ψ) hab hm hG h hsign).2
  · rintro rfl; exact hsign

end pgen

/-! ## `𝒫_{k,q}` (`def:net`): the general lemma with the box minors `±1` of `thm:t0` -/

section faure

lemma boxMatrix_bridge3 {R : Type*} [Zero R] {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) R)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) :
    Z3Net.boxMatrix C d = Z3NetF.boxMatrix C d := by
  ext r l
  have hr := r.isLt
  unfold Z3Net.boxMatrix Z3NetF.boxMatrix
  simp only [List.ofFn_succ, List.ofFn_zero, Z3NetF.boxLoc, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  split_ifs <;> first | rfl | omega

lemma P_box_unit (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : ∑ c, d c = 3 * k) :
    IsUnit (Z3NetF.boxMatrix (Z3Net.PGen k) d).det := by
  have hd' : d 0 + d 1 + d 2 = 3 * k := by rw [← hd, Fin.sum_univ_three]
  rw [← boxMatrix_bridge3 _ d hd']
  rcases Z3Net.Proofs.P_boxMinor k hk d hd' with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

/-- **`rem:projlines` for `𝒫_{k,q}`** (`k` odd, `r = (3k-1)/2`): an integer sign `g = ±1`, the same for every base
`q`, such that in every base the relation holds with coefficient `g` and with no other coefficient. -/
theorem P_rowRel_core (k : ℕ) (hk : Odd k) {a b : Fin 3} (hab : a ≠ b) :
    ∃ g : ℤ, (g = 1 ∨ g = -1) ∧ ∀ (q : ℕ) (g' : ZMod q),
      Z3NetF.RowRel ((Z3Net.PGen k a).map (Int.cast : ℤ → ZMod q))
        ((Z3Net.PGen k b).map (Int.cast : ℤ → ZMod q)) ((3 * k - 1) / 2) g' ↔ g' = g := by
  obtain ⟨j, rfl⟩ := hk
  set r := (3 * (2 * j + 1) - 1) / 2
  have hm : 3 * (2 * j + 1) = 2 * r + 1 := by omega
  have hk1 : 1 ≤ 2 * j + 1 := by omega
  have hd1 : ∑ c, Z3NetF.pairDepth a b r c = 3 * (2 * j + 1) := by rw [pairDepth_sum hab, hm]
  have hd2 : ∑ c, Z3NetF.pairDepth b a r c = 3 * (2 * j + 1) := by rw [pairDepth_sum (Ne.symm hab), hm]
  obtain ⟨g, hg⟩ := rowRel_of_box (Z3Net.PGen (2 * j + 1)) hab hm (P_box_unit _ hk1 _ hd1)
  have hu := (rowRel_unique_of_box (Z3Net.PGen (2 * j + 1)) hab hm (P_box_unit _ hk1 _ hd2) hg hg).1
  refine ⟨g, Int.isUnit_iff.mp hu, fun q g' => ?_⟩
  have hmap := rowRel_map (Int.castRingHom (ZMod q)) hg
  have hG : IsUnit (Z3NetF.boxMatrix (fun c => (Z3Net.PGen (2 * j + 1) c).map (Int.castRingHom (ZMod q)))
      (Z3NetF.pairDepth b a r)).det := by
    rw [box_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (P_box_unit _ hk1 _ hd2).map _
  constructor
  · intro h
    have := (rowRel_unique_of_box (fun c => (Z3Net.PGen (2 * j + 1) c).map (Int.castRingHom (ZMod q)))
      hab hm hG h hmap).2
    simpa using this
  · rintro rfl; simpa using hmap

end faure

/-! ## Rescaling one row (the remedy) -/

section scale

variable {R : Type*} [CommRing R] {s m : ℕ}

lemma dig_rowScale (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ) (ρ : Fin s → R) (c : Fin s)
    (v : Fin m → R) (l : ℕ) :
    Z3NetF.dig (Z3NetF.rowScale C r ρ c) v l = (if l = r then ρ c else 1) * Z3NetF.dig (C c) v l := by
  unfold Z3NetF.dig
  by_cases hl : l < m
  · rw [dif_pos hl, dif_pos hl]
    simp only [mulVec, dotProduct, Z3NetF.rowScale]
    by_cases hr : l = r
    · rw [if_pos hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [if_pos hr, mul_assoc]
    · rw [if_neg hr, one_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [if_neg hr]
  · rw [dif_neg hl, dif_neg hl, mul_zero]

/-- The weights of the rows of a box after rescaling row `r`. -/
def scaleVec (d : Fin s → ℕ) (r : ℕ) (ρ : Fin s → R) (n : Fin m) : R :=
  if h : (Z3NetF.boxLoc (List.ofFn d) 0 n).1 < s then
    (if (Z3NetF.boxLoc (List.ofFn d) 0 n).2 = r then ρ ⟨_, h⟩ else 1) else 1

lemma scaleVec_pre (d : Fin s → ℕ) (hd : ∑ c, d c = m) (r : ℕ) (ρ : Fin s → R) (c : Fin s) (i : ℕ)
    (hi : i < d c) : scaleVec (m := m) d r ρ ⟨pre d c + i, pre_add_lt d hd c i hi⟩ = if i = r then ρ c else 1 := by
  have hloc := boxLoc_pre d c i hi
  simp [scaleVec, hloc]

lemma box_rowScale (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ) (ρ : Fin s → R) (d : Fin s → ℕ)
    (hd : ∑ c, d c = m) :
    Z3NetF.boxMatrix (Z3NetF.rowScale C r ρ) d = diagonal (scaleVec d r ρ) * Z3NetF.boxMatrix C d := by
  ext n j
  obtain ⟨c, i, hi, hn, -⟩ := box_row_cover d hd n
  have hn' : n = ⟨pre d c + i, pre_add_lt d hd c i hi⟩ := Fin.ext hn
  subst hn'
  rw [diagonal_mul, scaleVec_pre d hd r ρ c i hi, box_row_pre _ d hd c i hi, box_row_pre C d hd c i hi]
  simp only [Z3NetF.rowScale]
  split_ifs <;> simp

lemma prod_cols {M : Type*} [CommMonoid M] (K : Fin s → ℕ) (hK : ∑ c, K c = m) (f : Fin m → M) :
    ∏ j, f j = ∏ d : Fin s, ∏ l : Fin (K d), f ⟨pre K d + l, pre_add_lt K hK d l l.isLt⟩ := by
  rw [← Fintype.prod_sigma (fun (p : Σ d : Fin s, Fin (K d)) =>
    f ⟨pre K p.1 + p.2, pre_add_lt K hK p.1 p.2 p.2.isLt⟩)]
  symm
  apply Fintype.prod_bijective (fun p : Σ d : Fin s, Fin (K d) =>
    (⟨pre K p.1 + p.2, pre_add_lt K hK p.1 p.2 p.2.isLt⟩ : Fin m))
  · constructor
    · rintro ⟨d, l⟩ ⟨d', l'⟩ h
      have := pos_inj K d d' l l' l.isLt l'.isLt (congrArg Fin.val h)
      exact sigma_eq_of d d' l l' this.1 this.2
    · intro j
      obtain ⟨e, l, hl, rfl⟩ := col_cover K hK j
      exact ⟨⟨e, ⟨l, hl⟩⟩, rfl⟩
  · intro p; rfl

lemma prod_scaleVec (d : Fin s → ℕ) (hd : ∑ c, d c = m) (r : ℕ) (ρ : Fin s → R) :
    ∏ n, scaleVec (m := m) d r ρ n = ∏ c, if r < d c then ρ c else 1 := by
  rw [prod_cols d hd]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [scaleVec_pre d hd r ρ c _ (Fin.isLt _)]
  by_cases h : r < d c
  · rw [if_pos h, Fintype.prod_eq_single (⟨r, h⟩ : Fin (d c)), if_pos rfl]
    intro l hl
    rw [if_neg]; intro h'; exact hl (Fin.ext h')
  · rw [if_neg h]
    exact Finset.prod_eq_one fun l _ => if_neg (by have := l.isLt; omega)

/-- **The rescaled box minors**: rescaling row `r` of every `C_c` by `ρ_c` multiplies the box minor with depths `d`
by the product of the `ρ_c` with `r < d_c` (`eq:scr` for the diagonal scramble). -/
theorem rowScale_box_core (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ) (ρ : Fin s → R) (d : Fin s → ℕ)
    (hd : ∑ c, d c = m) :
    (Z3NetF.boxMatrix (Z3NetF.rowScale C r ρ) d).det =
      (∏ c, if r < d c then ρ c else 1) * (Z3NetF.boxMatrix C d).det := by
  rw [box_rowScale C r ρ d hd, det_mul, det_diagonal, prod_scaleVec d hd r ρ]

/-- **The remedy keeps `t = 0`**: with units `ρ_c`, the rescaled digital point set over `ℤ/qℤ` is a
`(0,m,s)`-net iff the original one is. -/
theorem rowScale_net_core {q : ℕ} [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (r : ℕ)
    (ρ : Fin s → ZMod q) (hρ : ∀ c, IsUnit (ρ c)) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m (Z3NetF.rowScale C r ρ)) ↔
      Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m C) := by
  rw [nie_zmod q, nie_zmod q]
  refine forall_congr' fun d => imp_congr_right fun hd => ?_
  rw [rowScale_box_core C r ρ d hd, IsUnit.mul_iff]
  have hu : IsUnit (∏ c, if r < d c then ρ c else 1) := by
    rw [IsUnit.prod_univ_iff]; intro c; split_ifs
    · exact hρ c
    · exact isUnit_one
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- **The remedy's effect on the relation**: after rescaling row `r` by `ρ`, the coefficient `g` becomes
`ρ_b g ρ_a⁻¹`. -/
theorem rowScale_rowRel_core (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ) (ρ : Fin s → R) {a b : Fin s}
    {g : R} (ha : IsUnit (ρ a)) (h : Z3NetF.RowRel (C a) (C b) r g) :
    Z3NetF.RowRel (Z3NetF.rowScale C r ρ a) (Z3NetF.rowScale C r ρ b) r (ρ b * g * Ring.inverse (ρ a)) := by
  obtain ⟨α, β, h⟩ := h
  refine ⟨fun l => ρ b * α l, fun l => ρ b * β l, fun v => ?_⟩
  simp only [dig_rowScale, ite_true]
  have hs : ∑ l ∈ range r, (ρ b * α l * ((if l = r then ρ a else 1) * Z3NetF.dig (C a) v l) +
      ρ b * β l * ((if l = r then ρ b else 1) * Z3NetF.dig (C b) v l)) =
      ρ b * ∑ l ∈ range r, (α l * Z3NetF.dig (C a) v l + β l * Z3NetF.dig (C b) v l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [if_neg (ne_of_lt (Finset.mem_range.mp hl)), if_neg (ne_of_lt (Finset.mem_range.mp hl))]; ring
  rw [hs, h v]
  have hi : Ring.inverse (ρ a) * ρ a = 1 := Ring.inverse_mul_cancel _ ha
  linear_combination (-(ρ b * g * Z3NetF.dig (C a) v r)) * hi

/-- Rescaling an offset row `r ≥ k` of a graph form with depths `(k, …, k)` is the graph form with that offset row of
every block `Φ_cd` rescaled by `ρ_c`. -/
lemma rowScale_graphGenK {s k : ℕ} (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R) {r : ℕ} (hr : k ≤ r)
    (ρ : Fin s → R) :
    Z3NetF.rowScale (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) r ρ =
      Z3NetF.graphGenK (m := s * k) (fun _ => k)
        (fun c d i l => if k + (i : ℕ) = r then ρ c * Φ c d i l else Φ c d i l) := by
  funext c
  ext i j
  simp only [Z3NetF.rowScale, Z3NetF.graphGenK]
  split_ifs <;> first | rfl | omega | simp

end scale

/-! ## The statements in the paper's form -/

section paper

/-- `m = s k` odd with `(s, k) ≠ (3, 1)` gives `m = 2 r* + 1` with `r* = (m-1)/2 ≥ k + 1`. -/
lemma rstar_ok {s k : ℕ} (hs : 2 ≤ s) (hodd : Odd (s * k)) (hsk : (s, k) ≠ (3, 1)) :
    s * k = 2 * ((s * k - 1) / 2) + 1 ∧ k + 1 ≤ (s * k - 1) / 2 := by
  obtain ⟨hs', hk'⟩ := Nat.odd_mul.mp hodd
  obtain ⟨t, ht⟩ := hodd
  obtain ⟨j, hj⟩ := hk'
  obtain ⟨i, hi⟩ := hs'
  refine ⟨by omega, ?_⟩
  by_cases h3 : s = 3
  · subst h3
    have : k ≠ 1 := fun h => hsk (by rw [h])
    omega
  · have h5 : 5 ≤ s := by omega
    have := Nat.mul_le_mul_right k h5
    omega

variable {R : Type*} [CommRing R] {s k : ℕ} (inf : Fin s) (x : Fin s → R) (F : ℕ → Fin s → Fin s → R)
  (lam : Fin s → R) (Ur β : Fin s → ℕ → ℕ → R)

lemma two_le_of_ne {a b : Fin s} (hab : a ≠ b) : 2 ≤ s := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  have : a ≠ b := fun h => hab (Fin.ext h)
  omega

theorem projlines_core (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur)
    (hodd : Odd (s * k)) (hsk : (s, k) ≠ (3, 1)) {a b : Fin s} (hab : a ≠ b) (g : R) :
    Z3NetF.RowRel (Z3NetF.PGen k inf x F lam Ur β a) (Z3NetF.PGen k inf x F lam Ur β b) ((s * k - 1) / 2) g ↔
      g = (Z3NetF.projSign inf a b ((s * k - 1) / 2) : R) :=
  PGen_rowRel_iff inf x F lam Ur β hx hres (rstar_ok (two_le_of_ne hab) hodd hsk).1
    (rstar_ok (two_le_of_ne hab) hodd hsk).2 hab g

theorem projlines_zmod_core {q : ℕ} (ψ : R →+* ZMod q) (hx : Z3NetF.PlacesOK inf x)
    (hres : Z3NetF.Residual inf x F lam Ur) (hodd : Odd (s * k)) (hsk : (s, k) ≠ (3, 1)) {a b : Fin s}
    (hab : a ≠ b) (g : ZMod q) :
    Z3NetF.RowRel ((Z3NetF.PGen k inf x F lam Ur β a).map ψ) ((Z3NetF.PGen k inf x F lam Ur β b).map ψ)
      ((s * k - 1) / 2) g ↔ g = (Z3NetF.projSign inf a b ((s * k - 1) / 2) : ZMod q) :=
  PGen_rowRel_iff_map inf x F lam Ur β ψ hx hres (rstar_ok (two_le_of_ne hab) hodd hsk).1
    (rstar_ok (two_le_of_ne hab) hodd hsk).2 hab g

/-- The general lemma: both boxes `(r+1, r)` and `(r, r+1)` invertible give a unique relation coefficient, a unit. -/
theorem projlines_box_core {m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) {a b : Fin s} (hab : a ≠ b) {r : ℕ}
    (hm : m = 2 * r + 1) (h1 : IsUnit (Z3NetF.boxMatrix C (Z3NetF.pairDepth a b r)).det)
    (h2 : IsUnit (Z3NetF.boxMatrix C (Z3NetF.pairDepth b a r)).det) :
    ∃ g, IsUnit g ∧ Z3NetF.RowRel (C a) (C b) r g ∧ ∀ g', Z3NetF.RowRel (C a) (C b) r g' → g' = g := by
  obtain ⟨g, hg⟩ := rowRel_of_box C hab hm h1
  exact ⟨g, (rowRel_unique_of_box C hab hm h2 hg hg).1, hg,
    fun g' hg' => ((rowRel_unique_of_box C hab hm h2 hg hg').2).symm⟩

theorem tsk_net_rowScale_core {q : ℕ} [NeZero q] (ψ : R →+* ZMod q) (hx : Z3NetF.PlacesOK inf x)
    (hres : Z3NetF.Residual inf x F lam Ur) (r : ℕ) (ρ : Fin s → ZMod q) (hρ : ∀ c, IsUnit (ρ c)) :
    Z3NetF.IsNet0 s q (s * k) (Z3NetF.digPoint q (s * k)
      (Z3NetF.rowScale (fun c => (Z3NetF.PGen k inf x F lam Ur β c).map ψ) r ρ)) :=
  (rowScale_net_core _ r ρ hρ).mpr (tsk_net_core k inf x ψ hx F lam Ur β hres)

theorem P_net_rowScale_core (q : ℕ) [NeZero q] (k : ℕ) (hk : 1 ≤ k) (r : ℕ) (ρ : Fin 3 → ZMod q)
    (hρ : ∀ c, IsUnit (ρ c)) :
    Z3NetF.IsNet0 3 q (3 * k) (Z3NetF.digPoint q (3 * k)
      (Z3NetF.rowScale (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ)) := by
  refine (rowScale_net_core _ r ρ hρ).mpr ?_
  rw [nie_zmod q]
  intro d hd
  have e := box_map (Int.castRingHom (ZMod q)) (Z3Net.PGen k) d
  simp only [Int.coe_castRingHom] at e
  rw [e, ← Int.coe_castRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (P_box_unit k hk d hd).map _

end paper

end

end Z3NetF.Proofs
