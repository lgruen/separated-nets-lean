/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DShiftDefs
public import Z3Net.FNie
public import Z3Net.FFrame

@[expose] public section

/-!
# V14 stage S10′: digital shifts (`def:dshift`, `lem:shift`)

* Digits of an integer coordinate at scale `q^m` (`digSum_digit`, `digSum_recon`); the shift of one
  coordinate (`dshiftCoord`): its digits, the prefix of its leading `d` digits is the shift of the
  prefix (`dshiftCoord_prefix`), and it is a bijection of `[0, q^d)` (`dshiftCoord_neg`).
* `digPointShift` is `dshiftPt` of `digPoint` (`digPointShift_eq_dshiftPt`); `τ = 0` gives `digPoint`.
* A digital shift maps every elementary box of shape `d` bijectively onto one of the same shape, so it
  preserves the exactness of every box shape (`dshift_boxExact`) and the `(0,m,s)`-property
  (`dshift_net`, `digPointShift_net`) of any point set.
* `lem:shift` for graph forms with any depths `K` (`shift_graph`): after re-indexing `n = v + T`, the
  shifted net is the affine graph form with offsets `Φ n + γ`, `γ_c = τ^off_c − ∑_d Φ_cd τ^cell_d`; one
  point in every cell (`shift_graph_cells`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

/-! ## Digits of an integer coordinate -/

section digits

variable {q : ℕ}

lemma digSum_eq_fin (m : ℕ) (f : Fin m → ℕ) :
    Z3Net.Proofs.digSum q m f = ∑ j : Fin m, f j * q ^ (m - 1 - (j : ℕ)) := rfl

/-- Digit `j` of a digit sum. -/
lemma digSum_digit (hq : 0 < q) (m : ℕ) (f : Fin m → ℕ) (hf : ∀ j, f j < q) (j : Fin m) :
    Z3Net.Proofs.digSum q m f / q ^ (m - 1 - (j : ℕ)) % q = f j := by
  have hj := j.isLt
  have h1 := digSum_div_prefix q hq m f hf ((j : ℕ) + 1) (by omega)
  rw [show m - ((j : ℕ) + 1) = m - 1 - (j : ℕ) by omega] at h1
  rw [h1, Z3Net.Proofs.digSum_succ, Nat.mul_add_mod, Nat.mod_eq_of_lt (hf _)]
  rfl

/-- An integer `x < q^m` is the digit sum of its digits. -/
lemma digSum_recon (hq : 0 < q) : ∀ (m x : ℕ), x < q ^ m →
    Z3Net.Proofs.digSum q m (fun j => x / q ^ (m - 1 - (j : ℕ)) % q) = x := by
  intro m
  induction m with
  | zero => intro x hx; rw [pow_zero] at hx; simp [Z3Net.Proofs.digSum]; omega
  | succ m ih =>
    intro x hx
    rw [Z3Net.Proofs.digSum_succ]
    have hxq : x / q < q ^ m := by
      rw [Nat.div_lt_iff_lt_mul hq]; rw [pow_succ] at hx; exact hx
    have e : (fun j : Fin m => x / q ^ (m + 1 - 1 - ((Fin.castSucc j : Fin (m + 1)) : ℕ)) % q) =
        (fun j : Fin m => x / q / q ^ (m - 1 - (j : ℕ)) % q) := by
      funext j
      have hj := j.isLt
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simp only [Fin.val_castSucc]
      congr 3; omega
    rw [e, ih (x / q) hxq]
    simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.div_one]
    exact Nat.div_add_mod x q

variable [NeZero q]

omit [NeZero q] in
lemma dshiftCoord_eq (m : ℕ) (t : Fin m → ZMod q) (x : ℕ) :
    dshiftCoord q m t x = Z3Net.Proofs.digSum q m
      (fun j => ((((x / q ^ (m - 1 - (j : ℕ))) % q : ℕ) : ZMod q) + t j).val) := rfl

lemma dshiftCoord_lt (m : ℕ) (t : Fin m → ZMod q) (x : ℕ) : dshiftCoord q m t x < q ^ m :=
  Z3Net.Proofs.digSum_lt q m _ (fun _ => ZMod.val_lt _)

/-- The digits of a shifted coordinate. -/
lemma dshiftCoord_digit (m : ℕ) (t : Fin m → ZMod q) (x : ℕ) (j : Fin m) :
    dshiftCoord q m t x / q ^ (m - 1 - (j : ℕ)) % q =
      ((((x / q ^ (m - 1 - (j : ℕ))) % q : ℕ) : ZMod q) + t j).val := by
  rw [dshiftCoord_eq]
  exact digSum_digit (Nat.pos_of_neZero q) m _ (fun _ => ZMod.val_lt _) j

/-- The shift by `-t` undoes the shift by `t` on `[0, q^m)`. -/
lemma dshiftCoord_neg (m : ℕ) (t : Fin m → ZMod q) (x : ℕ) (hx : x < q ^ m) :
    dshiftCoord q m (-t) (dshiftCoord q m t x) = x := by
  rw [dshiftCoord_eq]
  conv_rhs => rw [← digSum_recon (Nat.pos_of_neZero q) m x hx]
  congr 1
  funext j
  rw [dshiftCoord_digit, ZMod.natCast_zmod_val, Pi.neg_apply, add_neg_cancel_right, ZMod.val_natCast,
    Nat.mod_mod]

/-- The leading `d` digits of a shifted coordinate are the shift of the leading `d` digits. -/
lemma dshiftCoord_prefix (m : ℕ) (t : Fin m → ZMod q) (x : ℕ) (d : ℕ) (hd : d ≤ m) :
    dshiftCoord q m t x / q ^ (m - d) =
      dshiftCoord q d (fun j => t ⟨j, lt_of_lt_of_le j.isLt hd⟩) (x / q ^ (m - d)) := by
  rw [dshiftCoord_eq, digSum_div_prefix q (Nat.pos_of_neZero q) m _ (fun _ => ZMod.val_lt _) d hd,
    dshiftCoord_eq]
  congr 1
  funext j
  have hj := j.isLt
  simp only
  rw [Nat.div_div_eq_div_mul, ← pow_add, show m - d + (d - 1 - (j : ℕ)) = m - 1 - (j : ℕ) by omega]

end digits

/-! ## Digital point sets -/

section digital

variable {q : ℕ} [NeZero q] {s m : ℕ}

/-- Digit `j` of a coordinate of a digital point. -/
lemma coord_digit (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) (j : Fin m) :
    Z3NetF.coord q m C v / q ^ (m - 1 - (j : ℕ)) % q = ((C *ᵥ v) j).val :=
  digSum_digit (Nat.pos_of_neZero q) m (fun j => ((C *ᵥ v) j).val) (fun _ => ZMod.val_lt _) j

/-- **`def:dshift`**: `digPointShift` is the shift (`dshiftPt`) of the digital point set. -/
theorem digPointShift_eq_dshiftPt (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (v : Fin m → ZMod q) :
    Z3NetF.digPointShift q m C τ v = Z3NetF.dshiftPt q m τ (Z3NetF.digPoint q m C v) := by
  funext c
  simp only [Z3NetF.digPointShift, Z3NetF.dshiftPt, Z3NetF.dshiftCoord, Z3NetF.digPoint]
  refine sum_congr rfl fun j _ => ?_
  rw [coord_digit, ZMod.natCast_zmod_val, Pi.add_apply]

omit [NeZero q] in
/-- `τ = 0`: the unshifted net. -/
theorem digPointShift_zero (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetF.digPointShift q m C 0 = Z3NetF.digPoint q m C := by
  funext v c
  simp [Z3NetF.digPointShift, Z3NetF.digPoint, Z3NetF.coord]

/-- Re-indexing by any `T`: the shift `τ` at index `v` is the shift `τ - C T` at index `v + T`. -/
theorem digPointShift_reindex (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (T v : Fin m → ZMod q) :
    Z3NetF.digPointShift q m C τ v =
      Z3NetF.digPointShift q m C (fun c => τ c - C c *ᵥ T) (v + T) := by
  funext c
  simp only [Z3NetF.digPointShift]
  have e : C c *ᵥ (v + T) + (τ c - C c *ᵥ T) = C c *ᵥ v + τ c := by rw [mulVec_add]; abel
  rw [e]

lemma digPointShift_lt (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (v : Fin m → ZMod q) (c : Fin s) :
    Z3NetF.digPointShift q m C τ v c < q ^ m :=
  Z3Net.Proofs.digSum_lt q m _ (fun _ => ZMod.val_lt _)

lemma digPoint_lt (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) (c : Fin s) :
    Z3NetF.digPoint q m C v c < q ^ m :=
  Z3Net.Proofs.digSum_lt q m _ (fun _ => ZMod.val_lt _)

end digital

/-! ## Boxes and nets -/

section boxes

variable {q : ℕ} [NeZero q] {s m : ℕ}

/-- Every elementary box of shape `d` holds exactly one point of `X`. -/
def BoxExactX (X : (Fin m → ZMod q) → Fin s → ℕ) (d : Fin s → ℕ) : Prop :=
  ∀ a : Fin s → ℕ, (∀ c, a c < q ^ d c) → ∃! v : Fin m → ZMod q, ∀ c, X v c / q ^ (m - d c) = a c

/-- A digital shift maps the boxes of shape `d` bijectively onto the boxes of shape `d`. -/
theorem dshift_boxExact (X : (Fin m → ZMod q) → Fin s → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (d : Fin s → ℕ) (hd : ∀ c, d c ≤ m) (τ : Fin s → Fin m → ZMod q) (h : BoxExactX X d) :
    BoxExactX (fun v => Z3NetF.dshiftPt q m τ (X v)) d := by
  intro a ha
  let tc : (c : Fin s) → Fin (d c) → ZMod q := fun c j => τ c ⟨j, lt_of_lt_of_le j.isLt (hd c)⟩
  -- the prefix of the target before the shift
  let a' : Fin s → ℕ := fun c => dshiftCoord q (d c) (-(tc c)) (a c)
  have ha' : ∀ c, a' c < q ^ d c := fun c => dshiftCoord_lt _ _ _
  have hpre : ∀ v c, Z3NetF.dshiftPt q m τ (X v) c / q ^ (m - d c) =
      dshiftCoord q (d c) (tc c) (X v c / q ^ (m - d c)) :=
    fun v c => dshiftCoord_prefix m (τ c) (X v c) (d c) (hd c)
  have hXd : ∀ v c, X v c / q ^ (m - d c) < q ^ d c := by
    intro v c
    rw [Nat.div_lt_iff_lt_mul (pow_pos (Nat.pos_of_neZero q) _), ← pow_add, show d c + (m - d c) = m by have := hd c; omega]
    exact hX v c
  -- `y ↦ shift_t y` is a bijection of `[0, q^d)`
  have hiff : ∀ v c, (dshiftCoord q (d c) (tc c) (X v c / q ^ (m - d c)) = a c ↔
      X v c / q ^ (m - d c) = a' c) := by
    intro v c
    constructor
    · intro e
      show X v c / q ^ (m - d c) = dshiftCoord q (d c) (-(tc c)) (a c)
      rw [← e, dshiftCoord_neg (d c) (tc c) _ (hXd v c)]
    · intro e
      rw [e]
      have := dshiftCoord_neg (d c) (-(tc c)) (a c) (ha c)
      rwa [neg_neg] at this
  obtain ⟨v, hv, huniq⟩ := h a' ha'
  refine ⟨v, fun c => ?_, fun w hw => huniq w fun c => ?_⟩
  · rw [hpre, hiff]; exact hv c
  · rw [← hiff, ← hpre]; exact hw c

/-- **`lem:shift`**, net part, for any point set: a digital shift preserves the `(0,m,s)`-property. -/
theorem dshift_net (X : (Fin m → ZMod q) → Fin s → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (τ : Fin s → Fin m → ZMod q) (h : Z3NetF.IsNet0 s q m X) :
    Z3NetF.IsNet0 s q m (fun v => Z3NetF.dshiftPt q m τ (X v)) := by
  intro d hd
  have hdm : ∀ c, d c ≤ m := fun c => by
    rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  exact dshift_boxExact X hX d hdm τ (h d hd)

/-- **`lem:shift`**, net part, digital nets: `P ⊕ τ` is a `(0,m,s)`-net if `P` is. -/
theorem digPointShift_net (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (h : Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m C)) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPointShift q m C τ) := by
  have := dshift_net (Z3NetF.digPoint q m C) (digPoint_lt C) τ h
  simpa only [← digPointShift_eq_dshiftPt] using this

end boxes

/-! ## `lem:shift` for graph forms -/

section graph

variable {q : ℕ} [NeZero q] {s m : ℕ}

/-- The index whose cells are `τ^cell` (level `l` of the cell of coordinate `d` is `τc d l`). -/
def Tcell (K : Fin s → ℕ) (τc : (c : Fin s) → Fin (K c) → ZMod q) : Fin m → ZMod q := fun j =>
  if hb : (Z3NetF.boxLoc (List.ofFn K) 0 j).1 < s then
    if hl : (Z3NetF.boxLoc (List.ofFn K) 0 j).2 < K ⟨_, hb⟩ then τc ⟨_, hb⟩ ⟨_, hl⟩ else 0
  else 0

omit [NeZero q] in
lemma Tcell_apply (K : Fin s → ℕ) (hK : ∑ c, K c = m) (τc : (c : Fin s) → Fin (K c) → ZMod q)
    (d : Fin s) (l : Fin (K d)) :
    Tcell (m := m) K τc ⟨pre K d + l, pre_add_lt K hK d l l.isLt⟩ = τc d l := by
  have h := boxLoc_pre K d l l.isLt
  unfold Tcell
  have key : ∀ (p : ℕ × ℕ), p = ((d : ℕ), (l : ℕ)) →
      (if hb : p.1 < s then if hl : p.2 < K ⟨_, hb⟩ then τc ⟨_, hb⟩ ⟨_, hl⟩ else 0 else 0) = τc d l := by
    rintro p rfl
    simp [d.isLt, l.isLt]
  exact key _ h

omit [NeZero q] in
/-- `τ - G T = (0, τ^off - Φ τ^cell)`. -/
lemma shift_graph_gamma (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q))
    (τc : (c : Fin s) → Fin (K c) → ZMod q) (τo : (c : Fin s) → Fin (m - K c) → ZMod q) (c : Fin s) :
    Z3NetF.cellOff (τc c) (τo c) - Z3NetF.graphGenK K Φ c *ᵥ Tcell K τc =
      Z3NetF.cellOff 0 (fun r => τo c r - ∑ d, ∑ l, Φ c d r l * τc d l) := by
  funext j
  simp only [Pi.sub_apply, Z3NetF.cellOff]
  by_cases hj : (j : ℕ) < K c
  · rw [dif_pos hj, dif_pos hj]
    have e := graphGenK_mulVec_cell K hK Φ c (Tcell K τc) j hj
    rw [show (⟨(j : ℕ), lt_of_lt_of_le hj (le_of_sum K hK c)⟩ : Fin m) = j from Fin.ext rfl] at e
    rw [e, Tcell_apply K hK τc c ⟨j, hj⟩]
    simp
  · rw [dif_neg hj, dif_neg hj]
    have e := graphGenK_mulVec_off K hK Φ c (Tcell K τc) ⟨(j : ℕ) - K c, by omega⟩
    rw [show (⟨K c + ((j : ℕ) - K c), by omega⟩ : Fin m) = j from Fin.ext (by simp; omega)] at e
    rw [e]
    congr 1
    refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
    rw [Tcell_apply K hK τc d l]

/-- **`lem:shift`**: after re-indexing by the cells `n = v + T` (`T` the index with cells `τ^cell`), the
shifted graph form is the affine graph form with offsets `Φ n + γ`, `γ_c = τ^off_c - ∑_d Φ_cd τ^cell_d`. -/
theorem shift_graph (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q))
    (τc : (c : Fin s) → Fin (K c) → ZMod q) (τo : (c : Fin s) → Fin (m - K c) → ZMod q) :
    ∃ T : Fin m → ZMod q, ∀ v : Fin m → ZMod q,
      Z3NetF.digPointShift q m (Z3NetF.graphGenK K Φ) (fun c => Z3NetF.cellOff (τc c) (τo c)) v =
        Z3NetF.digPointShift q m (Z3NetF.graphGenK K Φ)
          (fun c => Z3NetF.cellOff 0 (fun r => τo c r - ∑ d, ∑ l, Φ c d r l * τc d l)) (v + T) := by
  refine ⟨Tcell K τc, fun v => ?_⟩
  rw [digPointShift_reindex _ _ (Tcell K τc) v]
  congr 1
  funext c
  exact shift_graph_gamma K hK Φ τc τo c

/-- Graph forms hold one point in every cell (the box of shape `K`). -/
lemma graph_cells (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q)) :
    BoxExactX (Z3NetF.digPoint q m (Z3NetF.graphGenK K Φ)) K := by
  have h := (nie_box (zmodE q) (Z3NetF.graphGenK K Φ) K hK).mpr (by rw [box_minor_self K hK Φ]; exact isUnit_one)
  exact h

/-- **`lem:shift`**: every digital shift of a graph form holds one point in every cell. -/
theorem shift_graph_cells (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q)) (τ : Fin s → Fin m → ZMod q) :
    BoxExactX (Z3NetF.digPointShift q m (Z3NetF.graphGenK K Φ) τ) K := by
  have := dshift_boxExact _ (digPoint_lt _) K (le_of_sum K hK) τ (graph_cells K hK Φ)
  simpa only [← digPointShift_eq_dshiftPt] using this

end graph

end

end Z3NetF.Proofs
