/-
Entry WhyLat: `cor:linoff` (c) and `lem:phase` (ii) of `paper/core.tex`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.WLGDefs
public import Z3Net.FMain
public import Z3Net.FSep

@[expose] public section

/-!
# `cor:linoff` (c) (locally a lattice) and `lem:phase` (ii) (unit minors, rank)

(c) uses the decomposition `X = q^a·cell + q^(a−1)·r + tail` of a graph-form coordinate from
entry F (`X_decompF`, `cell_of_digPoint`), the digit extraction `zmod_digit` and the offset-row
formula `graphGen_off`.  (ii) uses `lem:box` (`box_minor`) for the box with depths `k + 1` on
`T`, `k − 1` on `Z`, `k` elsewhere, and `lem:nie` (`nie_zmod`).
-/

namespace Z3NetF

open Matrix Finset

/-! ## `cor:linoff` (c) -/

theorem linoff_c' (q s k : ℕ) [NeZero q] (hq : 2 ≤ q) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q)) (M : Fin s → Fin s → ℤ)
    (hM : ∀ c d (r : Fin (s * k - k)) (l : Fin k), (r : ℕ) = 0 → (l : ℕ) = k - 1 →
      ((M c d : ℤ) : ZMod q) = Φ c d r l)
    (v w : Fin (s * k) → ZMod q) (E : Fin s → ℤ)
    (hcell : ∀ d, (cellPart q (s * k - k) (gfPt q s k Φ w d) : ℤ) =
      cellPart q (s * k - k) (gfPt q s k Φ v d) + E d)
    (hnc : ∀ d, 0 ≤ ((cellPart q (s * k - k) (gfPt q s k Φ v d) % q : ℕ) : ℤ) + E d ∧
      ((cellPart q (s * k - k) (gfPt q s k Φ v d) % q : ℕ) : ℤ) + E d < q)
    (hr : ∀ c, 0 ≤ (geoPart q (s * k - k) (gfPt q s k Φ v c) : ℤ) + ∑ d, M c d * E d ∧
      (geoPart q (s * k - k) (gfPt q s k Φ v c) : ℤ) + ∑ d, M c d * E d < q) (c : Fin s) :
    (geoPart q (s * k - k) (gfPt q s k Φ w c) : ℤ) =
        geoPart q (s * k - k) (gfPt q s k Φ v c) + ∑ d, M c d * E d ∧
      (gfPt q s k Φ w c : ℤ) - gfPt q s k Φ v c =
        (q : ℤ) ^ (s * k - k) * E c + (q : ℤ) ^ (s * k - k - 1) * ∑ d, M c d * E d +
          ((deepPart q (s * k - k) (gfPt q s k Φ w c) : ℤ) -
            deepPart q (s * k - k) (gfPt q s k Φ v c)) := by
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hq1 : 1 < q := by omega
  have hq0 : 0 < q := by omega
  have ha1 : 1 ≤ s * k - k := by omega
  have hqa : q ^ (s * k - k) = q ^ (s * k - k - 1) * q := by rw [← pow_succ]; congr 1; omega
  -- the three parts of a coordinate
  have hX : ∀ u c, (gfPt q s k Φ u c : ℤ) = (q : ℤ) ^ (s * k - k) * Z3NetU.Proofs.cellN s q k u c +
      ((q : ℤ) ^ (s * k - k - 1) * Proofs.o0F s q k Φ u c + Proofs.tlF s q k Φ u c) :=
    fun u c => Proofs.X_decompF s q k Φ hsk u c
  have htl : ∀ u c, Proofs.tlF s q k Φ u c < q ^ (s * k - k - 1) := fun u c =>
    Z3NetU.Proofs.tail_lt s q k hsk _
  have ho0 : ∀ u c, Proofs.o0F s q k Φ u c < q := fun u c => Z3NetU.Proofs.dv_lt s q k _ k
  have hcellN : ∀ u d, cellPart q (s * k - k) (gfPt q s k Φ u d) = Z3NetU.Proofs.cellN s q k u d :=
    fun u d => (Proofs.cell_of_digPoint s q k Φ hsk u d).1
  have hgeo : ∀ u c, geoPart q (s * k - k) (gfPt q s k Φ u c) = Proofs.o0F s q k Φ u c := by
    intro u c
    unfold geoPart gfPt
    rw [(Proofs.cell_of_digPoint s q k Φ hsk u c).2, Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt (htl u c), add_zero]
  have hdeep : ∀ u c, deepPart q (s * k - k) (gfPt q s k Φ u c) = Proofs.tlF s q k Φ u c := by
    intro u c
    unfold deepPart
    have hXn : gfPt q s k Φ u c = q ^ (s * k - k - 1) * (q * Z3NetU.Proofs.cellN s q k u c +
        Proofs.o0F s q k Φ u c) + Proofs.tlF s q k Φ u c := by
      have := hX u c
      have hqaZ : (q : ℤ) ^ (s * k - k) = (q : ℤ) ^ (s * k - k - 1) * q := by exact_mod_cast hqa
      have h' : (gfPt q s k Φ u c : ℤ) = (((q ^ (s * k - k - 1) * (q * Z3NetU.Proofs.cellN s q k u c +
          Proofs.o0F s q k Φ u c) + Proofs.tlF s q k Φ u c : ℕ)) : ℤ) := by
        rw [this, hqaZ]; push_cast; ring
      exact_mod_cast h'
    rw [hXn, Nat.mul_add_mod, Nat.mod_eq_of_lt (htl u c)]
  -- digits of the cells: only the last level changes, by `E`
  have hdig : ∀ d (l : Fin k), w (Z3NetU.Proofs.ix k d l) - v (Z3NetU.Proofs.ix k d l) =
      if (l : ℕ) = k - 1 then ((E d : ℤ) : ZMod q) else 0 := by
    intro d l
    have hc := hcell d
    have hn := hnc d
    rw [hcellN, hcellN] at hc
    rw [hcellN] at hn
    set A := Z3NetU.Proofs.cellN s q k v d
    set B := Z3NetU.Proofs.cellN s q k w d
    rw [Z3NetU.Proofs.zmod_digit s q hq1 k w, Z3NetU.Proofs.zmod_digit s q hq1 k v]
    by_cases hl : (l : ℕ) = k - 1
    · rw [if_pos hl, show k - 1 - (l : ℕ) = 0 by omega, pow_zero, Nat.div_one, Nat.div_one]
      have : ((B : ℤ) : ZMod q) = ((A : ℤ) : ZMod q) + ((E d : ℤ) : ZMod q) := by
        rw [hc]; push_cast; ring
      push_cast at this
      rw [this]; ring
    · rw [if_neg hl]
      have hlt : (l : ℕ) < k - 1 := by have := l.isLt; omega
      -- B / q = A / q
      have hBq : B / q = A / q := by
        have hA := Nat.div_add_mod A q
        have hBZ : (B : ℤ) = q * (A / q : ℕ) + ((A % q : ℕ) + E d) := by
          rw [hc]; have : ((A : ℕ) : ℤ) = q * (A / q : ℕ) + (A % q : ℕ) := by exact_mod_cast hA.symm
          rw [this]; ring
        have h1 : ((B / q : ℕ) : ℤ) = ((A / q : ℕ) : ℤ) := by
          rw [Int.natCast_div, hBZ, show (q : ℤ) * ((A / q : ℕ) : ℤ) + (((A % q : ℕ) : ℤ) + E d) =
            (((A % q : ℕ) : ℤ) + E d) + ((A / q : ℕ) : ℤ) * q by ring,
            Int.add_mul_ediv_right _ _ (by exact_mod_cast hq0.ne'),
            Int.ediv_eq_zero_of_lt hn.1 hn.2, zero_add]
        exact_mod_cast h1
      have ht : k - 1 - (l : ℕ) = (k - 1 - (l : ℕ) - 1) + 1 := by omega
      rw [ht, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hBq, sub_self]
  -- the geometric digit changes by `M E` modulo `q`
  have hk' : k < s * k := by omega
  have h0 : 0 < s * k - k := by omega
  have hoff : ∀ u, ((Proofs.o0F s q k Φ u c : ℕ) : ZMod q) =
      ∑ d : Fin s, ∑ l : Fin k, Φ c d ⟨0, h0⟩ l * u (Z3NetU.Proofs.ix k d l) := by
    intro u
    rw [Proofs.o0_castF s q k Φ u c hk']
    have := Z3NetU.Proofs.graphGen_off k Φ c u ⟨0, h0⟩
    simp only [Proofs.DgF]
    convert this using 2
  have hmod : ((Proofs.o0F s q k Φ w c : ℤ) : ZMod q) =
      (((Proofs.o0F s q k Φ v c : ℤ) + ∑ d, M c d * E d : ℤ) : ZMod q) := by
    push_cast
    rw [hoff w, hoff v, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_sub_distrib]
    have : ∀ l : Fin k, Φ c d ⟨0, h0⟩ l * w (Z3NetU.Proofs.ix k d l) -
        Φ c d ⟨0, h0⟩ l * v (Z3NetU.Proofs.ix k d l) =
        if (l : ℕ) = k - 1 then ((M c d : ℤ) : ZMod q) * ((E d : ℤ) : ZMod q) else 0 := by
      intro l
      rw [← mul_sub, hdig d l]
      split_ifs with hl
      · rw [hM c d ⟨0, h0⟩ l rfl hl]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.univ.filter fun l : Fin k => (l : ℕ) = k - 1) = {⟨k - 1, by omega⟩} := by
      ext l; simp [Fin.ext_iff]
    rw [hfilt, Finset.sum_singleton]
  have hgeoeq : (Proofs.o0F s q k Φ w c : ℤ) = Proofs.o0F s q k Φ v c + ∑ d, M c d * E d := by
    have hr' := hr c
    rw [hgeo] at hr'
    rw [ZMod.intCast_eq_intCast_iff'] at hmod
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ho0 w c),
      Int.emod_eq_of_lt hr'.1 hr'.2] at hmod
    exact hmod
  refine ⟨by rw [hgeo, hgeo]; exact hgeoeq, ?_⟩
  rw [hX w c, hX v c, hdeep, hdeep]
  have hc := hcell c
  rw [hcellN, hcellN] at hc
  rw [hc, hgeoeq]
  ring

/-! ## `lem:phase` (ii) -/

/-- The depths `k + 1` on `T`, `k − 1` on `Z`, `k` elsewhere. -/
def boxTZ (k : ℕ) {s : ℕ} (T Z : Finset (Fin s)) (c : Fin s) : ℕ :=
  if c ∈ T then k + 1 else if c ∈ Z then k - 1 else k

theorem boxTZ_sum (k : ℕ) (hk : 1 ≤ k) {s : ℕ} (T Z : Finset (Fin s)) (hTZ : Disjoint T Z)
    (hcard : T.card = Z.card) : ∑ c, boxTZ k T Z c = s * k := by
  have h : ∀ c, boxTZ k T Z c + (if c ∈ Z then 1 else 0) = k + (if c ∈ T then 1 else 0) := by
    intro c
    unfold boxTZ
    by_cases hT : c ∈ T
    · have hZ : c ∉ Z := Finset.disjoint_left.1 hTZ hT
      simp [hT, hZ]
    · by_cases hZ : c ∈ Z
      · simp [hT, hZ]; omega
      · simp [hT, hZ]
  have hs := Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => h c
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
  rw [hcard] at hs
  have : s * k = k * s := Nat.mul_comm s k
  omega

theorem phase_ii' (q s k : ℕ) [NeZero q] (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : IsNet0 s q (s * k) (gfPt q s k Φ)) (M : Fin s → Fin s → ZMod q)
    (hM : ∀ c d (r : Fin (s * k - k)) (l : Fin k), (r : ℕ) = 0 → (l : ℕ) = k - 1 →
      M c d = Φ c d r l)
    (T Z : Finset (Fin s)) (hTZ : Disjoint T Z) (σ : Z ≃ T) :
    IsUnit (Matrix.of fun a b : Z => M (σ a) b).det := by
  -- the empty case
  by_cases hZ0 : Z = ∅
  · subst hZ0
    haveI : IsEmpty (↥(∅ : Finset (Fin s))) := ⟨fun x => absurd x.2 (Finset.notMem_empty _)⟩
    rw [Matrix.det_isEmpty]; exact isUnit_one
  obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.2 hZ0
  have hT0 : (σ ⟨z0, hz0⟩ : Fin s) ∈ T := (σ ⟨z0, hz0⟩).2
  have hzt : (σ ⟨z0, hz0⟩ : Fin s) ≠ z0 := fun h =>
    Finset.disjoint_left.1 hTZ (h ▸ hT0) hz0
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s ≤ 1 := by omega
    exact hzt (Fin.ext (by have := (σ ⟨z0, hz0⟩ : Fin s).isLt; have := z0.isLt; omega))
  have hcard : T.card = Z.card := by
    rw [← Fintype.card_coe T, ← Fintype.card_coe Z]; exact (Fintype.card_congr σ).symm
  set d := boxTZ k T Z with hd
  have hdsum := boxTZ_sum k hk T Z hTZ hcard
  have hKsum : ∑ _c : Fin s, k = s * k := by simp
  -- the box minor is a unit
  have hunit := (nie_zmod (graphGenK (m := s * k) (fun _ => k) Φ)).1 hnet d hdsum
  -- the over/under index types
  have hover : ∀ c, (fun _ => k) c < d c ↔ c ∈ T := by
    intro c; simp only [hd, boxTZ]; split_ifs with h1 h2 <;> simp [h1] <;> omega
  have hunder : ∀ e, d e < (fun _ => k) e ↔ e ∈ Z := by
    intro e; simp only [hd, boxTZ]
    split_ifs with h1 h2
    · simp only [Finset.disjoint_left.1 hTZ h1, iff_false]; omega
    · simp only [h2, iff_true]; omega
    · simp only [h2, iff_false]; omega
  have hov1 : ∀ c, c ∈ T → d c - k = 1 := by intro c hc; simp [hd, boxTZ, hc]
  have hun1 : ∀ e, e ∈ Z → k - d e = 1 := by
    intro e he; simp [hd, boxTZ, he, Finset.disjoint_right.1 hTZ he]; omega
  let eU : UnderCols (fun _ => k) d ≃ Z :=
    { toFun := fun y => ⟨y.1.1, (hunder _).1 y.1.2⟩
      invFun := fun z => ⟨⟨z.1, (hunder _).2 z.2⟩, ⟨0, by show 0 < k - d z.1; have := hun1 z.1 z.2; omega⟩⟩
      left_inv := fun y => by
        obtain ⟨⟨e, he⟩, i⟩ := y
        have : (i : ℕ) = 0 := by
          have hi := i.isLt; simp only at hi; have := hun1 e ((hunder e).1 he); omega
        simp only
        congr 1
        exact Fin.ext this.symm
      right_inv := fun z => rfl }
  let eO : OverRows (fun _ => k) d ≃ T :=
    { toFun := fun y => ⟨y.1.1, (hover _).1 y.1.2⟩
      invFun := fun t => ⟨⟨t.1, (hover _).2 t.2⟩, ⟨0, by show 0 < d t.1 - k; have := hov1 t.1 t.2; omega⟩⟩
      left_inv := fun y => by
        obtain ⟨⟨c, hc⟩, i⟩ := y
        have : (i : ℕ) = 0 := by
          have hi := i.isLt; simp only at hi; have := hov1 c ((hover c).1 hc); omega
        simp only
        congr 1
        exact Fin.ext this.symm
      right_inv := fun t => rfl }
  let σ' : UnderCols (fun _ => k) d ≃ OverRows (fun _ => k) d := eU.trans (σ.trans eO.symm)
  obtain ⟨-, hbox⟩ := box_minor (R := ZMod q) (m := s * k) (fun _ => k) d hKsum hdsum
  obtain ⟨ε, hε, hdet⟩ := hbox σ'
  have hred : redBox (m := s * k) (fun _ => k) d Φ σ' =
      Matrix.submatrix (Matrix.of fun a b : Z => M (σ a) b) eU eU := by
    funext x y
    simp only [redBox, Matrix.submatrix_apply]
    have hσx : ((σ' x).2 : ℕ) = 0 := by
      have hi := (σ' x).2.isLt; dsimp only at hi; have := hov1 _ ((hover _).1 (σ' x).1.2); omega
    have hy : (y.2 : ℕ) = 0 := by
      have hi := y.2.isLt; dsimp only at hi; have := hun1 _ ((hunder _).1 y.1.2); omega
    have hsk0 : k < s * k := by nlinarith
    rw [dif_pos (by rw [hσx]; omega)]
    have hyd : d y.1.1 = k - 1 := by
      simp [hd, boxTZ, (hunder _).1 y.1.2, Finset.disjoint_right.1 hTZ ((hunder _).1 y.1.2)]
    simp only [Matrix.of_apply]
    refine (hM _ _ _ _ ?_ ?_).symm
    · exact hσx
    · show d y.1.1 + (y.2 : ℕ) = k - 1
      omega
  rw [hdet, hred, Matrix.det_submatrix_equiv_self] at hunit
  rcases hε with rfl | rfl
  · simpa using hunit
  · simpa using hunit

theorem phase_ii_rank' (q s k : ℕ) [NeZero q] (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : IsNet0 s q (s * k) (gfPt q s k Φ)) (M : Fin s → Fin s → ZMod q)
    (hM : ∀ c d (r : Fin (s * k - k)) (l : Fin k), (r : ℕ) = 0 → (l : ℕ) = k - 1 →
      M c d = Φ c d r l) :
    ∀ ℓ : ℕ, ℓ.Prime → ∀ h : ℓ ∣ q,
      s / 2 ≤ (Matrix.map (M : Matrix (Fin s) (Fin s) (ZMod q)) (ZMod.castHom h (ZMod ℓ))).rank := by
  intro ℓ hℓ h
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  set t := s / 2
  let f : Fin t → Fin s := fun i => ⟨i, by omega⟩
  let g : Fin t → Fin s := fun i => ⟨i + t, by omega⟩
  have hf : Function.Injective f := fun i j hij => Fin.ext (by simpa [f] using congrArg Fin.val hij)
  have hg : Function.Injective g := fun i j hij => Fin.ext (by simpa [g] using congrArg Fin.val hij)
  set T : Finset (Fin s) := Finset.univ.map ⟨f, hf⟩
  set Z : Finset (Fin s) := Finset.univ.map ⟨g, hg⟩
  have hTZ : Disjoint T Z := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [T, Z, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hx hx'
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hx'
    have := congrArg Fin.val hj
    simp [f, g] at this
    omega
  let eT : Fin t ≃ T := Equiv.ofBijective (fun i => ⟨f i, by simp [T]⟩)
    ⟨fun i j hij => hf (congrArg Subtype.val hij), fun x => by
      obtain ⟨i, -, hi⟩ := Finset.mem_map.1 x.2; exact ⟨i, Subtype.ext hi⟩⟩
  let eZ : Fin t ≃ Z := Equiv.ofBijective (fun i => ⟨g i, by simp [Z]⟩)
    ⟨fun i j hij => hg (congrArg Subtype.val hij), fun x => by
      obtain ⟨i, -, hi⟩ := Finset.mem_map.1 x.2; exact ⟨i, Subtype.ext hi⟩⟩
  have hu := phase_ii' q s k hk Φ hnet M hM T Z hTZ (eZ.symm.trans eT)
  have hsub : Matrix.submatrix (Matrix.of fun a b : Z => M ((eZ.symm.trans eT) a) b) eZ eZ =
      Matrix.submatrix M f g := by
    funext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  rw [← Matrix.det_submatrix_equiv_self eZ, hsub] at hu
  have hu' : IsUnit (Matrix.submatrix (Matrix.map (M : Matrix (Fin s) (Fin s) (ZMod q))
      (ZMod.castHom h (ZMod ℓ))) f g).det := by
    have := hu.map (ZMod.castHom h (ZMod ℓ))
    rw [RingHom.map_det] at this
    convert this using 2
    rfl
  have hrank := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hu')
  have hle := Matrix.rank_submatrix_le (Matrix.map (M : Matrix (Fin s) (Fin s) (ZMod q))
    (ZMod.castHom h (ZMod ℓ))) f g
  rw [hrank, Fintype.card_fin] at hle
  exact hle

end Z3NetF
