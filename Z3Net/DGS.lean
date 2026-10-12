/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DGSDefs
public import Z3Net.DShift
public import Z3Net.TwoGeom
public import Z3Net.FMain
public import Z3Net.SepShift
public import Z3Net.ThmAShift
public import Z3Net.Main
public import Z3Net.AllmShift
public import Z3Net.S1Main
public import Z3Net.ColMain
public import Z3Net.HLShift2

@[expose] public section

/-!
# V14 stage S10′: `cor:dgs`, `rem:dgsfinite`, `prop:linf` (the question of Dick, Goda and Suzuki)

With the definitions of [DGS2] (`Z3Net/DGSDefs.lean`):
* Step 1 of `cor:dgs`, the strict `[DGS2, Lemma 3.7]` (`lemma37`, contrapositive `lemma37_strict`): toroidal
  `ℓ^∞`-separation `≥ b^{-κ}` gives `κ`-separation and toroidal `κ`-separation (the intervals are half-open).
* Step 2, the general statement (`dgs_main`), and the bridge from our nets to `[DGS2, Defs. 2.1, 2.2, 3.1]`
  (`isTMSNet_of_isNet0`, `dgsNet_eq`).
* The instances (1)–(5) for every digital shift (`dgs_P`, `dgs_A`, `dgs_HL`, `dgs_S1`, `dgs_allm`), through integer
  `ℓ^∞` bounds (`sep_of_int`, `pigeon`).
* `rem:dgsfinite` (`dgsfinite_sep`, `frame3_net`, `dgs_family`) and `prop:linf` (`linf_dist`, `linf_mesh`).
-/

namespace Z3NetDGS

open Finset Matrix

/-! ## Proofs -/

namespace Proofs

section basic

variable {d : ℕ}

/-- The toroidal residue `cres` as a real number, for `-N < u < N`. -/
lemma cres_real (N : ℕ) (u : ℤ) (h1 : -(N : ℤ) < u) (h2 : u < N) :
    ((Z3NetF.cres N u : ℕ) : ℝ) = min |(u : ℝ)| ((N : ℝ) - |(u : ℝ)|) := by
  unfold Z3NetF.cres
  rcases le_or_gt 0 u with hu | hu
  · have e : u % (N : ℤ) = u := Int.emod_eq_of_lt hu h2
    rw [e]
    have hn : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu
    have hle : u.toNat ≤ N := by omega
    rw [Nat.cast_min, Nat.cast_sub hle]
    have : ((u.toNat : ℕ) : ℝ) = (u : ℝ) := by exact_mod_cast hn
    rw [this, abs_of_nonneg (by exact_mod_cast hu)]
  · have e : u % (N : ℤ) = u + N := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [e]
    have hn : (((u + N).toNat : ℕ) : ℤ) = u + N := Int.toNat_of_nonneg (by omega)
    have hle : (u + N).toNat ≤ N := by omega
    rw [Nat.cast_min, Nat.cast_sub hle]
    have : (((u + N).toNat : ℕ) : ℝ) = (u : ℝ) + N := by exact_mod_cast hn
    rw [this, abs_of_neg (by exact_mod_cast hu), min_comm]
    congr 1 <;> ring

/-- The toroidal coordinate distance of `X/N`, `Y/N` is `cres N (X - Y) / N`. -/
lemma torCoord_cres (N : ℕ) (hN : 0 < N) (X Y : ℕ) (hX : X < N) (hY : Y < N) :
    torCoord ((X : ℝ) / N) ((Y : ℝ) / N) = ((Z3NetF.cres N ((X : ℤ) - Y) : ℕ) : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cres_real N _ (by omega) (by omega)]
  unfold torCoord
  have e : (X : ℝ) / N - (Y : ℝ) / N = (((X : ℤ) - Y : ℤ) : ℝ) / N := by push_cast; ring
  rw [e, abs_div, abs_of_pos hN', ← min_div_div_right hN'.le]
  congr 1
  field_simp

/-- Two points of a shifted elementary interval of side `b^{-κ}` differ by less than `b^{-κ}` in every
coordinate (the intervals are half-open). -/
lemma shiftedInt_close {b κ : ℕ} (hb : 0 < b) {a e : Fin d → ℕ} {x y : Fin d → ℝ}
    (hx : x ∈ shiftedInt b (fun _ => κ) a e) (hy : y ∈ shiftedInt b (fun _ => κ) a e) (j : Fin d) :
    |x j - y j| < 1 / (b : ℝ) ^ κ := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ κ := by positivity
  obtain ⟨hx1, hx2⟩ := hx j
  obtain ⟨hy1, hy2⟩ := hy j
  have e : ((a j : ℝ) + ((b : ℝ) - e j) / b) / (b : ℝ) ^ κ =
      ((a j : ℝ) - (e j : ℝ) / b) / (b : ℝ) ^ κ + 1 / (b : ℝ) ^ κ := by
    field_simp; ring
  rw [e] at hx2 hy2
  rw [abs_lt]; constructor <;> linarith

/-- Two points of `[α, α + ℓ) mod 1`, `0 < ℓ ≤ 1`, have toroidal distance less than `ℓ`. -/
lemma modOne_close {α ℓ : ℝ} (hℓ1 : ℓ ≤ 1) {x y : ℝ}
    (hx : x ∈ modOne (Set.Ico α (α + ℓ))) (hy : y ∈ modOne (Set.Ico α (α + ℓ))) :
    torCoord x y < ℓ := by
  obtain ⟨hx0, hx1, z, hz1, hz2⟩ := hx
  obtain ⟨hy0, hy1, z', hz1', hz2'⟩ := hy
  have hd : |(x - y) + ((z : ℝ) - z')| < ℓ := by rw [abs_lt]; constructor <;> linarith
  unfold torCoord
  rcases lt_trichotomy (z - z') 0 with h | h | h
  · -- z - z' ≤ -1
    have h1 : z - z' ≤ -1 := by omega
    have h1' : ((z : ℝ) - z') ≤ -1 := by exact_mod_cast h1
    have h2 : z - z' = -1 := by
      by_contra hne
      have : z - z' ≤ -2 := by omega
      have : ((z : ℝ) - z') ≤ -2 := by exact_mod_cast this
      rw [abs_lt] at hd; linarith
    have h2' : ((z : ℝ) - z') = -1 := by exact_mod_cast h2
    rw [h2'] at hd
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    rw [abs_of_pos (by rw [abs_lt] at hd; linarith : (0 : ℝ) < x - y)]
    rw [abs_lt] at hd; linarith
  · have h' : ((z : ℝ) - z') = 0 := by exact_mod_cast h
    rw [h', add_zero] at hd
    exact lt_of_le_of_lt (min_le_left _ _) hd
  · have h2 : z - z' = 1 := by
      by_contra hne
      have : 2 ≤ z - z' := by omega
      have : (2 : ℝ) ≤ (z : ℝ) - z' := by exact_mod_cast this
      rw [abs_lt] at hd; linarith
    have h2' : ((z : ℝ) - z') = 1 := by exact_mod_cast h2
    rw [h2'] at hd
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    rw [abs_of_neg (by rw [abs_lt] at hd; linarith : x - y < 0)]
    rw [abs_lt] at hd; linarith

lemma shiftedIntTor_close {b κ : ℕ} (hb : 0 < b) {a e : Fin d → ℕ} {x y : Fin d → ℝ}
    (hx : x ∈ shiftedIntTor b (fun _ => κ) a e) (hy : y ∈ shiftedIntTor b (fun _ => κ) a e) (j : Fin d) :
    torCoord (x j) (y j) < 1 / (b : ℝ) ^ κ := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ κ := by positivity
  have e : ((a j : ℝ) + ((b : ℝ) - e j) / b) / (b : ℝ) ^ κ =
      ((a j : ℝ) - (e j : ℝ) / b) / (b : ℝ) ^ κ + 1 / (b : ℝ) ^ κ := by
    field_simp; ring
  have hx' := hx j
  have hy' := hy j
  simp only at hx' hy'
  rw [e] at hx' hy'
  have hℓ : 1 / (b : ℝ) ^ κ ≤ 1 := by
    rw [div_le_one hbk]; exact one_le_pow₀ hb1
  exact modOne_close hℓ hx' hy'

lemma torCoord_le_abs (a b : ℝ) : torCoord a b ≤ |a - b| := min_le_left _ _

/-- **`cor:dgs`, Step 1** (`[DGS2, Lemma 3.7]` with strict inequality): if any two distinct points of
`P` have toroidal `ℓ^∞`-distance at least `b^{-κ}` (in some coordinate), then `P` is `κ`-separated and
toroidally `κ`-separated in base `b`. -/
theorem lemma37 (b κ : ℕ) (hb : 2 ≤ b) (P : Finset (Fin d → ℝ))
    (h : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ∃ j, 1 / (b : ℝ) ^ κ ≤ torCoord (x j) (y j)) :
    IsKSep b κ P ∧ IsKSepTor b κ P := by
  constructor
  · intro a e _ _ x ⟨hxP, hxJ⟩ y ⟨hyP, hyJ⟩
    by_contra hne
    obtain ⟨j, hj⟩ := h x hxP y hyP hne
    have := shiftedInt_close (by omega) hxJ hyJ j
    linarith [torCoord_le_abs (x j) (y j)]
  · intro a e _ _ x ⟨hxP, hxJ⟩ y ⟨hyP, hyJ⟩
    by_contra hne
    obtain ⟨j, hj⟩ := h x hxP y hyP hne
    have := shiftedIntTor_close (by omega) hxJ hyJ j
    linarith

end basic

section strict

variable {d : ℕ}

lemma torCoord_nonneg {a b : ℝ} (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) : 0 ≤ torCoord a b := by
  unfold torCoord
  refine le_min (abs_nonneg _) ?_
  have : |a - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  linarith

lemma iSup_lt_of_forall {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → ℝ} {L : ℝ} (h : ∀ i, f i < L) :
    (⨆ i, f i) < L := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← hi]; exact h i

/-- **`cor:dgs`, Step 1, contrapositive form** (`[DGS2, Lemma 3.7]` sharpened to a strict inequality):
a finite `P ⊂ [0,1)^d` that is not `κ`-separated has `q_∞(P) < 1/(2 b^κ)`; one that is not toroidally
`κ`-separated has `q_{∞,T}(P) < 1/(2 b^κ)`. -/
theorem lemma37_strict (b κ : ℕ) (hb : 2 ≤ b) (P : Finset (Fin d → ℝ))
    (hP : ∀ x ∈ P, ∀ j, 0 ≤ x j ∧ x j < 1) :
    (¬ IsKSep b κ P → sepRad distInf P < 1 / (2 * (b : ℝ) ^ κ)) ∧
      (¬ IsKSepTor b κ P → sepRad torDistInf P < 1 / (2 * (b : ℝ) ^ κ)) := by
  have hb0 : (0 : ℝ) < (b : ℝ) ^ κ := by positivity
  constructor
  · intro hns
    unfold IsKSep IsSep at hns
    push Not at hns
    obtain ⟨a, e, -, -, hns⟩ := hns
    obtain ⟨x, ⟨hxP, hxJ⟩, y, ⟨hyP, hyJ⟩, hne⟩ := hns
    have hd : Nonempty (Fin d) := by
      by_contra h0
      rw [not_nonempty_iff] at h0
      exact hne (funext fun j => (IsEmpty.false j).elim)
    have hlt : distInf x y < 1 / (b : ℝ) ^ κ :=
      iSup_lt_of_forall fun j => shiftedInt_close (by omega) hxJ hyJ j
    have hle : sepRad distInf P ≤ distInf x y / 2 := by
      refine ciInf_le ⟨0, ?_⟩ (⟨(x, y), hxP, hyP, hne⟩ : {xy : (Fin d → ℝ) × (Fin d → ℝ) //
        xy.1 ∈ P ∧ xy.2 ∈ P ∧ xy.1 ≠ xy.2})
      rintro _ ⟨⟨⟨x', y'⟩, hx', hy', -⟩, rfl⟩
      have : 0 ≤ distInf x' y' := by
        unfold distInf
        exact le_trans (abs_nonneg (x' (Classical.arbitrary _) - y' (Classical.arbitrary _)))
          (le_ciSup (f := fun j => |x' j - y' j|) (Set.finite_range _).bddAbove (Classical.arbitrary _))
      positivity
    calc sepRad distInf P ≤ distInf x y / 2 := hle
      _ < (1 / (b : ℝ) ^ κ) / 2 := by linarith
      _ = 1 / (2 * (b : ℝ) ^ κ) := by field_simp
  · intro hns
    unfold IsKSepTor IsSepTor at hns
    push Not at hns
    obtain ⟨a, e, -, -, hns⟩ := hns
    obtain ⟨x, ⟨hxP, hxJ⟩, y, ⟨hyP, hyJ⟩, hne⟩ := hns
    have hd : Nonempty (Fin d) := by
      by_contra h0
      rw [not_nonempty_iff] at h0
      exact hne (funext fun j => (IsEmpty.false j).elim)
    have hlt : torDistInf x y < 1 / (b : ℝ) ^ κ :=
      iSup_lt_of_forall fun j => shiftedIntTor_close (by omega) hxJ hyJ j
    have hle : sepRad torDistInf P ≤ torDistInf x y / 2 := by
      refine ciInf_le ⟨0, ?_⟩ (⟨(x, y), hxP, hyP, hne⟩ : {xy : (Fin d → ℝ) × (Fin d → ℝ) //
        xy.1 ∈ P ∧ xy.2 ∈ P ∧ xy.1 ≠ xy.2})
      rintro _ ⟨⟨⟨x', y'⟩, hx', hy', -⟩, rfl⟩
      have : 0 ≤ torDistInf x' y' := by
        unfold torDistInf
        exact le_trans (torCoord_nonneg (hP x' hx' (Classical.arbitrary _)) (hP y' hy' (Classical.arbitrary _)))
          (le_ciSup (f := fun j => torCoord (x' j) (y' j)) (Set.finite_range _).bddAbove (Classical.arbitrary _))
      positivity
    calc sepRad torDistInf P ≤ torDistInf x y / 2 := hle
      _ < (1 / (b : ℝ) ^ κ) / 2 := by linarith
      _ = 1 / (2 * (b : ℝ) ^ κ) := by field_simp

end strict

section points

variable {d m q : ℕ} [NeZero q]

lemma ptReal_mem (X : (Fin m → ZMod q) → Fin d → ℕ) (hX : ∀ v c, X v c < q ^ m) (v : Fin m → ZMod q)
    (c : Fin d) : 0 ≤ ptReal q X v c ∧ ptReal q X v c < 1 := by
  have hq : (0 : ℝ) < (q : ℝ) ^ m := by have := Nat.pos_of_neZero q; positivity
  unfold ptReal
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hq]; exact_mod_cast hX v c

lemma ptSet_mem (X : (Fin m → ZMod q) → Fin d → ℕ) (hX : ∀ v c, X v c < q ^ m) :
    ∀ x ∈ ptSet q X, ∀ j, 0 ≤ x j ∧ x j < 1 := by
  intro x hx j
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ptReal_mem X hX v j

/-- Integer `ℓ^∞` separation ⇒ DGS `κ`-separation (both forms), for points `X_v / q^m`. -/
theorem sep_of_int (κ : ℕ) (hκ : κ ≤ m) (hq : 2 ≤ q) (X : (Fin m → ZMod q) → Fin d → ℕ)
    (hX : ∀ v c, X v c < q ^ m)
    (h : ∀ v w, v ≠ w → ∃ c, q ^ (m - κ) ≤ Z3NetF.cres (q ^ m) ((X v c : ℤ) - (X w c : ℤ))) :
    IsKSep q κ (ptSet q X) ∧ IsKSepTor q κ (ptSet q X) := by
  apply lemma37 q κ hq
  intro x hx y hy hxy
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := fun h => hxy (h ▸ rfl)
  obtain ⟨c, hc⟩ := h v w hvw
  refine ⟨c, ?_⟩
  have hqm : 0 < q ^ m := Nat.pos_of_ne_zero (by positivity)
  unfold ptReal
  have e : ((q ^ m : ℕ) : ℝ) = (q : ℝ) ^ m := by push_cast; ring
  rw [← e, torCoord_cres (q ^ m) hqm _ _ (hX v c) (hX w c), e]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hc' : ((q ^ (m - κ) : ℕ) : ℝ) ≤ ((Z3NetF.cres (q ^ m) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) := by
    exact_mod_cast hc
  have e2 : 1 / (q : ℝ) ^ κ = ((q ^ (m - κ) : ℕ) : ℝ) / (q : ℝ) ^ m := by
    push_cast
    rw [show m = (m - κ) + κ by omega, pow_add]
    field_simp
    simp
  rw [e2]
  exact div_le_div_of_nonneg_right hc' (by positivity)

/-- A box of shape `c` (`c ≤ m`) in real coordinates. -/
lemma box_iff (c a X : ℕ) (hc : c ≤ m) :
    ((a : ℝ) / (q : ℝ) ^ c ≤ (X : ℝ) / (q : ℝ) ^ m ∧ (X : ℝ) / (q : ℝ) ^ m < ((a : ℝ) + 1) / (q : ℝ) ^ c) ↔
      X / q ^ (m - c) = a := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hP : 0 < q ^ (m - c) := pow_pos hq _
  have hqc : (0 : ℝ) < (q : ℝ) ^ c := by positivity
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  have e : (q : ℝ) ^ m = ((q ^ (m - c) : ℕ) : ℝ) * (q : ℝ) ^ c := by
    push_cast; rw [← pow_add]; congr 1; omega
  rw [div_le_div_iff₀ hqc hqm, div_lt_div_iff₀ hqm hqc, e]
  have hPr : (0 : ℝ) < ((q ^ (m - c) : ℕ) : ℝ) := by exact_mod_cast hP
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (a : ℝ) * (q ^ (m - c) : ℕ) ≤ X := by nlinarith
    have h2' : (X : ℝ) < ((a : ℝ) + 1) * (q ^ (m - c) : ℕ) := by nlinarith
    have h1n : a * q ^ (m - c) ≤ X := by exact_mod_cast h1'
    have h2n : X < (a + 1) * q ^ (m - c) := by exact_mod_cast h2'
    exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hP).mpr h2n))
      ((Nat.le_div_iff_mul_le hP).mpr h1n)
  · intro h
    have h1n : a * q ^ (m - c) ≤ X := by rw [← h]; exact Nat.div_mul_le_self X _
    have h2n : X < (a + 1) * q ^ (m - c) := by rw [← h]; exact (Nat.div_lt_iff_lt_mul hP).mp (Nat.lt_succ_self _)
    have h1' : (a : ℝ) * (q ^ (m - c) : ℕ) ≤ X := by exact_mod_cast h1n
    have h2' : (X : ℝ) < ((a : ℝ) + 1) * (q ^ (m - c) : ℕ) := by exact_mod_cast h2n
    constructor <;> nlinarith

end points

section bridge

variable {d m q : ℕ} [NeZero q]

lemma ptReal_injective (hd : 1 ≤ d) (X : (Fin m → ZMod q) → Fin d → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (h : Z3NetF.IsNet0 d q m X) : Function.Injective (ptReal q X) := by
  intro v w hvw
  have hq : (0 : ℝ) < (q : ℝ) ^ m := by have := Nat.pos_of_neZero q; positivity
  have hX' : ∀ c, X v c = X w c := by
    intro c
    have := congrFun hvw c
    unfold ptReal at this
    rw [div_left_inj' hq.ne'] at this
    exact_mod_cast this
  set c0 : Fin d := ⟨0, hd⟩
  let sh : Fin d → ℕ := fun c => if c = c0 then m else 0
  have hsh : ∑ c, sh c = m := by simp [sh]
  have hshm : ∀ c, sh c ≤ m := fun c => by simp only [sh]; split_ifs <;> omega
  obtain ⟨u, -, hu⟩ := h sh hsh (fun c => X v c / q ^ (m - sh c)) (fun c => by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (Nat.pos_of_neZero q) _), ← pow_add,
      show sh c + (m - sh c) = m by have := hshm c; omega]
    exact hX v c)
  have h1 := hu v (fun c => rfl)
  have h2 := hu w (fun c => by rw [hX' c])
  rw [h1, h2]

/-- Our `(0,m,s)`-nets (`Z3NetF.IsNet0`, integer points at scale `q^m`) are `(0,m,s)`-nets in base `q`
in the sense of `[DGS2, Def. 3.1]` (as point sets in `[0,1)^s`). -/
theorem isTMSNet_of_isNet0 (hd : 1 ≤ d) (X : (Fin m → ZMod q) → Fin d → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (h : Z3NetF.IsNet0 d q m X) : IsTMSNet q 0 m (ptSet q X) := by
  refine ⟨ptSet_mem X hX, ?_, ?_⟩
  · unfold ptSet
    rw [Finset.card_image_of_injective _ (ptReal_injective hd X hX h), Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · intro c hc a ha
    rw [Nat.sub_zero] at hc
    have hcm : ∀ j, c j ≤ m := fun j => by
      rw [← hc]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    obtain ⟨v0, hv0, huniq⟩ := h c hc a ha
    have hset : ((ptSet q X : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) ∩ elemInt q c a = {ptReal q X v0} := by
      ext y
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy, hyJ⟩
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hy
        have hv : ∀ j, X v j / q ^ (m - c j) = a j := fun j => (box_iff (c j) (a j) (X v j) (hcm j)).mp (hyJ j)
        rw [huniq v hv]
      · rintro rfl
        exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
          fun j => (box_iff (c j) (a j) (X v0 j) (hcm j)).mpr (hv0 j)⟩
    rw [hset, Set.ncard_singleton, pow_zero]

end bridge

section main

/-- `torCoord a b ≤ 1/2`. -/
lemma torCoord_le_half (a b : ℝ) : torCoord a b ≤ 1 / 2 := by
  unfold torCoord
  rcases le_total |a - b| (1 / 2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

/-- **`cor:dgs`, Step 2** (the general statement): `(0,m,s)`-nets in base `q` on an infinite `I ⊆ ℕ` whose
toroidal minimum distance is at least `c q^{-m/s}` are `κ_m`-separated and toroidally `κ_m`-separated,
`κ_m = ⌈m/s + log_q(√s/c)⌉ ≤ m/s + log_q(√s/c) + 1` (for `m ≥ 1`; then `κ_m ≥ 1`), so they form a
well-separated and toroidally well-separated family on `I` in the sense of `[DGS2, Def. 3.8]`. -/
theorem dgs_main (s q : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) (I : Set ℕ) (hI : I.Infinite)
    (P : ℕ → Finset (Fin s → ℝ)) (c : ℝ) (hc : 0 < c)
    (hnet : ∀ m ∈ I, IsTMSNet q 0 m (P m))
    (hδ : ∀ m ∈ I, ∀ x ∈ P m, ∀ y ∈ P m, x ≠ y → c * (q : ℝ) ^ (-((m : ℝ) / s)) ≤ torDist2 x y) :
    (∀ m ∈ I, IsKSep q (kappaM s q c m) (P m) ∧ IsKSepTor q (kappaM s q c m) (P m)) ∧
    (∀ m ∈ I, 1 ≤ m → 1 ≤ ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℤ) = ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℝ) ≤ (m : ℝ) / s + Real.logb q (Real.sqrt s / c) + 1) ∧
    WellSepFamily q 0 s I P ∧ WellSepFamilyTor q 0 s I P := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hss : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs0
  -- `q^{-κ_m} ≤ (c / √s) q^{-m/s}`
  have hkey : ∀ m : ℕ, 1 / (q : ℝ) ^ kappaM s q c m ≤ c / Real.sqrt s * (q : ℝ) ^ (-((m : ℝ) / s)) := by
    intro m
    set x : ℝ := (m : ℝ) / s + Real.logb q (Real.sqrt s / c)
    have hx : x ≤ (kappaM s q c m : ℝ) := by
      unfold kappaM
      have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
      have h2 : (⌈x⌉ : ℤ) ≤ ((⌈x⌉.toNat : ℕ) : ℤ) := Int.self_le_toNat _
      have h2' : ((⌈x⌉ : ℤ) : ℝ) ≤ (((⌈x⌉.toNat : ℕ) : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      linarith
    have hpow : (q : ℝ) ^ x ≤ (q : ℝ) ^ (kappaM s q c m) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hq1.le hx
    have hqx : (q : ℝ) ^ x = (q : ℝ) ^ ((m : ℝ) / s) * (Real.sqrt s / c) := by
      unfold x
      rw [Real.rpow_add hq0, Real.rpow_logb hq0 hq1.ne' (by positivity)]
    have hpos : 0 < (q : ℝ) ^ x := Real.rpow_pos_of_pos hq0 _
    rw [Real.rpow_neg hq0.le, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = c / Real.sqrt s * ((q : ℝ) ^ ((m : ℝ) / s))⁻¹ * (q : ℝ) ^ x := by
          rw [hqx]; field_simp
      _ ≤ c / Real.sqrt s * ((q : ℝ) ^ ((m : ℝ) / s))⁻¹ * (q : ℝ) ^ (kappaM s q c m) := by
          gcongr
  have hsepm : ∀ m ∈ I, IsKSep q (kappaM s q c m) (P m) ∧ IsKSepTor q (kappaM s q c m) (P m) := by
    intro m hm
    apply lemma37 q _ hq (P m)
    intro x hx y hy hxy
    have hd := hδ m hm x hx y hy hxy
    -- some coordinate carries `≥ δ/√s`
    by_contra hall
    push Not at hall
    have hlt : ∀ j, torCoord (x j) (y j) ^ 2 < (c / Real.sqrt s * (q : ℝ) ^ (-((m : ℝ) / s))) ^ 2 := by
      intro j
      have h0 := torCoord_nonneg ((hnet m hm).1 x hx j) ((hnet m hm).1 y hy j)
      have := lt_of_lt_of_le (hall j) (hkey m)
      exact pow_lt_pow_left₀ this h0 (by norm_num)
    have hsum : ∑ j, torCoord (x j) (y j) ^ 2 < (c * (q : ℝ) ^ (-((m : ℝ) / s))) ^ 2 := by
      calc ∑ j, torCoord (x j) (y j) ^ 2 < ∑ _j : Fin s, (c / Real.sqrt s * (q : ℝ) ^ (-((m : ℝ) / s))) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun j _ => hlt j
        _ = (c * (q : ℝ) ^ (-((m : ℝ) / s))) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, div_pow,
              Real.sq_sqrt hs0.le]
            field_simp
    have hδ' : (c * (q : ℝ) ^ (-((m : ℝ) / s))) ^ 2 ≤ ∑ j, torCoord (x j) (y j) ^ 2 := by
      have h0 : 0 ≤ c * (q : ℝ) ^ (-((m : ℝ) / s)) := by positivity
      have := pow_le_pow_left₀ h0 hd 2
      unfold torDist2 at this
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at this
    linarith
  have hκ1 : ∀ m ∈ I, 1 ≤ m → 1 ≤ ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ := by
    intro m hm hm1
    obtain ⟨hmem, hcard, -⟩ := hnet m hm
    have h2 : 1 < (P m).card := by
      rw [hcard]; exact Nat.one_lt_pow (by omega) (by omega)
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
    have hd := hδ m hm x hx y hy hxy
    have hup : torDist2 x y ≤ Real.sqrt s / 2 := by
      unfold torDist2
      rw [show Real.sqrt s / 2 = Real.sqrt (s / 4) by
        rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      apply Real.sqrt_le_sqrt
      calc ∑ j, torCoord (x j) (y j) ^ 2 ≤ ∑ _j : Fin s, (1 / 2 : ℝ) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact pow_le_pow_left₀ (torCoord_nonneg (hmem x hx j) (hmem y hy j)) (torCoord_le_half _ _) 2
        _ = s / 4 := by simp; ring
    have hlt : c * (q : ℝ) ^ (-((m : ℝ) / s)) < Real.sqrt s := by linarith
    rw [Int.one_le_ceil_iff]
    -- `0 < m/s + log_q(√s/c)` iff `c q^{-m/s} < √s`
    have hpos : 0 < Real.sqrt s / c * (q : ℝ) ^ ((m : ℝ) / s) := by positivity
    have hgt : 1 < Real.sqrt s / c * (q : ℝ) ^ ((m : ℝ) / s) := by
      rw [Real.rpow_neg hq0.le] at hlt
      have hqm : 0 < (q : ℝ) ^ ((m : ℝ) / s) := by positivity
      rw [mul_inv_lt_iff₀ hqm] at hlt
      rw [div_mul_eq_mul_div, one_lt_div hc]
      linarith
    have := Real.logb_pos hq1 hgt
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow hq0 hq1.ne'] at this
    linarith
  have hbnd : ∀ m ∈ I, 1 ≤ m → 1 ≤ ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℤ) = ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℝ) ≤ (m : ℝ) / s + Real.logb q (Real.sqrt s / c) + 1 := by
    intro m hm hm1
    have h1 := hκ1 m hm hm1
    have e : (kappaM s q c m : ℤ) = ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ := by
      unfold kappaM; exact Int.toNat_of_nonneg (by omega)
    refine ⟨h1, e, ?_⟩
    have : (kappaM s q c m : ℝ) = ((⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ : ℤ) : ℝ) := by
      rw [← e]; push_cast; rfl
    rw [this]
    exact (Int.ceil_lt_add_one _).le
  have hC : ∀ m ∈ I, (kappaM s q c m : ℝ) ≤ (m : ℝ) / s +
      max (Real.logb q (Real.sqrt s / c) + 1) (kappaM s q c 0 : ℝ) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp
    · have := (hbnd m hm h0).2.2
      have := le_max_left (Real.logb q (Real.sqrt s / c) + 1) (kappaM s q c 0 : ℝ)
      linarith
  exact ⟨hsepm, hbnd,
    ⟨hI, hnet, fun m => kappaM s q c m, _, fun m hm => ⟨(hsepm m hm).1, hC m hm⟩⟩,
    ⟨hI, hnet, fun m => kappaM s q c m, _, fun m hm => ⟨(hsepm m hm).2, hC m hm⟩⟩⟩

end main

section dgsdef

variable {d : ℕ}

/-- Every digit vector is `n⃗` for some `n < b^m` ([DGS2, Def. 2.1]: `n ↦ n⃗` is onto). -/
lemma dgsVec_surj (b m : ℕ) (hb : 2 ≤ b) (v : Fin m → ZMod b) :
    ∃ n < b ^ m, dgsVec b m n = v := by
  have : NeZero b := ⟨by omega⟩
  let g : ℕ → ℕ := fun t => if h : t < m then (v ⟨t, h⟩).val else 0
  have hg : ∀ t, g t < b := fun t => by
    simp only [g]; split_ifs
    · exact ZMod.val_lt _
    · omega
  refine ⟨∑ t ∈ Finset.range m, g t * b ^ t, Z3Net.Two.sum_digits_lt b (by omega) g hg m, ?_⟩
  funext i
  unfold dgsVec
  rw [Z3Net.Two.digit_extract b (by omega) m g hg i, if_pos i.isLt]
  simp [g, i.isLt]

/-- **[DGS2, Defs. 2.1, 2.2]**: for a prime (or any) base `b ≥ 2`, the digitally shifted digital net
`Q(F_1, …, F_d) ⊕ δ` of [DGS2] is the point set of `digPointShift b m F δ` (`def:dshift`). -/
theorem dgsNet_eq (b m : ℕ) [NeZero b] (hb : 2 ≤ b) (F : Fin d → Matrix (Fin m) (Fin m) (ZMod b))
    (δ : Fin d → Fin m → ZMod b) :
    dgsNet b m F δ = ptSet b (Z3NetF.digPointShift b m F δ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hpt : ∀ n, dgsPoint b m F δ n = ptReal b (Z3NetF.digPointShift b m F δ) (dgsVec b m n) := by
    intro n
    funext j
    unfold dgsPoint ptReal Z3NetF.digPointShift
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [mul_div_assoc, Pi.add_apply]
    have hpow : (b : ℝ) ^ m = (b : ℝ) ^ (m - 1 - (i : ℕ)) * (b : ℝ) ^ ((i : ℕ) + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    field_simp
  unfold dgsNet ptSet
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, -, rfl⟩
    exact ⟨dgsVec b m n, (hpt n).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨n, hn, hv⟩ := dgsVec_surj b m hb v
    exact ⟨n, hn, by rw [hpt, hv]⟩

end dgsdef

section finite

variable {d : ℕ}

lemma cres_pos (N : ℕ) (u : ℤ) (hu : u % (N : ℤ) ≠ 0) (hN : 0 < N) : 1 ≤ Z3NetF.cres N u := by
  unfold Z3NetF.cres
  have h0 := Int.emod_nonneg u (show (N : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos u (show (0 : ℤ) < N by omega)
  omega

/-- **`rem:dgsfinite`**: a `(0,m,s)`-net in base `q` (`[DGS2, Def. 3.1]`, `s ≥ 1`) on the grid `q^{-m} ℤ^s` is
`m`-separated and toroidally `m`-separated: the boxes of shape `(m, 0, …, 0)` hold one point each, so the
first coordinates are distinct multiples of `q^{-m}`, at toroidal distance `≥ q^{-m}`. -/
theorem dgsfinite_sep (q m : ℕ) (hd : 1 ≤ d) (hq : 2 ≤ q) (Q : Finset (Fin d → ℝ))
    (hgrid : ∀ x ∈ Q, ∀ j, ∃ n : ℕ, x j = (n : ℝ) / (q : ℝ) ^ m) (hQ : IsTMSNet q 0 m Q) :
    IsKSep q m Q ∧ IsKSepTor q m Q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  apply lemma37 q m hq Q
  intro x hx y hy hxy
  set j0 : Fin d := ⟨0, hd⟩
  refine ⟨j0, ?_⟩
  obtain ⟨n, hn⟩ := hgrid x hx j0
  obtain ⟨n', hn'⟩ := hgrid y hy j0
  have hlt : ∀ z ∈ Q, ∀ k : ℕ, z j0 = (k : ℝ) / (q : ℝ) ^ m → k < q ^ m := by
    intro z hz k hk
    have := (hQ.1 z hz j0).2
    rw [hk, div_lt_one hqm] at this
    exact_mod_cast this
  have hnl := hlt x hx n hn
  have hnl' := hlt y hy n' hn'
  -- the two points lie in different boxes of shape `(m, 0, …, 0)`
  have hne : n ≠ n' := by
    intro hnn
    subst hnn
    let c : Fin d → ℕ := fun j => if j = j0 then m else 0
    let a : Fin d → ℕ := fun j => if j = j0 then n else 0
    have hc : ∑ j, c j = m - 0 := by simp [c]
    have ha : ∀ j, a j < q ^ c j := fun j => by
      simp only [a, c]; split_ifs
      · exact hnl
      · simp
    have h1 := hQ.2.2 c hc a ha
    have hmem : ∀ z ∈ Q, z j0 = (n : ℝ) / (q : ℝ) ^ m → z ∈ elemInt q c a := by
      intro z hz hzj j
      simp only [a, c]
      by_cases hj : j = j0
      · subst hj; simp only [if_true]; rw [hzj]
        constructor
        · exact le_refl _
        · exact div_lt_div_of_pos_right (by linarith) hqm
      · simp only [hj, if_false, pow_zero, div_one, Nat.cast_zero, zero_add]
        exact (hQ.1 z hz j)
    obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp (by rw [h1, pow_zero])
    have hxz : x ∈ ((Q : Set (Fin d → ℝ)) ∩ elemInt q c a) := ⟨hx, hmem x hx hn⟩
    have hyz : y ∈ ((Q : Set (Fin d → ℝ)) ∩ elemInt q c a) := ⟨hy, hmem y hy hn'⟩
    rw [hz] at hxz hyz
    exact hxy (hxz.trans hyz.symm)
  rw [hn, hn']
  have e : ((q ^ m : ℕ) : ℝ) = (q : ℝ) ^ m := by push_cast; ring
  rw [← e, torCoord_cres (q ^ m) (by positivity) n n' (by exact_mod_cast hnl) (by exact_mod_cast hnl'), e]
  rw [div_le_div_iff_of_pos_right hqm]
  have hu : ((n : ℤ) - n') % ((q ^ m : ℕ) : ℤ) ≠ 0 := by
    intro h0
    have hd' := Int.emod_emod_of_dvd ((n : ℤ) - n') (dvd_refl ((q ^ m : ℕ) : ℤ))
    have : ((q ^ m : ℕ) : ℤ) ∣ (n : ℤ) - n' := Int.dvd_of_emod_eq_zero h0
    have hb : |(n : ℤ) - n'| < ((q ^ m : ℕ) : ℤ) := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd this hb
    omega
  exact_mod_cast cres_pos (q ^ m) _ hu (by positivity)

/-- The frame of the places `∞, 0, 1` (`lem:Ts`): every box minor is `±1`, so it is a digital
`(0,m,3)`-net over `ℤ/qℤ` for every `q ≥ 1` and every `m` (`rem:dgsfinite`). -/
theorem frame3_net (q m : ℕ) [NeZero q] :
    Z3NetF.IsNet0 3 q m (Z3NetF.digPoint q m (Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1])) := by
  rw [Z3NetF.Proofs.nie_zmod]
  intro dd hdd
  rcases Z3NetF.frame_minor (R := ZMod q) (0 : Fin 3) ![0, 0, 1] dd hdd with h | h <;>
  · rw [h]
    simp only [Fin.prod_univ_three, Fin.isValue]
    simp [Fin.lt_def]

end finite

section instances

/-- `Z3Net.IsNet0` (dimension three) is `Z3NetF.IsNet0 3`. -/
lemma isNet0_three {q m : ℕ} (X : (Fin m → ZMod q) → Fin 3 → ℕ) :
    Z3Net.IsNet0 q m X ↔ Z3NetF.IsNet0 3 q m X := by
  unfold Z3Net.IsNet0 Z3NetF.IsNet0
  simp only [Fin.sum_univ_three]

/-- Pigeonhole: if `s E² ≤ ∑_c f_c²` then some `f_c ≥ E`. -/
lemma pigeon {s : ℕ} (hs : 1 ≤ s) (f : Fin s → ℕ) (E : ℕ) (h : s * E ^ 2 ≤ ∑ c, f c ^ 2) :
    ∃ c, E ≤ f c := by
  by_contra hall
  push Not at hall
  have hlt : ∑ c, f c ^ 2 < ∑ _c : Fin s, E ^ 2 :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ =>
      Nat.pow_lt_pow_left (hall c) (by norm_num)
  simp at hlt
  omega

lemma P_shift_net (q k : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : 1 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) :
    Z3NetF.IsNet0 3 q (3 * k) (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) := by
  apply Z3NetF.Proofs.digPointShift_net
  exact (isNet0_three _).mp (Z3Net.P_net q k hq hk)

/-- **`cor:dgs`(1)** for every digital shift: `𝒫_{k,q} ⊕ τ` (`thm:main`, every `q ≥ 4`, `k ≥ 2`) is a
`(0,3k,3)`-net in base `q` and `(k+1)`-separated and toroidally `(k+1)`-separated. -/
theorem dgs_P (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) :
    IsTMSNet q 0 (3 * k) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ∧
      IsKSep q (k + 1) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ∧
      IsKSepTor q (k + 1) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) := by
  refine ⟨isTMSNet_of_isNet0 (by norm_num) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
    (P_shift_net q k (by omega) (by omega) τ), ?_⟩
  apply sep_of_int (k + 1) (by omega) (by omega) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
  intro v w hvw
  obtain ⟨c, hc⟩ := (Z3Net.Sep.P_sep_shift_main q k hq hk τ v w hvw).2
  refine ⟨c, ?_⟩
  have e : 3 * k - (k + 1) = 2 * k - 1 := by omega
  rw [e]
  have hq3 : (1 : ℤ) ≤ (q : ℤ) - 3 := by have : (4 : ℤ) ≤ q := by exact_mod_cast hq
                                         linarith
  have hpos : (0 : ℤ) ≤ (q : ℤ) ^ (2 * k - 1) := by positivity
  have : ((q ^ (2 * k - 1) : ℕ) : ℤ) ≤ ((Z3NetF.cres (q ^ (3 * k)) ((Z3NetF.digPointShift q (3 * k)
      (PGenZ q k) τ v c : ℤ) - (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ w c : ℤ)) : ℕ) : ℤ) := by
    push_cast
    refine le_trans ?_ hc
    nlinarith
  exact_mod_cast this

/-- **`cor:dgs`(2)** for every digital shift: the nets of `thm:A`(2) (`q ≥ 5a*_s + 4`, every `k ≥ 1`) are
`(0,sk,s)`-nets in base `q` and `(k+1)`-separated and toroidally `(k+1)`-separated. -/
theorem dgs_A (s q k : ℕ) [NeZero s] [NeZero q] (hs : 3 ≤ s) (hq : Z3NetA.AdmBase s q)
    (hqa : 5 * Z3NetA.aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) :
    IsTMSNet q 0 (s * k) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) ∧
      IsKSep q (k + 1) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) ∧
      IsKSepTor q (k + 1) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) := by
  refine ⟨isTMSNet_of_isNet0 (by omega) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
    (Z3NetA.Proofs.A_net_shift_core s q k hs hq τ), ?_⟩
  have hsk : k + 1 ≤ s * k := by nlinarith
  apply sep_of_int (k + 1) hsk (hq.1) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
  intro v w hvw
  have hZ := Z3NetA.Proofs.A_sep_shift_core s q k hs hq hqa hk τ v w hvw
  set X := Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ
  apply pigeon (by omega) (fun c => Z3NetF.cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)))
  -- `(q - a*)² ≥ s`
  have hqs : s ≤ q + 1 := by
    obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by have := hq.1; omega)
    have := hq.2 p hp hpq
    have := Nat.le_of_dvd (by have := hq.1; omega) hpq
    omega
  set a := Z3NetA.aStar s
  have hqaZ : (5 : ℤ) * a + 4 ≤ q := by exact_mod_cast hqa
  have hsZ : (s : ℤ) ≤ q + 1 := by exact_mod_cast hqs
  have hs3 : (3 : ℤ) ≤ s := by exact_mod_cast hs
  have hsq : (s : ℤ) ≤ ((q : ℤ) - a) ^ 2 := by nlinarith
  have e : (q : ℤ) ^ (2 * (s * k - k)) = (q : ℤ) ^ 2 * ((q ^ (s * k - (k + 1)) : ℕ) : ℤ) ^ 2 := by
    push_cast; rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [e] at hZ
  have hq2 : (0 : ℤ) < (q : ℤ) ^ 2 := by have := hq.1; positivity
  have h2 : ((q ^ (s * k - (k + 1)) : ℕ) : ℤ) ^ 2 * ((q : ℤ) - a) ^ 2 ≤
      (Z3NetF.torusDist2 (q ^ (s * k)) (X v) (X w) : ℤ) := by
    rw [mul_assoc] at hZ
    exact le_of_mul_le_mul_left hZ hq2
  have h3 : (s : ℤ) * ((q ^ (s * k - (k + 1)) : ℕ) : ℤ) ^ 2 ≤
      (Z3NetF.torusDist2 (q ^ (s * k)) (X v) (X w) : ℤ) := by
    have h0 : (0 : ℤ) ≤ ((q ^ (s * k - (k + 1)) : ℕ) : ℤ) ^ 2 := by positivity
    nlinarith
  unfold Z3NetF.torusDist2 at h3
  exact_mod_cast h3

end instances

section linf

lemma torCoord_le_torDistInf {d : ℕ} (x y : Fin d → ℝ) (j : Fin d) :
    torCoord (x j) (y j) ≤ torDistInf x y :=
  le_ciSup (f := fun j => torCoord (x j) (y j)) (Set.finite_range _).bddAbove j

lemma torDistInf_le_distInf {d : ℕ} (x y : Fin d → ℝ) : torDistInf x y ≤ distInf x y := by
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · simp [torDistInf, distInf]
  · exact ciSup_mono (Set.finite_range _).bddAbove fun j => torCoord_le_abs _ _

/-- **`prop:linf`**, the distance: any two distinct points of `𝒫_{k,q} ⊕ τ` (`q ≥ 4`, `k ≥ 2`, every
digital shift) have toroidal `ℓ^∞`-distance at least `(1 - 3/q) q^{-k}`. -/
theorem linf_dist (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - 3 / (q : ℝ)) / (q : ℝ) ^ k ≤
      torDistInf (ptReal q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) v)
        (ptReal q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) w) := by
  obtain ⟨c, hc⟩ := (Z3Net.Sep.P_sep_shift_main q k hq hk τ v w hvw).2
  refine le_trans ?_ (torCoord_le_torDistInf _ _ c)
  set X := Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqm : 0 < q ^ (3 * k) := pow_pos (by omega) _
  unfold ptReal
  have e : ((q ^ (3 * k) : ℕ) : ℝ) = (q : ℝ) ^ (3 * k) := by push_cast; ring
  rw [← e, torCoord_cres (q ^ (3 * k)) hqm _ _ (Z3NetF.Proofs.digPointShift_lt _ τ v c)
    (Z3NetF.Proofs.digPointShift_lt _ τ w c), e]
  have hc' : ((q : ℝ) - 3) * (q : ℝ) ^ (2 * k - 1) ≤
      ((Z3NetF.cres (q ^ (3 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hc
    push_cast at this
    exact this
  have hpow : (q : ℝ) ^ (3 * k) = (q : ℝ) ^ (2 * k - 1) * ((q : ℝ) * (q : ℝ) ^ k) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [le_div_iff₀ (by positivity), hpow]
  calc (1 - 3 / (q : ℝ)) / (q : ℝ) ^ k * ((q : ℝ) ^ (2 * k - 1) * ((q : ℝ) * (q : ℝ) ^ k))
      = ((q : ℝ) - 3) * (q : ℝ) ^ (2 * k - 1) := by field_simp
    _ ≤ _ := hc'

/-- One point in every cell: every `x ∈ [0,1]^3` is within `ℓ^∞`-distance `q^{-k}` of a point. -/
lemma linf_cover (q k : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : 1 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (x : Fin 3 → ℝ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    ∃ v, distInf x (ptReal q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) v) ≤ 1 / (q : ℝ) ^ k := by
  set X := Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hqkn : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  let a : Fin 3 → ℕ := fun c => min ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1)
  have ha : ∀ c, a c < q ^ k := fun c => by simp only [a]; omega
  have hnet := P_shift_net q k hq hk τ
  obtain ⟨v, hv, -⟩ := hnet (fun _ => k) (by simp) a ha
  refine ⟨v, ?_⟩
  unfold distInf
  refine ciSup_le fun c => ?_
  have hb := (box_iff (m := 3 * k) (q := q) k (a c) (X v c) (by omega)).mpr (hv c)
  have hxa : (a c : ℝ) / (q : ℝ) ^ k ≤ x c ∧ x c ≤ ((a c : ℝ) + 1) / (q : ℝ) ^ k := by
    rw [div_le_iff₀ hqk, le_div_iff₀ hqk]
    have hfl := Nat.floor_le (show 0 ≤ x c * (q : ℝ) ^ k by have := (hx c).1; positivity)
    have hfl2 := Nat.lt_floor_add_one (x c * (q : ℝ) ^ k)
    rcases le_total ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1) with h | h
    · have e : a c = ⌊x c * (q : ℝ) ^ k⌋₊ := min_eq_left h
      rw [e]; constructor <;> linarith
    · have e : a c = q ^ k - 1 := min_eq_right h
      have e' : ((q ^ k - 1 : ℕ) : ℝ) = (q : ℝ) ^ k - 1 := by
        rw [Nat.cast_sub hqkn]; push_cast; ring
      rw [e, e']
      have h' : ((q ^ k - 1 : ℕ) : ℝ) ≤ ⌊x c * (q : ℝ) ^ k⌋₊ := by exact_mod_cast h
      rw [e'] at h'
      constructor
      · linarith
      · have := (hx c).2; nlinarith
  unfold ptReal
  rw [abs_le]
  constructor
  · have : (X v c : ℝ) / (q : ℝ) ^ (3 * k) < ((a c : ℝ) + 1) / (q : ℝ) ^ k := hb.2
    have h2 : ((a c : ℝ) + 1) / (q : ℝ) ^ k = (a c : ℝ) / (q : ℝ) ^ k + 1 / (q : ℝ) ^ k := by
      rw [add_div]
    linarith
  · have : (a c : ℝ) / (q : ℝ) ^ k ≤ (X v c : ℝ) / (q : ℝ) ^ (3 * k) := hb.1
    have h2 : ((a c : ℝ) + 1) / (q : ℝ) ^ k = (a c : ℝ) / (q : ℝ) ^ k + 1 / (q : ℝ) ^ k := by
      rw [add_div]
    linarith

lemma covRad_le {d : ℕ} (dist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (P : Finset (Fin d → ℝ)) (B : ℝ)
    (h : ∀ x : Fin d → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → ∃ y ∈ P, dist x y ≤ B) : covRad dist P ≤ B := by
  unfold covRad
  have : Nonempty {x : Fin d → ℝ // ∀ j, 0 ≤ x j ∧ x j ≤ 1} := ⟨⟨0, fun j => by simp⟩⟩
  refine ciSup_le fun x => ?_
  obtain ⟨y, hy, hxy⟩ := h x.1 x.2
  exact le_trans (ciInf_le (Set.finite_range _).bddBelow (⟨y, hy⟩ : P)) hxy

lemma sepRad_ge {d : ℕ} (dist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (P : Finset (Fin d → ℝ)) (B : ℝ)
    (hne : ∃ x ∈ P, ∃ y ∈ P, x ≠ y) (h : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → B ≤ dist x y) :
    B / 2 ≤ sepRad dist P := by
  unfold sepRad
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  have : Nonempty {xy : (Fin d → ℝ) × (Fin d → ℝ) // xy.1 ∈ P ∧ xy.2 ∈ P ∧ xy.1 ≠ xy.2} :=
    ⟨⟨(x, y), hx, hy, hxy⟩⟩
  refine le_ciInf fun z => ?_
  have := h z.1.1 z.2.1 z.1.2 z.2.2.1 z.2.2.2
  linarith

lemma distInf_nonneg {d : ℕ} (x y : Fin d → ℝ) : 0 ≤ distInf x y := by
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · simp [distInf]
  · exact le_trans (abs_nonneg _) (le_ciSup (f := fun j => |x j - y j|) (Set.finite_range _).bddAbove
      (Classical.arbitrary _))

/-- **`prop:linf`**, the mesh ratio: the `ℓ^∞` mesh ratio of `𝒫_{k,q} ⊕ τ` in the sense of `[DGS2, §2.2]`,
non-toroidal (`ρ_∞`) and toroidal (`ρ_{∞,T}`), is at most `2q/(q - 3)`. -/
theorem linf_mesh (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) :
    meshRatio distInf (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ≤ 2 * q / ((q : ℝ) - 3) ∧
      meshRatio torDistInf (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ≤
        2 * q / ((q : ℝ) - 3) := by
  set X := Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq3 : (0 : ℝ) < (q : ℝ) - 3 := by have : (4 : ℝ) ≤ q := by exact_mod_cast hq
                                         linarith
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hXlt := Z3NetF.Proofs.digPointShift_lt (PGenZ q k) τ
  have hmem := ptSet_mem X hXlt
  have hinj := ptReal_injective (by norm_num) X hXlt (P_shift_net q k (by omega) (by omega) τ)
  -- two distinct points
  have hne : ∃ x ∈ ptSet q X, ∃ y ∈ ptSet q X, x ≠ y := by
    refine ⟨ptReal q X 0, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ptReal q X (fun _ => 1), Finset.mem_image_of_mem _ (Finset.mem_univ _), fun h => ?_⟩
    have := congrFun (hinj h) ⟨0, by omega⟩
    have h1 : (1 : ZMod q) ≠ 0 := by
      have : Fact (1 < q) := ⟨by omega⟩
      exact one_ne_zero
    exact h1 this.symm
  have hsepT : ∀ x ∈ ptSet q X, ∀ y ∈ ptSet q X, x ≠ y → (1 - 3 / (q : ℝ)) / (q : ℝ) ^ k ≤ torDistInf x y := by
    intro x hx y hy hxy
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hy
    exact linf_dist q k hq hk τ v w (fun h => hxy (h ▸ rfl))
  have hcov : ∀ x : Fin 3 → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → ∃ y ∈ ptSet q X, distInf x y ≤ 1 / (q : ℝ) ^ k := by
    intro x hx
    obtain ⟨v, hv⟩ := linf_cover q k (by omega) (by omega) τ x hx
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ v), hv⟩
  have hB : 0 < (1 - 3 / (q : ℝ)) / (q : ℝ) ^ k / 2 := by
    have : 0 < 1 - 3 / (q : ℝ) := by rw [sub_pos, div_lt_one hq0]; linarith
    positivity
  have hratio : (1 / (q : ℝ) ^ k) / ((1 - 3 / (q : ℝ)) / (q : ℝ) ^ k / 2) = 2 * q / ((q : ℝ) - 3) := by
    field_simp
  constructor
  · unfold meshRatio
    rw [← hratio]
    refine div_le_div₀ (by positivity) (covRad_le _ _ _ hcov) hB
      (sepRad_ge _ _ _ hne fun x hx y hy hxy => le_trans (hsepT x hx y hy hxy) (torDistInf_le_distInf x y))
  · unfold meshRatio
    rw [← hratio]
    refine div_le_div₀ (by positivity) (covRad_le _ _ _ fun x hx => ?_) hB (sepRad_ge _ _ _ hne hsepT)
    · obtain ⟨y, hy, hxy⟩ := hcov x hx
      exact ⟨y, hy, le_trans (torDistInf_le_distInf x y) hxy⟩

end linf

section more

/-- **`cor:dgs`(4)** for every digital shift: the nets `𝒮¹_{k,p,ρ}` of `thm:S1` (`s ≥ 3`, `p` prime, `ρ ≥ 2`,
`ρ^s < p`; `m = sk + s - 1`) are `(0,m,s)`-nets in base `p`, `(k+1)`-separated and toroidally `(k+1)`-separated
if `(ρ - 1)² ≥ s`, and `(k+2)`-separated and toroidally `(k+2)`-separated in any case. -/
theorem dgs_S1 (s p k ρ : ℕ) [NeZero p] (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    IsTMSNet p 0 (s * k + (s - 1))
        (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      (s ≤ (ρ - 1) ^ 2 →
        IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
        IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ))) ∧
      IsKSep p (k + 2) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      IsKSepTor p (k + 2) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) := by
  obtain ⟨hskel, hnet⟩ := Z3NetS1.S1gen_net s p k ρ hs hp hρ hρp
  set X := Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ
  have hXlt := Z3NetF.Proofs.digPointShift_lt (Z3NetS1.S1gen s p k ρ) τ
  have hnetS : Z3NetF.IsNet0 s p (s * k + (s - 1)) X := Z3NetF.Proofs.digPointShift_net _ τ hnet
  have hD := fun v w hvw => Z3NetS1.Proofs.S1_sep_shift_core s p k ρ hs hp hρ hρp _ hskel τ v w hvw
  have hp2 := hp.two_le
  have hgen : ∀ κ e, κ ≤ (s * k + (s - 1)) → (s - 1) * (k + 1) - 1 = ((s * k + (s - 1)) - κ) + e → s ≤ (ρ - 1) ^ 2 * p ^ (2 * e) →
      IsKSep p κ (ptSet p X) ∧ IsKSepTor p κ (ptSet p X) := by
    intro κ e hκ he hcoef
    apply sep_of_int κ hκ hp2 X hXlt
    intro v w hvw
    apply pigeon (by omega) (fun c => Z3NetF.cres (p ^ (s * k + (s - 1))) ((X v c : ℤ) - (X w c : ℤ)))
    have h1 := hD v w hvw
    rw [he, show 2 * (((s * k + (s - 1)) - κ) + e) = 2 * ((s * k + (s - 1)) - κ) + 2 * e by ring, pow_add] at h1
    have e2 : (p ^ ((s * k + (s - 1)) - κ)) ^ 2 = p ^ (2 * ((s * k + (s - 1)) - κ)) := by rw [← pow_mul, mul_comm]
    rw [e2]
    calc s * p ^ (2 * ((s * k + (s - 1)) - κ)) ≤ (ρ - 1) ^ 2 * p ^ (2 * e) * p ^ (2 * ((s * k + (s - 1)) - κ)) :=
          Nat.mul_le_mul_right _ hcoef
      _ = (ρ - 1) ^ 2 * (p ^ (2 * ((s * k + (s - 1)) - κ)) * p ^ (2 * e)) := by ring
      _ ≤ _ := h1
  have hs1 : (s - 1) * (k + 1) ≥ 2 := by
    have : (s - 1) * (k + 1) ≥ 2 * 1 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmk : (s * k + (s - 1)) = (s - 1) * (k + 1) + k := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  refine ⟨isTMSNet_of_isNet0 (by omega) X hXlt hnetS, fun hsρ => ?_, ?_⟩
  · exact hgen (k + 1) 0 (by omega) (by omega) (by simpa using hsρ)
  · refine hgen (k + 2) 1 (by omega) (by omega) ?_
    have hρ1 : 1 ≤ ρ - 1 := by omega
    have hps : s < p := by
      have : s < 2 ^ s := Nat.lt_two_pow_self
      have : 2 ^ s ≤ ρ ^ s := Nat.pow_le_pow_left hρ s
      omega
    have h1 : 1 ≤ (ρ - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : s ≤ p ^ (2 * 1) := by
      rw [mul_one]; nlinarith
    nlinarith

end more

section allm

lemma isNet0_KN {q m : ℕ} (X : (Fin m → ZMod q) → Fin 3 → ℕ) :
    Z3NetKN.IsNet0 q m X ↔ Z3NetF.IsNet0 3 q m X := by
  unfold Z3NetKN.IsNet0 Z3NetF.IsNet0
  simp only [Fin.sum_univ_three]

/-- **`cor:dgs`(5)** for every digital shift: for every prime `p ≥ 37` and every `m ≥ 3` there are generator
matrices (in the proof, those of the nets of `cor:allm`: `𝒞_p` for `m = 3`, `thm:main`, `thm:allm`, `thm:S1` at
`s = 3` otherwise) such that every digital shift of the net is a `(0,m,3)`-net in base `p` and
`(⌊m/3⌋ + 1)`-separated and toroidally `(⌊m/3⌋ + 1)`-separated. -/
theorem dgs_allm (p m : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 3 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSep p (m / 3 + 1) (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSepTor p (m / 3 + 1) (ptSet p (Z3NetF.digPointShift p m C τ)) := by
  have hp2 := hp.two_le
  rcases (show m = 3 ∨ 4 ≤ m by omega) with h3 | h4
  · subst h3
    refine ⟨Z3NetC.colGen p, fun τ => ?_⟩
    have hnet : Z3NetF.IsNet0 3 p 3 (Z3NetF.digPoint p 3 (Z3NetC.colGen p)) :=
      (isNet0_KN _).mp (Z3NetKN.Proofs.D3.col_isNet0 p hp (by omega))
    have hXlt := Z3NetF.Proofs.digPointShift_lt (Z3NetC.colGen p) τ
    refine ⟨isTMSNet_of_isNet0 (by norm_num) _ hXlt (Z3NetF.Proofs.digPointShift_net _ τ hnet), ?_⟩
    apply sep_of_int 2 (by norm_num) hp2 _ hXlt
    intro v w hvw
    set X := Z3NetF.digPointShift p 3 (Z3NetC.colGen p) τ
    apply pigeon (by norm_num) (fun c => Z3NetF.cres (p ^ 3) ((X v c : ℤ) - (X w c : ℤ)))
    have hlow := (Z3NetC.colshift_lower (Nat.Coprime.symm (by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)) (by omega) τ).1 v w hvw
    set W : ℤ := if p % 3 = 2 then (2 : ℤ) else 4 with hW
    have hW4 : W ≤ 4 := by rw [hW]; split_ifs <;> norm_num
    have hp0 : (37 : ℝ) ≤ p := by exact_mod_cast hp37
    have hWr : (W : ℝ) ≤ 4 := by exact_mod_cast hW4
    have hA : 3 * (p : ℝ) ≤ (p : ℝ) ^ 2 - ((W : ℝ) + 3) * p + 3 := by nlinarith
    set T := Z3NetF.torusDist2 (p ^ 3) (X v) (X w)
    have hT : ((p : ℝ) ^ 2 - ((W : ℝ) + 3) * p + 3) ^ 2 / 3 ≤ (T : ℝ) := by
      have h0 : 0 ≤ ((p : ℝ) ^ 2 - ((W : ℝ) + 3) * p + 3) / Real.sqrt 3 := by
        apply div_nonneg _ (Real.sqrt_nonneg _); nlinarith
      have := pow_le_pow_left₀ h0 hlow 2
      rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by norm_num)] at this
      exact this
    have h3 : 3 * (p : ℝ) ^ 2 ≤ (T : ℝ) := by
      have : (3 * (p : ℝ)) ^ 2 ≤ ((p : ℝ) ^ 2 - ((W : ℝ) + 3) * p + 3) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hA 2
      nlinarith
    have : 3 * (p ^ (3 - (3 / 3 + 1))) ^ 2 ≤ T := by
      norm_num
      exact_mod_cast h3
    exact this
  · obtain ⟨C, hC⟩ := Z3NetKN.Proofs.allmshift_core p m hp hp37 h4
    refine ⟨C, fun τ => ?_⟩
    obtain ⟨hnet, -, -, hinf⟩ := hC τ
    have hXlt := Z3NetF.Proofs.digPointShift_lt C τ
    refine ⟨isTMSNet_of_isNet0 (by norm_num) _ hXlt ((isNet0_KN _).mp hnet), ?_⟩
    exact sep_of_int (m / 3 + 1) (by omega) hp2 _ hXlt hinf

/-- **`rem:dgsfinite`**, the assembly in dimension three for every prime `p ≥ 37`: there are digital
`(0,m,3)`-nets over `𝔽_p` for every `m ∈ ℕ` (the frame of the places `∞, 0, 1` for `m ≤ 2`, the nets of
`dgs_allm` for `m ≥ 3`) such that for every choice of digital shifts `τ_m` the family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is
well separated and toroidally well separated on all of `ℕ` in the sense of `[DGS2, Def. 3.8]`, with
`κ_m = m` for `m ≤ 2` and `κ_m = ⌊m/3⌋ + 1` for `m ≥ 3`. -/
theorem dgs_family (p : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  have hp2 := hp.two_le
  classical
  let C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p) := fun m =>
    if h : 3 ≤ m then Classical.choose (dgs_allm p m hp hp37 h)
    else Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1]
  let κ : ℕ → ℕ := fun m => if 3 ≤ m then m / 3 + 1 else m
  have key : ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p, ∀ m,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      IsKSep p (κ m) (ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      IsKSepTor p (κ m) (ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
    intro τ m
    by_cases h : 3 ≤ m
    · have hC : C m = Classical.choose (dgs_allm p m hp hp37 h) := by simp only [C, dif_pos h]
      have hκ : κ m = m / 3 + 1 := by simp only [κ, if_pos h]
      rw [hC, hκ]
      exact Classical.choose_spec (dgs_allm p m hp hp37 h) (τ m)
    · have hC : C m = Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1] := by simp only [C, dif_neg h]
      have hκ : κ m = m := by simp only [κ, if_neg h]
      rw [hC, hκ]
      have hXlt := Z3NetF.Proofs.digPointShift_lt (Z3NetF.frameRead (R := ZMod p) m (0 : Fin 3) ![0, 0, 1]) (τ m)
      have hN := isTMSNet_of_isNet0 (by norm_num) _ hXlt
        (Z3NetF.Proofs.digPointShift_net _ (τ m) (frame3_net p m))
      refine ⟨hN, dgsfinite_sep p m (by norm_num) hp2 _ ?_ hN⟩
      intro x hx j
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨_, rfl⟩
  refine ⟨C, fun τ => ⟨⟨Set.infinite_univ, fun m _ => (key τ m).1, κ, 2, fun m _ => ⟨(key τ m).2.1, ?_⟩⟩,
    ⟨Set.infinite_univ, fun m _ => (key τ m).1, κ, 2, fun m _ => ⟨(key τ m).2.2, ?_⟩⟩⟩⟩ <;>
  · simp only [κ]
    split_ifs with h
    · have : ((m / 3 : ℕ) : ℝ) ≤ (m : ℝ) / 3 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self m 3
      push_cast; linarith
    · have : (m : ℝ) ≤ 2 := by exact_mod_cast (show m ≤ 2 by omega)
      have : (0 : ℝ) ≤ m := by positivity
      norm_num; linarith

end allm

section hl

/-- **`cor:dgs`(3)** for every digital shift: the nets `𝓗^s_{k,p}` of `thm:HL` (`s ≥ 2`, `p` prime,
`p ≥ max(2s, 2B_s + 4)`, every `k ≥ 1`) are `(0,sk,s)`-nets in base `p`, `(k+1)`-separated and toroidally
`(k+1)`-separated. -/
theorem dgs_HL (s p k : ℕ) [NeZero p] (hs : 2 ≤ s) (hp : p.Prime) (hps : 2 * s ≤ p)
    (hpB : 2 * Z3NetHL.BH s + 4 ≤ p) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod p) :
    IsTMSNet p 0 (s * k) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) ∧
      IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) ∧
      IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) := by
  obtain ⟨hnet, hsep⟩ := Z3NetHL.Proofs.HL_main_shift_core s p k hs hp hps (by omega) hk τ
  set X := Z3NetF.digPointShift p (s * k)
    (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ
  have hXlt := Z3NetF.Proofs.digPointShift_lt
    (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ
  have hp2 := hp.two_le
  refine ⟨isTMSNet_of_isNet0 (by omega) X hXlt hnet, ?_⟩
  have hsk : k + 1 ≤ s * k := by nlinarith
  apply sep_of_int (k + 1) hsk hp2 X hXlt
  intro v w hvw
  apply pigeon (by omega) (fun c => Z3NetF.cres (p ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)))
  have h1 := hsep v w hvw
  have e : s * k - (k + 1) = s * k - k - 1 := by omega
  rw [e]
  set B := Z3NetHL.BH s
  set E : ℕ := p ^ (s * k - k - 1)
  have hBZ : (2 : ℤ) * B + 4 ≤ p := by exact_mod_cast hpB
  have hsZ : (2 : ℤ) * s ≤ p := by exact_mod_cast hps
  have hs2 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hmin : 4 * (s : ℤ) ≤ min ((s : ℤ) * ((p : ℤ) - 2 * B - 2) ^ 2) (8 * ((p : ℤ) - B - 1) ^ 2) := by
    apply le_min
    · have : (4 : ℤ) ≤ ((p : ℤ) - 2 * B - 2) ^ 2 := by nlinarith
      nlinarith
    · have : (s : ℤ) + 1 ≤ (p : ℤ) - B - 1 := by
        have hB0 : (0 : ℤ) ≤ B := by positivity
        nlinarith
      nlinarith
  have hE : ((p : ℤ) ^ (2 * (s * k - k - 1))) = ((E : ℕ) : ℤ) ^ 2 := by
    simp only [E]; push_cast; rw [← pow_mul, mul_comm]
  rw [hE] at h1
  have hE0 : (0 : ℤ) ≤ ((E : ℕ) : ℤ) ^ 2 := by positivity
  have h2 : 4 * ((s : ℤ) * ((E : ℕ) : ℤ) ^ 2) ≤
      4 * (Z3NetHL.torusDist2 (p ^ (s * k)) (X v) (X w) : ℤ) := by nlinarith
  have h3 : ((s * E ^ 2 : ℕ) : ℤ) ≤ (Z3NetHL.torusDist2 (p ^ (s * k)) (X v) (X w) : ℤ) := by
    push_cast; linarith
  have h4 : s * E ^ 2 ≤ Z3NetHL.torusDist2 (p ^ (s * k)) (X v) (X w) := by exact_mod_cast h3
  unfold Z3NetHL.torusDist2 at h4
  exact h4

end hl

end Proofs

end Z3NetDGS
