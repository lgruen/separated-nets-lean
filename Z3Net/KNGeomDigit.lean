module
public import Mathlib
public import Z3Net.KNGeomCarry

@[expose] public section

/-!
# KN separation, part 3: digits of the coordinates, blocks, graph form

Total accessors over `ℕ` indices (`vz`, `dg`), the decomposition of `Fin (3k+r)` into the three
coarse blocks, graph-form digits, coarse integers `nC`, and the change of a designed row.
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p : ℕ}

/-- Total accessor of an index / digit vector. -/
def vz {m : ℕ} (v : Fin m → ZMod p) (j : ℕ) : ZMod p := if h : j < m then v ⟨j, h⟩ else 0

/-- Digit `j` (as a natural number) of the point with generator matrix `A` at index `v`. -/
def dg {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (j : ℕ) : ℕ :=
  (vz (A *ᵥ v) j).val

/-- Index digit as a natural number. -/
def vv {m : ℕ} (v : Fin m → ZMod p) (j : ℕ) : ℕ := (vz v j).val

lemma dg_lt [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (j : ℕ) :
    dg A v j < p := ZMod.val_lt _

lemma vv_lt [NeZero p] {m : ℕ} (v : Fin m → ZMod p) (j : ℕ) : vv v j < p := ZMod.val_lt _

lemma coord_eq_pre {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) :
    coord p m A v = pre p (dg A v) m := by
  rw [pre_eq_sum, coord, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  simp [dg, vz, j.isLt]

lemma mulVec_vz {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (i : ℕ)
    (hi : i < m) : vz (A *ᵥ v) i = ∑ j ∈ range m, ent A i j * vz v j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => ent A i j * vz v j)]
  simp only [vz, dif_pos hi, mulVec, dotProduct, ent]
  refine sum_congr rfl fun j _ => ?_
  simp [hi, j.isLt]

/-! ## Blocks -/

lemma depth_sum (r k : ℕ) (hr : r = 1 ∨ r = 2) :
    depth r k 0 + depth r k 1 + depth r k 2 = 3 * k + r := by
  rcases hr with rfl | rfl <;> simp [depth] <;> omega

lemma sum_blocks (r k : ℕ) (hr : r = 1 ∨ r = 2) {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ j ∈ range (3 * k + r), g j = ∑ c : Fin 3, ∑ l ∈ range (depth r k c), g (off r k c + l) := by
  rw [Fin.sum_univ_three, ← depth_sum r k hr, sum_range_add, sum_range_add]
  simp [off]

lemma depth_ge (r k : ℕ) (c : Fin 3) : k ≤ depth r k c := by unfold depth; split_ifs <;> omega

lemma depth_le (r k : ℕ) (c : Fin 3) : depth r k c ≤ k + 1 := by unfold depth; split_ifs <;> omega

lemma off_add_depth (r k : ℕ) (hr : r = 1 ∨ r = 2) (c : Fin 3) :
    off r k c + depth r k c ≤ 3 * k + r := by
  have := depth_sum r k hr
  fin_cases c <;> simp [off] <;> omega

lemma jrow_eq (r k : ℕ) (c : Fin 3) : jrow r k c = k + 1 := by
  unfold jrow depth; split_ifs <;> omega

lemma blocks_cover (r k : ℕ) (hr : r = 1 ∨ r = 2) (j : ℕ) (hj : j < 3 * k + r) :
    ∃ c : Fin 3, ∃ l < depth r k c, j = off r k c + l := by
  have := depth_sum r k hr
  by_cases h0 : j < depth r k 0
  · exact ⟨0, j, h0, by simp [off]⟩
  by_cases h1 : j < depth r k 0 + depth r k 1
  · exact ⟨1, j - depth r k 0, by omega, by simp [off]; omega⟩
  · exact ⟨2, j - (depth r k 0 + depth r k 1), by omega, by simp [off]; omega⟩

/-! ## Graph form -/

variable {r k : ℕ}

lemma graph_digit (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hr : r = 1 ∨ r = 2)
    (hC : IsKNskel r p k sk C) (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) (j : ℕ)
    (hj : j < depth r k c) : dg (C c) v j = vv v (off r k c + j) := by
  have hjm : j < 3 * k + r := by have := depth_le r k c; have := depth_ge r k c; omega
  have ho := off_add_depth r k hr c
  unfold dg vv
  rw [mulVec_vz _ _ _ hjm]
  congr 1
  have : ∀ col ∈ range (3 * k + r), ent (C c) j col * vz v col =
      if col = off r k c + j then vz v col else 0 := by
    intro col hcol
    simp only [mem_range] at hcol
    rw [hC.1 c j col hj hcol]; split_ifs <;> simp
  rw [sum_congr rfl this, sum_ite_eq', if_pos (by simp only [mem_range]; omega)]

/-- Coarse integer of block `c` (`K_c` base-`p` digits). -/
def nC (r k : ℕ) (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) : ℕ :=
  pre p (fun l => vv v (off r k c + l)) (depth r k c)

lemma nC_lt [NeZero p] (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) : nC r k v c < p ^ depth r k c :=
  pre_lt p (Nat.pos_of_neZero p) _ _ (fun j _ => vv_lt v _)

lemma pre_dg_depth (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hr : r = 1 ∨ r = 2)
    (hC : IsKNskel r p k sk C) (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) :
    pre p (dg (C c) v) (depth r k c) = nC r k v c :=
  pre_congr p _ _ _ (fun j hj => graph_digit sk C hr hC v c j hj)

lemma nC_digit [NeZero p] (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) (i : ℕ) (hi : i < depth r k c) :
    nC r k v c / p ^ i % p = vv v (off r k c + (depth r k c - 1 - i)) :=
  pre_digit p (Nat.pos_of_neZero p) _ _ (fun j _ => vv_lt v _) i hi

lemma vz_eq_of_nC_eq [NeZero p] (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3)
    (h : nC r k v c = nC r k w c) (l : ℕ) (hl : l < depth r k c) :
    vz v (off r k c + l) = vz w (off r k c + l) := by
  have := pre_inj_digit p (Nat.pos_of_neZero p) _ _ _ (fun j _ => vv_lt v _) (fun j _ => vv_lt w _) h l hl
  exact ZMod.val_injective p this

lemma eq_of_nC_eq [NeZero p] (hr : r = 1 ∨ r = 2) (v w : Fin (3 * k + r) → ZMod p)
    (h : ∀ c, nC r k v c = nC r k w c) : v = w := by
  funext j
  obtain ⟨c, l, hl, hj⟩ := blocks_cover r k hr j j.isLt
  have := vz_eq_of_nC_eq v w c (h c) l hl
  rw [← hj] at this
  simpa [vz, j.isLt] using this

/-! ## Change of a row -/

lemma row_diff (hr : r = 1 ∨ r = 2) (A : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p))
    (v w : Fin (3 * k + r) → ZMod p) (i : ℕ) (hi : i < 3 * k + r) :
    vz (A *ᵥ v) i - vz (A *ᵥ w) i = ∑ c : Fin 3, ∑ l ∈ range (depth r k c),
      ent A i (off r k c + l) * (vz v (off r k c + l) - vz w (off r k c + l)) := by
  rw [mulVec_vz _ _ _ hi, mulVec_vz _ _ _ hi, ← sum_sub_distrib, sum_blocks r k hr]
  refine sum_congr rfl fun c _ => sum_congr rfl fun l _ => by ring

/-- Change of a designed row under per-block digit patterns. -/
lemma designed_row_diff (hr : r = 1 ∨ r = 2)
    (A : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (rows : Fin 3 → Fin 4 → ℤ)
    (v w : Fin (3 * k + r) → ZMod p) (i : ℕ) (hi : i < 3 * k + r)
    (hA : ∀ d : Fin 3, ∀ l < depth r k d,
      ent A i (off r k d + l) = ((winEntry (rows d) (win r d) (depth r k d) l : ℤ) : ZMod p))
    (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) (hch : ∀ d, ch d < min (depth r k d) (win r d))
    (hD : ∀ d : Fin 3, ∀ l < depth r k d, depth r k d - 1 - l < win r d →
      vz v (off r k d + l) - vz w (off r k d + l) = ((pat (dl d) (ch d) (depth r k d - 1 - l) : ℤ) : ZMod p)) :
    vz (A *ᵥ v) i - vz (A *ᵥ w) i = ((linC rows dl ch : ℤ) : ZMod p) := by
  rw [row_diff hr A v w i hi, Fin.sum_univ_three]
  have hw : ∀ d : Fin 3, win r d ≤ 4 := fun d => by unfold win; split_ifs <;> omega
  have e : ∀ d : Fin 3, ∑ l ∈ range (depth r k d),
      ent A i (off r k d + l) * (vz v (off r k d + l) - vz w (off r k d + l)) =
      ((lin1 (rows d) (dl d) (ch d) : ℤ) : ZMod p) := by
    intro d
    rw [← window_sum (rows d) (win r d) (depth r k d) (hw d)
      (fun l => vz v (off r k d + l) - vz w (off r k d + l)) (dl d) (ch d) (hch d) (hD d)]
    refine sum_congr rfl fun l hl => ?_
    simp only [mem_range] at hl
    rw [hA d l hl]
  rw [e 0, e 1, e 2, linC]; push_cast; ring

end Z3NetKN.Geom
