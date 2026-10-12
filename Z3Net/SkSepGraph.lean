module
public import Mathlib
public import Z3Net.SkSepBasic

@[expose] public section

/-!
# Entry Skel, separation part 2: skeleton graph forms (`sec:fine`)

The block layout of `IsSkGF` (depths `k + 1` on `r` full coordinates, `k` on the others, blocks
starting at `skOff`), digits of a graph form, the fine positions `P_c` (`finePos`) as base-`p`
prefixes, their last two digits, and "the fine positions determine the index". The centred
difference `a_c` of the fine positions reduces modulo `p` to the change of digit `k`.
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

open Z3NetKN.Geom (vz dg pre pre_lt pre_digit pre_succ pre_inj_digit mulVec_vz coord_split low
  low_lt dg_lt Pf Pf_lt cen eq_of_cen_zero cen_cast_mod)

/-! ## Layout -/

/-- Depth of block `c` (natural-number index). -/
def depthN (r k c : ℕ) : ℕ := if c < r then k + 1 else k

lemma skDepth_eq {s : ℕ} (r k : ℕ) (c : Fin s) : skDepth r k c = depthN r k c := rfl

lemma depthN_le (r k c : ℕ) : depthN r k c ≤ k + 1 := by unfold depthN; split_ifs <;> omega

lemma skOff_succ (r k c : ℕ) : skOff r k (c + 1) = skOff r k c + depthN r k c := by
  unfold skOff depthN; rw [Nat.succ_mul]; split_ifs <;> omega

lemma skOff_mono (r k : ℕ) {c c' : ℕ} (h : c ≤ c') : skOff r k c ≤ skOff r k c' := by
  unfold skOff
  have := Nat.mul_le_mul_right k h
  have : min c r ≤ min c' r := min_le_min_right r h
  omega

lemma skOff_top (s r k : ℕ) (hr : r ≤ s) : skOff r k s = s * k + r := by
  unfold skOff; rw [min_eq_right hr]

lemma off_add_depth (s r k : ℕ) (hr : r ≤ s) (c : ℕ) (hc : c < s) :
    skOff r k c + depthN r k c ≤ s * k + r := by
  rw [← skOff_succ, ← skOff_top s r k hr]; exact skOff_mono r k hc

lemma sum_blocks_nat {M : Type*} [AddCommMonoid M] (r k : ℕ) (g : ℕ → M) : ∀ n : ℕ,
    ∑ col ∈ range (skOff r k n), g col =
      ∑ c ∈ range n, ∑ l ∈ range (depthN r k c), g (skOff r k c + l)
  | 0 => by simp [skOff]
  | n + 1 => by
    rw [skOff_succ, sum_range_add, sum_blocks_nat r k g n, Finset.sum_range_succ]

/-- Splitting a sum over the index digits into the blocks. -/
lemma sum_blocks {M : Type*} [AddCommMonoid M] (s r k : ℕ) (hr : r ≤ s) (g : ℕ → M) :
    ∑ col ∈ range (s * k + r), g col =
      ∑ c : Fin s, ∑ l ∈ range (skDepth r k c), g (skOff r k (c : ℕ) + l) := by
  rw [← skOff_top s r k hr, sum_blocks_nat r k g s]
  exact (Fin.sum_univ_eq_sum_range (fun c => ∑ l ∈ range (depthN r k c), g (skOff r k c + l)) s).symm

lemma cover_nat (r k : ℕ) : ∀ n col, col < skOff r k n →
    ∃ c < n, ∃ j < depthN r k c, col = skOff r k c + j
  | 0, col, h => by simp [skOff] at h
  | n + 1, col, h => by
    rw [skOff_succ] at h
    by_cases h' : col < skOff r k n
    · obtain ⟨c, hc, j, hj, e⟩ := cover_nat r k n col h'
      exact ⟨c, by omega, j, hj, e⟩
    · exact ⟨n, by omega, col - skOff r k n, by omega, by omega⟩

/-- Every index digit lies in a block. -/
lemma blocks_cover (s r k : ℕ) (hr : r ≤ s) (col : ℕ) (hcol : col < s * k + r) :
    ∃ c : Fin s, ∃ j < skDepth r k c, col = skOff r k (c : ℕ) + j := by
  rw [← skOff_top s r k hr] at hcol
  obtain ⟨c, hc, j, hj, e⟩ := cover_nat r k s col hcol
  exact ⟨⟨c, hc⟩, j, hj, e⟩

/-! ## Digits of a skeleton graph form -/

variable {s r p k : ℕ} {C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)}

lemma graph_digit (hr : r ≤ s) (hC : IsSkGF s r p k C) (v : Fin (s * k + r) → ZMod p) (c : Fin s)
    (j : ℕ) (hj : j < skDepth r k c) : vz (C c *ᵥ v) j = vz v (skOff r k (c : ℕ) + j) := by
  have ho := off_add_depth s r k hr c c.isLt
  rw [skDepth_eq] at hj
  rw [mulVec_vz _ _ _ (by omega)]
  have : ∀ col ∈ range (s * k + r), Z3NetKN.ent (C c) j col * vz v col =
      if col = skOff r k (c : ℕ) + j then vz v col else 0 := by
    intro col hcol
    simp only [mem_range] at hcol
    rw [← ent_eq, hC c j hj col hcol]; split_ifs <;> simp
  rw [sum_congr rfl this, sum_ite_eq', if_pos (by simp only [mem_range]; omega)]

/-- Change of row `i` between two indices, block by block. -/
lemma row_diff (hr : r ≤ s) (A : Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (v w : Fin (s * k + r) → ZMod p) (i : ℕ) (hi : i < s * k + r) :
    vz (A *ᵥ w) i - vz (A *ᵥ v) i = ∑ d : Fin s, ∑ l ∈ range (skDepth r k d),
      ent A i (skOff r k (d : ℕ) + l) * (vz w (skOff r k (d : ℕ) + l) - vz v (skOff r k (d : ℕ) + l)) := by
  rw [mulVec_vz _ _ _ hi, mulVec_vz _ _ _ hi, ← sum_sub_distrib,
    sum_blocks s r k hr (fun j => Z3NetKN.ent A i j * vz w j - Z3NetKN.ent A i j * vz v j)]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => by rw [ent_eq]; ring

/-! ## Fine positions -/

lemma finePos_eq [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (v : Fin m → ZMod p) (c : Fin s) : finePos p m k C v c = Pf k (C c) v := by
  unfold finePos digPoint
  rw [coord_eq, coord_split _ v (k + 1) hkm, Nat.mul_comm, Nat.mul_add_div (pow_pos (Nat.pos_of_neZero p) _),
    Nat.div_eq_of_lt (low_lt _ _ _), add_zero]
  rfl

lemma finePos_lt [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (v : Fin m → ZMod p) (c : Fin s) : finePos p m k C v c < p ^ (k + 1) := by
  rw [finePos_eq k hkm]; exact Pf_lt _ _

lemma dg_cast [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (j : ℕ) :
    ((dg A v j : ℕ) : ZMod p) = vz (A *ᵥ v) j := by
  simp [dg, ZMod.natCast_zmod_val]

/-- `P_c mod p` is digit `k` of coordinate `c`. -/
lemma finePos_mod [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (v : Fin m → ZMod p) (c : Fin s) :
    ((finePos p m k C v c % p : ℕ) : ZMod p) = vz (C c *ᵥ v) k := by
  rw [finePos_eq k hkm]
  unfold Pf
  rw [pre_succ, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _), dg_cast]

/-- `⌊P_c / p⌋ mod p` is digit `k - 1` of coordinate `c` (`k ≥ 1`). -/
lemma finePos_div_mod [NeZero p] {m : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (c : Fin s) :
    ((finePos p m k C v c / p ^ 1 % p : ℕ) : ZMod p) = vz (C c *ᵥ v) (k - 1) := by
  rw [finePos_eq k hkm]
  unfold Pf
  rw [pre_digit p (Nat.pos_of_neZero p) _ _ (fun j _ => dg_lt _ _ _) 1 (by omega), dg_cast,
    show k + 1 - 1 - 1 = k - 1 by omega]

/-- The fine positions determine the index. -/
lemma eq_of_finePos_eq [NeZero p] (hr : r ≤ s) (hC : IsSkGF s r p k C) (hkm : k + 1 ≤ s * k + r)
    (v w : Fin (s * k + r) → ZMod p)
    (h : ∀ c, finePos p (s * k + r) k C v c = finePos p (s * k + r) k C w c) : v = w := by
  funext col
  obtain ⟨c, j, hj, hcol⟩ := blocks_cover s r k hr col col.isLt
  have hjk : j < k + 1 := lt_of_lt_of_le hj (by rw [skDepth_eq]; exact depthN_le r k c)
  have hP := h c
  rw [finePos_eq k hkm, finePos_eq k hkm] at hP
  have hd := pre_inj_digit p (Nat.pos_of_neZero p) _ _ (k + 1) (fun i _ => dg_lt _ v i)
    (fun i _ => dg_lt _ w i) hP j hjk
  have h1 : vz (C c *ᵥ v) j = vz (C c *ᵥ w) j := ZMod.val_injective p hd
  rw [graph_digit hr hC v c j hj, graph_digit hr hC w c j hj, ← hcol] at h1
  simpa [vz, col.isLt] using h1

/-- Centred difference of the fine positions. -/
def aDiff {m : ℕ} (p k : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (c : Fin s) : ℤ :=
  cmod (p ^ (k + 1)) ((finePos p m k C w c : ℤ) - finePos p m k C v c)

lemma aDiff_cast [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (v w : Fin m → ZMod p) (c : Fin s) :
    ((aDiff p k C v w c : ℤ) : ZMod p) = vz (C c *ᵥ w) k - vz (C c *ᵥ v) k := by
  unfold aDiff
  rw [cmod_eq_cen, cen_cast_mod (k + 1) _ _ (by omega), finePos_mod k hkm, finePos_mod k hkm]

lemma ne_zero_of_ne [NeZero p] (hr : r ≤ s) (hC : IsSkGF s r p k C) (hkm : k + 1 ≤ s * k + r)
    (v w : Fin (s * k + r) → ZMod p) (hvw : v ≠ w) : ∃ c, aDiff p k C v w c ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hvw
  refine eq_of_finePos_eq hr hC hkm v w fun c => ?_
  have := hall c
  unfold aDiff at this
  rw [cmod_eq_cen] at this
  exact (eq_of_cen_zero _ _ _ (finePos_lt k hkm C w c) (finePos_lt k hkm C v c) this).symm

lemma abs_aDiff_le [NeZero p] {m : ℕ} (k : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (v w : Fin m → ZMod p) (c : Fin s) : 2 * |aDiff p k C v w c| ≤ p ^ (k + 1) := by
  unfold aDiff; rw [cmod_eq_cen]
  exact_mod_cast Z3NetKN.Geom.cen_abs _ (pow_pos (Nat.pos_of_neZero p) _) _

end SkSep

end Z3NetF.Proofs
