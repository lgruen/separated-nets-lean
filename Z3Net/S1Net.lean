module
public import Mathlib
public import Z3Net.S1Defs
public import Z3Net.S1Sep
public import Z3Net.SUThm1

@[expose] public section

/-!
# Entry S1, part 3: net completion (`S1_net`), every `k ≥ 0`

Note §2.4 (`t = 1`): the frame of `s` places `∞, 0, …, s-2` (entry U's `frameGen`, Lemma T_s =
`Z3NetU.Proofs.lemmaT`) is read in graph form with depths `(k+1, …, k+1, k)`:

* `Bm` — the box matrix of the depth composition (rows: the first `K_c` digits of every reading);
  it has trivial kernel (Lemma T_s), hence is invertible over `𝔽_p`.
* `ψ = (row k of reading z) · Bm⁻¹` — the frame's skeleton row in graph form. Its last-level
  entries on the full blocks are nonzero (`psi_ne`, the `1 × 1` box argument: otherwise the
  composition `K + e_z - e_d` would have a nonzero kernel vector `Bm⁻¹ e_r`).
* `Dm` — the column gauge: lower triangular, identity except the last-level rows of the full
  blocks, which turn `ψ` into the target `ρ^(d+1)` and kill the other levels of block `d`.
* The net `Cg`: coarse rows = unit vectors, skeleton row = the S1 row, all other rows
  `Fr c · Bm⁻¹ · Dm`. Kernel argument: vanishing first digits of `Cg` force vanishing first digits
  of every frame reading of `V = Bm⁻¹ Dm n`, so `V = 0` (Lemma T_s), `Dm n = 0`, `n = 0`.
-/

namespace Z3NetS1.Proofs

open Finset Matrix

section Net

variable (s k : ℕ)

local notation "MM" => s * k + (s - 1)

/-- Frame reading `c` over `ZMod p` (places `∞, 0, …, s-2`). -/
noncomputable def Fr (p : ℕ) (c : Fin s) : Matrix (Fin MM) (Fin MM) (ZMod p) :=
  (Z3NetU.frameGen (s := s) MM c).map (Int.cast : ℤ → ZMod p)

/-- Block of index digit `r`. -/
def cOf (hs : 0 < s) (r : ℕ) : Fin s := ⟨min (r / (k + 1)) (s - 1), by omega⟩

/-- Level of index digit `r` inside its block. -/
def jOf (hs : 0 < s) (r : ℕ) : ℕ := r - (cOf s k hs r : ℕ) * (k + 1)

lemma cOf_mul_le (hs : 0 < s) (r : ℕ) : (cOf s k hs r : ℕ) * (k + 1) ≤ r := by
  unfold cOf; simp only
  calc min (r / (k + 1)) (s - 1) * (k + 1) ≤ r / (k + 1) * (k + 1) :=
        Nat.mul_le_mul_right _ (min_le_left _ _)
    _ ≤ r := Nat.div_mul_le_self r (k + 1)

lemma jOf_le (hs : 0 < s) (r : ℕ) : jOf s k hs r ≤ r := by unfold jOf; omega

lemma cOf_off (hs : 0 < s) (c : Fin s) (j : ℕ) (hj : j < depth s k c) :
    cOf s k hs (off k c + j) = c := by
  have hjk : j < k + 1 := lt_of_lt_of_le hj (depth_le s k c)
  have e : (off k c + j) / (k + 1) = c := by
    unfold off; rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hjk, add_zero]
  apply Fin.ext
  unfold cOf; simp only
  rw [e]; have := c.isLt; omega

lemma jOf_off (hs : 0 < s) (c : Fin s) (j : ℕ) (hj : j < depth s k c) :
    jOf s k hs (off k c + j) = j := by
  unfold jOf; rw [cOf_off s k hs c j hj]; unfold off; omega

lemma off_jOf (hs : 0 < s) (r : ℕ) (hr : r < MM) :
    off k (cOf s k hs r) + jOf s k hs r = r ∧ jOf s k hs r < depth s k (cOf s k hs r) := by
  obtain ⟨c, j, hj, rfl⟩ := blocks_cover s k hs r hr
  rw [cOf_off s k hs c j hj, jOf_off s k hs c j hj]
  exact ⟨rfl, hj⟩

/-- Box matrix of the depth composition: row `r` is digit `jOf r` of reading `cOf r`. -/
noncomputable def Bm (p : ℕ) (hs : 0 < s) : Matrix (Fin MM) (Fin MM) (ZMod p) :=
  fun r col => Fr s k p (cOf s k hs r) ⟨jOf s k hs r, lt_of_le_of_lt (jOf_le s k hs r) r.isLt⟩ col

lemma Bm_mulVec (p : ℕ) (hs : 0 < s) (c : Fin s) (i : Fin MM) (hi : (i : ℕ) < depth s k c)
    (x : Fin MM → ZMod p) :
    (Bm s k p hs *ᵥ x) ⟨off k c + i, lt_of_lt_of_le (Nat.add_lt_add_left hi _) (off_add_depth s k c)⟩ =
      (Fr s k p c *ᵥ x) i := by
  simp only [mulVec, dotProduct, Bm]
  have h1 := cOf_off s k hs c i hi
  have h2 := jOf_off s k hs c i hi
  have key : ∀ (c' : Fin s) (j' : ℕ) (hj' : j' < MM), c' = c → j' = i →
      ∀ col, Fr s k p c' ⟨j', hj'⟩ col = Fr s k p c i col := by
    rintro c' j' hj' rfl rfl col; rfl
  refine sum_congr rfl fun col _ => ?_
  rw [key _ _ _ h1 h2 col]

/-- `∑_c depth = m`. -/
lemma depth_sum (hs : 0 < s) : ∑ c : Fin s, depth s k c = MM := by
  show ∑ c : Fin s, (if (c : ℕ) + 1 < s then k + 1 else k) = MM
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < s then k + 1 else k) s]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [sum_range_succ, if_neg (by omega), Nat.add_sub_cancel]
  rw [sum_congr rfl (g := fun _ => k + 1) (fun i hi => by simp only [mem_range] at hi; rw [if_pos (by omega)])]
  simp; ring

/-- **Lemma T_s for the frame over `ZMod p`** (`p` prime, `s - 2 < p`), kernel form. -/
lemma frame_kernel (p : ℕ) [Fact p.Prime] (hs : 0 < s) (hps : s - 2 < p) (d : Fin s → ℕ)
    (hd : ∑ c, d c = MM) (n : Fin MM → ZMod p)
    (h : ∀ c (i : Fin MM), (i : ℕ) < d c → (Fr s k p c *ᵥ n) i = 0) : n = 0 := by
  have hdle : ∀ c, d c ≤ MM := fun c => by
    rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  apply Z3NetU.Proofs.pv_eq_zero
  refine Z3NetU.Proofs.lemmaT hs (fun c => ((Z3NetU.place c : ℤ) : ZMod p)) ?_ MM _
    (Z3NetU.Proofs.degree_pv_lt _) d hd ?_ ?_
  · intro c c' hc hc' hne
    rw [← Int.cast_sub, isUnit_iff_ne_zero]
    intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hlt : |Z3NetU.place c - Z3NetU.place c'| < (p : ℤ) := by
      unfold Z3NetU.place
      have := c.isLt; have := c'.isLt
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h0 hlt
    apply hne; apply Fin.ext; unfold Z3NetU.place at this; omega
  · intro c hc i hi
    have := Z3NetU.Proofs.frame_fin MM c hc n ⟨i, by have := hdle c; omega⟩
    rw [← this]; exact h c _ hi
  · intro i hi
    have := Z3NetU.Proofs.frame_inf MM (Z3NetU.Proofs.c0 hs) rfl n ⟨i, by have := hdle (Z3NetU.Proofs.c0 hs); omega⟩
    rw [← this]; exact h _ _ hi

lemma Bm_ker (p : ℕ) [Fact p.Prime] (hs : 0 < s) (hps : s - 2 < p) (x : Fin MM → ZMod p)
    (h : Bm s k p hs *ᵥ x = 0) : x = 0 := by
  refine frame_kernel s k p hs hps (depth s k) (depth_sum s k hs) x fun c i hi => ?_
  rw [← Bm_mulVec s k p hs c i hi, h]; rfl

lemma Bm_det (p : ℕ) [Fact p.Prime] (hs : 0 < s) (hps : s - 2 < p) : IsUnit (Bm s k p hs).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have := Bm_ker s k p hs hps (x - y) (by rw [mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

end Net

end Z3NetS1.Proofs
