/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `def:B` (`𝓑¹`), `prop:Bnet`.
Entry Dim3 (`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3B2

@[expose] public section

/-!
# Entry Dim3, part 5: the explicit net `𝓑¹_{k,p,ρ}` (`B1gen_net`)

As for `𝓑²` (`D3B2`): the frame graph form times the invertible lower-triangular column gauge is
`t = 0`, and `T0_of_scale` (moves (a), (b)) adds the block scalings `scalB1`, the coarse rows and
the diagonal blocks. The pivots are those of `KNBnet1` (`piv_Yk`, `piv_Zk`, `piv_Z2k`, `piv_Y3k`,
`piv_det`). The skeleton rows are computed column by column (Cramer's rule on the `x` block).
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset Z3NetKN.Frame

section B1

variable (p k ρ : ℕ)

local notation "m1" => 3 * k + 1

lemma blkN1_eq (x : ℕ) : blkN 1 k x = if x < k + 1 then 0 else if x < 2 * k + 1 then 1 else 2 := by
  unfold blkN depN
  simp only [show (0 : ℕ) < 1 from by norm_num, if_true, show ¬ ((1 : ℕ) < 1) by omega, if_false]
  split_ifs <;> omega

/-- Support of the gauge: lower triangular inside the blocks. -/
lemma gB1_supp (r col : Fin m1) (h : gaugeB1 p k ρ r col ≠ 0) :
    (col : ℕ) ≤ r ∧ blkN 1 k col = blkN 1 k r := by
  rw [blkN1_eq, blkN1_eq]
  unfold gaugeB1 at h
  split_ifs at h <;>
    first
    | exact absurd rfl h
    | (subst_vars; exact ⟨le_refl _, rfl⟩)
    | (constructor <;> [omega; (split_ifs <;> omega)])

lemma gB1_lower (i j : Fin m1) (hij : i < j) : gaugeB1 p k ρ i j = 0 := by
  by_contra h
  have := (gB1_supp p k ρ i j h).1
  have : (i : ℕ) < j := hij
  omega

/-! ### The columns of the gauge -/

lemma gB1_xk (t col : Fin m1) (hcol : (col : ℕ) = k) :
    gaugeB1 p k ρ t col =
      if (t : ℕ) = k then (ρ : ZMod p) ^ 2 * detB1 p k * (zB1 p k k * yB1 p k k)⁻¹ else 0 := by
  unfold gaugeB1; rw [if_pos hcol.le, if_pos hcol]

lemma gB1_xk1 (t col : Fin m1) (hcol : (col : ℕ) + 1 = k) :
    gaugeB1 p k ρ t col =
      if (t : ℕ) = k then -(yB1 p k (k - 1)) * (yB1 p k k)⁻¹ else if t = col then 1 else 0 := by
  unfold gaugeB1; rw [if_pos (by omega), if_neg (by omega), if_pos hcol]

lemma gB1_xl (t col : Fin m1) (hcol : (col : ℕ) + 1 < k) :
    gaugeB1 p k ρ t col =
      if (t : ℕ) = k then
        -(zB1 p k (k - 1) * yB1 p k col - yB1 p k (k - 1) * zB1 p k col) * (detB1 p k)⁻¹
      else if (t : ℕ) + 1 = k then
        -(yB1 p k k * zB1 p k col - zB1 p k k * yB1 p k col) * (detB1 p k)⁻¹
      else if t = col then 1 else 0 := by
  unfold gaugeB1; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]

lemma gB1_y (t col : Fin m1) (hcol : k < (col : ℕ) ∧ (col : ℕ) < 2 * k) :
    gaugeB1 p k ρ t col =
      if (t : ℕ) = 2 * k then -(zB1 p k col) * (zB1 p k (2 * k))⁻¹ else if t = col then 1 else 0 := by
  unfold gaugeB1
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases ht : (t : ℕ) = 2 * k
  · rw [if_pos ⟨hcol.2, ht⟩, if_pos ht]
  · rw [if_neg (fun h => ht h.2), if_neg ht]

lemma gB1_yk (t col : Fin m1) (hcol : (col : ℕ) = 2 * k) (hk : 1 ≤ k) :
    gaugeB1 p k ρ t col = if t = col then 1 else 0 := by
  unfold gaugeB1
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]

lemma gB1_z (t col : Fin m1) (hcol : 2 * k < (col : ℕ) ∧ (col : ℕ) < 3 * k) :
    gaugeB1 p k ρ t col =
      if (t : ℕ) = 3 * k then -(yB1 p k col) * (yB1 p k (3 * k))⁻¹ else if t = col then 1 else 0 := by
  unfold gaugeB1
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases ht : (t : ℕ) = 3 * k
  · rw [if_pos ⟨hcol.2, ht⟩, if_pos ht]
  · rw [if_neg (fun h => ht h.2), if_neg ht]

lemma gB1_zk (t col : Fin m1) (hcol : (col : ℕ) = 3 * k) (hk : 1 ≤ k) :
    gaugeB1 p k ρ t col = if t = col then 1 else 0 := by
  unfold gaugeB1
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma B1gen_off (c : Fin 3) (i col : Fin m1) (hi : ¬ (i : ℕ) < depN 1 k c)
    (hb : blkN 1 k col ≠ c) :
    B1gen p k ρ c i col = scalB1 p k ρ c (blkN 1 k col) * (frameGrN 1 p k c * gaugeB1 p k ρ) i col := by
  unfold B1gen; rw [if_neg hi, if_neg hb]

lemma sc10 : scalB1 p k ρ 1 0 = zB1 p k k * ((ρ : ZMod p) * detB1 p k)⁻¹ := by
  unfold scalB1; simp
lemma sc20 : scalB1 p k ρ 2 0 = yB1 p k k * (detB1 p k)⁻¹ := by
  unfold scalB1; simp
lemma sc21 : scalB1 p k ρ 2 1 = (zB1 p k (2 * k))⁻¹ := by
  unfold scalB1; simp
lemma sc12 : scalB1 p k ρ 1 2 = (yB1 p k (3 * k))⁻¹ := by
  unfold scalB1; simp

variable [Fact p.Prime]

lemma yB1_eq (j : ℕ) : yB1 p k j = Y1 p k j := by
  unfold yB1 Y1
  rw [show frameGrN 1 p k 1 = frameGF 1 p k 1 from frameGrN_eq 1 p k (by norm_num) 1]

lemma zB1_eq (j : ℕ) : zB1 p k j = Z1 p k j := by
  unfold zB1 Z1
  rw [show frameGrN 1 p k 2 = frameGF 1 p k 2 from frameGrN_eq 1 p k (by norm_num) 2]

lemma detB1_eq : detB1 p k = Y1 p k k * Z1 p k (k - 1) - Y1 p k (k - 1) * Z1 p k k := by
  unfold detB1; rw [yB1_eq, yB1_eq, zB1_eq, zB1_eq]

lemma frameGrN1_rowY (t : Fin m1) (hk : 1 ≤ k) : frameGrN 1 p k 1 ⟨k, by omega⟩ t = yB1 p k t := by
  unfold yB1 ent; rw [dif_pos ⟨by omega, t.isLt⟩]

lemma frameGrN1_rowZ (t : Fin m1) (hk : 1 ≤ k) : frameGrN 1 p k 2 ⟨k, by omega⟩ t = zB1 p k t := by
  unfold zB1 ent; rw [dif_pos ⟨by omega, t.isLt⟩]

section Piv

variable (hk : 1 ≤ k)
include hk

lemma pY : yB1 p k k ≠ 0 := by rw [yB1_eq]; exact piv_Yk p k hk
lemma pZ : zB1 p k k ≠ 0 := by rw [zB1_eq]; exact piv_Zk p k hk
lemma pZ2 : zB1 p k (2 * k) ≠ 0 := by rw [zB1_eq]; exact piv_Z2k p k hk
lemma pY3 : yB1 p k (3 * k) ≠ 0 := by rw [yB1_eq]; exact piv_Y3k p k hk
lemma pD : detB1 p k ≠ 0 := by rw [detB1_eq]; exact piv_det p k hk

lemma gB1_diag (hρ : (ρ : ZMod p) ≠ 0) (i : Fin m1) : gaugeB1 p k ρ i i ≠ 0 := by
  have h1 := pY p k hk
  have h2 := pZ p k hk
  have h3 := pD p k hk
  unfold gaugeB1
  split_ifs <;> first
    | exact one_ne_zero
    | exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hρ) h3) (inv_ne_zero (mul_ne_zero h2 h1))
    | omega
    | (exfalso; omega)

lemma scalB1_ne (hρ : (ρ : ZMod p) ≠ 0) (c d : ℕ) : scalB1 p k ρ c d ≠ 0 := by
  have h1 := pY p k hk
  have h2 := pZ p k hk
  have h3 := pD p k hk
  have h4 := pZ2 p k hk
  have h5 := pY3 p k hk
  unfold scalB1
  split_ifs
  · exact mul_ne_zero h1 (inv_ne_zero h3)
  · exact mul_ne_zero h2 (inv_ne_zero (mul_ne_zero hρ h3))
  · exact inv_ne_zero h4
  · exact inv_ne_zero h5
  · exact one_ne_zero

end Piv

end B1

section B1s

variable (p k ρ : ℕ)

local notation "m1" => 3 * k + 1

/-- The `y` skeleton row of `𝓑¹`: `S_y = ρ x_k + z_{k-1}`. -/
lemma B1gen_skelY (hp : p.Prime) (hk : 1 ≤ k) (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m1) :
    B1gen p k ρ 1 ⟨k, by omega⟩ col =
      if (col : ℕ) = k then (ρ : ZMod p) else if (col : ℕ) = 3 * k then 1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := pY p k hk
  have h2 := pZ p k hk
  have h3 := pD p k hk
  have h5 := pY3 p k hk
  have hc := col.isLt
  have hi : ¬ ((⟨k, by omega⟩ : Fin m1) : ℕ) < depN 1 k ((1 : Fin 3) : ℕ) := by simp [depN]
  let tk : Fin m1 := ⟨k, by omega⟩
  let tk1 : Fin m1 := ⟨k - 1, by omega⟩
  let t3k : Fin m1 := ⟨3 * k, by omega⟩
  rcases (show (col : ℕ) + 1 < k ∨ (col : ℕ) + 1 = k ∨ (col : ℕ) = k ∨
      (k < (col : ℕ) ∧ (col : ℕ) < 2 * k + 1) ∨ (2 * k < (col : ℕ) ∧ (col : ℕ) < 3 * k) ∨
      (col : ℕ) = 3 * k by omega) with h | h | h | h | h | h
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 1 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 3 * k by omega)]
    rw [mul_supp3 _ _ _ _ col tk1 tk (Fin.ne_of_val_ne (by simp [tk1]; omega))
      (Fin.ne_of_val_ne (by simp [tk]; omega)) (Fin.ne_of_val_ne (by simp [tk1, tk]; omega))
      (by intro t ht1 ht2 ht3
          rw [gB1_xl p k ρ t col h, if_neg (fun e => ht3 (Fin.ext (by simp [tk]; omega))),
            if_neg (fun e => ht2 (Fin.ext (by simp [tk1]; omega))), if_neg ht1])]
    rw [gB1_xl p k ρ col col h, gB1_xl p k ρ tk1 col h, gB1_xl p k ρ tk col h,
      if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by simp [tk1]; omega),
      if_pos (by simp [tk1]; omega), if_pos (by simp [tk])]
    simp only [Fin.val_one, frameGrN1_rowY p k _ hk, hb, sc10]
    simp only [tk, tk1]
    field_simp
    unfold detB1; ring
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 1 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 3 * k by omega)]
    rw [mul_supp2 _ _ _ _ col tk (Fin.ne_of_val_ne (by simp [tk]; omega))
      (by intro t ht1 ht2
          rw [gB1_xk1 p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [tk]; omega))),
            if_neg ht1])]
    rw [gB1_xk1 p k ρ col col h, gB1_xk1 p k ρ tk col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [tk])]
    simp only [Fin.val_one, frameGrN1_rowY p k _ hk, hb, sc10]
    simp only [tk]
    rw [show (col : ℕ) = k - 1 by omega]
    field_simp; ring
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 1 _ col hi (by rw [hb]; simp), if_pos h]
    rw [mul_supp1 _ _ _ _ tk
      (by intro t ht
          rw [gB1_xk p k ρ t col h, if_neg (fun e => ht (Fin.ext (by simp [tk]; omega)))])]
    rw [gB1_xk p k ρ tk col h, if_pos (by simp [tk])]
    simp only [Fin.val_one, frameGrN1_rowY p k _ hk, hb, sc10]
    simp only [tk]
    field_simp
  · -- own block
    have hb : blkN 1 k col = 1 := by rw [blkN1_eq, if_neg (by omega), if_pos (by omega)]
    unfold B1gen
    rw [if_neg hi, if_pos (by rw [hb]; simp), if_neg (by simp), if_neg (by omega),
      if_neg (by omega)]
  · have hb : blkN 1 k col = 2 := by rw [blkN1_eq, if_neg (by omega), if_neg (by omega)]
    rw [B1gen_off p k ρ 1 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 3 * k by omega)]
    rw [mul_supp2 _ _ _ _ col t3k (Fin.ne_of_val_ne (by simp [t3k]; omega))
      (by intro t ht1 ht2
          rw [gB1_z p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [t3k]; omega))),
            if_neg ht1])]
    rw [gB1_z p k ρ col col h, gB1_z p k ρ t3k col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [t3k])]
    simp only [Fin.val_one, frameGrN1_rowY p k _ hk, hb, sc12]
    simp only [t3k]
    field_simp; ring
  · have hb : blkN 1 k col = 2 := by rw [blkN1_eq, if_neg (by omega), if_neg (by omega)]
    rw [B1gen_off p k ρ 1 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_pos h]
    rw [mul_supp1 _ _ _ _ col
      (by intro t ht; rw [gB1_zk p k ρ t col h hk, if_neg ht])]
    rw [gB1_zk p k ρ col col h hk, if_pos rfl, hb]
    simp only [Fin.val_one, frameGrN1_rowY p k _ hk, sc12]
    have h5' : yB1 p k col ≠ 0 := by rw [h]; exact h5
    rw [h] at h5' ⊢
    field_simp

/-- The `z` skeleton row of `𝓑¹`: `S_z = ρ² x_k + x_{k-1} + y_{k-1} - z_{k-1}`. -/
lemma B1gen_skelZ (hp : p.Prime) (hk : 1 ≤ k) (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m1) :
    B1gen p k ρ 2 ⟨k, by omega⟩ col =
      if (col : ℕ) = k then (ρ : ZMod p) ^ 2 else if (col : ℕ) + 1 = k then 1
      else if (col : ℕ) = 2 * k then 1 else if (col : ℕ) = 3 * k then -1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := pY p k hk
  have h2 := pZ p k hk
  have h3 := pD p k hk
  have h4 := pZ2 p k hk
  have hc := col.isLt
  have hi : ¬ ((⟨k, by omega⟩ : Fin m1) : ℕ) < depN 1 k ((2 : Fin 3) : ℕ) := by simp [depN]
  let tk : Fin m1 := ⟨k, by omega⟩
  let tk1 : Fin m1 := ⟨k - 1, by omega⟩
  let t2k : Fin m1 := ⟨2 * k, by omega⟩
  rcases (show (col : ℕ) + 1 < k ∨ (col : ℕ) + 1 = k ∨ (col : ℕ) = k ∨
      (k < (col : ℕ) ∧ (col : ℕ) < 2 * k) ∨ (col : ℕ) = 2 * k ∨ 2 * k < (col : ℕ) by omega) with
    h | h | h | h | h | h
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) + 1 = k by omega), if_neg (show ¬ (col : ℕ) = 2 * k by omega),
      if_neg (show ¬ (col : ℕ) = 3 * k by omega)]
    rw [mul_supp3 _ _ _ _ col tk1 tk (Fin.ne_of_val_ne (by simp [tk1]; omega))
      (Fin.ne_of_val_ne (by simp [tk]; omega)) (Fin.ne_of_val_ne (by simp [tk1, tk]; omega))
      (by intro t ht1 ht2 ht3
          rw [gB1_xl p k ρ t col h, if_neg (fun e => ht3 (Fin.ext (by simp [tk]; omega))),
            if_neg (fun e => ht2 (Fin.ext (by simp [tk1]; omega))), if_neg ht1])]
    rw [gB1_xl p k ρ col col h, gB1_xl p k ρ tk1 col h, gB1_xl p k ρ tk col h,
      if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by simp [tk1]; omega),
      if_pos (by simp [tk1]; omega), if_pos (by simp [tk])]
    simp only [Fin.val_two, frameGrN1_rowZ p k _ hk, hb, sc20]
    simp only [tk, tk1]
    field_simp
    unfold detB1; ring
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_pos h]
    rw [mul_supp2 _ _ _ _ col tk (Fin.ne_of_val_ne (by simp [tk]; omega))
      (by intro t ht1 ht2
          rw [gB1_xk1 p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [tk]; omega))),
            if_neg ht1])]
    rw [gB1_xk1 p k ρ col col h, gB1_xk1 p k ρ tk col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [tk]), hb]
    simp only [Fin.val_two, frameGrN1_rowZ p k _ hk, sc20]
    simp only [tk]
    rw [show (col : ℕ) = k - 1 by omega]
    field_simp; unfold detB1; ring
  · have hb : blkN 1 k col = 0 := by rw [blkN1_eq, if_pos (by omega)]
    rw [B1gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_pos h]
    rw [mul_supp1 _ _ _ _ tk
      (by intro t ht
          rw [gB1_xk p k ρ t col h, if_neg (fun e => ht (Fin.ext (by simp [tk]; omega)))])]
    rw [gB1_xk p k ρ tk col h, if_pos (by simp [tk]), hb]
    simp only [Fin.val_two, frameGrN1_rowZ p k _ hk, sc20]
    simp only [tk]
    field_simp
  · have hb : blkN 1 k col = 1 := by rw [blkN1_eq, if_neg (by omega), if_pos (by omega)]
    rw [B1gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) + 1 = k by omega), if_neg (show ¬ (col : ℕ) = 2 * k by omega),
      if_neg (show ¬ (col : ℕ) = 3 * k by omega)]
    rw [mul_supp2 _ _ _ _ col t2k (Fin.ne_of_val_ne (by simp [t2k]; omega))
      (by intro t ht1 ht2
          rw [gB1_y p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [t2k]; omega))),
            if_neg ht1])]
    rw [gB1_y p k ρ col col h, gB1_y p k ρ t2k col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [t2k])]
    simp only [Fin.val_two, frameGrN1_rowZ p k _ hk, hb, sc21]
    simp only [t2k]
    field_simp; ring
  · have hb : blkN 1 k col = 1 := by rw [blkN1_eq, if_neg (by omega), if_pos (by omega)]
    rw [B1gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) + 1 = k by omega), if_pos h]
    rw [mul_supp1 _ _ _ _ col
      (by intro t ht; rw [gB1_yk p k ρ t col h hk, if_neg ht])]
    rw [gB1_yk p k ρ col col h hk, if_pos rfl, hb]
    simp only [Fin.val_two, frameGrN1_rowZ p k _ hk, sc21]
    have h4' : zB1 p k col ≠ 0 := by rw [h]; exact h4
    rw [h] at h4' ⊢
    field_simp
  · -- own block
    have hb : blkN 1 k col = 2 := by rw [blkN1_eq, if_neg (by omega), if_neg (by omega)]
    unfold B1gen
    rw [if_neg hi, if_pos (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) + 1 = k by omega), if_neg (show ¬ (col : ℕ) = 2 * k by omega)]
    by_cases h3k : (col : ℕ) = 3 * k
    · rw [if_pos ⟨by simp, by simp, h3k⟩, if_pos h3k]
    · rw [if_neg (fun e => h3k e.2.2), if_neg h3k]

end B1s

end Z3NetKN.Proofs.D3

namespace Z3NetKN.Proofs

open Matrix Finset Z3NetKN.Frame D3

/-- The skeleton rows of `𝓑¹` are `skB1 ρ` (no `Fact` instance in scope). -/
lemma D3.B1gen_isKNskel (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ0 : (ρ : ZMod p) ≠ 0) :
    IsKNskel 1 p k (skB1 ρ) (B1gen p k ρ) := by
  have hsum := depth_sum 1 k (by norm_num)
  refine ⟨?_, ?_⟩
  · intro c j col hj hcol
    unfold ent
    rw [dif_pos ⟨by fin_cases c <;> simp [depth] at hj ⊢ <;> omega, hcol⟩]
    unfold B1gen
    rw [if_pos (by rw [← depth_eq_depN]; exact hj)]
    have : offN 1 k c = off 1 k c := by
      rw [← offK_eq_offN]; rfl
    rw [this]
  · intro c d hc l hl
    have hlt : off 1 k d + l < 3 * k + 1 := by
      have := offK_lt (depth 1 k) hsum d l hl
      rwa [← off_eq] at this
    have hcd : depth 1 k c = k := by
      rcases c with ⟨_ | _ | _ | c, h⟩ <;> simp [depth] at hc ⊢ <;> omega
    rw [hcd]
    unfold ent
    rw [dif_pos ⟨by omega, hlt⟩]
    obtain rfl | rfl : c = 1 ∨ c = 2 := by
      rcases c with ⟨_ | _ | _ | c, h⟩ <;> simp at hc ⊢ <;> omega
    · rw [B1gen_skelY p k ρ hp hk hρ0 ⟨off 1 k d + l, hlt⟩]
      simp only
      obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
      · have hd : depth 1 k 0 = k + 1 := by simp [depth]
        have ho : off 1 k 0 = 0 := by simp [off]
        rw [hd] at hl
        have hw : skB1 ρ 1 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
        rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl]
        simp only [ho, zero_add]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl
      · have hd : depth 1 k 1 = k := by simp [depth]
        have ho : off 1 k 1 = k + 1 := by simp [off, depth]
        rw [hd] at hl
        have hw : skB1 ρ 1 1 = ![((0 : ℕ) : ℤ), 0, 0, 0] := by
          ext i; fin_cases i <;> rfl
        rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl]
        simp only [ho]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl
      · have hd : depth 1 k 2 = k := by simp [depth]
        have ho : off 1 k 2 = 2 * k + 1 := by simp [off, depth]; ring
        rw [hd] at hl
        have hw : skB1 ρ 1 2 = ![1, 0, 0, 0] := rfl
        rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl]
        simp only [ho]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl
    · rw [B1gen_skelZ p k ρ hp hk hρ0 ⟨off 1 k d + l, hlt⟩]
      simp only
      obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
      · have hd : depth 1 k 0 = k + 1 := by simp [depth]
        have ho : off 1 k 0 = 0 := by simp [off]
        rw [hd] at hl
        have hw : skB1 ρ 2 0 = ![(ρ : ℤ) ^ 2, 1, 0, 0] := rfl
        rw [hw, hd, winEntry_two _ _ _ _ _ (by simp [win]) hl]
        simp only [ho, zero_add]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl
      · have hd : depth 1 k 1 = k := by simp [depth]
        have ho : off 1 k 1 = k + 1 := by simp [off, depth]
        rw [hd] at hl
        have hw : skB1 ρ 2 1 = ![1, 0, 0, 0] := rfl
        rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl]
        simp only [ho]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl
      · have hd : depth 1 k 2 = k := by simp [depth]
        have ho : off 1 k 2 = 2 * k + 1 := by simp [off, depth]; ring
        rw [hd] at hl
        have hw : skB1 ρ 2 2 = ![-1, 0, 0, 0] := rfl
        rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl]
        simp only [ho]
        split_ifs <;> first | omega | (simp; done) | (simp; rfl) | rfl


/-- **`def:B` (`𝓑¹`) and `prop:Bnet`.** -/
theorem B1gen_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : ¬ p ∣ ρ) :
    IsKNskel 1 p k (skB1 ρ) (B1gen p k ρ) ∧
      IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) (B1gen p k ρ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρ0 : (ρ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hρ
  have hsum := depth_sum 1 k (by norm_num)
  have hF := frame_T0 (ZMod p) (3 * k + 1) (by omega)
  have hG : T0 (fun c : Fin 3 => frameGrN 1 p k c) := by
    have : (fun c : Fin 3 => frameGrN 1 p k c) = gr (frameF (ZMod p) (3 * k + 1)) (depth 1 k) :=
      funext (frameGrN_eq 1 p k (by norm_num))
    rw [this]; exact T0_gr hF _ hsum
  have hU : IsUnit (gaugeB1 p k ρ) :=
    isUnit_of_lower _ (gB1_lower p k ρ) (gB1_diag p k ρ hk hρ0)
  have hX := T0_mul_right hG _ hU
  have hGc : ∀ (c : Fin 3) (j col : Fin (3 * k + 1)), (j : ℕ) < depth 1 k c →
      frameGrN 1 p k c j col = if (col : ℕ) = offK (depth 1 k) c + j then 1 else 0 := by
    intro c j col hj
    rw [frameGrN_eq 1 p k (by norm_num) c]
    exact gr_coarse hF _ hsum c j col hj
  let bl : Fin (3 * k + 1) → Fin 3 := fun col => ⟨blkN 1 k col, blkN_lt 1 k col⟩
  have hY : T0 (B1gen p k ρ) := by
    refine T0_of_scale hX (depth 1 k) hsum bl ?_ ?_ ?_ (fun c d => scalB1 p k ρ c d)
      (fun c d _ => scalB1_ne p k ρ hk hρ0 c d) ?_
    · intro col
      have hc := col.isLt
      simp only [bl, blkN1_eq]
      rcases (show (col : ℕ) < k + 1 ∨ (k + 1 ≤ (col : ℕ) ∧ (col : ℕ) < 2 * k + 1) ∨
          2 * k + 1 ≤ (col : ℕ) by omega) with h | h | h
      · simp only [if_pos h]; exact ⟨col, by simp [depth]; omega, by simp [offK]⟩
      · simp only [if_neg (show ¬ (col : ℕ) < k + 1 by omega), if_pos h.2]
        exact ⟨(col : ℕ) - (k + 1), by simp [depth]; omega, by simp [offK, depth]; omega⟩
      · simp only [if_neg (show ¬ (col : ℕ) < k + 1 by omega),
          if_neg (show ¬ (col : ℕ) < 2 * k + 1 by omega)]
        exact ⟨(col : ℕ) - (2 * k + 1), by simp [depth]; omega, by simp [offK, depth]; omega⟩
    · intro c i col hi hne
      have hlt := offK_lt (depth 1 k) hsum c i hi
      have e := mul_unit_row (frameGrN 1 p k c) (gaugeB1 p k ρ) i (offK (depth 1 k) c + i) hlt
        (fun t => hGc c i t hi) col
      rw [e] at hne
      obtain ⟨h1, h2⟩ := gB1_supp p k ρ _ col hne
      refine ⟨Fin.ext ?_, h1⟩
      simp only [bl]
      rw [h2]
      obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
      · simp only [offK, depth] at hi ⊢; rw [blkN1_eq]; norm_num at hi ⊢; split_ifs <;> omega
      · simp only [offK, depth] at hi ⊢; rw [blkN1_eq]; norm_num at hi ⊢; split_ifs <;> omega
      · simp only [offK, depth] at hi ⊢; rw [blkN1_eq]; norm_num at hi ⊢; split_ifs <;> omega
    · intro c i col hi
      unfold B1gen
      rw [if_pos (by rw [← depth_eq_depN]; exact hi), offK_eq_offN]
    · intro c i col hi hb
      unfold B1gen
      rw [if_neg (by rw [← depth_eq_depN]; omega),
        if_neg (fun h => hb (Fin.ext (by simp only [bl]; exact h)))]
  exact ⟨B1gen_isKNskel p k ρ hp hk hρ0, hY.isNet0⟩

end Z3NetKN.Proofs
