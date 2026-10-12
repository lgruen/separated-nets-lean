/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `def:B` (`𝓑²`), `prop:Bnet`.
Entry Dim3 (`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3Gauge
public import Z3Net.D3Rem

@[expose] public section

/-!
# Entry Dim3, part 4: the explicit net `𝓑²_{k,p,ρ}` (`B2gen_net`)

`t = 0`: the frame graph form is `t = 0` (`frameGF_T0`), so is its product with the invertible
lower-triangular column gauge (`T0_mul_right`, `isUnit_of_lower`), and resetting the coarse rows
and the diagonal blocks preserves it (`T0_of_scale` with all scalings `1`). The skeleton row is
computed column by column from the sparse columns of the gauge; it is entry S1's skeleton row,
and `B2_skel_iff` converts.
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset Z3NetKN.Frame

section B2

variable (p k ρ : ℕ)

local notation "m2" => 3 * k + 2

lemma blkN2_eq (x : ℕ) : blkN 2 k x = if x < k + 1 then 0 else if x < 2 * k + 2 then 1 else 2 := by
  simp only [blkN, depN]; norm_num; congr 2; ring

/-- Support of the gauge: lower triangular inside the blocks. -/
lemma gB2_supp (r col : Fin m2) (h : gaugeB2 p k ρ r col ≠ 0) :
    (col : ℕ) ≤ r ∧ blkN 2 k col = blkN 2 k r := by
  rw [blkN2_eq, blkN2_eq]
  unfold gaugeB2 at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;>
    first
    | exact absurd rfl h
    | (subst_vars; exact ⟨le_refl _, rfl⟩)
    | (constructor <;> [omega; (split_ifs <;> omega)])

lemma gB2_lower (i j : Fin m2) (hij : i < j) : gaugeB2 p k ρ i j = 0 := by
  by_contra h
  have := (gB2_supp p k ρ i j h).1
  have : (i : ℕ) < j := hij
  omega

variable [Fact p.Prime]

lemma aB2_eq (j : ℕ) : aB2 p k j = A2 p k j := by
  unfold aB2 A2
  rw [show frameGrN 2 p k 2 = frameGF 2 p k 2 from frameGrN_eq 2 p k (by norm_num) 2]

lemma aB2_k : aB2 p k k ≠ 0 := by
  have := pivot2 p k 0 (by simp)
  rw [aB2_eq]; simpa [offK] using this

lemma aB2_2k : aB2 p k (2 * k + 1) ≠ 0 := by
  have := pivot2 p k 1 (by simp)
  rw [aB2_eq]
  have ho : offK (depth 2 k) 1 + k = 2 * k + 1 := by simp [offK, depth]; ring
  rwa [ho] at this

lemma gB2_diag (hρ : (ρ : ZMod p) ≠ 0) (i : Fin m2) : gaugeB2 p k ρ i i ≠ 0 := by
  have h1 := aB2_k p k
  have h2 := aB2_2k p k
  unfold gaugeB2
  split_ifs <;> first
    | exact one_ne_zero
    | exact mul_ne_zero hρ (inv_ne_zero h1)
    | exact mul_ne_zero (pow_ne_zero 2 hρ) (inv_ne_zero h2)
    | omega

lemma frameGrN2_row (t : Fin m2) : frameGrN 2 p k 2 ⟨k, by omega⟩ t = aB2 p k t := by
  unfold aB2 ent; rw [dif_pos ⟨by omega, t.isLt⟩]

lemma gB2_x (t col : Fin m2) (hcol : (col : ℕ) < k) :
    gaugeB2 p k ρ t col =
      if (t : ℕ) = k then -(aB2 p k col) * (aB2 p k k)⁻¹ else if t = col then 1 else 0 := by
  unfold gaugeB2
  rw [if_pos hcol.le]
  by_cases ht : (t : ℕ) = k
  · simp only [ht, if_true, show ¬ ((col : ℕ) = k) by omega, if_false]
    rfl
  · rw [if_neg ht, if_neg ht]

lemma gB2_xk (t col : Fin m2) (hcol : (col : ℕ) = k) :
    gaugeB2 p k ρ t col = if (t : ℕ) = k then (ρ : ZMod p) * (aB2 p k k)⁻¹ else 0 := by
  unfold gaugeB2
  rw [if_pos hcol.le]
  by_cases ht : (t : ℕ) = k
  · rw [if_pos ht, if_pos hcol, if_pos ht]
  · rw [if_neg ht, if_neg ht, if_neg (fun e => ht (by rw [e]; exact hcol))]

lemma gB2_y (t col : Fin m2) (hcol : k < (col : ℕ) ∧ (col : ℕ) < 2 * k + 1) :
    gaugeB2 p k ρ t col =
      if (t : ℕ) = 2 * k + 1 then -(aB2 p k col) * (aB2 p k (2 * k + 1))⁻¹
      else if t = col then 1 else 0 := by
  unfold gaugeB2
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases ht : (t : ℕ) = 2 * k + 1
  · simp only [ht, if_true, show ¬ ((col : ℕ) = 2 * k + 1) by omega, if_false]
    rfl
  · rw [if_neg ht, if_neg ht]

lemma gB2_yk (t col : Fin m2) (hcol : (col : ℕ) = 2 * k + 1) :
    gaugeB2 p k ρ t col =
      if (t : ℕ) = 2 * k + 1 then (ρ : ZMod p) ^ 2 * (aB2 p k (2 * k + 1))⁻¹ else 0 := by
  unfold gaugeB2
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases ht : (t : ℕ) = 2 * k + 1
  · rw [if_pos ht, if_pos hcol, if_pos ht]
  · rw [if_neg ht, if_neg ht, if_neg (fun e => ht (by rw [e]; exact hcol))]

lemma B2gen_off (c : Fin 3) (i col : Fin m2) (hi : ¬ (i : ℕ) < depN 2 k c)
    (hb : blkN 2 k col ≠ c) :
    B2gen p k ρ c i col = (frameGrN 2 p k c * gaugeB2 p k ρ) i col := by
  unfold B2gen; rw [if_neg hi, if_neg hb]

/-- The skeleton row of `𝓑²`. -/
lemma B2gen_skel (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m2) :
    B2gen p k ρ 2 ⟨k, by omega⟩ col =
      if (col : ℕ) = k then (ρ : ZMod p) else if (col : ℕ) = 2 * k + 1 then (ρ : ZMod p) ^ 2 else 0 := by
  have h1 := aB2_k p k
  have h2 := aB2_2k p k
  have hc := col.isLt
  have hi : ¬ ((⟨k, by omega⟩ : Fin m2) : ℕ) < depN 2 k ((2 : Fin 3) : ℕ) := by simp [depN]
  let tk : Fin m2 := ⟨k, by omega⟩
  let t2k : Fin m2 := ⟨2 * k + 1, by omega⟩
  rcases (show (col : ℕ) < k ∨ (col : ℕ) = k ∨ (k < (col : ℕ) ∧ (col : ℕ) < 2 * k + 1) ∨
      (col : ℕ) = 2 * k + 1 ∨ 2 * k + 2 ≤ (col : ℕ) by omega) with h | h | h | h | h
  · have hb : blkN 2 k col = 0 := by rw [blkN2_eq, if_pos (by omega)]
    rw [B2gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 2 * k + 1 by omega)]
    rw [mul_supp2 _ _ _ _ col tk (Fin.ne_of_val_ne (by simp [tk]; omega))
      (by intro t ht1 ht2
          rw [gB2_x p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [tk]; omega))),
            if_neg ht1])]
    rw [gB2_x p k ρ col col h, gB2_x p k ρ tk col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [tk])]
    simp only [Fin.val_two, frameGrN2_row]
    simp only [tk]
    field_simp; ring
  · have hb : blkN 2 k col = 0 := by rw [blkN2_eq, if_pos (by omega)]
    rw [B2gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_pos h]
    rw [mul_supp1 _ _ _ _ tk
      (by intro t ht
          rw [gB2_xk p k ρ t col h, if_neg (fun e => ht (Fin.ext (by simp [tk]; omega)))])]
    rw [gB2_xk p k ρ tk col h, if_pos (by simp [tk])]
    simp only [Fin.val_two, frameGrN2_row]
    simp only [tk]
    field_simp
  · have hb : blkN 2 k col = 1 := by rw [blkN2_eq, if_neg (by omega), if_pos (by omega)]
    rw [B2gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 2 * k + 1 by omega)]
    rw [mul_supp2 _ _ _ _ col t2k (Fin.ne_of_val_ne (by simp [t2k]; omega))
      (by intro t ht1 ht2
          rw [gB2_y p k ρ t col h, if_neg (fun e => ht2 (Fin.ext (by simp [t2k]; omega))),
            if_neg ht1])]
    rw [gB2_y p k ρ col col h, gB2_y p k ρ t2k col h, if_neg (by omega), if_pos rfl,
      if_pos (by simp [t2k])]
    simp only [Fin.val_two, frameGrN2_row]
    simp only [t2k]
    field_simp; ring
  · have hb : blkN 2 k col = 1 := by rw [blkN2_eq, if_neg (by omega), if_pos (by omega)]
    rw [B2gen_off p k ρ 2 _ col hi (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_pos h]
    rw [mul_supp1 _ _ _ _ t2k
      (by intro t ht
          rw [gB2_yk p k ρ t col h, if_neg (fun e => ht (Fin.ext (by simp [t2k]; omega)))])]
    rw [gB2_yk p k ρ t2k col h, if_pos (by simp [t2k])]
    simp only [Fin.val_two, frameGrN2_row]
    simp only [t2k]
    have h2' : aB2 p k col ≠ 0 := by rw [h]; exact h2
    rw [← h]; field_simp
  · have hb : blkN 2 k col = 2 := by rw [blkN2_eq, if_neg (by omega), if_neg (by omega)]
    unfold B2gen
    rw [if_neg hi, if_pos (by rw [hb]; simp), if_neg (show ¬ (col : ℕ) = k by omega),
      if_neg (show ¬ (col : ℕ) = 2 * k + 1 by omega)]

end B2

end Z3NetKN.Proofs.D3

namespace Z3NetKN.Proofs

open Matrix Finset Z3NetKN.Frame D3

/-- **`def:B` (`𝓑²`) and `prop:Bnet`.** -/
theorem B2gen_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : ¬ p ∣ ρ) :
    IsKNskel 2 p k (skB2 ρ) (B2gen p k ρ) ∧
      IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) (B2gen p k ρ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρ0 : (ρ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hρ
  have hsum := depth_sum 2 k (by norm_num)
  have hF := frame_T0 (ZMod p) (3 * k + 2) (by omega)
  have hG : T0 (fun c : Fin 3 => frameGrN 2 p k c) := by
    have : (fun c : Fin 3 => frameGrN 2 p k c) = gr (frameF (ZMod p) (3 * k + 2)) (depth 2 k) :=
      funext (frameGrN_eq 2 p k (by norm_num))
    rw [this]; exact T0_gr hF _ hsum
  have hU : IsUnit (gaugeB2 p k ρ) :=
    isUnit_of_lower _ (gB2_lower p k ρ) (gB2_diag p k ρ hρ0)
  have hX := T0_mul_right hG _ hU
  have hGc : ∀ (c : Fin 3) (j col : Fin (3 * k + 2)), (j : ℕ) < depth 2 k c →
      frameGrN 2 p k c j col = if (col : ℕ) = offK (depth 2 k) c + j then 1 else 0 := by
    intro c j col hj
    rw [frameGrN_eq 2 p k (by norm_num) c]
    exact gr_coarse hF _ hsum c j col hj
  let bl : Fin (3 * k + 2) → Fin 3 := fun col => ⟨blkN 2 k col, blkN_lt 2 k col⟩
  have hY : T0 (B2gen p k ρ) := by
    refine T0_of_scale hX (depth 2 k) hsum bl ?_ ?_ ?_ (fun _ _ => 1) (fun _ _ _ => one_ne_zero) ?_
    · intro col
      have hc := col.isLt
      simp only [bl, blkN2_eq]
      rcases (show (col : ℕ) < k + 1 ∨ (k + 1 ≤ (col : ℕ) ∧ (col : ℕ) < 2 * k + 2) ∨
          2 * k + 2 ≤ (col : ℕ) by omega) with h | h | h
      · simp only [if_pos h]; exact ⟨col, by simp [depth]; omega, by simp [offK]⟩
      · simp only [if_neg (show ¬ (col : ℕ) < k + 1 by omega), if_pos h.2]
        exact ⟨(col : ℕ) - (k + 1), by simp [depth]; omega, by simp [offK, depth]; omega⟩
      · simp only [if_neg (show ¬ (col : ℕ) < k + 1 by omega),
          if_neg (show ¬ (col : ℕ) < 2 * k + 2 by omega)]
        exact ⟨(col : ℕ) - (2 * k + 2), by simp [depth]; omega, by simp [offK, depth]; omega⟩
    · intro c i col hi hne
      have hlt := offK_lt (depth 2 k) hsum c i hi
      have e := mul_unit_row (frameGrN 2 p k c) (gaugeB2 p k ρ) i (offK (depth 2 k) c + i) hlt
        (fun t => hGc c i t hi) col
      rw [e] at hne
      obtain ⟨h1, h2⟩ := gB2_supp p k ρ _ col hne
      refine ⟨Fin.ext ?_, h1⟩
      simp only [bl]
      rw [h2]
      obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
      · simp only [offK, depth] at hi ⊢; rw [blkN2_eq]; norm_num at hi ⊢; split_ifs <;> omega
      · simp only [offK, depth] at hi ⊢; rw [blkN2_eq]; norm_num at hi ⊢; split_ifs <;> omega
      · simp only [offK, depth] at hi ⊢; rw [blkN2_eq]; norm_num at hi ⊢; split_ifs <;> omega
    · intro c i col hi
      unfold B2gen
      rw [if_pos (by rw [← depth_eq_depN]; exact hi), offK_eq_offN]
    · intro c i col hi hb
      unfold B2gen
      rw [if_neg (by rw [← depth_eq_depN]; omega),
        if_neg (fun h => hb (Fin.ext (by simp only [bl]; exact h))), one_mul]
  refine ⟨?_, hY.isNet0⟩
  apply (B2_skel_iff p k ρ (B2gen p k ρ)).1
  refine ⟨?_, ?_⟩
  · intro c j hj col hcol
    unfold ent
    rw [dif_pos ⟨by fin_cases c <;> simp [depthS1] at hj ⊢ <;> omega, hcol⟩]
    unfold B2gen
    rw [if_pos (by fin_cases c <;> simp [depthS1, depN] at hj ⊢ <;> omega)]
    have : offN 2 k c = offS1 k c := by
      fin_cases c <;> simp [offN, offS1, depN] <;> ring
    rw [this]
  · intro z hz col hcol
    have hz2 : z = 2 := Fin.ext (by simp; omega)
    subst hz2
    have hcol' : col < 3 * k + 2 := hcol
    unfold ent
    rw [dif_pos ⟨by omega, hcol'⟩, B2gen_skel p k ρ hρ0 ⟨col, hcol'⟩, skRowS1_eq k ρ col hcol']
    simp only
    split_ifs <;> push_cast <;> rfl

end Z3NetKN.Proofs
