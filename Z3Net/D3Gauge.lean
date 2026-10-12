/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `def:B`, `prop:Bnet` (moves of
`lem:box` in kernel form). Entry Dim3 (`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.Dim3Defs
public import Z3Net.KNBnet1

@[expose] public section

/-!
# Entry Dim3, part 3: the moves of `lem:box` in kernel form, and the frame of `ChallengeDim3`

* `T0_of_scale` — the moves (a), (b) and (c) of `lem:box` at once, in kernel form (`T0`: every box
  matrix has trivial kernel), for three coordinates: let `X` be `t = 0`, let the coarse rows of
  `X c` be supported on the own block at levels `≤` their own, and let `Y` be in graph form (coarse
  rows unit vectors) with offset rows `Y c i col = s c d · X c i col` on every other block `d`
  (`s c d ≠ 0`) and arbitrary on the own block. Then `Y` is `t = 0`. (The kernel argument scales
  the index blocks: for at most one "over-full" coordinate `c` by `s c ·`; with two over-full
  coordinates the vector lives on one block and all conditions are homogeneous.)
* `isUnit_of_lower` — a lower-triangular matrix with nonzero diagonal is invertible.
* `frameGrN_eq` — the frame graph form of `ChallengeDim3` is `gr frameF (depth r k)` of `KNFrame`.
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset Z3NetKN.Frame

section Generic

variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

lemma fin3_third (a b c e : Fin 3) (hce : c ≠ e) (ha1 : a ≠ c) (ha2 : a ≠ e) (hb1 : b ≠ c)
    (hb2 : b ≠ e) : a = b := by
  revert a b c e; decide

/-- **Moves (a), (b), (c) of `lem:box`, kernel form.** -/
theorem T0_of_scale {X Y : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) (bl : Fin m → Fin 3)
    (hbl : ∀ col : Fin m, ∃ j < K (bl col), (col : ℕ) = offK K (bl col) + j)
    (hXc : ∀ c (i col : Fin m), (i : ℕ) < K c → X c i col ≠ 0 →
      bl col = c ∧ (col : ℕ) ≤ offK K c + i)
    (hYc : ∀ c (i col : Fin m), (i : ℕ) < K c → Y c i col = if (col : ℕ) = offK K c + i then 1 else 0)
    (s : Fin 3 → Fin 3 → 𝕜) (hs : ∀ c d, c ≠ d → s c d ≠ 0)
    (hYo : ∀ c (i col : Fin m), K c ≤ (i : ℕ) → bl col ≠ c → Y c i col = s c (bl col) * X c i col) :
    T0 Y := by
  intro d hd v hv
  -- coarse digits killed by the box
  have F2 : ∀ c (j : ℕ) (hj : j < K c), j < d c → v ⟨offK K c + j, offK_lt K hK c j hj⟩ = 0 := by
    intro c j hj hjd
    have hjm : j < m := lt_of_lt_of_le hj (by
      have : K c ≤ K 0 + K 1 + K 2 := by fin_cases c <;> simp <;> omega
      omega)
    have := hv c ⟨j, hjm⟩ hjd
    rwa [mulVec_coarse (Y c) (offK K c) (K c) (fun j col hj => hYc c j col hj) v ⟨j, hjm⟩ hj
      (offK_lt K hK c j hj)] at this
  have F1 : ∀ c, K c < d c → ∀ col : Fin m, bl col = c → v col = 0 := by
    intro c hc col hb
    obtain ⟨j, hj, hcol⟩ := hbl col
    rw [hb] at hj hcol
    have := F2 c j hj (by omega)
    rwa [show (⟨offK K c + j, offK_lt K hK c j hj⟩ : Fin m) = col from Fin.ext hcol.symm] at this
  -- the block scaling
  suffices H : ∃ t : Fin 3 → 𝕜, (∀ e, t e ≠ 0) ∧ ∀ c, K c < d c → ∃ u : 𝕜, u ≠ 0 ∧
      ∀ col : Fin m, bl col ≠ c → v col ≠ 0 → t (bl col) = u * s c (bl col) by
    obtain ⟨t, ht0, ht⟩ := H
    set v' : Fin m → 𝕜 := fun col => t (bl col) * v col with hv'
    have hz : v' = 0 := by
      apply hX d hd v'
      intro c i hi
      by_cases hiK : (i : ℕ) < K c
      · simp only [mulVec, dotProduct]
        apply Finset.sum_eq_zero
        intro col _
        by_cases hx : X c i col = 0
        · rw [hx, zero_mul]
        · obtain ⟨hb, hle⟩ := hXc c i col hiK hx
          obtain ⟨j, hj, hcol⟩ := hbl col
          rw [hb] at hj hcol
          have h0 := F2 c j hj (by omega)
          rw [show (⟨offK K c + j, offK_lt K hK c j hj⟩ : Fin m) = col from Fin.ext hcol.symm] at h0
          show X c i col * (t (bl col) * v col) = 0
          rw [h0]; ring
      · have hcd : K c < d c := by omega
        obtain ⟨u, -, hu⟩ := ht c hcd
        have hsum : (X c *ᵥ v') i = u * (Y c *ᵥ v) i := by
          simp only [mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro col _
          by_cases hb : bl col = c
          · have h0 := F1 c hcd col hb
            simp [hv', h0]
          · by_cases hv0 : v col = 0
            · simp [hv', hv0]
            · rw [hYo c i col (by omega) hb]
              simp only [hv']
              rw [hu col hb hv0]; ring
        rw [hsum, hv c i hi, mul_zero]
    funext col
    have := congrFun hz col
    simp only [hv', Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (ht0 _)
    · exact h
  by_cases hA : ∃ c, K c < d c ∧ ∀ e, K e < d e → e = c
  · obtain ⟨c, -, hc⟩ := hA
    refine ⟨fun e => if e = c then 1 else s c e, ?_, ?_⟩
    · intro e
      by_cases he : e = c
      · simp [he]
      · simp only [he, if_false]; exact hs c e (Ne.symm he)
    · intro c' hc'
      have := hc c' hc'
      subst this
      refine ⟨1, one_ne_zero, ?_⟩
      intro col hb _
      simp [hb]
  · push Not at hA
    refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    intro c hc
    obtain ⟨e, he, hec⟩ := hA c hc
    by_cases hex : ∃ col : Fin m, bl col ≠ c ∧ v col ≠ 0
    · obtain ⟨col0, hb0, hv0⟩ := hex
      have hf2 : bl col0 ≠ e := fun h => hv0 (F1 e he col0 h)
      refine ⟨(s c (bl col0))⁻¹, inv_ne_zero (hs c _ (Ne.symm hb0)), ?_⟩
      intro col hb hv1
      have hb2 : bl col ≠ e := fun h => hv1 (F1 e he col h)
      have heq : bl col = bl col0 := fin3_third _ _ c e (Ne.symm hec) hb hb2 hb0 hf2
      rw [heq, inv_mul_cancel₀ (hs c _ (Ne.symm hb0))]
    · push Not at hex
      exact ⟨1, one_ne_zero, fun col hb hv1 => absurd (hex col hb) hv1⟩

/-- A lower-triangular matrix with nonzero diagonal is a unit. -/
lemma isUnit_of_lower (U : Matrix (Fin m) (Fin m) 𝕜) (hlow : ∀ i j : Fin m, i < j → U i j = 0)
    (hdiag : ∀ i, U i i ≠ 0) : IsUnit U := by
  have hbt : U.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hlow i j hij
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular U hbt]
  exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hdiag i)

/-- A product with a graph-form coarse row reads a row of the right factor. -/
lemma mul_unit_row (A U : Matrix (Fin m) (Fin m) 𝕜) (i : Fin m) (o : ℕ) (ho : o < m)
    (hA : ∀ t : Fin m, A i t = if (t : ℕ) = o then 1 else 0) (col : Fin m) :
    (A * U) i col = U ⟨o, ho⟩ col := by
  rw [mul_apply, Finset.sum_eq_single ⟨o, ho⟩]
  · rw [hA, if_pos rfl, one_mul]
  · intro t _ ht
    rw [hA, if_neg (fun h => ht (Fin.ext h)), zero_mul]
  · simp

/-- A product whose right factor's column `col` is supported on one row. -/
lemma mul_supp1 (A U : Matrix (Fin m) (Fin m) 𝕜) (i col t1 : Fin m)
    (h : ∀ t, t ≠ t1 → U t col = 0) : (A * U) i col = A i t1 * U t1 col := by
  rw [mul_apply, Finset.sum_eq_single t1 (fun t _ ht => by rw [h t ht, mul_zero]) (by simp)]

/-- A product whose right factor's column `col` is supported on two rows. -/
lemma mul_supp2 (A U : Matrix (Fin m) (Fin m) 𝕜) (i col t1 t2 : Fin m) (h12 : t1 ≠ t2)
    (h : ∀ t, t ≠ t1 → t ≠ t2 → U t col = 0) :
    (A * U) i col = A i t1 * U t1 col + A i t2 * U t2 col := by
  rw [mul_apply]
  exact Fintype.sum_eq_add t1 t2 h12 (fun t ⟨h1, h2⟩ => by rw [h t h1 h2, mul_zero])

/-- A product whose right factor's column `col` is supported on three rows. -/
lemma mul_supp3 (A U : Matrix (Fin m) (Fin m) 𝕜) (i col t1 t2 t3 : Fin m) (h12 : t1 ≠ t2)
    (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) (h : ∀ t, t ≠ t1 → t ≠ t2 → t ≠ t3 → U t col = 0) :
    (A * U) i col = A i t1 * U t1 col + A i t2 * U t2 col + A i t3 * U t3 col := by
  rw [mul_apply, ← Finset.sum_subset (Finset.subset_univ {t1, t2, t3})]
  · rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton, add_assoc]
  · intro t _ ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [h t ht.1 ht.2.1 ht.2.2, mul_zero]

end Generic

/-! ## The frame of `ChallengeDim3` -/

lemma depth_eq_depN (r k : ℕ) (c : Fin 3) : depth r k c = depN r k c := rfl

lemma offK_eq_offN (r k : ℕ) (c : Fin 3) : offK (depth r k) c = offN r k c := by
  fin_cases c <;> rfl

lemma blkN_lt (r k i : ℕ) : blkN r k i < 3 := by
  unfold blkN; split_ifs <;> omega

lemma frameZD_eq (m : ℕ) (c : Fin 3) : frameZD m c = frameZ m c := by
  fin_cases c <;> rfl

lemma ent_fin {R : Type*} [Zero R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (i col : Fin m) (j : ℕ)
    (hj : j = i) : ent A j col = A i col := by
  subst hj; unfold ent; rw [dif_pos ⟨i.isLt, col.isLt⟩]

lemma frameBoxD_eq (r p k : ℕ) (hr : r ≤ 3) :
    (frameBoxD r k).map (Int.cast : ℤ → ZMod p) =
      Z3Net.boxMatrix (fun c => (frameZ (3 * k + r) c).map (Int.cast : ℤ → ZMod p)) (depth r k) := by
  ext i col
  have hs := depth_sum r k hr
  have hd0 : depth r k 0 = depN r k 0 := rfl
  have hd1 : depth r k 1 = depN r k 1 := rfl
  have e0 : frameZD (3 * k + r) 0 = frameZ (3 * k + r) 0 := rfl
  have e1 : frameZD (3 * k + r) 1 = frameZ (3 * k + r) 1 := rfl
  have e2 : frameZD (3 * k + r) 2 = frameZ (3 * k + r) 2 := rfl
  simp only [Matrix.map_apply, frameBoxD, Z3Net.boxMatrix, blkN, hd0, hd1]
  by_cases h0 : (i : ℕ) < depN r k 0
  · simp only [h0, if_true, Matrix.map_apply]
    rw [e0, ent_fin _ i col _ (by simp [offN])]
  · by_cases h1 : (i : ℕ) < depN r k 0 + depN r k 1
    · simp only [h0, h1, if_true, if_false, Matrix.map_apply]
      rw [e1, ent_fin _ ⟨(i : ℕ) - depN r k 0, by omega⟩ col _ (by simp [offN])]
    · simp only [h0, h1, if_false, Matrix.map_apply]
      rw [e2, ent_fin _ ⟨(i : ℕ) - depN r k 0 - depN r k 1, by omega⟩ col _ (by simp [offN]; omega)]

lemma frameGrN_eq (r p k : ℕ) [Fact p.Prime] (hr : r ≤ 3) (c : Fin 3) :
    frameGrN r p k c = gr (frameF (ZMod p) (3 * k + r)) (depth r k) c := by
  unfold frameGrN gr
  rw [frameBoxD_eq r p k hr, frameZD_eq]
  rfl

end Z3NetKN.Proofs.D3
