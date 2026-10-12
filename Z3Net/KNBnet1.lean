module
public import Z3Net.KNBnet2

@[expose] public section

/-!
# `B1_net`: the all-`p` family for `m = 3k + 1` (net part)

Frame graph form `G = frameGF 1 p k` (depths `(k+1, k, k)`, offsets `0, k+1, 2k+1`), skeleton
rows `Y = G_y[k]`, `Z = G_z[k]`.  Box minors give `Y_k, Z_k ≠ 0` (boxes `(k,k+1,k)`, `(k,k,k+1)`),
`Y_k Z_{k-1} - Y_{k-1} Z_k ≠ 0` (box `(k-1,k+1,k+1)`), `Z_{2k} ≠ 0` (box `(k+1,k-1,k+1)`),
`Y_{3k} ≠ 0` (box `(k+1,k+1,k-1)`).  With `α = ρ Y_k / Z_k` the lower-triangular row moves
`x_k ← ρ⁻¹ Y|_x`, `x_{k-1} ← (α Z - ρ Y)|_{x, < k}`, `y_k ← Y - Y|_y`, `y_{k-1} ← α Z|_y`,
`z_k ← α Z - (α Z + Y)|_z`, `z_{k-1} ← Y|_z` give
`y_k = ρ x_k + z_{k-1}`, `z_k = ρ² x_k + x_{k-1} + y_{k-1} - z_{k-1}`; re-taking the graph form
gives skeleton rows `skB1 ρ`.
-/

namespace Z3NetKN.Frame

open Matrix Finset

section B1

variable (p k : ℕ) [Fact p.Prime]

local notation "m1" => 3 * k + 1

lemma depth1_0 : depth 1 k 0 = k + 1 := by simp [depth]
lemma depth1_1 : depth 1 k 1 = k := by simp [depth]
lemma depth1_2 : depth 1 k 2 = k := by simp [depth]
lemma offK1_0 : offK (depth 1 k) 0 = 0 := by simp [offK]
lemma offK1_1 : offK (depth 1 k) 1 = k + 1 := by simp [offK, depth]
lemma offK1_2 : offK (depth 1 k) 2 = 2 * k + 1 := by simp [offK, depth]; ring

lemma depth1_sum : depth 1 k 0 + depth 1 k 1 + depth 1 k 2 = m1 := depth_sum 1 k (by norm_num)

lemma G1c (c : Fin 3) (j col : Fin m1) (hj : (j : ℕ) < depth 1 k c) :
    frameGF 1 p k c j col = if (col : ℕ) = offK (depth 1 k) c + j then 1 else 0 :=
  frameGF_coarse 1 p k (by norm_num) (by omega) c j col hj

/-- The `y`- and `z`-skeleton rows of the frame graph form. -/
noncomputable def Y1 (n : ℕ) : ZMod p := ent (frameGF 1 p k 1) k n
noncomputable def Z1 (n : ℕ) : ZMod p := ent (frameGF 1 p k 2) k n

lemma Y1_eq (hk : 1 ≤ k) (col : Fin m1) : frameGF 1 p k 1 ⟨k, by omega⟩ col = Y1 p k col := by
  unfold Y1 ent; rw [dif_pos ⟨by omega, col.isLt⟩]

lemma Z1_eq (hk : 1 ≤ k) (col : Fin m1) : frameGF 1 p k 2 ⟨k, by omega⟩ col = Z1 p k col := by
  unfold Z1 ent; rw [dif_pos ⟨by omega, col.isLt⟩]

lemma box3_le1 (a b c : ℕ) (ha : a ≤ k + 2) (hb : b ≤ k + 1) (hc : c ≤ k + 1) :
    ∀ e, box3 a b c e ≤ depth 1 k e + 1 := by
  intro e; rcases e with ⟨_ | _ | _ | e, he⟩ <;> simp [box3, depth] <;> omega

section Pivots

variable (hk : 1 ≤ k)
include hk

lemma piv_Yk : Y1 p k k ≠ 0 := by
  have h := pivot_single (frameGF_T0 1 p k (by norm_num) (by omega)) (depth 1 k) (depth1_sum k)
    (G1c p k) (box3 k (k + 1) k) (by rw [box3_sum]; ring) (box3_le1 k _ _ _ (by omega) (by omega) (by omega))
    ⟨k, by omega⟩
    (by intro c l hl hld; rcases c with ⟨_ | _ | _ | c, hc⟩ <;> simp [box3, offK, depth] at hl hld ⊢ <;> omega)
    1 (by intro c hc; rcases c with ⟨_ | _ | _ | c, hc'⟩ <;> simp [box3, depth] at hc ⊢ <;> omega)
    ⟨k, by omega⟩ (by simp [depth])
  rwa [Y1_eq p k hk] at h

lemma piv_Zk : Z1 p k k ≠ 0 := by
  have h := pivot_single (frameGF_T0 1 p k (by norm_num) (by omega)) (depth 1 k) (depth1_sum k)
    (G1c p k) (box3 k k (k + 1)) (by rw [box3_sum]; ring) (box3_le1 k _ _ _ (by omega) (by omega) (by omega))
    ⟨k, by omega⟩
    (by intro c l hl hld; rcases c with ⟨_ | _ | _ | c, hc⟩ <;> simp [box3, offK, depth] at hl hld ⊢ <;> omega)
    2 (by intro c hc; rcases c with ⟨_ | _ | _ | c, hc'⟩ <;> simp [box3, depth] at hc ⊢ <;> omega)
    ⟨k, by omega⟩ (by simp [depth])
  rwa [Z1_eq p k hk] at h

lemma piv_Z2k : Z1 p k (2 * k) ≠ 0 := by
  have h := pivot_single (frameGF_T0 1 p k (by norm_num) (by omega)) (depth 1 k) (depth1_sum k)
    (G1c p k) (box3 (k + 1) (k - 1) (k + 1)) (by rw [box3_sum]; omega)
    (box3_le1 k _ _ _ (by omega) (by omega) (by omega))
    ⟨2 * k, by omega⟩
    (by intro c l hl hld; rcases c with ⟨_ | _ | _ | c, hc⟩ <;> simp [box3, offK, depth] at hl hld ⊢ <;> omega)
    2 (by intro c hc; rcases c with ⟨_ | _ | _ | c, hc'⟩ <;> simp [box3, depth] at hc ⊢ <;> omega)
    ⟨k, by omega⟩ (by simp [depth])
  rwa [Z1_eq p k hk] at h

lemma piv_Y3k : Y1 p k (3 * k) ≠ 0 := by
  have h := pivot_single (frameGF_T0 1 p k (by norm_num) (by omega)) (depth 1 k) (depth1_sum k)
    (G1c p k) (box3 (k + 1) (k + 1) (k - 1)) (by rw [box3_sum]; omega)
    (box3_le1 k _ _ _ (by omega) (by omega) (by omega))
    ⟨3 * k, by omega⟩
    (by intro c l hl hld; rcases c with ⟨_ | _ | _ | c, hc⟩ <;> simp [box3, offK, depth] at hl hld ⊢ <;> omega)
    1 (by intro c hc; rcases c with ⟨_ | _ | _ | c, hc'⟩ <;> simp [box3, depth] at hc ⊢ <;> omega)
    ⟨k, by omega⟩ (by simp [depth])
  rwa [Y1_eq p k hk] at h

/-- The `2 × 2` pivot of the `x` block (box `(k-1, k+1, k+1)`). -/
lemma piv_det : Y1 p k k * Z1 p k (k - 1) - Y1 p k (k - 1) * Z1 p k k ≠ 0 := by
  intro h0
  have hG := frameGF_T0 1 p k (by norm_num) (by omega)
  let n1 : Fin m1 := ⟨k - 1, by omega⟩
  let n2 : Fin m1 := ⟨k, by omega⟩
  let v : Fin m1 → ZMod p := Y1 p k k • Pi.single n1 1 - Y1 p k (k - 1) • Pi.single n2 1
  have hv := kernel_test hG (depth 1 k) (depth1_sum k) (G1c p k) (box3 (k - 1) (k + 1) (k + 1))
    (by rw [box3_sum]; omega) (box3_le1 k _ _ _ (by omega) (by omega) (by omega)) v
    (by
      intro c l hl hld
      simp only [v, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, n1, n2, Fin.ext_iff]
      rcases c with ⟨_ | _ | _ | c, hc⟩ <;> simp [box3, offK, depth] at hl hld ⊢ <;>
        rw [if_neg (by omega), if_neg (by omega)] <;> simp)
    (by
      intro c hc s hs
      have hcs : c = 1 ∨ c = 2 := by
        rcases c with ⟨_ | _ | _ | c, hc'⟩ <;> simp [box3, depth] at hc ⊢ <;> omega
      have hs' : s = ⟨k, by omega⟩ := by
        apply Fin.ext; rw [hs]; rcases hcs with rfl | rfl <;> simp [depth]
      simp only [v, mulVec_sub, mulVec_smul, mulVec_single_one, Pi.sub_apply, Pi.smul_apply,
        Matrix.col_apply, smul_eq_mul, hs']
      rcases hcs with rfl | rfl
      · rw [Y1_eq p k hk, Y1_eq p k hk]; ring
      · rw [Z1_eq p k hk, Z1_eq p k hk]
        simp only [n1, n2]
        linear_combination h0)
  have := congrFun hv n1
  simp only [v, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, n1, n2, Fin.ext_iff, smul_eq_mul,
    Pi.zero_apply] at this
  rw [if_pos trivial, if_neg (by omega)] at this
  simp only [mul_one, mul_zero] at this
  exact piv_Yk p k hk (by linear_combination this)

end Pivots

/-! ### Row moves -/

/-- `α = ρ Y_k / Z_k`. -/
noncomputable def al1 (ρ : ℕ) : ZMod p := (ρ : ZMod p) * Y1 p k k / Z1 p k k

noncomputable def bxk (ρ : ℕ) (j : Fin m1) : ZMod p :=
  if (j : ℕ) ≤ k then (ρ : ZMod p)⁻¹ * Y1 p k j else 0
noncomputable def bxk1 (ρ : ℕ) (j : Fin m1) : ZMod p :=
  if (j : ℕ) < k then al1 p k ρ * Z1 p k j - (ρ : ZMod p) * Y1 p k j else 0
noncomputable def byk (j : Fin m1) : ZMod p :=
  if (j : ℕ) = k then 1 else if (j : ℕ) < k then 0 - Y1 p k (k + 1 + j) else 0
noncomputable def byk1 (ρ : ℕ) (j : Fin m1) : ZMod p :=
  if (j : ℕ) < k then al1 p k ρ * Z1 p k (k + 1 + j) else 0
noncomputable def bzk (ρ : ℕ) (j : Fin m1) : ZMod p :=
  if (j : ℕ) = k then al1 p k ρ
  else if (j : ℕ) < k then 0 - (al1 p k ρ * Z1 p k (2 * k + 1 + j) + Y1 p k (2 * k + 1 + j)) else 0
noncomputable def bzk1 (j : Fin m1) : ZMod p :=
  if (j : ℕ) < k then Y1 p k (2 * k + 1 + j) else 0

/-- Row-moved frame: rows `k` and `k - 1` of every coordinate. -/
noncomputable def H1 (ρ : ℕ) : Fin 3 → Matrix (Fin m1) (Fin m1) (ZMod p) :=
  ![((frameGF 1 p k 0).updateRow ⟨k, by omega⟩ (bxk p k ρ ᵥ* frameGF 1 p k 0)).updateRow
      ⟨k - 1, by omega⟩ (bxk1 p k ρ ᵥ* frameGF 1 p k 0),
    ((frameGF 1 p k 1).updateRow ⟨k, by omega⟩ (byk p k ᵥ* frameGF 1 p k 1)).updateRow
      ⟨k - 1, by omega⟩ (byk1 p k ρ ᵥ* frameGF 1 p k 1),
    ((frameGF 1 p k 2).updateRow ⟨k, by omega⟩ (bzk p k ρ ᵥ* frameGF 1 p k 2)).updateRow
      ⟨k - 1, by omega⟩ (bzk1 p k ᵥ* frameGF 1 p k 2)]

section Moves

variable (hk : 1 ≤ k)
include hk

lemma al1_ne (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) : al1 p k ρ ≠ 0 := by
  unfold al1
  exact div_ne_zero (mul_ne_zero hρ (piv_Yk p k hk)) (piv_Zk p k hk)

lemma al1_spec (ρ : ℕ) : al1 p k ρ * Z1 p k k = (ρ : ZMod p) * Y1 p k k := by
  unfold al1
  rw [div_mul_cancel₀ _ (piv_Zk p k hk)]

/-- two successive lower-triangular row moves -/
lemma prefImp_two (X : Matrix (Fin m1) (Fin m1) (ZMod p)) (β γ : Fin m1 → ZMod p)
    (hβ : ∀ j : Fin m1, k < (j : ℕ) → β j = 0) (hβk : β ⟨k, by omega⟩ ≠ 0)
    (hγ : ∀ j : Fin m1, k - 1 < (j : ℕ) → γ j = 0) (hγk : γ ⟨k - 1, by omega⟩ ≠ 0) :
    PrefImp ((X.updateRow ⟨k, by omega⟩ (β ᵥ* X)).updateRow ⟨k - 1, by omega⟩ (γ ᵥ* X)) X := by
  have e : γ ᵥ* X = γ ᵥ* (X.updateRow ⟨k, by omega⟩ (β ᵥ* X)) :=
    (vecMul_updateRow_of_zero X _ _ γ (hγ _ (by simp; omega))).symm
  rw [e]
  refine PrefImp.trans (prefImp_updateRow _ _ γ (fun j hj => hγ j hj) hγk) ?_
  exact prefImp_updateRow X _ β (fun j hj => hβ j hj) hβk

lemma H1_T0 (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) : T0 (H1 p k ρ) := by
  have hG := frameGF_T0 1 p k (by norm_num) (by omega)
  have ha := al1_ne p k hk ρ hρ
  apply T0_of_prefImp hG
  intro c
  rcases c with ⟨_ | _ | _ | c, hc⟩
  · apply prefImp_two p k hk
    · intro j hj; simp only [bxk]; rw [if_neg (by omega)]
    · simp only [bxk]; rw [if_pos (by simp)]
      exact mul_ne_zero (inv_ne_zero hρ) (piv_Yk p k hk)
    · intro j hj; simp only [bxk1]; rw [if_neg (by omega)]
    · simp only [bxk1]; rw [if_pos (by simp; omega)]
      intro h0
      apply piv_det p k hk
      have h1 := al1_spec p k hk ρ
      have hZ := piv_Zk p k hk
      have : (ρ : ZMod p) * (Y1 p k k * Z1 p k (k - 1) - Y1 p k (k - 1) * Z1 p k k) = 0 := by
        have : (al1 p k ρ * Z1 p k (k - 1) - (ρ : ZMod p) * Y1 p k (k - 1)) * Z1 p k k = 0 := by
          rw [h0, zero_mul]
        linear_combination this - Z1 p k (k - 1) * h1
      exact (mul_eq_zero.mp this).resolve_left hρ
  · apply prefImp_two p k hk
    · intro j hj; simp only [byk]; rw [if_neg (by omega), if_neg (by omega)]
    · simp [byk]
    · intro j hj; simp only [byk1]; rw [if_neg (by omega)]
    · simp only [byk1]; rw [if_pos (by simp; omega)]
      refine mul_ne_zero ha ?_
      have := piv_Z2k p k hk
      rwa [show k + 1 + (k - 1) = 2 * k by omega]
  · apply prefImp_two p k hk
    · intro j hj; simp only [bzk]; rw [if_neg (by omega), if_neg (by omega)]
    · simp only [bzk]; rw [if_pos (by simp)]; exact ha
    · intro j hj; simp only [bzk1]; rw [if_neg (by omega)]
    · simp only [bzk1]; rw [if_pos (by simp; omega)]
      have := piv_Y3k p k hk
      rwa [show 2 * k + 1 + (k - 1) = 3 * k by omega]
  · omega

/-! Entries of the moved rows. -/

lemma vx (β : Fin m1 → ZMod p) (hβ : ∀ j : Fin m1, k < (j : ℕ) → β j = 0) (col : Fin m1) :
    (β ᵥ* frameGF 1 p k 0) col = if (col : ℕ) ≤ k then β col else 0 := by
  rw [vecMul_graph (frameGF 1 p k 0) (offK (depth 1 k) 0) (k + 1)
    (fun j col hj => G1c p k 0 j col (by rw [depth1_0]; exact hj)) β ⟨k + 1, by omega⟩ rfl
    (fun j hj => hβ j (by omega)) col]
  rw [hβ _ (by simp), zero_mul, zero_add]
  simp only [offK1_0]
  by_cases h : (col : ℕ) ≤ k
  · rw [dif_pos ⟨by omega, by omega⟩, if_pos h]; rfl
  · rw [dif_neg (by omega), if_neg h]

lemma vy (β : Fin m1 → ZMod p) (hβ : ∀ j : Fin m1, k < (j : ℕ) → β j = 0) (col : Fin m1) :
    (β ᵥ* frameGF 1 p k 1) col = β ⟨k, by omega⟩ * Y1 p k col +
      if k + 1 ≤ (col : ℕ) ∧ (col : ℕ) < 2 * k + 1 then β ⟨(col : ℕ) - (k + 1), by omega⟩ else 0 := by
  rw [vecMul_graph (frameGF 1 p k 1) (offK (depth 1 k) 1) k
    (fun j col hj => G1c p k 1 j col (by rw [depth1_1]; exact hj)) β ⟨k, by omega⟩ rfl
    (fun j hj => hβ j hj) col, Y1_eq p k hk]
  simp only [offK1_1]
  by_cases h : k + 1 ≤ (col : ℕ) ∧ (col : ℕ) < 2 * k + 1
  · rw [dif_pos ⟨by omega, by omega⟩, if_pos h]
  · rw [dif_neg (by omega), if_neg h]

lemma vz' (β : Fin m1 → ZMod p) (hβ : ∀ j : Fin m1, k < (j : ℕ) → β j = 0) (col : Fin m1) :
    (β ᵥ* frameGF 1 p k 2) col = β ⟨k, by omega⟩ * Z1 p k col +
      if 2 * k + 1 ≤ (col : ℕ) then β ⟨(col : ℕ) - (2 * k + 1), by omega⟩ else 0 := by
  rw [vecMul_graph (frameGF 1 p k 2) (offK (depth 1 k) 2) k
    (fun j col hj => G1c p k 2 j col (by rw [depth1_2]; exact hj)) β ⟨k, by omega⟩ rfl
    (fun j hj => hβ j hj) col, Z1_eq p k hk]
  simp only [offK1_2]
  have hc := col.isLt
  by_cases h : 2 * k + 1 ≤ (col : ℕ)
  · rw [dif_pos ⟨by omega, by omega⟩, if_pos h]
  · rw [dif_neg (by omega), if_neg h]

/-- `y_k = ρ x_k + z_{k-1}` as linear forms. -/
lemma H1_idY (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) :
    H1 p k ρ 1 ⟨k, by omega⟩ =
      (ρ : ZMod p) • H1 p k ρ 0 ⟨k, by omega⟩ + H1 p k ρ 2 ⟨k - 1, by omega⟩ := by
  have hne : (⟨k, by omega⟩ : Fin m1) ≠ ⟨k - 1, by omega⟩ := by simp; omega
  ext col
  simp only [H1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, updateRow_self, updateRow_ne hne, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [vy p k hk _ (fun j hj => by simp only [byk]; rw [if_neg (by omega), if_neg (by omega)]),
    vx p k hk _ (fun j hj => by simp only [bxk]; rw [if_neg (by omega)]),
    vz' p k hk _ (fun j hj => by simp only [bzk1]; rw [if_neg (by omega)])]
  simp only [byk, bxk, bzk1, Fin.val_mk]
  have hc := col.isLt
  have hr1 : ∀ y : ZMod p, (ρ : ZMod p) * ((ρ : ZMod p)⁻¹ * y) = y := fun y => by field_simp
  split_ifs <;> (try (exfalso; omega))
  all_goals (try rw [Nat.add_sub_cancel' (show k + 1 ≤ (col : ℕ) by omega)])
  all_goals (try rw [Nat.add_sub_cancel' (show 2 * k + 1 ≤ (col : ℕ) by omega)])
  all_goals (try simp only [hr1])
  all_goals ring

/-- `z_k = ρ² x_k + x_{k-1} + y_{k-1} - z_{k-1}` as linear forms. -/
lemma H1_idZ (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) :
    H1 p k ρ 2 ⟨k, by omega⟩ =
      (ρ : ZMod p) ^ 2 • H1 p k ρ 0 ⟨k, by omega⟩ + H1 p k ρ 0 ⟨k - 1, by omega⟩ +
        H1 p k ρ 1 ⟨k - 1, by omega⟩ - H1 p k ρ 2 ⟨k - 1, by omega⟩ := by
  have hne : (⟨k, by omega⟩ : Fin m1) ≠ ⟨k - 1, by omega⟩ := by simp; omega
  have hs := al1_spec p k hk ρ
  ext col
  simp only [H1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, updateRow_self, updateRow_ne hne, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [vz' p k hk _ (fun j hj => by simp only [bzk]; rw [if_neg (by omega), if_neg (by omega)]),
    vx p k hk _ (fun j hj => by simp only [bxk]; rw [if_neg (by omega)]),
    vx p k hk _ (fun j hj => by simp only [bxk1]; rw [if_neg (by omega)]),
    vy p k hk _ (fun j hj => by simp only [byk1]; rw [if_neg (by omega)]),
    vz' p k hk _ (fun j hj => by simp only [bzk1]; rw [if_neg (by omega)])]
  simp only [bzk, bxk, bxk1, byk1, bzk1, Fin.val_mk]
  have hc := col.isLt
  have hr2 : ∀ y : ZMod p, (ρ : ZMod p) ^ 2 * ((ρ : ZMod p)⁻¹ * y) = ρ * y := fun y => by field_simp
  have hs' : ∀ c : ℕ, c = k → al1 p k ρ * Z1 p k c = (ρ : ZMod p) * Y1 p k c := by
    intro c hc; rw [hc]; exact hs
  split_ifs <;> (try (exfalso; omega))
  all_goals (try rw [Nat.add_sub_cancel' (show k + 1 ≤ (col : ℕ) by omega)])
  all_goals (try rw [Nat.add_sub_cancel' (show 2 * k + 1 ≤ (col : ℕ) by omega)])
  all_goals (try rw [hs' (col : ℕ) (by omega)])
  all_goals (try simp only [hr2])
  all_goals ring

/-- graph form: `y`-skeleton row `ρ e_{x,k} + e_{z,k-1}`. -/
lemma C1_skelY (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m1) :
    gr (H1 p k ρ) (depth 1 k) 1 ⟨k, by omega⟩ col =
      (ρ : ZMod p) * (if (col : ℕ) = k then 1 else 0) + (if (col : ℕ) = 3 * k then 1 else 0) := by
  have hH := H1_T0 p k hk ρ hρ
  rw [gr_row, H1_idY p k hk ρ hρ, add_vecMul, smul_vecMul, ← gr_row, ← gr_row]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [gr_coarse hH _ (depth1_sum k) 0 _ col (by simp [depth]),
    gr_coarse hH _ (depth1_sum k) 2 _ col (by simp [depth]; omega), offK1_0, offK1_2]
  simp only [zero_add]
  congr 2
  rw [show 2 * k + 1 + (k - 1) = 3 * k by omega]

/-- graph form: `z`-skeleton row `ρ² e_{x,k} + e_{x,k-1} + e_{y,k-1} - e_{z,k-1}`. -/
lemma C1_skelZ (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m1) :
    gr (H1 p k ρ) (depth 1 k) 2 ⟨k, by omega⟩ col =
      (ρ : ZMod p) ^ 2 * (if (col : ℕ) = k then 1 else 0) + (if (col : ℕ) = k - 1 then 1 else 0) +
        (if (col : ℕ) = 2 * k then 1 else 0) - (if (col : ℕ) = 3 * k then 1 else 0) := by
  have hH := H1_T0 p k hk ρ hρ
  rw [gr_row, H1_idZ p k hk ρ hρ, sub_vecMul, add_vecMul, add_vecMul, smul_vecMul, ← gr_row,
    ← gr_row, ← gr_row, ← gr_row]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [gr_coarse hH _ (depth1_sum k) 0 _ col (by simp [depth]),
    gr_coarse hH _ (depth1_sum k) 0 _ col (by simp [depth]),
    gr_coarse hH _ (depth1_sum k) 1 _ col (by simp [depth]; omega),
    gr_coarse hH _ (depth1_sum k) 2 _ col (by simp [depth]; omega), offK1_0, offK1_1, offK1_2]
  simp only [zero_add]
  rw [show k + 1 + (k - 1) = 2 * k by omega, show 2 * k + 1 + (k - 1) = 3 * k by omega]

end Moves

end B1

/-- `winEntry` of a row supported on its first two entries. -/
lemma winEntry_two (x y : ℤ) (L K l : ℕ) (hL : 2 ≤ L) (hl : l < K) :
    winEntry ![x, y, 0, 0] L K l = if l + 1 = K then x else if l + 2 = K then y else 0 := by
  unfold winEntry
  by_cases h1 : l + 1 = K
  · rw [if_pos h1, dif_pos (by omega), if_pos (by omega)]
    have : K - 1 - l = 0 := by omega
    simp [this]
  · rw [if_neg h1]
    by_cases h2 : l + 2 = K
    · rw [if_pos h2, dif_pos (by omega), if_pos (by omega)]
      have : K - 1 - l = 1 := by omega
      simp [this]
    · rw [if_neg h2]
      have hz : ∀ (i : ℕ) (hi : i < 4), 2 ≤ i → (![x, y, 0, 0] : Fin 4 → ℤ) ⟨i, hi⟩ = 0 := by
        intro i hi h1; interval_cases i <;> rfl
      split_ifs with h3 h4
      · exact hz _ h3 (by omega)
      · rfl
      · rfl

end Z3NetKN.Frame

namespace Z3NetKN.Proofs

open Matrix Z3NetKN.Frame

/-- **`m ≡ 1`, all primes, net part** (`B1_net` of `ChallengeKN.lean`). -/
theorem B1_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKNskel 1 p k (skB1 ρ) C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρp' : ρ < p := by nlinarith
  have hρ0 := rho_ne_zero p ρ (by omega) hρp'
  have hH := H1_T0 p k hk ρ hρ0
  have hC := T0_gr hH (depth 1 k) (depth1_sum k)
  refine ⟨gr (H1 p k ρ) (depth 1 k), ⟨?_, ?_⟩, hC.isNet0⟩
  · intro c j col hj hcol
    have hjm : j < 3 * k + 1 := by
      have : depth 1 k c ≤ k + 1 := by unfold depth; split_ifs <;> omega
      omega
    unfold ent
    rw [dif_pos ⟨hjm, hcol⟩, gr_coarse hH _ (depth1_sum k) c ⟨j, hjm⟩ ⟨col, hcol⟩ hj, off_eq]
  · intro c d hc l hl
    have off0 : off 1 k 0 = 0 := by simp [off]
    have off1 : off 1 k 1 = k + 1 := by simp [off, depth]
    have off2 : off 1 k 2 = 2 * k + 1 := by simp [off, depth]; ring
    have hlt : off 1 k d + l < 3 * k + 1 := by
      have := offK_lt (depth 1 k) (depth1_sum k) d l hl
      rwa [← off_eq] at this
    obtain rfl | rfl : c = 1 ∨ c = 2 := by
      rcases c with ⟨_ | _ | _ | c, h⟩ <;> simp at hc ⊢ <;> omega
    · have hdep : depth 1 k 1 = k := depth1_1 k
      unfold ent
      rw [dif_pos ⟨by omega, hlt⟩]
      simp only [hdep]
      rw [C1_skelY p k hk ρ hρ0 ⟨off 1 k d + l, hlt⟩]
      obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
      · rw [depth1_0] at hl
        have hw : skB1 ρ 1 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
        rw [hw, depth1_0, winEntry_single _ _ _ _ (by simp [win]) hl]
        simp only [off0, zero_add]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
      · rw [depth1_1] at hl
        have hw : skB1 ρ 1 1 = ![((0 : ℕ) : ℤ), 0, 0, 0] := by ext i; fin_cases i <;> rfl
        rw [hw, depth1_1, winEntry_single _ _ _ _ (by simp [win]) hl]
        simp only [off1]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
      · rw [depth1_2] at hl
        have hw : skB1 ρ 1 2 = ![((1 : ℕ) : ℤ), 0, 0, 0] := rfl
        rw [hw, depth1_2, winEntry_single _ _ _ _ (by simp [win]) hl]
        simp only [off2]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
    · have hdep : depth 1 k 2 = k := depth1_2 k
      unfold ent
      rw [dif_pos ⟨by omega, hlt⟩]
      simp only [hdep]
      rw [C1_skelZ p k hk ρ hρ0 ⟨off 1 k d + l, hlt⟩]
      obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
      · rw [depth1_0] at hl
        have hw : skB1 ρ 2 0 = ![(ρ : ℤ) ^ 2, 1, 0, 0] := rfl
        rw [hw, depth1_0, winEntry_two _ _ _ _ _ (by simp [win]) hl]
        simp only [off0, zero_add]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
      · rw [depth1_1] at hl
        have hw : skB1 ρ 2 1 = ![((1 : ℕ) : ℤ), 0, 0, 0] := rfl
        rw [hw, depth1_1, winEntry_single _ _ _ _ (by simp [win]) hl]
        simp only [off1]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
      · rw [depth1_2] at hl
        have hw : skB1 ρ 2 2 = ![((-1 : ℤ)), 0, 0, 0] := rfl
        rw [hw, depth1_2, winEntry_single _ _ _ _ (by simp [win]) hl]
        simp only [off2]
        split_ifs <;> (try (exfalso; omega)) <;> push_cast <;> ring
end Z3NetKN.Proofs

