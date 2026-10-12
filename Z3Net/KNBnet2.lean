module
public import Z3Net.KNFrame

@[expose] public section

/-!
# `B2_net`: the all-`p` family for `m = 3k + 2` (net part)

Start from the Möbius frame in graph form `G = frameGF 2 p k` (depths `(k+1, k+1, k)`), with
`z`-skeleton row `a = G_z[k]`.  Its pivots `a_{x,k}`, `a_{y,k}` (last level of the `x`, `y`
blocks) are nonzero (`1 × 1` box minors).  Row moves (lower-triangular, nonzero diagonal):
`x_k ← ρ⁻¹ a|_x`, `y_k ← ρ⁻² a|_y`, `z_k ← a - a|_z`; then `z_k = ρ x_k + ρ² y_k` as linear forms,
and re-taking the graph form makes the `z`-skeleton row equal to `skB2 ρ`.
-/

namespace Z3NetKN.Frame

open Matrix Finset

section B2

variable (p k : ℕ) [Fact p.Prime]

local notation "m2" => 3 * k + 2

lemma depth2_0 : depth 2 k 0 = k + 1 := by simp [depth]
lemma depth2_1 : depth 2 k 1 = k + 1 := by simp [depth]
lemma depth2_2 : depth 2 k 2 = k := by simp [depth]

lemma depth2_sum : depth 2 k 0 + depth 2 k 1 + depth 2 k 2 = m2 := depth_sum 2 k (by norm_num)

/-- graph form of the frame, coarse rows, in `offK` form -/
lemma G2c (c : Fin 3) (j col : Fin m2) (hj : (j : ℕ) < depth 2 k c) :
    frameGF 2 p k c j col = if (col : ℕ) = offK (depth 2 k) c + j then 1 else 0 :=
  frameGF_coarse 2 p k (by norm_num) (by omega) c j col hj

/-- The `z`-skeleton row of the frame graph form (total accessor). -/
noncomputable def A2 (n : ℕ) : ZMod p := ent (frameGF 2 p k 2) k n

lemma A2_eq (col : Fin m2) : frameGF 2 p k 2 ⟨k, by omega⟩ col = A2 p k col := by
  unfold A2 ent
  rw [dif_pos ⟨by omega, col.isLt⟩]

lemma pivot2 (c : Fin 3) (hc : (c : ℕ) < 2) : A2 p k (offK (depth 2 k) c + k) ≠ 0 := by
  intro h0
  have hG := frameGF_T0 2 p k (by norm_num) (by omega)
  have hlt : offK (depth 2 k) c + k < m2 := by
    rcases c with ⟨_ | _ | c, hc'⟩ <;> simp [offK, depth] at hc ⊢ <;> omega
  set n : Fin m2 := ⟨offK (depth 2 k) c + k, hlt⟩ with hn
  let d : Fin 3 → ℕ := fun e => if e = c then k else if (e : ℕ) = 2 then k + 1 else k + 1
  have hv := kernel_test hG (depth 2 k) (depth2_sum k) (G2c p k) d
    (by rcases c with ⟨_ | _ | c, hc'⟩ <;> simp [d] at hc ⊢ <;> omega)
    (by intro e; rcases e with ⟨_ | _ | _ | e, he⟩ <;> rcases c with ⟨_ | _ | c, hc'⟩ <;>
          simp [d, depth] at hc ⊢ <;> omega)
    (Pi.single n 1)
    (by
      intro e l hl hld
      rw [Pi.single_apply, if_neg]
      intro heq
      have := congrArg Fin.val heq
      simp only [hn] at this
      rcases e with ⟨_ | _ | _ | e, he⟩ <;> rcases c with ⟨_ | _ | c, hc'⟩ <;>
        simp [d, offK, depth] at hc hl hld this <;> omega)
    (by
      intro e he s hs
      rw [mulVec_single_one]
      have hec : e = 2 := by
        rcases e with ⟨_ | _ | _ | e, he'⟩ <;> rcases c with ⟨_ | _ | c, hc'⟩ <;>
          simp [d, depth] at hc he ⊢ <;> omega
      subst hec
      have hs' : s = ⟨k, by omega⟩ := Fin.ext (by rw [hs]; simp [depth])
      rw [Matrix.col_apply, hs', A2_eq]; exact h0)
  have := congrFun hv n
  simp at this

/-- Row-move vectors. -/
noncomputable def bx2 (ρ : ℕ) (j : Fin m2) : ZMod p :=
  if (j : ℕ) < k + 1 then (ρ : ZMod p)⁻¹ * A2 p k j else 0

noncomputable def by2 (ρ : ℕ) (j : Fin m2) : ZMod p :=
  if (j : ℕ) < k + 1 then ((ρ : ZMod p) ^ 2)⁻¹ * A2 p k (k + 1 + j) else 0

noncomputable def bz2 (j : Fin m2) : ZMod p :=
  if (j : ℕ) = k then 1 else if (j : ℕ) < k then -A2 p k (2 * k + 2 + j) else 0

/-- The row-moved frame. -/
noncomputable def H2 (ρ : ℕ) : Fin 3 → Matrix (Fin m2) (Fin m2) (ZMod p) :=
  ![(frameGF 2 p k 0).updateRow ⟨k, by omega⟩ (bx2 p k ρ ᵥ* frameGF 2 p k 0),
    (frameGF 2 p k 1).updateRow ⟨k, by omega⟩ (by2 p k ρ ᵥ* frameGF 2 p k 1),
    (frameGF 2 p k 2).updateRow ⟨k, by omega⟩ (bz2 p k ᵥ* frameGF 2 p k 2)]

lemma H2_T0 (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) : T0 (H2 p k ρ) := by
  have hG := frameGF_T0 2 p k (by norm_num) (by omega)
  apply T0_of_prefImp hG
  intro c
  rcases c with ⟨_ | _ | _ | c, hc⟩
  · apply prefImp_updateRow
    · intro j hj; simp only [bx2]; rw [if_neg]; have : k < (j : ℕ) := hj; omega
    · simp only [bx2]; rw [if_pos (by simp)]
      have := pivot2 p k 0 (by simp)
      simp [offK] at this
      exact mul_ne_zero (inv_ne_zero hρ) this
  · apply prefImp_updateRow
    · intro j hj; simp only [by2]; rw [if_neg]; have : k < (j : ℕ) := hj; omega
    · simp only [by2]; rw [if_pos (by simp)]
      have := pivot2 p k 1 (by simp)
      simp [offK, depth] at this
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hρ)) this
  · apply prefImp_updateRow
    · intro j hj; simp only [bz2]; have : k < (j : ℕ) := hj
      rw [if_neg (by omega), if_neg (by omega)]
    · simp [bz2]
  · omega

/-- The key identity of linear forms: `z_k = ρ x_k + ρ² y_k`. -/
lemma H2_identity (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) :
    H2 p k ρ 2 ⟨k, by omega⟩ =
      (ρ : ZMod p) • H2 p k ρ 0 ⟨k, by omega⟩ + (ρ : ZMod p) ^ 2 • H2 p k ρ 1 ⟨k, by omega⟩ := by
  ext col
  simp only [H2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e0 := vecMul_graph (frameGF 2 p k 0) (offK (depth 2 k) 0) (k + 1)
    (fun j col hj => G2c p k 0 j col (by rw [depth2_0]; exact hj)) (bx2 p k ρ) ⟨k + 1, by omega⟩ rfl
    (by intro j hj; simp only [bx2]; rw [if_neg (by omega)]) col
  have e1 := vecMul_graph (frameGF 2 p k 1) (offK (depth 2 k) 1) (k + 1)
    (fun j col hj => G2c p k 1 j col (by rw [depth2_1]; exact hj)) (by2 p k ρ) ⟨k + 1, by omega⟩ rfl
    (by intro j hj; simp only [by2]; rw [if_neg (by omega)]) col
  have e2 := vecMul_graph (frameGF 2 p k 2) (offK (depth 2 k) 2) k
    (fun j col hj => G2c p k 2 j col (by rw [depth2_2]; exact hj)) (bz2 p k) ⟨k, by omega⟩ rfl
    (by intro j hj; simp only [bz2]; rw [if_neg (by omega), if_neg (by omega)]) col
  rw [e0, e1, e2, A2_eq]
  simp only [bx2, by2, bz2, offK, depth2_0, depth2_1]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, one_ne_zero, ↓reduceIte, lt_self_iff_false, add_lt_iff_neg_left,
    not_lt_zero', zero_mul, zero_add, one_mul]
  have hc := col.isLt
  rcases (show (col : ℕ) < k + 1 ∨ (k + 1 ≤ (col : ℕ) ∧ (col : ℕ) < 2 * k + 2) ∨
      2 * k + 2 ≤ (col : ℕ) by omega) with h | h | h
  · rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega)]
    rw [if_pos (by omega), Nat.sub_zero, mul_inv_cancel_left₀ hρ]
    ring
  · rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    rw [if_pos (by omega), show k + 1 + ((col : ℕ) - (k + 1)) = col by omega,
      mul_inv_cancel_left₀ (pow_ne_zero 2 hρ)]
    ring
  · rw [dif_pos (by omega), dif_neg (by omega), dif_neg (by omega)]
    rw [if_neg (by omega), if_pos (by omega),
      show 2 * k + 2 + ((col : ℕ) - (k + 1 + (k + 1))) = col by omega]
    simp only [mul_zero, add_zero]
    exact add_neg_cancel _

/-- `C := gr (H2 p k ρ) (depth 2 k)`: its `z`-skeleton row is `ρ e_{x,k} + ρ² e_{y,k}`. -/
lemma C2_skel (ρ : ℕ) (hρ : (ρ : ZMod p) ≠ 0) (col : Fin m2) :
    gr (H2 p k ρ) (depth 2 k) 2 ⟨k, by omega⟩ col =
      (ρ : ZMod p) * (if (col : ℕ) = k then 1 else 0) +
        (ρ : ZMod p) ^ 2 * (if (col : ℕ) = 2 * k + 1 then 1 else 0) := by
  have hH := H2_T0 p k ρ hρ
  rw [gr_row, H2_identity p k ρ hρ, add_vecMul, smul_vecMul, smul_vecMul, ← gr_row, ← gr_row]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [gr_coarse hH _ (depth2_sum k) 0 _ col (by simp [depth]),
    gr_coarse hH _ (depth2_sum k) 1 _ col (by simp [depth])]
  have o0 : offK (depth 2 k) 0 = 0 := by simp [offK]
  have o1 : offK (depth 2 k) 1 = k + 1 := by simp [offK, depth]
  rw [o0, o1, zero_add, show k + 1 + k = 2 * k + 1 by ring]

end B2

/-- `winEntry` of a row supported on its first entry. -/
lemma winEntry_single (x : ℤ) (L K l : ℕ) (hL : 1 ≤ L) (hl : l < K) :
    winEntry ![x, 0, 0, 0] L K l = if l + 1 = K then x else 0 := by
  unfold winEntry
  by_cases h : l + 1 = K
  · rw [if_pos h, dif_pos (by omega), if_pos (by omega)]
    have : K - 1 - l = 0 := by omega
    simp [this]
  · rw [if_neg h]
    have hz : ∀ (i : ℕ) (hi : i < 4), 1 ≤ i → (![x, 0, 0, 0] : Fin 4 → ℤ) ⟨i, hi⟩ = 0 := by
      intro i hi h1; interval_cases i <;> rfl
    split_ifs with h1 h2
    · exact hz _ h1 (by omega)
    · rfl
    · rfl

lemma rho_ne_zero (p ρ : ℕ) [Fact p.Prime] (hρ : 1 ≤ ρ) (hρp : ρ < p) : (ρ : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

end Z3NetKN.Frame

namespace Z3NetKN.Proofs

open Matrix Z3NetKN.Frame

/-- **`m ≡ 2`, all primes, net part** (`B2_net` of `ChallengeKN.lean`). -/
theorem B2_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 1 ≤ ρ)
    (hρp : ρ * (1 + ρ + ρ ^ 2) ≤ p) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKNskel 2 p k (skB2 ρ) C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρp' : ρ < p := by nlinarith
  have hρ0 := rho_ne_zero p ρ hρ hρp'
  have hH := H2_T0 p k ρ hρ0
  have hC := T0_gr hH (depth 2 k) (depth2_sum k)
  refine ⟨gr (H2 p k ρ) (depth 2 k), ⟨?_, ?_⟩, hC.isNet0⟩
  · intro c j col hj hcol
    have hjm : j < 3 * k + 2 := by
      have : depth 2 k c ≤ k + 1 := by unfold depth; split_ifs <;> omega
      omega
    unfold ent
    rw [dif_pos ⟨hjm, hcol⟩, gr_coarse hH _ (depth2_sum k) c ⟨j, hjm⟩ ⟨col, hcol⟩ hj, off_eq]
  · intro c d hc l hl
    have hc2 : c = 2 := by
      rcases c with ⟨_ | _ | _ | c, h⟩ <;> simp at hc ⊢ <;> omega
    subst hc2
    have hdep : depth 2 k 2 = k := depth2_2 k
    have hlt : off 2 k d + l < 3 * k + 2 := by
      have := offK_lt (depth 2 k) (depth2_sum k) d l hl
      rwa [← off_eq] at this
    unfold ent
    rw [dif_pos ⟨by omega, hlt⟩]
    have e := C2_skel p k ρ hρ0 ⟨off 2 k d + l, hlt⟩
    simp only [hdep] at e ⊢
    rw [e]
    have off0 : off 2 k 0 = 0 := by simp [off]
    have off1 : off 2 k 1 = k + 1 := by simp [off, depth]
    have off2 : off 2 k 2 = 2 * k + 2 := by simp [off, depth]; ring
    obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
    · rw [depth2_0] at hl
      have hw : skB2 ρ 2 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
      have hwin : win 2 0 = 3 := rfl
      rw [hw, hwin, depth2_0, winEntry_single _ _ _ _ (by norm_num) hl]
      simp only [off0, zero_add]
      by_cases h : l = k
      · rw [if_pos h, if_neg (by omega), if_pos (by omega)]; simp
      · rw [if_neg h, if_neg (by omega), if_neg (by omega)]; simp
    · rw [depth2_1] at hl
      have hw : skB2 ρ 2 1 = ![(ρ : ℤ) ^ 2, 0, 0, 0] := rfl
      have hwin : win 2 1 = 3 := rfl
      rw [hw, hwin, depth2_1, winEntry_single _ _ _ _ (by norm_num) hl]
      simp only [off1]
      by_cases h : l = k
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; simp
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
    · rw [depth2_2] at hl
      have hw : skB2 ρ 2 2 = ![((0 : ℕ) : ℤ), 0, 0, 0] := by
        ext i; fin_cases i <;> rfl
      rw [hw, winEntry_single _ _ _ _ (by simp [win]) (by rw [depth2_2]; exact hl)]
      simp only [off2]
      rw [if_neg (by omega), if_neg (by omega)]
      simp

end Z3NetKN.Proofs
