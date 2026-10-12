/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23CertDefs

@[expose] public section

/-!
# V14 stage S14′: from the code-level chains to `def:lift`

* `vecOf_lc`: the digits of a code `t b^(M+2) + u b² + j₁ b + j₀` (top, block, jitter digits of `def:lift`).
* `colMat_liftCols`: the column codes of `liftCols` are the generator matrices `liftGen` of `def:lift`;
  `shOf_liftShCode`: the same for the shift (`liftShift`).
* `colMat_seedCols`: the seed codes are the matrices `(I, A_y, A_z)` of `tab:b23seeds` (printed rows).
-/

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

variable {b : ℕ}

/-- The code with top digit `t`, block `u` (`M` digits) and jitter digits `j₁, j₀`. -/
def lc (b M t u j1 j0 : ℕ) : ℕ := t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0

lemma lc_lt (hb : 0 < b) {M t u j1 j0 : ℕ} (ht : t < b) (hu : u < b ^ M) (hj1 : j1 < b) (hj0 : j0 < b) :
    lc b M t u j1 j0 < b ^ (M + 3) := by
  unfold lc
  have h1 : j1 * b + j0 < b ^ 2 := by nlinarith
  have h2 : u * b ^ 2 + (j1 * b + j0) < b ^ (M + 2) := by
    calc u * b ^ 2 + (j1 * b + j0) < u * b ^ 2 + b ^ 2 := by omega
      _ = (u + 1) * b ^ 2 := by ring
      _ ≤ b ^ M * b ^ 2 := Nat.mul_le_mul_right _ hu
      _ = b ^ (M + 2) := by ring
  calc t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0 = t * b ^ (M + 2) + (u * b ^ 2 + (j1 * b + j0)) := by ring
    _ < t * b ^ (M + 2) + b ^ (M + 2) := by omega
    _ = (t + 1) * b ^ (M + 2) := by ring
    _ ≤ b * b ^ (M + 2) := Nat.mul_le_mul_right _ ht
    _ = b ^ (M + 3) := by ring

lemma vecOf_lc (hb : 0 < b) (M t u j1 j0 : ℕ) (ht : t < b) (hu : u < b ^ M) (hj1 : j1 < b) (hj0 : j0 < b)
    (r : Fin (M + 3)) :
    vecOf b (M + 3) (lc b M t u j1 j0) r =
      if h0 : (r : ℕ) = 0 then (t : ZMod b)
      else if h : (r : ℕ) ≤ M then vecOf b M u ⟨(r : ℕ) - 1, by omega⟩
      else if (r : ℕ) = M + 1 then (j1 : ZMod b) else (j0 : ZMod b) := by
  rw [vecOf_apply]
  congr 1
  have hj : j1 * b + j0 < b ^ 2 := by nlinarith
  rcases r with ⟨r, hr⟩
  simp only [dg, lc]
  by_cases h0 : r = 0
  · subst h0
    simp only [Fin.val_mk, dite_true, show M + 3 - 1 - 0 = M + 2 by omega]
    have : u * b ^ 2 + j1 * b + j0 < b ^ (M + 2) := by
      calc u * b ^ 2 + j1 * b + j0 = u * b ^ 2 + (j1 * b + j0) := by ring
        _ < (u + 1) * b ^ 2 := by nlinarith
        _ ≤ b ^ M * b ^ 2 := Nat.mul_le_mul_right _ hu
        _ = b ^ (M + 2) := by ring
    rw [show t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0 = (u * b ^ 2 + j1 * b + j0) + b ^ (M + 2) * t by ring,
      Nat.add_mul_div_left _ _ (pow_pos hb _), Nat.div_eq_of_lt this, zero_add, Nat.mod_eq_of_lt ht]
  · simp only [Fin.val_mk, dif_neg h0]
    by_cases h1 : r ≤ M
    · rw [dif_pos h1]
      simp only [vecOf_apply, dg]
      push_cast
      congr 1
      -- digit of weight 
      have e1 : M + 2 - r = (M - r) + 2 := by omega
      have e2 : M - 1 - (r - 1) = M - r := by omega
      rw [e1, e2]
      rw [show t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0 =
          (u * b ^ 2 + (j1 * b + j0)) + b ^ (M - r + 2) * (t * b ^ r) by
            rw [show M + 2 = (M - r + 2) + r by omega, pow_add]; ring,
        Nat.add_mul_div_left _ _ (pow_pos hb _)]
      obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [show t * b ^ r = b * (t * b ^ s) by rw [hs, pow_succ]; ring, Nat.add_mul_mod_self_left]
      rw [show M - r + 2 = 2 + (M - r) by omega, pow_add, ← Nat.div_div_eq_div_mul,
        show u * b ^ 2 + (j1 * b + j0) = (j1 * b + j0) + b ^ 2 * u by ring,
        Nat.add_mul_div_left _ _ (pow_pos hb _), Nat.div_eq_of_lt hj, zero_add]
    · rw [dif_neg h1]
      by_cases h2 : r = M + 1
      · subst h2
        simp only [if_true, show M + 3 - 1 - (M + 1) = 1 by omega, pow_one]
        rw [show t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0 = j0 + b * (t * b ^ (M + 1) + u * b + j1) by ring,
          Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hj0, zero_add,
          show t * b ^ (M + 1) + u * b + j1 = j1 + b * (t * b ^ M + u) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hj1]
      · have h3 : r = M + 2 := by omega
        subst h3
        simp only [if_neg h2, show M + 3 - 1 - (M + 2) = 0 by omega, pow_zero, Nat.div_one]
        rw [show t * b ^ (M + 2) + u * b ^ 2 + j1 * b + j0 = j0 + b * (t * b ^ (M + 1) + u * b + j1) by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj0]

section liftcols

variable (b M : ℕ) (cols : List (List ℕ)) (sA sB : List ℕ)

/-- Top digit of column `j` of coordinate `c` of the lift. -/
def tpC (c j : ℕ) : ℕ := if j < M then 0 else if j = M then 1 else if j = M + 1 then (if c = 0 then 0 else 1)
  else (if c = 2 then 1 else 0)
/-- Block of column `j`. -/
def blC (c j : ℕ) : ℕ := if j < M then (cols.getD c []).getD j 0 else if j = M then 0 else if j = M + 1 then
  sA.getD c 0 else sB.getD c 0
/-- First jitter digit of column `j`. -/
def j1C (c j : ℕ) : ℕ := if j ≤ M then 0 else if j = M + 1 then (if c = 0 then 0 else 1) else (if c = 2 then 0 else 1)
/-- Second jitter digit of column `j`. -/
def j0C (c j : ℕ) : ℕ := if j ≤ M then 0 else if j = M + 1 then (if c = 2 then 0 else 1) else (if c = 2 then 1 else 0)

lemma getD_shape (l : List ℕ) (q x y z : ℕ) (hl : l.length = M) (j : ℕ) (hj : j < M + 3) :
    ((l.map (· * q)) ++ [x, y, z]).getD j 0 =
      if j < M then l.getD j 0 * q else if j = M then x else if j = M + 1 then y else z := by
  by_cases h : j < M
  · rw [if_pos h, List.getD_append _ _ _ _ (by simpa [hl] using h), List.getD_eq_getElem _ _ (by simpa [hl] using h),
      List.getD_eq_getElem _ _ (by rw [hl]; exact h), List.getElem_map]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by simp [hl]; omega)]
    simp only [List.length_map, hl]
    have : j = M ∨ j = M + 1 ∨ j = M + 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp

lemma liftCols_getD (hl : ∀ c : Fin 3, (cols.getD c []).length = M) (c : Fin 3) (j : ℕ) (hj : j < M + 3) :
    ((liftCols b M cols sA sB).getD c []).getD j 0 =
      lc b M (tpC M c j) (blC M cols sA sB c j) (j1C M c j) (j0C M c j) := by
  fin_cases c
  · show (((cols.getD 0 []).map (· * b ^ 2)) ++ [b ^ (M + 2), sA.getD 0 0 * b ^ 2 + 1, sB.getD 0 0 * b ^ 2 + b]).getD j 0 = _
    have hl0 : (cols.getD 0 []).length = M := hl 0
    rw [getD_shape M _ _ _ _ _ hl0 j hj]
    have : j < M ∨ j = M ∨ j = M + 1 ∨ j = M + 2 := by omega
    rcases this with h | rfl | rfl | rfl
    · simp [tpC, blC, j1C, j0C, lc, h, le_of_lt h]
    all_goals simp [tpC, blC, j1C, j0C, lc]
  · show (((cols.getD 1 []).map (· * b ^ 2)) ++ [b ^ (M + 2), b ^ (M + 2) + sA.getD 1 0 * b ^ 2 + b + 1,
      sB.getD 1 0 * b ^ 2 + b]).getD j 0 = _
    have hl1 : (cols.getD 1 []).length = M := hl 1
    rw [getD_shape M _ _ _ _ _ hl1 j hj]
    have : j < M ∨ j = M ∨ j = M + 1 ∨ j = M + 2 := by omega
    rcases this with h | rfl | rfl | rfl
    · simp [tpC, blC, j1C, j0C, lc, h, le_of_lt h]
    all_goals simp [tpC, blC, j1C, j0C, lc]; try ring
  · show (((cols.getD 2 []).map (· * b ^ 2)) ++ [b ^ (M + 2), b ^ (M + 2) + sA.getD 2 0 * b ^ 2 + b,
      b ^ (M + 2) + sB.getD 2 0 * b ^ 2 + 1]).getD j 0 = _
    have hl2 : (cols.getD 2 []).length = M := hl 2
    rw [getD_shape M _ _ _ _ _ hl2 j hj]
    have : j < M ∨ j = M ∨ j = M + 1 ∨ j = M + 2 := by omega
    rcases this with h | rfl | rfl | rfl
    · simp [tpC, blC, j1C, j0C, lc, h, le_of_lt h]
    all_goals simp [tpC, blC, j1C, j0C, lc]; try ring

end liftcols

lemma tp_eq (b M : ℕ) (c : Fin 3) (j : ℕ) (hj : j < M + 3) : ((tpC M c j : ℕ) : ZMod b) = liftTop M c j := by
  unfold tpC liftTop
  fin_cases c <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> split_ifs <;> first | rfl | (exfalso; omega) | simp | omega

lemma jit_eq0 (b M : ℕ) (c : Fin 3) (j : ℕ) (hj : j < M + 3) : ((j1C M c j : ℕ) : ZMod b) = liftJit M c 0 j := by
  unfold j1C liftJit
  fin_cases c <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> split_ifs <;> first | rfl | (exfalso; omega) | simp | omega

lemma jit_eq1 (b M : ℕ) (c : Fin 3) (j : ℕ) (hj : j < M + 3) : ((j0C M c j : ℕ) : ZMod b) = liftJit M c 1 j := by
  unfold j0C liftJit
  fin_cases c <;> simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> split_ifs <;> first | rfl | (exfalso; omega) | simp | omega

/-- **`def:lift` on codes**: the generator matrices of `liftCols` are those of `liftGen`. -/
theorem colMat_liftCols (hb : 2 ≤ b) (M : ℕ) (cols : List (List ℕ)) (sA sB : List ℕ)
    (hl : ∀ c : Fin 3, (cols.getD c []).length = M) (hbd : ∀ c : Fin 3, ∀ x ∈ cols.getD c [], x < b ^ M)
    (hsA : ∀ c : Fin 3, sA.getD c 0 < b ^ M) (hsB : ∀ c : Fin 3, sB.getD c 0 < b ^ M) :
    colMat b (M + 3) (liftCols b M cols sA sB) = liftGen (colMat b M cols) (shOf b M sA) (shOf b M sB) := by
  have hb0 : 0 < b := by omega
  funext c r j
  have hj := j.isLt
  rw [show colMat b (M + 3) (liftCols b M cols sA sB) c r j =
    vecOf b (M + 3) (((liftCols b M cols sA sB).getD c []).getD j 0) r from rfl,
    liftCols_getD b M cols sA sB hl c j hj]
  have htp : tpC M c j < b := by unfold tpC; split_ifs <;> omega
  have hj1 : j1C M c j < b := by unfold j1C; split_ifs <;> omega
  have hj0 : j0C M c j < b := by unfold j0C; split_ifs <;> omega
  have hbl : blC M cols sA sB c j < b ^ M := by
    unfold blC
    split_ifs with h1 h2 h3
    · rw [List.getD_eq_getElem _ _ (by rw [hl c]; exact h1)]; exact hbd c _ (List.getElem_mem _)
    · exact pow_pos hb0 _
    · exact hsA c
    · exact hsB c
  rw [vecOf_lc hb0 M _ _ _ _ htp hbl hj1 hj0]
  rcases r with ⟨r, hr⟩
  simp only [liftGen, Fin.val_mk]
  by_cases h0 : r = 0
  · rw [dif_pos h0, dif_pos h0]; exact tp_eq b M c j hj
  · rw [dif_neg h0, dif_neg h0]
    by_cases h1 : r ≤ M
    · rw [dif_pos h1, dif_pos h1]
      unfold blC
      by_cases ha : (j : ℕ) < M
      · rw [if_pos ha, dif_pos ha]; rfl
      · rw [if_neg ha, dif_neg ha]
        by_cases hb' : (j : ℕ) = M
        · rw [if_pos hb', if_neg (by omega), if_neg (by omega), vecOf_zero]; rfl
        · rw [if_neg hb']
          by_cases hc : (j : ℕ) = M + 1
          · rw [if_pos hc, if_pos hc]; rfl
          · rw [if_neg hc, if_neg hc, if_pos (by omega)]; rfl
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : r = M + 1
      · rw [if_pos h2, show r - (M + 1) = 0 by omega]; exact jit_eq0 b M c j hj
      · rw [if_neg h2, show r - (M + 1) = 1 by omega]; exact jit_eq1 b M c j hj

/-- The shift of the lift on codes. -/
theorem shOf_liftShCode (hb : 2 ≤ b) (M : ℕ) (sh : List ℕ) (hsh : ∀ c : Fin 3, sh.getD c 0 < b ^ M) (hlen : sh.length = 3) :
    shOf b (M + 3) (liftShCode b sh) = liftShift (shOf b M sh) := by
  have hb0 : 0 < b := by omega
  funext c r
  have e : (liftShCode b sh).getD c 0 = lc b M 0 (sh.getD c 0) 0 0 := by
    simp only [liftShCode, lc]
    rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_map]
    ring
  show vecOf b (M + 3) ((liftShCode b sh).getD c 0) r = _
  rw [e, vecOf_lc hb0 M _ _ _ _ hb0 (hsh c) hb0 hb0]
  rcases r with ⟨r, hr⟩
  simp only [liftShift, shOf, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega

/-! ## The seeds of `tab:b23seeds` -/

lemma list_sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma vecOf_sum_digits (hb : 0 < b) (M : ℕ) (g : ℕ → ℕ) (hg : ∀ d, g d < b) (r : Fin M) :
    vecOf b M (((List.range M).map (fun d => g d * b ^ (M - 1 - d))).sum) r = (g r : ZMod b) := by
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range (fun d => g d * b ^ (M - 1 - d)), vecOf_apply, dg]
  congr 1
  exact Z3NetF.Proofs.digSum_digit hb M (fun d : Fin M => g d) (fun d => hg d) r

/-- **The seeds** (`tab:b23seeds`): the seed codes are the generator matrices `(I, A_y, A_z)` with the printed rows. -/
theorem colMat_seedCols (hb : 2 ≤ b) (M : ℕ) (ry rz : List ℕ) :
    colMat b M (seedCols b M ry rz) = ![1, rowMat b M ry, rowMat b M rz] := by
  have hb0 : 0 < b := by omega
  funext c r i
  fin_cases c
  · show vecOf b M (((List.range M).map (fun i => b ^ (M - 1 - i))).getD i 0) r = (1 : Matrix (Fin M) (Fin M) (ZMod b)) r i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, vecOf_apply, dg, Matrix.one_apply]
    rcases lt_trichotomy (r : ℕ) (i : ℕ) with h | h | h
    · rw [if_neg (fun e => by rw [e] at h; exact lt_irrefl _ h), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
      simp
    · rw [if_pos (Fin.ext h), h, Nat.div_self (pow_pos hb0 _), Nat.mod_eq_of_lt (by omega)]; simp
    · rw [if_neg (fun e => by rw [e] at h; exact lt_irrefl _ h), Nat.pow_div (by omega) hb0]
      obtain ⟨t, ht⟩ : ∃ t, M - 1 - (i : ℕ) - (M - 1 - (r : ℕ)) = t + 1 := ⟨M - 1 - i - (M - 1 - r) - 1, by omega⟩
      rw [ht, pow_succ, Nat.mul_mod_left]; simp
  · show vecOf b M (((List.range M).map (fun i => ((List.range M).map (fun d =>
        digAt b M (ry.getD d 0) i * b ^ (M - 1 - d))).sum)).getD i 0) r = rowMat b M ry r i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      vecOf_sum_digits hb0 M (fun d => digAt b M (ry.getD d 0) i) (fun d => Nat.mod_lt _ hb0) r]
    rfl
  · show vecOf b M (((List.range M).map (fun i => ((List.range M).map (fun d =>
        digAt b M (rz.getD d 0) i * b ^ (M - 1 - d))).sum)).getD i 0) r = rowMat b M rz r i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      vecOf_sum_digits hb0 M (fun d => digAt b M (rz.getD d 0) i) (fun d => Nat.mod_lt _ hb0) r]
    rfl

end Z3NetB23.Proofs
