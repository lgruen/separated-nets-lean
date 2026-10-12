/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `rem:B2`. Entry Dim3 (`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.Dim3Defs
public import Z3Net.S1Main

@[expose] public section

/-!
# Entry Dim3, part 1: `rem:B2`

`B2_skel_iff` identifies entry S1's skeleton predicate at `s = 3` with `IsKNskel 2 p k (skB2 ρ)`;
the separation statements then follow from entry S1's `S1_sep`, `S1_sep_real` (under `ρ³ < p`),
the relaxation from Lemma L2_s (`L2s_min`), and the constants from `S1_const`.
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset

lemma depthS1_eq (k : ℕ) (c : Fin 3) : depthS1 3 k c = depth 2 k c := by
  fin_cases c <;> simp [depthS1, depth]

lemma offS1_eq (k : ℕ) (c : Fin 3) : offS1 k c = off 2 k c := by
  fin_cases c <;> simp [offS1, off, depth] <;> ring

/-- The S1 skeleton row at `s = 3`, block by block. -/
lemma skRowS1_eq (k ρ col : ℕ) (hcol : col < 3 * k + 2) :
    skRowS1 3 k ρ col = if col = k then ρ else if col = 2 * k + 1 then ρ ^ 2 else 0 := by
  unfold skRowS1
  have hk1 : 0 < k + 1 := by omega
  rcases (show col < k + 1 ∨ (k + 1 ≤ col ∧ col < 2 * k + 2) ∨ 2 * k + 2 ≤ col by omega) with
    h | h | h
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    by_cases hc : col = k
    · simp [hc]
    · rw [if_neg (by omega), if_neg hc, if_neg (by omega)]
  · have hd : col / (k + 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hm : col % (k + 1) = col - (k + 1) := by
      have := Nat.mod_add_div col (k + 1); rw [hd] at this; omega
    rw [hd, hm]
    by_cases hc : col = 2 * k + 1
    · rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg (by omega), if_neg hc]
  · have hd : col / (k + 1) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `winEntry` of a row supported on its first entry. -/
lemma winEntry_single' (x : ℤ) (L K l : ℕ) (hL : 1 ≤ L) (hl : l < K) :
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

/-- The KN skeleton entry of `skB2 ρ` at block `d`, level `l`, as the S1 skeleton row. -/
lemma skB2_entry (k ρ : ℕ) (d : Fin 3) (l : ℕ) (hl : l < depth 2 k d) :
    ((winEntry (skB2 ρ 2 d) (win 2 d) (depth 2 k d) l : ℤ)) =
      ((skRowS1 3 k ρ (off 2 k d + l) : ℕ) : ℤ) := by
  have hlt : off 2 k d + l < 3 * k + 2 := by
    fin_cases d <;> simp [off, depth] at hl ⊢ <;> omega
  rw [skRowS1_eq k ρ _ hlt]
  obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
  · have hd : depth 2 k 0 = k + 1 := by simp [depth]
    have ho : off 2 k 0 = 0 := by simp [off]
    rw [hd] at hl
    have hw : skB2 ρ 2 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
    rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl, ho, zero_add]
    by_cases h : l = k
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, if_neg (by omega)]; simp
  · have hd : depth 2 k 1 = k + 1 := by simp [depth]
    have ho : off 2 k 1 = k + 1 := by simp [off, depth]
    rw [hd] at hl
    have hw : skB2 ρ 2 1 = ![(ρ : ℤ) ^ 2, 0, 0, 0] := rfl
    rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl, ho]
    by_cases h : l = k
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; push_cast; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · have hd : depth 2 k 2 = k := by simp [depth]
    have ho : off 2 k 2 = 2 * k + 2 := by simp [off, depth]; ring
    rw [hd] at hl
    have hw : skB2 ρ 2 2 = ![((0 : ℕ) : ℤ), 0, 0, 0] := by
      ext i; fin_cases i <;> rfl
    rw [hw, hd, winEntry_single' _ _ _ _ (by simp [win]) hl, ho]
    rw [if_neg (show ¬ (2 * k + 2 + l = k) by omega),
      if_neg (show ¬ (2 * k + 2 + l = 2 * k + 1) by omega)]
    split_ifs <;> simp

end Z3NetKN.Proofs.D3

namespace Z3NetKN.Proofs

open Matrix Finset D3

/-- **`rem:B2`, the two skeleton predicates coincide.** -/
theorem B2_skel_iff (p k ρ : ℕ) (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p)) :
    IsS1skel 3 p k ρ C ↔ IsKNskel 2 p k (skB2 ρ) C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro c j col hj hcol
      rw [← offS1_eq]
      exact h1 c j (by rw [depthS1_eq]; exact hj) col hcol
    · intro c d hc l hl
      have hc2 : c = 2 := by
        rcases c with ⟨_ | _ | _ | c, h⟩ <;> simp at hc ⊢ <;> omega
      subst hc2
      have hlt : off 2 k d + l < 3 * k + 2 := by
        fin_cases d <;> simp [off, depth] at hl ⊢ <;> omega
      have := h2 2 rfl (off 2 k d + l) hlt
      rw [show depth 2 k 2 = k by simp [depth], this, skB2_entry k ρ d l hl]
      push_cast; rfl
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro c j hj col hcol
      rw [offS1_eq]
      exact h1 c j col (by rw [← depthS1_eq]; exact hj) hcol
    · intro z hz col hcol
      have hz2 : z = 2 := Fin.ext (by simp; omega)
      subst hz2
      have hcol' : col < 3 * k + 2 := hcol
      -- decompose `col` into its block and level
      obtain ⟨d, l, hl, rfl⟩ : ∃ d : Fin 3, ∃ l, l < depth 2 k d ∧ col = off 2 k d + l := by
        rcases (show col < k + 1 ∨ (k + 1 ≤ col ∧ col < 2 * k + 2) ∨ 2 * k + 2 ≤ col by omega)
          with h | h | h
        · exact ⟨0, col, by simp [depth]; omega, by simp [off]⟩
        · exact ⟨1, col - (k + 1), by simp [depth]; omega, by simp [off, depth]; omega⟩
        · exact ⟨2, col - (2 * k + 2), by simp [depth]; omega, by simp [off, depth]; omega⟩
      have := h2 2 d (by simp) l hl
      rw [show depth 2 k 2 = k by simp [depth]] at this
      rw [this, skB2_entry k ρ d l hl]
      push_cast; rfl

/-- **`rem:B2`, separation (integer form).** -/
theorem B2_rem_sep (p k ρ : ℕ) (hp : p.Prime) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (4 * k + 2) ≤
      torusDist2 (p ^ (3 * k + 2)) (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) := by
  rcases Nat.lt_or_ge ρ 2 with h | h
  · rw [show ρ - 1 = 0 by omega]; simp
  · have hS : Z3NetS1.IsS1skel 3 p k ρ C := (B2_skel_iff p k ρ C).2 hC
    have := Z3NetS1.S1_sep 3 p k ρ (le_refl 3) hp h hρp C hS v w hvw
    rw [show 2 * ((3 - 1) * (k + 1) - 1) = 4 * k + 2 by omega] at this
    exact this

/-- **`rem:B2`, separation (real form).** -/
theorem B2_rem_sep_real (p k ρ : ℕ) (hp : p.Prime) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((digPoint p (3 * k + 2) C v c : ℤ) - (digPoint p (3 * k + 2) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
  rcases Nat.lt_or_ge ρ 2 with h | h
  · rw [show ρ = 1 by omega]; simp only [Nat.cast_one, sub_self, zero_mul]
    exact Real.sqrt_nonneg _
  · have hS : Z3NetS1.IsS1skel 3 p k ρ C := (B2_skel_iff p k ρ C).2 hC
    have := Z3NetS1.S1_sep_real 3 p k ρ (le_refl 3) hp h hρp C hS v w hvw
    simp only [Nat.cast_ofNat] at this
    exact this

/-- **`rem:B2`, the free-jitter relaxation and its binding step.** -/
theorem B2_relax (p ρ : ℕ) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p) :
    (∀ a : Fin 3 → ℤ, (p : ℤ) ∣ a 2 - (ρ : ℤ) * a 0 - (ρ : ℤ) ^ 2 * a 1 → a ≠ 0 →
      ((ρ : ℤ) - 1) ^ 2 ≤ ∑ c, (max (|a c| - 1) 0) ^ 2) ∧
    ((p : ℤ) ∣ (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 2 - (ρ : ℤ) * (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 0
        - (ρ : ℤ) ^ 2 * (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 1) ∧
    (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) ≠ 0 ∧
    ∑ c, (max (|(![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) c| - 1) 0) ^ 2 = ((ρ : ℤ) - 1) ^ 2 := by
  have hρ' : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a hdiv ha
    have hL := Z3NetS1.L2s_min 3 p ρ (by norm_num) hρp ![a 0, a 1] (a 2)
      (by
        have e : a 2 - ∑ i : Fin (3 - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * (![a 0, a 1] : Fin 2 → ℤ) i =
            a 2 - (ρ : ℤ) * a 0 - (ρ : ℤ) ^ 2 * a 1 := by
          simp [Fin.sum_univ_two]; ring
        rw [e]; exact hdiv)
      (by
        rintro ⟨hx, hz⟩
        apply ha
        funext c
        fin_cases c
        · simpa using congrFun hx 0
        · simpa using congrFun hx 1
        · simpa using hz)
    -- one coordinate has `|a c| ≥ ρ`
    have hsq : ∀ c : Fin 3, 0 ≤ (max (|a c| - 1) 0) ^ 2 := fun c => sq_nonneg _
    have key : ∃ c : Fin 3, (ρ : ℤ) ≤ |a c| := by
      rcases hL with h | ⟨i, hi⟩
      · exact ⟨2, h⟩
      · fin_cases i
        · exact ⟨0, by simpa using hi⟩
        · exact ⟨1, by simpa using hi⟩
    obtain ⟨c, hc⟩ := key
    have h1 : ((ρ : ℤ) - 1) ^ 2 ≤ (max (|a c| - 1) 0) ^ 2 := by
      have : (ρ : ℤ) - 1 ≤ max (|a c| - 1) 0 := le_max_of_le_left (by linarith)
      nlinarith
    calc ((ρ : ℤ) - 1) ^ 2 ≤ (max (|a c| - 1) 0) ^ 2 := h1
      _ ≤ ∑ c, (max (|a c| - 1) 0) ^ 2 :=
        Finset.single_le_sum (fun c _ => hsq c) (Finset.mem_univ c)
  · have e : (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 2 - (ρ : ℤ) * (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 0
        - (ρ : ℤ) ^ 2 * (![-(ρ : ℤ), 1, 0] : Fin 3 → ℤ) 1 = 0 := by simp; ring
    rw [e]; exact dvd_zero _
  · intro h
    have := congrFun h 1
    simp at this
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, abs_neg, abs_one, sub_self, abs_zero, zero_sub]
    rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    simp

/-- `ρ_3(p) = ρ` from `ρ³ < p ≤ (ρ+1)³`. -/
lemma D3.rhoS3_eq (p ρ : ℕ) (h1 : ρ ^ 3 < p) (h2 : p ≤ (ρ + 1) ^ 3) : rhoS 3 p = ρ := by
  unfold rhoS
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => h1, ?_⟩
  · have : ρ ≤ ρ ^ 3 := Nat.le_self_pow (by norm_num) ρ
    omega
  · intro n hn _ hP
    have : (ρ + 1) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    omega

/-- The real `(·)^(1/3)` is a cube root. -/
lemma D3.rpow_third_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / (3 : ℝ))) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `b < a · x^(-1/3)` from `b³ x < a³` (`x > 0`, `a > 0`). -/
lemma D3.lt_mul_rpow_neg_third (a b x : ℝ) (hx : 0 < x) (ha : 0 < a) (h : b ^ 3 * x < a ^ 3) :
    b < a * x ^ (-(1 / (3 : ℝ))) := by
  have ht : 0 < x ^ (1 / (3 : ℝ)) := by positivity
  rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, lt_div_iff₀ ht]
  rcases lt_or_ge (b * x ^ (1 / (3 : ℝ))) 0 with hb | hb
  · linarith
  · apply lt_of_pow_lt_pow_left₀ 3 ha.le
    rw [mul_pow, rpow_third_cube x hx.le]; exact h

/-- `a · x^(-1/3) ≤ b` from `a³ ≤ b³ x` (`x > 0`, `b ≥ 0`). -/
lemma D3.mul_rpow_neg_third_le (a b x : ℝ) (hx : 0 < x) (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 3 * x) :
    a * x ^ (-(1 / (3 : ℝ))) ≤ b := by
  have ht : 0 < x ^ (1 / (3 : ℝ)) := by positivity
  rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, div_le_iff₀ ht]
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, rpow_third_cube x hx.le]; exact h

/-- **`rem:B2`, constants.** -/
theorem B2_const :
    Nat.Prime 1361 ∧ 0.9 < ((rhoS 3 1361 : ℝ) - 1) * (1361 : ℝ) ^ (-(1 / (3 : ℝ))) ∧
    (∀ p : ℕ, p.Prime → p < 1361 → ((rhoS 3 p : ℝ) - 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) ≤ 0.9) ∧
    (∀ p : ℕ, p.Prime → 6863 ≤ p →
      19 ≤ rhoS 3 p ∧ 0.9 < ((rhoS 3 p : ℝ) - 1) * (p : ℝ) ^ (-(1 / (3 : ℝ)))) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [D3.rhoS3_eq 1361 11 (by norm_num) (by norm_num)]
    apply D3.lt_mul_rpow_neg_third _ _ _ (by norm_num) (by norm_num)
    norm_num
  · intro p hp hlt
    set ρ := rhoS 3 p with hρ
    have hsp : ρ ^ 3 < p := Nat.findGreatest_spec (P := fun ρ => ρ ^ 3 < p) (Nat.zero_le p)
      (by simp; exact hp.pos)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rcases Nat.lt_or_ge ρ 11 with h11 | h11
    · rcases Nat.eq_zero_or_pos ρ with h0 | h0
      · rw [h0]; simp only [Nat.cast_zero, zero_sub, neg_one_mul]
        have : 0 ≤ (p : ℝ) ^ (-(1 / (3 : ℝ))) := by positivity
        linarith
      · -- `(ρ - 1) p^(-1/3) ≤ (ρ - 1)/ρ ≤ 0.9`
        apply D3.mul_rpow_neg_third_le _ _ _ hp0 (by norm_num)
        have hρr : (ρ : ℝ) ≤ 10 := by exact_mod_cast (show ρ ≤ 10 by omega)
        have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast h0
        have hpρ : (ρ : ℝ) ^ 3 ≤ p := by exact_mod_cast hsp.le
        have h3 : ((ρ : ℝ) - 1) ^ 3 ≤ (0.9 * ρ) ^ 3 := by
          apply pow_le_pow_left₀ (by linarith); linarith
        calc ((ρ : ℝ) - 1) ^ 3 ≤ (0.9 * ρ) ^ 3 := h3
          _ = 0.9 ^ 3 * (ρ : ℝ) ^ 3 := by ring
          _ ≤ 0.9 ^ 3 * p := by gcongr
    · exfalso
      have : 11 ^ 3 ≤ ρ ^ 3 := Nat.pow_le_pow_left h11 3
      have h1332 : 1332 ≤ p := by omega
      interval_cases p <;> norm_num at hp
  · intro p hp h6863
    have h19 : 19 ≤ rhoS 3 p := Nat.le_findGreatest (by omega) (by norm_num; omega)
    refine ⟨h19, ?_⟩
    have hc := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
    obtain ⟨-, -, -, hlt, -, -⟩ := hc
    have e : Z3NetS1.rhoS 3 p = rhoS 3 p := rfl
    rw [e] at hlt
    simp only [Nat.cast_ofNat] at hlt
    refine lt_of_le_of_lt ?_ hlt
    have : (19 : ℝ) ≤ rhoS 3 p := by exact_mod_cast h19
    rw [le_div_iff₀ (by linarith)]; linarith

end Z3NetKN.Proofs
