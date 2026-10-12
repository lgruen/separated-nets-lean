/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColNet

@[expose] public section

/-!
# V14 stage S9′: the net `𝒞_q` (`thm:col`(1)), the gap `3g` of digital column nets
(`thm:col`(2), `lem:drift`(3)), covering

* `wCol_props`, `col_boxMinor_unit`, `col_net`: `thm:col`(1) through `lem:nie` (`nie_zmod`): the
  box minors `±1`, `±a_c`, `a_x + a_y` are units for `gcd(q, 6) = 1` (`3a_c = q + w_c`).
* `gap_formula`: for a digital column net with `0 ≤ a_i < q`, every step has
  `3Δ_i - 2q² ≡ ε_i - 3qκ' - q² (mod 3q²)` (`ε_i = q w_i + 3 r_i`, `κ'` the wrap of the third digit),
  so `3g = q² - max_i ε_i` as soon as `0 ≤ max ε ≤ q²` and `ε_i - 3q ≥ -q²` (the printed case
  analysis of the proof of `thm:col`(2) and of `lem:drift`(3)).
* `col_gap`: `3g(𝒞_q) = τ`; `drift_eta`: `lem:drift`(3).
* `col_cover`: one point per cell gives `h ≤ √3 N^{-1/3}`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ## Residues and units -/

lemma val_intCast_of (z : ℤ) (h0 : 0 ≤ z) (h1 : z < q) : (((z : ZMod q).val : ℕ) : ℤ) = z := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]

lemma val_neg_one (hq : 2 ≤ q) : ((((-1 : ℤ) : ZMod q).val : ℕ) : ℤ) = q - 1 := by
  rw [ZMod.val_intCast, show (-1 : ℤ) = (q - 1) + q * (-1) by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) (by omega)]

lemma unit_two (h6 : Nat.Coprime q 6) : IsUnit (2 : ZMod q) := by
  have := (ZMod.isUnit_iff_coprime 2 q).2
    (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) h6).symm
  simpa using this

lemma unit_three (h6 : Nat.Coprime q 6) : IsUnit (3 : ZMod q) := by
  have := (ZMod.isUnit_iff_coprime 3 q).2
    (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h6).symm
  simpa using this

lemma q_mod3 (h6 : Nat.Coprime q 6) : q % 3 = 1 ∨ q % 3 = 2 := by
  have h3 : Nat.Coprime q 3 := Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h6
  have : q % 3 ≠ 0 := by
    intro h
    have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h
    have := Nat.Coprime.coprime_dvd_left this h3
    norm_num at this
  omega

/-- `w` of `def:col`: `∑ w = 0`, `w_c ≡ -q (mod 3)`, `|w_c| ≤ 2`, and `w_c` is a unit. -/
lemma wCol_props (h6 : Nat.Coprime q 6) :
    ∑ c, wCol q c = 0 ∧ (∀ c, (3 : ℤ) ∣ q + wCol q c) ∧ (∀ c, |wCol q c| ≤ 2) ∧
      ∀ c, IsUnit ((wCol q c : ℤ) : ZMod q) := by
  have h2 := unit_two h6
  rcases q_mod3 h6 with h | h
  · have hw : wCol q = ![-1, -1, 2] := by simp [wCol, h]
    refine ⟨by simp [hw, Fin.sum_univ_three], fun c => ?_, fun c => ?_, fun c => ?_⟩
    · fin_cases c <;> simp [hw] <;> omega
    · fin_cases c <;> simp [hw]
    · fin_cases c <;> simp [hw, h2]
  · have hw : wCol q = ![-2, 1, 1] := by simp [wCol, h]
    refine ⟨by simp [hw, Fin.sum_univ_three], fun c => ?_, fun c => ?_, fun c => ?_⟩
    · fin_cases c <;> simp [hw] <;> omega
    · fin_cases c <;> simp [hw]
    · fin_cases c <;> simp [hw, h2]

lemma three_colA (w : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (c : Fin 3) :
    (3 : ZMod q) * ((colA q w c : ℤ) : ZMod q) = ((w c : ℤ) : ZMod q) := by
  have h : 3 * colA q w c = q + w c := Int.mul_ediv_cancel' (hw3 c)
  have := congrArg (fun z : ℤ => (z : ZMod q)) h
  push_cast at this
  rw [this]; simp

/-- **`thm:col`(1)**: the box minors of `𝒞_q` are units. -/
lemma col_boxMinor_unit (h6 : Nat.Coprime q 6) (d : Fin 3 → ℕ) (hd : ∑ c, d c = 3) :
    IsUnit (boxMatrix (colGen q) d).det := by
  obtain ⟨hw0, hw3, -, hwu⟩ := wCol_props (q := q) h6
  have h3 := unit_three (q := q) h6
  have ha : ∀ c, IsUnit (((colA q (wCol q) c : ℤ) : ZMod q)) := by
    intro c
    have := hwu c
    rw [← three_colA _ hw3 c] at this
    exact isUnit_of_mul_isUnit_right this
  have hab : IsUnit (((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)) := by
    have e : (3 : ZMod q) * (((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)) =
        -((wCol q 2 : ℤ) : ZMod q) := by
      rw [mul_add, three_colA _ hw3, three_colA _ hw3]
      have : ((wCol q 0 + wCol q 1 + wCol q 2 : ℤ) : ZMod q) = 0 := by
        rw [show wCol q 0 + wCol q 1 + wCol q 2 = ∑ c, wCol q c by simp [Fin.sum_univ_three], hw0]
        simp
      push_cast at this
      linear_combination this
    have := (hwu 2).neg
    rw [← e] at this
    exact isUnit_of_mul_isUnit_right this
  have hm := colW_boxMinor (q := q) (wCol q) d hd
  simp only [colGen]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h | h | h | h | h | h | h | h <;> rw [h]
  · exact isUnit_one
  · exact ha 0
  · exact (ha 0).neg
  · exact ha 1
  · exact (ha 1).neg
  · exact (ha 2).neg
  · exact ha 2
  · exact hab

/-- **`thm:col`(1)**: `𝒞_q` is a digital `(0,3,3)`-net over `ℤ/qℤ`. -/
lemma col_net (h6 : Nat.Coprime q 6) : IsNet0 3 q 3 (digPoint q 3 (colGen q)) :=
  (Z3NetF.Proofs.nie_zmod q (colGen q)).2 fun d hd => col_boxMinor_unit h6 d hd

/-! ## Covering -/

lemma cube_rpow (x : ℝ) (hx : 0 < x) : (x ^ 3) ^ (-(1 / (3 : ℝ))) = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num [Real.rpow_neg_one]

/-- One point per cell: every `y ∈ [0,1)³` is within `√3/q = √3 N^{-1/3}` of a point. -/
lemma col_cover (φ : (Fin 3 → ZMod q) → ℕ) (hφ : ∀ n, φ n < q ^ 2) (y : Fin 3 → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ n : Fin 3 → ZMod q, Real.sqrt (∑ c, (y c - (colPt q φ n c : ℝ) / (q : ℝ) ^ 3) ^ 2) ≤
      Real.sqrt 3 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set f : Fin 3 → ℕ := fun c => ⌊y c * q⌋₊
  have hf : ∀ c, f c < q := by
    intro c
    have : y c * q < q := by nlinarith [(hy c).2]
    exact (Nat.floor_lt (by nlinarith [(hy c).1])).2 (by exact_mod_cast this)
  refine ⟨fun c => (f c : ZMod q), ?_⟩
  rw [cube_rpow _ hq]
  have hval : ∀ c, (((f c : ℕ) : ZMod q)).val = f c := fun c => ZMod.val_cast_of_lt (hf c)
  have hb : ∀ c, (y c - (colPt q φ (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) ^ 2 ≤
      ((q : ℝ)⁻¹) ^ 2 := by
    intro c
    simp only [colPt, hval]
    have h1 : (f c : ℝ) ≤ y c * q := Nat.floor_le (by nlinarith [(hy c).1])
    have h2 : y c * q < f c + 1 := Nat.lt_floor_add_one _
    have hφ1 : (φ (fun c => (f c : ZMod q)) : ℝ) < (q : ℝ) ^ 2 := by
      exact_mod_cast hφ _
    have hφ0 : (0 : ℝ) ≤ φ (fun c => (f c : ZMod q)) := by positivity
    set u : ℝ := ((q ^ 2 * f c + φ (fun c => (f c : ZMod q)) : ℕ) : ℝ) / (q : ℝ) ^ 3 with hu
    have hqu : (q : ℝ) * u = f c + φ (fun c => (f c : ZMod q)) / (q : ℝ) ^ 2 := by
      rw [hu]; push_cast; field_simp
    have ht1 : φ (fun c => (f c : ZMod q)) / (q : ℝ) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; exact hφ1
    have ht0 : 0 ≤ φ (fun c => (f c : ZMod q)) / (q : ℝ) ^ 2 := by positivity
    have e : y c - u = (q : ℝ)⁻¹ * ((q : ℝ) * y c - (q : ℝ) * u) := by field_simp
    have hi : 0 < (q : ℝ)⁻¹ := inv_pos.2 hq
    rw [e]
    apply sq_le_sq'
    · nlinarith
    · nlinarith

  calc Real.sqrt (∑ c, (y c - (colPt q φ (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) ^ 2)
      ≤ Real.sqrt (3 * ((q : ℝ)⁻¹) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc _ ≤ ∑ _c : Fin 3, ((q : ℝ)⁻¹) ^ 2 := Finset.sum_le_sum fun c _ => hb c
          _ = 3 * ((q : ℝ)⁻¹) ^ 2 := by simp
    _ = Real.sqrt 3 * (q : ℝ)⁻¹ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]

/-! ## The gap `3g` of digital column nets -/

lemma wrapI_cases (x y : ℕ) : wrapI q x y = 0 ∨ wrapI q x y = 1 := by
  unfold wrapI; split_ifs <;> simp

lemma gap_lb (e M : ℤ) (h1 : e ≤ M) (h0 : 0 ≤ M) (h2 : M ≤ (q : ℤ) ^ 2) (h3 : -(q : ℤ) ^ 2 ≤ e) :
    (q : ℤ) ^ 2 - M ≤ cres (3 * q ^ 2) (e - q ^ 2) := by
  have hq : (0 : ℤ) < (q : ℤ) ^ 2 := by
    have : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  apply cres_ge _ (by have := Nat.pos_of_ne_zero (NeZero.ne q); positivity)
  intro k
  push_cast
  rcases le_or_gt k 0 with hk | hk
  · have : e - (q : ℤ) ^ 2 + 3 * (q : ℤ) ^ 2 * k ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]; nlinarith
  · have : 0 ≤ e - (q : ℤ) ^ 2 + 3 * (q : ℤ) ^ 2 * k := by nlinarith
    rw [abs_of_nonneg this]; nlinarith

lemma gap_eq (M : ℤ) (h0 : 0 ≤ M) (h2 : M ≤ (q : ℤ) ^ 2) :
    (cres (3 * q ^ 2) (M - q ^ 2) : ℤ) = q ^ 2 - M := by
  rw [cres_eq_abs _ (by have := Nat.pos_of_ne_zero (NeZero.ne q); positivity)]
  · rw [abs_of_nonpos (by linarith)]; ring
  · rw [abs_of_nonpos (by linarith)]; push_cast; linarith

/-- `3Δ_i - 2q² = (ε_i - 3qκ') - q² - 3q²κ` for a digital column net with `0 ≤ a_i < q`. -/
lemma step3 (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (hval : ((((colA q w i : ℤ) : ZMod q)).val : ℤ) = colA q w i) (n : Fin 3 → ZMod q) :
    3 * colStep q (colPhi q w ℓ) i n - 2 * q ^ 2 =
      ((q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val -
          3 * q * wrapI q (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val) - q ^ 2 +
        ((3 * q ^ 2 : ℕ) : ℤ) * (-wrapI q (colH q w n).val (((colA q w i : ℤ) : ZMod q)).val) := by
  have ha : 3 * colA q w i = q + w i := Int.mul_ediv_cancel' (hw3 i)
  rw [step_formula, hval]
  push_cast
  linear_combination (q : ℤ) * ha

/-- The gap formula: `3g = q² - M`, `M = max_i ε_i`. -/
lemma gap_formula (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c)
    (hval : ∀ i, ((((colA q w i : ℤ) : ZMod q)).val : ℤ) = colA q w i) (M : ℤ)
    (hM : ∀ i, (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val ≤ M)
    (i0 : Fin 3) (hi0 : (q : ℤ) * w i0 + 3 * (((ℓ i0 : ℤ) : ZMod q)).val = M)
    (h0 : 0 ≤ M) (h2 : M ≤ (q : ℤ) ^ 2)
    (hlow : ∀ i, -(q : ℤ) ^ 2 ≤ (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q) :
    (colGap q (colPhi q w ℓ) : ℤ) = q ^ 2 - M := by
  apply le_antisymm
  · have h := colGap_le (colPhi q w ℓ) i0 0
    have e := step3 w ℓ hw3 i0 (hval i0) 0
    have hJ : colJ q ℓ 0 = 0 := by simp [colJ]
    have hH : colH q w 0 = 0 := by simp [colH]
    simp only [hJ, hH, ZMod.val_zero, wrapI, zero_add, ZMod.val_lt, if_true] at e
    rw [e] at h
    simp only [mul_zero, sub_zero, neg_zero, add_zero, hi0] at h
    have := gap_eq (q := q) M h0 h2
    exact_mod_cast (show (colGap q (colPhi q w ℓ) : ℤ) ≤ _ by exact_mod_cast h).trans this.le
  · obtain ⟨⟨i, n⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (univ : Finset (Fin 3 × (Fin 3 → ZMod q)))) univ_nonempty
      (fun x => cres (3 * q ^ 2) (3 * colStep q (colPhi q w ℓ) x.1 x.2 - 2 * q ^ 2))
    have hG : colGap q (colPhi q w ℓ) = cres (3 * q ^ 2) (3 * colStep q (colPhi q w ℓ) i n - 2 * q ^ 2) :=
      hmin
    rw [hG, step3 w ℓ hw3 i (hval i) n, cres_add_mul]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    refine gap_lb _ _ ?_ h0 h2 ?_
    · rcases wrapI_cases (q := q) (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val with h | h <;> rw [h] <;>
        linarith [hM i]
    · rcases wrapI_cases (q := q) (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val with h | h <;> rw [h] <;>
        linarith [hlow i]

/-! ## `𝒞_q`: the values `ε_i`, `3g = τ` -/

lemma col_vals (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (∀ i, ((((colA q (wCol q) i : ℤ) : ZMod q)).val : ℤ) = colA q (wCol q) i) ∧
    (q % 3 = 2 → (q : ℤ) * wCol q 0 + 3 * (((ellCol 0 : ℤ) : ZMod q)).val = q - 3 ∧
      (q : ℤ) * wCol q 1 + 3 * (((ellCol 1 : ℤ) : ZMod q)).val = q + 3 ∧
      (q : ℤ) * wCol q 2 + 3 * (((ellCol 2 : ℤ) : ZMod q)).val = q) ∧
    (q % 3 = 1 → (q : ℤ) * wCol q 0 + 3 * (((ellCol 0 : ℤ) : ZMod q)).val = 2 * q - 3 ∧
      (q : ℤ) * wCol q 1 + 3 * (((ellCol 1 : ℤ) : ZMod q)).val = 3 - q ∧
      (q : ℤ) * wCol q 2 + 3 * (((ellCol 2 : ℤ) : ZMod q)).val = 2 * q) := by
  have hm1 := val_neg_one (q := q) (by omega)
  have h1 : ((((1 : ℤ) : ZMod q)).val : ℤ) = 1 := val_intCast_of 1 (by norm_num) (by omega)
  refine ⟨fun i => ?_, fun h => ?_, fun h => ?_⟩
  · apply val_intCast_of
    · rcases q_mod3 h6 with h | h <;> fin_cases i <;> simp [colA, wCol, h] <;> omega
    · rcases q_mod3 h6 with h | h <;> fin_cases i <;> simp [colA, wCol, h] <;> omega
  · have hw : wCol q = ![-2, 1, 1] := by simp [wCol, h]
    rw [hw]
    refine ⟨?_, ?_, ?_⟩
    · show (q : ℤ) * (-2) + 3 * ((((-1 : ℤ) : ZMod q)).val : ℤ) = q - 3
      rw [hm1]; ring
    · show (q : ℤ) * 1 + 3 * ((((1 : ℤ) : ZMod q)).val : ℤ) = q + 3
      rw [h1]; ring
    · show (q : ℤ) * 1 + 3 * ((((0 : ℤ) : ZMod q)).val : ℤ) = q
      rw [Int.cast_zero, ZMod.val_zero]; ring
  · have hw : wCol q = ![-1, -1, 2] := by simp [wCol, show q % 3 ≠ 2 by omega]
    rw [hw]
    refine ⟨?_, ?_, ?_⟩
    · show (q : ℤ) * (-1) + 3 * ((((-1 : ℤ) : ZMod q)).val : ℤ) = 2 * q - 3
      rw [hm1]; ring
    · show (q : ℤ) * (-1) + 3 * ((((1 : ℤ) : ZMod q)).val : ℤ) = 3 - q
      rw [h1]; ring
    · show (q : ℤ) * 2 + 3 * ((((0 : ℤ) : ZMod q)).val : ℤ) = 2 * q
      rw [Int.cast_zero, ZMod.val_zero]; ring

lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp

/-- **`thm:col`(2)**: `3g(𝒞_q) = τ`. -/
lemma col_gap (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (colGap q (colPhi q (wCol q) ellCol) : ℤ) = tauCol q := by
  obtain ⟨hval, h2v, h1v⟩ := col_vals h6 hq
  obtain ⟨-, hw3, -, -⟩ := wCol_props (q := q) h6
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  rcases q_mod3 h6 with h | h
  · obtain ⟨e0, e1, e2⟩ := h1v h
    have ht : tauCol q = (q : ℤ) ^ 2 - 2 * q := by simp [tauCol, show q % 3 ≠ 2 by omega]
    rw [ht]
    apply gap_formula _ _ hw3 hval (2 * q)
      (fun i => by rcases fin3_cases i with rfl | rfl | rfl <;> linarith) 2 e2 (by omega) (by nlinarith)
    intro i; rcases fin3_cases i with rfl | rfl | rfl <;> nlinarith
  · obtain ⟨e0, e1, e2⟩ := h2v h
    have ht : tauCol q = (q : ℤ) ^ 2 - q - 3 := by simp [tauCol, h]
    rw [ht, show (q : ℤ) ^ 2 - q - 3 = q ^ 2 - (q + 3) by ring]
    apply gap_formula _ _ hw3 hval (q + 3)
      (fun i => by rcases fin3_cases i with rfl | rfl | rfl <;> linarith) 1 e1 (by omega) (by nlinarith)
    intro i; rcases fin3_cases i with rfl | rfl | rfl <;> nlinarith

end Z3NetC.Proofs
