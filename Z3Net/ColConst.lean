/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColDist

@[expose] public section

/-!
# V14 stage S9′: the constant `δN^{1/3}` of `𝒞_q` (`thm:col`(2), (3))

`cCol q = √((2q⁴ + τ²)/3)/q² = √((2 + t²)/3)`, `t = τ/q²` (`1 - 1/q - 3/q²` for `q ≡ 2`,
`1 - 2/q` for `q ≡ 1 (mod 3)`): monotone in each residue class (`cCol_lt`), the values at
`q = 5, 7, 37, 41` (`√513/25`, `√2009/49`), the expansions of `thm:col`(2) with explicit
`O(q⁻³)` constants (`cCol_exp2`, `cCol_exp1`), `cCol → 1`, and the real-valued separation
`cCol_sep` (toroidal, at unit scale times `N^{1/3}`).
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix Filter Topology

set_option linter.unusedSectionVars false

/-- `t = τ/q²`. -/
noncomputable def tC (q : ℕ) : ℝ := (tauCol q : ℝ) / (q : ℝ) ^ 2

lemma cCol_eq (q : ℕ) (hq : 0 < q) : cCol q = Real.sqrt ((2 + tC q ^ 2) / 3) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : (2 + tC q ^ 2) / 3 = ((2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2) / 3) / ((q : ℝ) ^ 2) ^ 2 := by
    unfold tC; field_simp
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  rfl

lemma tC_two (q : ℕ) (hq : 0 < q) (h : q % 3 = 2) : tC q = 1 - 1 / q - 3 / (q : ℝ) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold tC tauCol; rw [if_pos h]; push_cast; field_simp

lemma tC_one (q : ℕ) (hq : 0 < q) (h : q % 3 ≠ 2) : tC q = 1 - 2 / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold tC tauCol; rw [if_neg h]; push_cast; field_simp

lemma tC_bounds (q : ℕ) (hq : 5 ≤ q) : 1 - 4 / (q : ℝ) ≤ tC q ∧ tC q ≤ 1 ∧ 0 ≤ tC q := by
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  by_cases h : q % 3 = 2
  · rw [tC_two q (by omega) h]
    have h1 : 1 / (q : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hq'
    have h2 : 3 / (q : ℝ) ^ 2 ≤ 3 / (q : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hq0; nlinarith
    have h3 : 0 < 3 / (q : ℝ) ^ 2 := by positivity
    have h4 : 0 < 1 / (q : ℝ) := by positivity
    refine ⟨?_, by linarith, ?_⟩
    · have : 4 / (q : ℝ) = 1 / q + 3 / q := by ring
      linarith
    · have : 3 / (q : ℝ) ≤ 3 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq'
      linarith
  · rw [tC_one q (by omega) h]
    have h1 : 2 / (q : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq'
    have h4 : 0 < 2 / (q : ℝ) := by positivity
    refine ⟨?_, by linarith, by linarith⟩
    have : 2 / (q : ℝ) ≤ 4 / q := div_le_div_of_nonneg_right (by norm_num) hq0.le
    linarith

lemma cCol_le_one (q : ℕ) (hq : 5 ≤ q) : cCol q ≤ 1 := by
  rw [cCol_eq q (by omega)]
  obtain ⟨-, h1, h0⟩ := tC_bounds q hq
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  nlinarith

lemma tC_le_cCol (q : ℕ) (hq : 5 ≤ q) : tC q ≤ cCol q := by
  rw [cCol_eq q (by omega)]
  obtain ⟨-, h1, h0⟩ := tC_bounds q hq
  rw [Real.le_sqrt h0 (by positivity)]
  nlinarith

/-- `cCol → 1`. -/
lemma cCol_tendsto : Tendsto cCol atTop (𝓝 1) := by
  have hl : Tendsto (fun q : ℕ => 1 - 4 / (q : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (4 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 5] with q hq
    exact (tC_bounds q hq).1.trans (tC_le_cCol q hq)
  · filter_upwards [eventually_ge_atTop 5] with q hq
    exact cCol_le_one q hq

/-- **`thm:col`(3)**: within each residue class modulo `3`, `cCol` increases with `q`. -/
lemma cCol_lt (q q' : ℕ) (hq : 5 ≤ q) (hlt : q < q') (hmod : q % 3 = q' % 3) : cCol q < cCol q' := by
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hqq : (q : ℝ) < q' := by exact_mod_cast hlt
  have hq0 : (0 : ℝ) < q := by linarith
  have ht : tC q < tC q' := by
    by_cases h : q % 3 = 2
    · rw [tC_two q (by omega) h, tC_two q' (by omega) (by omega)]
      have a1 : 1 / (q' : ℝ) < 1 / q := one_div_lt_one_div_of_lt hq0 hqq
      have a2 : 3 / (q' : ℝ) ^ 2 < 3 / (q : ℝ) ^ 2 :=
        div_lt_div_of_pos_left (by norm_num) (by positivity) (by nlinarith)
      linarith
    · rw [tC_one q (by omega) h, tC_one q' (by omega) (by omega)]
      have : 2 / (q' : ℝ) < 2 / q := div_lt_div_of_pos_left (by norm_num) hq0 hqq
      linarith
  obtain ⟨-, -, h0⟩ := tC_bounds q hq
  rw [cCol_eq q (by omega), cCol_eq q' (by omega)]
  apply Real.sqrt_lt_sqrt (by positivity)
  nlinarith

lemma cCol_le (q q' : ℕ) (hq : 5 ≤ q) (hle : q ≤ q') (hmod : q % 3 = q' % 3) : cCol q ≤ cCol q' := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact le_refl _
  · exact (cCol_lt q q' hq hlt hmod).le

lemma cCol_5 : cCol 5 = Real.sqrt 513 / 25 := by
  unfold cCol tauCol; norm_num

lemma cCol_7 : cCol 7 = Real.sqrt 2009 / 49 := by
  unfold cCol tauCol; norm_num

lemma cCol_37 : cCol 37 = Real.sqrt 1808449 / 1369 := by
  unfold cCol tauCol; norm_num

lemma cCol_41 : cCol 41 = Real.sqrt 2777097 / 1681 := by
  unfold cCol tauCol; norm_num

/-- **`thm:col`(3)**: the values. -/
lemma col_values :
    0.9059 < cCol 5 ∧ cCol 5 < 0.9060 ∧ 0.9147 < cCol 7 ∧ cCol 7 < 0.9148 ∧
      0.9823 < cCol 37 ∧ cCol 37 < 0.9824 ∧ 0.9913 < cCol 41 := by
  rw [cCol_5, cCol_7, cCol_37, cCol_41]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num

lemma coprime6_ge (q : ℕ) (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (q % 3 = 2 ∧ 5 ≤ q) ∨ (q % 3 = 1 ∧ 7 ≤ q) := by
  have : NeZero q := ⟨by omega⟩
  have h2 : Nat.Coprime q 2 := Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) h6
  have hodd : q % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have : 2 ∣ q := Nat.dvd_of_mod_eq_zero h
      have := Nat.Coprime.coprime_dvd_left this h2
      norm_num at this
    · exact h
  rcases q_mod3 h6 with h | h
  · right; refine ⟨h, ?_⟩; omega
  · left; exact ⟨h, hq⟩

lemma coprime6_ge37 (q : ℕ) (h6 : Nat.Coprime q 6) (hq : 37 ≤ q) :
    (q % 3 = 2 ∧ 41 ≤ q) ∨ (q % 3 = 1 ∧ 37 ≤ q) := by
  have : NeZero q := ⟨by omega⟩
  have h2 : Nat.Coprime q 2 := Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) h6
  have hodd : q % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have : 2 ∣ q := Nat.dvd_of_mod_eq_zero h
      have := Nat.Coprime.coprime_dvd_left this h2
      norm_num at this
    · exact h
  rcases q_mod3 h6 with h | h
  · right; exact ⟨h, hq⟩
  · left; refine ⟨h, ?_⟩; omega

/-- **`thm:col`(3)**: `cCol q > 0.9059` for every `q ≥ 5` coprime to `6`, `> 0.9823` from `q ≥ 37`. -/
lemma col_bounds (q : ℕ) (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    0.9059 < cCol q ∧ (37 ≤ q → 0.9823 < cCol q) := by
  obtain ⟨v5, -, v7, -, v37, -, v41⟩ := col_values
  constructor
  · rcases coprime6_ge q h6 hq with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact lt_of_lt_of_le v5 (cCol_le 5 q (by norm_num) h' (by omega))
    · exact lt_of_lt_of_le (by linarith) (cCol_le 7 q (by norm_num) h' (by omega))
  · intro h37
    rcases coprime6_ge37 q h6 h37 with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact lt_of_lt_of_le (by linarith) (cCol_le 41 q (by norm_num) h' (by omega))
    · exact lt_of_lt_of_le v37 (cCol_le 37 q (by norm_num) h' (by omega))

/-- **`thm:col`(2)**, the expansion for `q ≡ 2 (mod 3)`, with an explicit `O(q⁻³)`. -/
lemma cCol_exp2 (q : ℕ) (hq : 5 ≤ q) (h : q % 3 = 2) :
    |cCol q - (1 - 1 / (3 * q) - 8 / (9 * (q : ℝ) ^ 2))| ≤ 2 / (q : ℝ) ^ 3 := by
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := 1 / q with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hq'
  have e1 : 1 - 1 / (3 * (q : ℝ)) - 8 / (9 * (q : ℝ) ^ 2) = 1 - x / 3 - 8 * x ^ 2 / 9 := by
    rw [hx]; field_simp
  have e2 : 2 / (q : ℝ) ^ 3 = 2 * x ^ 3 := by rw [hx]; field_simp
  have e3 : tC q = 1 - x - 3 * x ^ 2 := by rw [tC_two q (by omega) h, hx]; field_simp
  rw [e1, e2, cCol_eq q (by omega), e3, abs_le]
  have hA : 0 ≤ 1 - x / 3 - 8 * x ^ 2 / 9 := by nlinarith
  constructor
  · have : 1 - x / 3 - 8 * x ^ 2 / 9 ≤ Real.sqrt ((2 + (1 - x - 3 * x ^ 2) ^ 2) / 3) := by
      rw [Real.le_sqrt hA (by positivity)]
      nlinarith [pow_pos hx0 3, pow_pos hx0 4, mul_pos hx0 hx0]
    nlinarith [pow_pos hx0 3]
  · have : Real.sqrt ((2 + (1 - x - 3 * x ^ 2) ^ 2) / 3) ≤ 1 - x / 3 - 8 * x ^ 2 / 9 + 2 * x ^ 3 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by nlinarith [pow_pos hx0 3], ?_⟩
      nlinarith [pow_pos hx0 3, pow_pos hx0 4, pow_pos hx0 5, pow_pos hx0 6, mul_pos hx0 hx0,
        mul_nonneg (pow_pos hx0 3).le (sub_nonneg.2 hx1), mul_nonneg (pow_pos hx0 4).le (sub_nonneg.2 hx1)]
    linarith

/-- **`thm:col`(2)**, the expansion for `q ≡ 1 (mod 3)`, with an explicit `O(q⁻³)`. -/
lemma cCol_exp1 (q : ℕ) (hq : 5 ≤ q) (h : q % 3 = 1) :
    |cCol q - (1 - 2 / (3 * q) + 4 / (9 * (q : ℝ) ^ 2))| ≤ 1 / (q : ℝ) ^ 3 := by
  have hq' : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := 1 / q with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hq'
  have e1 : 1 - 2 / (3 * (q : ℝ)) + 4 / (9 * (q : ℝ) ^ 2) = 1 - 2 * x / 3 + 4 * x ^ 2 / 9 := by
    rw [hx]; field_simp
  have e2 : 1 / (q : ℝ) ^ 3 = x ^ 3 := by rw [hx]; field_simp
  have e3 : tC q = 1 - 2 * x := by rw [tC_one q (by omega) (by omega), hx]; field_simp
  rw [e1, e2, cCol_eq q (by omega), e3, abs_le]
  have hA : 0 ≤ 1 - 2 * x / 3 + 4 * x ^ 2 / 9 := by nlinarith
  constructor
  · have : 1 - 2 * x / 3 + 4 * x ^ 2 / 9 ≤ Real.sqrt ((2 + (1 - 2 * x) ^ 2) / 3) := by
      rw [Real.le_sqrt hA (by positivity)]
      nlinarith [pow_pos hx0 3, pow_pos hx0 4, mul_nonneg (pow_pos hx0 3).le (sub_nonneg.2 hx1)]
    nlinarith [pow_pos hx0 3]
  · have : Real.sqrt ((2 + (1 - 2 * x) ^ 2) / 3) ≤ 1 - 2 * x / 3 + 4 * x ^ 2 / 9 + x ^ 3 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by nlinarith [pow_pos hx0 3], ?_⟩
      nlinarith [pow_pos hx0 3, pow_pos hx0 4, pow_pos hx0 5, pow_pos hx0 6,
        mul_nonneg (pow_pos hx0 3).le (sub_nonneg.2 hx1), mul_nonneg (pow_pos hx0 4).le (sub_nonneg.2 hx1)]
    linarith

/-! ## Real-valued separation -/

lemma sqrt_cres_sum (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) :
    Real.sqrt (∑ c, ((cres N ((x c : ℤ) - (y c : ℤ)) : ℝ) / (N : ℝ)) ^ 2) =
      Real.sqrt (torusDist2 N x y : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∑ c, ((cres N ((x c : ℤ) - (y c : ℤ)) : ℝ) / (N : ℝ)) ^ 2 =
      (torusDist2 N x y : ℝ) / ((N : ℝ)) ^ 2 := by
    unfold torusDist2
    push_cast
    rw [Finset.sum_div]
    congr 1; funext c; rw [div_pow]
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN'.le]

/-- The separation of a column point set with `3d² ≥ G` at unit scale times `N^{1/3}` (`N = q³`). -/
lemma sep_real (q : ℕ) (hq : 0 < q) (x y : Fin 3 → ℕ) (G : ℝ) (hG : 0 ≤ G)
    (h : G ≤ 3 * (torusDist2 (q ^ 3) x y : ℝ)) :
    Real.sqrt (G / 3) / (q : ℝ) ^ 2 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ 3) ((x c : ℤ) - (y c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e := sqrt_cres_sum (q ^ 3) (by positivity) x y
  push_cast at e
  rw [e, cube_rpow _ hq']
  have : Real.sqrt (G / 3) ≤ Real.sqrt (torusDist2 (q ^ 3) x y : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  calc Real.sqrt (G / 3) / (q : ℝ) ^ 2 * (q : ℝ)⁻¹ = Real.sqrt (G / 3) / (q : ℝ) ^ 3 := by
        field_simp
    _ ≤ Real.sqrt (torusDist2 (q ^ 3) x y : ℝ) / (q : ℝ) ^ 3 := by
        gcongr

end Z3NetC.Proofs
