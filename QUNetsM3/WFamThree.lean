/-
`prop:wfamily` (3) on the torus: `F(τ) ≤ μ*²`, with equality only at `τ*` (the six-contact proof)
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WFamTwo

@[expose] public section

/-!
# `prop:wfamily` (3), the torus part

`six_contacts`: if every option of `τ` has `|V|² ≥ μ*²`, then `τ ≡ τ*`. As printed, with the representatives
`g, g', f ∈ [0, 1)` of `τ_x, τ_y, τ_z`: the step `e_z` (options `(0,0)`, `(f−1,−1)`, `(f−1,0)`, `(f,0)`) gives
`0 < f < 2/15` and `f ≥ 2ε*`; the steps `e_x`, `e_y` give `g, g' ∈ (7/15, 8/15)`; the lock `𝟏` gives
`α + β ≥ γ`; the diagonal steps `(1,0,−1)`, `(0,1,−1)` give `q_a(s/3), q_a(s'/3) ≥ μ*²`. Lean concludes with
`s, s' ≤ 3ε*` (`q_a` decreases on `[0, 1/18]`) and `s + s' ≥ 3f ≥ 6ε*` instead of the maximum of the printed proof
(the same inequalities). The constants `246/225`, `17/16`, `9/25 < μ*²` and `q_a(ε*) = q_b(ε*) = μ*²` are exact
(`√31` enters through `√31² = 31` and rational bounds checked by squaring).
-/

namespace QUNetsM3

theorem sqrt31_sq : Real.sqrt 31 ^ 2 = 31 := Real.sq_sqrt (by norm_num)
theorem sqrt31_gt : 5.5677 < Real.sqrt 31 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
theorem sqrt31_lt : Real.sqrt 31 < 5.5678 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `q_a(ε*) = μ*²`. -/
theorem qaW_star : qaW epsStar = muStarSq := by
  unfold qaW epsStar muStarSq; linear_combination (1 / 25 : ℝ) * sqrt31_sq

/-- `q_b(ε*) = μ*²`. -/
theorem qbW_star : qbW epsStar = muStarSq := by
  unfold qbW epsStar muStarSq; linear_combination (4 / 225 : ℝ) * sqrt31_sq

theorem epsStar_bounds : 0.0207 < epsStar ∧ epsStar < 0.0208 := by
  have := sqrt31_gt; have := sqrt31_lt
  unfold epsStar; constructor <;> linarith

theorem muStarSq_bounds : 246 / 225 < muStarSq ∧ muStarSq < 5 / 4 := by
  -- `402² = 161604 > 72²·31 = 160704`, i.e. `72√31 < 402`
  have := sqrt31_gt; have := sqrt31_lt
  unfold muStarSq; constructor <;> linarith

theorem muStarSq_pos : 0 < muStarSq := by have := muStarSq_bounds; linarith

theorem muStar_sq : muStar ^ 2 = muStarSq := Real.sq_sqrt muStarSq_pos.le

/-- `F(τ + k) = F(τ)` for `k ∈ ℤ³`. -/
theorem optSet_shift (τ : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    optSet (fun c => τ c + k c) = optSet τ := by
  have hopt : ∀ E δ κ, IsOptW (fun c => τ c + k c) E δ κ ↔ IsOptW τ E δ κ := by
    intro E δ κ
    unfold IsOptW
    have hs : ∑ c, (τ c + (k c : ℝ)) * (E c : ℝ) = ∑ c, τ c * (E c : ℝ) + ((∑ c, k c * E c : ℤ) : ℝ) := by
      push_cast; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [hs]
    constructor
    · rintro ⟨h1, h2, ⟨m, hm⟩, h4⟩
      exact ⟨h1, h2, ⟨m + ∑ c, k c * E c, by rw [hm]; push_cast; ring⟩, h4⟩
    · rintro ⟨h1, h2, ⟨m, hm⟩, h4⟩
      exact ⟨h1, h2, ⟨m - ∑ c, k c * E c, by rw [hm]; push_cast; ring⟩, h4⟩
  ext v
  simp only [optSet, Set.mem_ofPred_eq, hopt]

theorem Ffam_shift (τ : Fin 3 → ℝ) (k : Fin 3 → ℤ) : Ffam (fun c => τ c + k c) = Ffam τ := by
  rw [Ffam_def, Ffam_def, optSet_shift]

/-- `F(τ*) = μ*²` (by (2) at `ε*`). -/
theorem Ffam_star : Ffam tauStar = muStarSq := by
  have he := epsStar_bounds
  unfold tauStar
  rw [wfam_two (by linarith) (by linarith), qaW_star, qbW_star, min_self]

theorem sum3 (τ : Fin 3 → ℝ) (a b c : ℤ) :
    ∑ i, τ i * (((![a, b, c] : Fin 3 → ℤ) i : ℤ) : ℝ) = τ 0 * a + τ 1 * b + τ 2 * c := by
  simp [Fin.sum_univ_three]

theorem optValW3 (a b c : ℤ) (δ : ℝ) (κ : ℤ) :
    optValW ![a, b, c] δ κ = ((a : ℝ) + 2 * δ - κ) ^ 2 + ((b : ℝ) + 2 * δ - κ) ^ 2 + ((c : ℝ) + δ) ^ 2 := by
  rw [optValW_eval]; simp

/-- The steps `e_x`, `e_y` of the six-contact proof, for one representative `g ∈ [0, 1)`. -/
theorem step_x {μ g : ℝ} (hμ : 246 / 225 < μ) (h0 : 0 ≤ g) (h1 : g < 1) (hA : g = 0 → μ ≤ 1)
    (hB : 0 < g → μ ≤ (2 * g) ^ 2 + (2 * g - 1) ^ 2 + g ^ 2)
    (hC : 1 / 2 < g → μ ≤ (2 * g - 1) ^ 2 + (2 * (g - 1)) ^ 2 + (g - 1) ^ 2) :
    7 / 15 < g ∧ g < 8 / 15 := by
  have hpos : 0 < g := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · have := hA h.symm; linarith
  have hlo : 7 / 15 < g := by
    by_contra hc; push Not at hc
    have := hB hpos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith : g - 7 / 15 ≤ 0)]
  refine ⟨hlo, ?_⟩
  by_contra hc; push Not at hc
  have := hC (by linarith)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - g) (by linarith : (1 - g) - 7 / 15 ≤ 0)]

/-- A diagonal step: `μ*² ≤ q_a(s/3)` with `s < 1/6` forces `s ≤ 3ε*` (`q_a` decreases on `[0, 1/18]`). -/
theorem diag_le {μ e s : ℝ} (hqa : qaW e = μ) (he : 0.0207 < e ∧ e < 0.0208) (h1 : s < 1 / 6)
    (h2 : μ ≤ (1 - 2 * s) ^ 2 + (2 * s) ^ 2 + (1 / 2 + s) ^ 2) : s ≤ 3 * e := by
  by_contra hc; push Not at hc
  have : qaW (s / 3) < qaW e := by
    unfold qaW
    nlinarith [mul_pos (by linarith : (0 : ℝ) < s / 3 - e) (by linarith : (0 : ℝ) < 9 - 81 * (s / 3 + e))]
  rw [hqa] at this
  unfold qaW at this
  nlinarith

/-- The lock `𝟏`: `|V|² = 9σ̃² < 9/25 < μ*²` for `0 < σ̃ < 1/5`. -/
theorem lock_lt {μ σ : ℝ} (hμ : 246 / 225 < μ) (h0 : 0 < σ) (h1 : σ < 1 / 5)
    (h : μ ≤ 9 * σ ^ 2) : False := by
  nlinarith

/-- **The six contacts**: if every option of `τ` has `|V|² ≥ μ*²`, then `τ ≡ τ* (mod ℤ³)`. -/
theorem six_contacts (τ : Fin 3 → ℝ) (H : ∀ v ∈ optSet τ, muStarSq ≤ v) :
    ∃ k : Fin 3 → ℤ, τ = fun c => tauStar c + k c := by
  have he := epsStar_bounds
  have hμ := muStarSq_bounds
  have hqa := qaW_star
  have hqb := qbW_star
  set e := epsStar
  set μ := muStarSq
  -- the options used
  have use : ∀ (a b c : ℤ) (δ : ℝ) (κ k : ℤ), (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) → -1 < δ → δ < 1 →
      δ = τ 0 * a + τ 1 * b + τ 2 * c + k → (κ = sgnR δ ∨ (κ = 0 ∧ |δ| < 1 / 2)) →
      μ ≤ ((a : ℝ) + 2 * δ - κ) ^ 2 + ((b : ℝ) + 2 * δ - κ) ^ 2 + ((c : ℝ) + δ) ^ 2 := by
    intro a b c δ κ k hE h1 h2 h3 h4
    rw [← optValW3]
    refine H _ ⟨![a, b, c], ?_, δ, κ, ⟨h1, h2, ⟨k, by rw [sum3]; exact h3⟩, h4⟩, rfl⟩
    intro h0
    have := congrFun h0 0; have := congrFun h0 1; have := congrFun h0 2
    simp at *; omega
  -- representatives
  set g := Int.fract (τ 0)
  set g' := Int.fract (τ 1)
  set f := Int.fract (τ 2)
  have eg : τ 0 = g + ⌊τ 0⌋ := by rw [add_comm]; exact (Int.floor_add_fract _).symm
  have eg' : τ 1 = g' + ⌊τ 1⌋ := by rw [add_comm]; exact (Int.floor_add_fract _).symm
  have ef : τ 2 = f + ⌊τ 2⌋ := by rw [add_comm]; exact (Int.floor_add_fract _).symm
  have hg0 : 0 ≤ g := Int.fract_nonneg _
  have hg1 : g < 1 := Int.fract_lt_one _
  have hg0' : 0 ≤ g' := Int.fract_nonneg _
  have hg1' : g' < 1 := Int.fract_lt_one _
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  -- the step `e_z`
  have hfpos : 0 < f := by
    rcases hf0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := use 0 0 1 0 0 (-⌊τ 2⌋) (by omega) (by norm_num) (by norm_num)
        (by push_cast; linarith) (Or.inl (by simp [sgnR]))
      norm_num at this; linarith
  have hz1 := use 0 0 1 (f - 1) (-1) (-⌊τ 2⌋ - 1) (by omega) (by linarith) (by linarith)
    (by push_cast; linarith) (Or.inl (by rw [sgnR_neg (by linarith)]))
  push_cast at hz1
  have hf34 : f ≤ 3 / 4 := by
    by_contra hc; push Not at hc
    have hz2 := use 0 0 1 (f - 1) 0 (-⌊τ 2⌋ - 1) (by omega) (by linarith) (by linarith)
      (by push_cast; linarith) (Or.inr ⟨rfl, by rw [abs_lt]; constructor <;> linarith⟩)
    push_cast at hz2
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ f - 3 / 4) (by linarith : f - 1 ≤ 0)]
  have hf215 : f < 2 / 15 := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ f - 2 / 15) (by linarith : f - 3 / 4 ≤ 0)]
  have hz3 := use 0 0 1 f 0 (-⌊τ 2⌋) (by omega) (by linarith) (by linarith)
    (by push_cast; linarith) (Or.inr ⟨rfl, by rw [abs_lt]; constructor <;> linarith⟩)
  push_cast at hz3
  have hfe : 2 * e ≤ f := by
    by_contra hc; push Not at hc
    -- `q_b(f/2) < q_b(ε*) = μ*²`
    have h1 : qbW (f / 2) < qbW e := by
      unfold qbW; nlinarith [mul_pos (by linarith : (0 : ℝ) < e - f / 2) (by linarith : (0 : ℝ) < 4 + 36 * (f / 2 + e))]
    rw [hqb] at h1
    unfold qbW at h1
    linarith
  -- the steps `e_x`, `e_y`
  have hgx : 7 / 15 < g ∧ g < 8 / 15 := by
    refine step_x hμ.1 hg0 hg1 (fun h => ?_) (fun h => ?_) (fun h => ?_)
    · have := use 1 0 0 0 0 (-⌊τ 0⌋) (by omega) (by norm_num) (by norm_num) (by push_cast; linarith)
        (Or.inl (by simp [sgnR]))
      push_cast at this; linarith
    · have := use 1 0 0 g 1 (-⌊τ 0⌋) (by omega) (by linarith) hg1 (by push_cast; linarith)
        (Or.inl (by rw [sgnR_pos h]))
      push_cast at this; linarith
    · have := use 1 0 0 (g - 1) 0 (-⌊τ 0⌋ - 1) (by omega) (by linarith) (by linarith) (by push_cast; linarith)
        (Or.inr ⟨rfl, by rw [abs_lt]; constructor <;> linarith⟩)
      push_cast at this; linarith
  have hgy : 7 / 15 < g' ∧ g' < 8 / 15 := by
    refine step_x hμ.1 hg0' hg1' (fun h => ?_) (fun h => ?_) (fun h => ?_)
    · have := use 0 1 0 0 0 (-⌊τ 1⌋) (by omega) (by norm_num) (by norm_num) (by push_cast; linarith)
        (Or.inl (by simp [sgnR]))
      push_cast at this; linarith
    · have := use 0 1 0 g' 1 (-⌊τ 1⌋) (by omega) (by linarith) hg1' (by push_cast; linarith)
        (Or.inl (by rw [sgnR_pos h]))
      push_cast at this; linarith
    · have := use 0 1 0 (g' - 1) 0 (-⌊τ 1⌋ - 1) (by omega) (by linarith) (by linarith) (by push_cast; linarith)
        (Or.inr ⟨rfl, by rw [abs_lt]; constructor <;> linarith⟩)
      push_cast at this; linarith
  -- the lock `𝟏`
  have hlock : g + g' + f ≤ 1 := by
    by_contra hc; push Not at hc
    have h1 := use 1 1 1 (g + g' + f - 2) (-1) (-⌊τ 0⌋ - ⌊τ 1⌋ - ⌊τ 2⌋ - 2) (by omega)
      (by linarith) (by linarith) (by push_cast; linarith)
      (Or.inl (by rw [sgnR_neg (by linarith)]))
    push_cast at h1
    exact lock_lt (σ := g + g' + f - 1) hμ.1 (by linarith) (by linarith) (le_of_le_of_eq h1 (by ring))
  -- the diagonal steps
  have hd1 := use 1 0 (-1) (g - f) 1 (-⌊τ 0⌋ + ⌊τ 2⌋) (by omega) (by linarith) (by linarith)
    (by push_cast; linarith) (Or.inl (by rw [sgnR_pos (by linarith)]))
  have hd2 := use 0 1 (-1) (g' - f) 1 (-⌊τ 1⌋ + ⌊τ 2⌋) (by omega) (by linarith) (by linarith)
    (by push_cast; linarith) (Or.inl (by rw [sgnR_pos (by linarith)]))
  push_cast at hd1 hd2
  -- `s = ½ − g + f`, `s' = ½ − g' + f` satisfy `s, s' ≤ 3ε*`
  have hs1 := diag_le hqa he (s := 1 / 2 - g + f) (by linarith) (le_of_le_of_eq hd1 (by ring))
  have hs2 := diag_le hqa he (s := 1 / 2 - g' + f) (by linarith) (le_of_le_of_eq hd2 (by ring))
  -- equality throughout
  have hf : f = 2 * e := by linarith
  have hgv : g = 1 / 2 - e := by linarith
  have hgv' : g' = 1 / 2 - e := by linarith
  refine ⟨![⌊τ 0⌋, ⌊τ 1⌋, ⌊τ 2⌋], ?_⟩
  funext c
  fin_cases c
  · show τ 0 = tauEps e 0 + (⌊τ 0⌋ : ℝ)
    simp only [tauEps, Matrix.cons_val_zero]; linarith
  · show τ 1 = tauEps e 1 + (⌊τ 1⌋ : ℝ)
    simp only [tauEps, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith
  · show τ 2 = tauEps e 2 + (⌊τ 2⌋ : ℝ)
    simp only [tauEps, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; linarith

/-- **`prop:wfamily` (3), the torus part** (proof of `Wfam_three_tau`): `F(τ) ≤ μ*²` for every `τ`, with equality
iff `τ ≡ τ* (mod ℤ³)`. -/
theorem wfam_three_tau (τ : Fin 3 → ℝ) :
    Ffam τ ≤ muStarSq ∧ (Ffam τ = muStarSq ↔ ∃ k : Fin 3 → ℤ, τ = fun c => tauStar c + k c) := by
  have key : muStarSq ≤ Ffam τ → ∃ k : Fin 3 → ℤ, τ = fun c => tauStar c + k c := by
    intro h
    exact six_contacts τ fun v hv => le_trans h (csInf_le (optSet_bdd τ) hv)
  refine ⟨?_, ⟨fun h => key h.ge, ?_⟩⟩
  · by_contra hc; push Not at hc
    obtain ⟨k, rfl⟩ := key hc.le
    rw [Ffam_shift, Ffam_star] at hc
    exact lt_irrefl _ hc
  · rintro ⟨k, rfl⟩
    rw [Ffam_shift, Ffam_star]

/-- `√31` is irrational, so no `u/p` is `≡ τ*`. -/
theorem tauOf_ne_star (p : ℕ) (u : Fin 3 → ZMod p) (k : Fin 3 → ℤ) :
    tauOf p u ≠ fun c => tauStar c + k c := by
  intro h
  have h2 := congrFun h 2
  simp only [tauOf, tauStar, tauEps, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  have hirr : Irrational (Real.sqrt 31) := by
    have := Nat.Prime.irrational_sqrt (show Nat.Prime 31 by norm_num)
    simpa using this
  apply hirr
  refine ⟨(13 - 45 * (((u 2).val : ℚ) / p - k 2)) / 2, ?_⟩
  push_cast
  rw [h2]
  unfold epsStar
  ring

/-- **The constants of the balance** (proof of `Wfam_star`): `q_a(ε*) = q_b(ε*) = μ*²`, `0.02071 < ε* < 0.02072`,
`1.0480 < μ* < 1.0481`, and `2K = 9 − 162ε* = |q_a'(ε*)|` with `K = (9√31 − 36)/5`. -/
theorem wfam_star : qaW epsStar = muStarSq ∧ qbW epsStar = muStarSq ∧ 0.02071 < epsStar ∧ epsStar < 0.02072 ∧
    1.0480 < muStar ∧ muStar < 1.0481 ∧ 2 * KW = 9 - 162 * epsStar := by
  have := sqrt31_gt; have := sqrt31_lt
  refine ⟨qaW_star, qbW_star, by unfold epsStar; linarith, by unfold epsStar; linarith, ?_, ?_, ?_⟩
  · unfold muStar muStarSq; rw [Real.lt_sqrt (by norm_num)]; linarith
  · unfold muStar muStarSq; rw [Real.sqrt_lt' (by norm_num)]; linarith
  · unfold KW epsStar; ring

end QUNetsM3
