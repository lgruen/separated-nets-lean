/-
`prop:wnet` (4): `δN^{1/3} > 1` for every prime `p ≥ 17` and `> √66/8` for every prime `p ≥ 53`
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WExact
public import QUNetsM3.WPair

@[expose] public section

/-!
# `prop:wnet` (4)

As printed: by (2), `δN^{1/3} ≥ c_W(p) > 1` for `p ≥ 67` and `> √66/8` for `p ≥ 97`; the remaining primes
`17 ≤ p ≤ 89` by the exact minimum distances (`WExact.lean`, kernel checks). `w_least`: the least values at the
primes `17 ≤ p ≤ 61` and `53 ≤ p ≤ 89` are at `p = 47` (`1.0009…`) and `p = 89` (`1.0257…`).
-/

namespace QUNetsM3

variable {p : ℕ}

/-- A lower bound for all pairs and a pair attaining it give `δN^{1/3}`. -/
theorem deltaG_eq (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (d : ℕ)
    (hlb : ∀ x x' : ℕ, ∀ t : Fin 3 → ℤ, x < p ^ 3 → x' < p ^ 3 → x ≠ x' → (d : ℤ) ≤ sepSqG p C x x' t)
    (hw : ∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < p ^ 3 ∧ x' < p ^ 3 ∧ x ≠ x' ∧ sepSqG p C x x' t = d) :
    deltaG p C = Real.sqrt d / (p : ℝ) ^ 2 := by
  obtain ⟨x, x', t, hx, hx', hne, hv⟩ := hw
  unfold deltaG
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨y, y', s, -, -, -, rfl⟩
      positivity
    · exact ⟨x, x', t, hx, hx', hne, by rw [hv]; push_cast; rfl⟩
  · apply le_csInf
    · exact ⟨_, x, x', t, hx, hx', hne, rfl⟩
    rintro e ⟨y, y', s, hy, hy', hne', rfl⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.sqrt_le_sqrt
    exact_mod_cast hlb y y' s hy hy' hne'

/-- `δN^{1/3}` at the primes of the table. -/
theorem w_exact_delta : ∀ q ∈ wExactTab, deltaW q.1 = Real.sqrt q.2 / (q.1 : ℝ) ^ 2 := by
  intro q hq
  obtain ⟨hlb, hw⟩ := wexact_tab q hq
  exact deltaG_eq _ _ hlb hw

/-- The table covers exactly the primes `17 ≤ p ≤ 89`. -/
theorem wexact_cover (hp : p.Prime) (h17 : 17 ≤ p) (h89 : p ≤ 89) : ∃ d, (p, d) ∈ wExactTab := by
  interval_cases p <;> norm_num at hp <;> simp [wExactTab]

/-- `1 < √d/p²` iff `p⁴ < d`; `√66/8 < √d/p²` iff `66p⁴ < 64d`. -/
theorem one_lt_sqrt_div {d : ℕ} (hp : 0 < p) (h : p ^ 4 < d) : 1 < Real.sqrt d / (p : ℝ) ^ 2 := by
  rw [one_lt_div (by positivity), Real.lt_sqrt (by positivity)]
  have : ((p ^ 4 : ℕ) : ℝ) < d := by exact_mod_cast h
  push_cast at this; nlinarith

theorem s66_lt_sqrt_div {d : ℕ} (hp : 0 < p) (h : 66 * p ^ 4 < 64 * d) :
    Real.sqrt 66 / 8 < Real.sqrt d / (p : ℝ) ^ 2 := by
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  rw [div_lt_div_iff₀ (by norm_num) hp2]
  have e1 : Real.sqrt 66 * (p : ℝ) ^ 2 = Real.sqrt (66 * ((p : ℝ) ^ 2) ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt d * 8 = Real.sqrt (64 * d) := by
    rw [Real.sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring
  rw [e1, e2]
  apply Real.sqrt_lt_sqrt (by positivity)
  have : ((66 * p ^ 4 : ℕ) : ℝ) < ((64 * d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; nlinarith

/-- **`prop:wnet` (4)** (proof of `W_four`). -/
theorem w_four : (∀ p : ℕ, p.Prime → 17 ≤ p → 1 < deltaW p) ∧
    (∀ p : ℕ, p.Prime → 53 ≤ p → Real.sqrt 66 / 8 < deltaW p) := by
  have hT1 : ∀ q ∈ wExactTab, q.1 ≤ 61 → q.1 ^ 4 < q.2 := by decide
  have hT2 : ∀ q ∈ wExactTab, 53 ≤ q.1 → 66 * q.1 ^ 4 < 64 * q.2 := by decide
  constructor
  · intro p hp h17
    rcases le_or_gt 67 p with h | h
    · exact lt_of_lt_of_le (cW_gt1 h) (w_delta hp (by omega)).1
    · obtain ⟨d, hd⟩ := wexact_cover hp h17 (by omega)
      have hp61 : p ≤ 61 := by
        by_contra hc; interval_cases p <;> exact absurd hp (by norm_num)
      rw [show deltaW p = deltaW (p, d).1 from rfl, w_exact_delta _ hd]
      exact one_lt_sqrt_div (by omega) (hT1 _ hd hp61)
  · intro p hp h53
    rcases le_or_gt 97 p with h | h
    · exact lt_of_lt_of_le (cW_gt66 h) (w_delta hp (by omega)).1
    · have hp89 : p ≤ 89 := by
        by_contra hc; interval_cases p <;> exact absurd hp (by norm_num)
      obtain ⟨d, hd⟩ := wexact_cover hp (by omega) hp89
      rw [show deltaW p = deltaW (p, d).1 from rfl, w_exact_delta _ hd]
      exact s66_lt_sqrt_div (by omega) (hT2 _ hd h53)

/-- `√d/p² ≤ √d'/p'²` iff `d p'⁴ ≤ d' p⁴`. -/
theorem sqrt_div_le {p p' d d' : ℕ} (hp : 0 < p) (hp' : 0 < p') (h : d * p' ^ 4 ≤ d' * p ^ 4) :
    Real.sqrt d / (p : ℝ) ^ 2 ≤ Real.sqrt d' / (p' : ℝ) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : Real.sqrt d * (p' : ℝ) ^ 2 = Real.sqrt (d * ((p' : ℝ) ^ 2) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt d' * (p : ℝ) ^ 2 = Real.sqrt (d' * ((p : ℝ) ^ 2) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have : ((d * p' ^ 4 : ℕ) : ℝ) ≤ ((d' * p ^ 4 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this; nlinarith

/-- **The values in the proof of `prop:wnet` (4)** (proof of `W_least`): among the primes `17 ≤ p ≤ 61` the least
`δN^{1/3}` is at `p = 47`, `1.0009 < δN^{1/3} < 1.0010`; among the primes `53 ≤ p ≤ 89` it is at `p = 89`,
`1.0257 < δN^{1/3} < 1.0258`. -/
theorem w_least : (∀ p : ℕ, p.Prime → 17 ≤ p → p ≤ 61 → deltaW 47 ≤ deltaW p) ∧
    1.0009 < deltaW 47 ∧ deltaW 47 < 1.0010 ∧
    (∀ p : ℕ, p.Prime → 53 ≤ p → p ≤ 89 → deltaW 89 ≤ deltaW p) ∧
    1.0257 < deltaW 89 ∧ deltaW 89 < 1.0258 := by
  have h47 : deltaW 47 = Real.sqrt (4889304 : ℕ) / ((47 : ℕ) : ℝ) ^ 2 :=
    w_exact_delta (47, 4889304) (by simp [wExactTab])
  have h89 : deltaW 89 = Real.sqrt (66013204 : ℕ) / ((89 : ℕ) : ℝ) ^ 2 :=
    w_exact_delta (89, 66013204) (by simp [wExactTab])
  have hL1 : ∀ q ∈ wExactTab, q.1 ≤ 61 → 4889304 * q.1 ^ 4 ≤ q.2 * 47 ^ 4 := by decide
  have hL2 : ∀ q ∈ wExactTab, 53 ≤ q.1 → 66013204 * q.1 ^ 4 ≤ q.2 * 89 ^ 4 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp h17 h61
    obtain ⟨d, hd⟩ := wexact_cover hp h17 (by omega)
    rw [h47, show deltaW p = deltaW (p, d).1 from rfl, w_exact_delta _ hd]
    exact sqrt_div_le (by norm_num) (by omega) (hL1 _ hd h61)
  · rw [h47, lt_div_iff₀ (by positivity), Real.lt_sqrt (by positivity)]; norm_num
  · rw [h47, div_lt_iff₀ (by positivity), Real.sqrt_lt' (by positivity)]; norm_num
  · intro p hp h53 h89'
    obtain ⟨d, hd⟩ := wexact_cover hp (by omega) h89'
    rw [h89, show deltaW p = deltaW (p, d).1 from rfl, w_exact_delta _ hd]
    exact sqrt_div_le (by norm_num) (by omega) (hL2 _ hd h53)
  · rw [h89, lt_div_iff₀ (by positivity), Real.lt_sqrt (by positivity)]; norm_num
  · rw [h89, div_lt_iff₀ (by positivity), Real.sqrt_lt' (by positivity)]; norm_num

end QUNetsM3
