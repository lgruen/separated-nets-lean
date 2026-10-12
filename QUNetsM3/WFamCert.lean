/-
`prop:wfamily` (2): the finite certificate (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WCore

@[expose] public section

/-!
# The options of `τ_ε = (½ − ε, ½ − ε, 2ε)`, `0 < ε ≤ 3/100`

With `ε = 3t/100`, `t ∈ (0, 1]`, a step `E ∈ {−2,…,2}³ ∖ 0` and an option `(δ, κ)` have `δ = J/2 − Qε`
(`J = 2M ≡ E_x + E_y (mod 2)`, `|J| ≤ 2`, `Q = E_x + E_y − 2E_z`), and
`10⁴|V|² = A₀ + A₁t + A₂t²` with `100V = (100(E_x + J − κ) − 6Qt, 100(E_y + J − κ) − 6Qt, 100E_z + 50J − 3Qt)`.
`famOK` certifies one case `(E, J, κ)`: the parity fails, or one of the linear conditions of an option
(`|δ| < 1`; `δ > 0` for `κ = 1`; `δ < 0` for `κ = −1`; `|δ| < ½` for `κ = 0`) fails on all of `t ∈ [0, 1]`, or
`10⁴(|V|² − q_a(ε))` or `10⁴(|V|² − q_b(ε))` has nonnegative Bernstein coefficients on `[0, 1]`. These are the
rules for `(M, κ)` and the rows of `tab:wcontacts` in the proof of `prop:wfamily` (2), carried out exhaustively
(the long options `|A|² ≥ 3` included).
-/

namespace QUNetsM3

/-- `a + b t ≤ 0` on all of `t ∈ [0, 1]`. -/
def infF (a b : ℤ) : Bool := decide (a ≤ 0) && decide (a + b ≤ 0)

/-- `c₀ + c₁t + c₂t²` has nonnegative Bernstein coefficients on `[0, 1]`. -/
def bernF (c0 c1 c2 : ℤ) : Bool := decide (0 ≤ c0) && decide (0 ≤ 2 * c0 + c1) && decide (0 ≤ c0 + c1 + c2)

/-- The coefficients of `10⁴|V|²`. -/
def famA0 (Ex Ey Ez J k : ℤ) : ℤ :=
  (100 * (Ex + J - k)) ^ 2 + (100 * (Ey + J - k)) ^ 2 + (100 * Ez + 50 * J) ^ 2
def famA1 (Ex Ey Ez J k : ℤ) : ℤ :=
  2 * ((100 * (Ex + J - k)) * (-6 * (Ex + Ey - 2 * Ez)) + (100 * (Ey + J - k)) * (-6 * (Ex + Ey - 2 * Ez)) +
    (100 * Ez + 50 * J) * (-3 * (Ex + Ey - 2 * Ez)))
def famA2 (Ex Ey Ez : ℤ) : ℤ := 81 * (Ex + Ey - 2 * Ez) ^ 2

/-- The certificate of one case `(E, J, κ)`. -/
def famOK (Ex Ey Ez J k : ℤ) : Bool :=
  decide ((J - (Ex + Ey)) % 2 ≠ 0) ||
  infF (50 * J + 100) (-3 * (Ex + Ey - 2 * Ez)) || infF (100 - 50 * J) (3 * (Ex + Ey - 2 * Ez)) ||
  (decide (k = 1) && infF (50 * J) (-3 * (Ex + Ey - 2 * Ez))) ||
  (decide (k = -1) && infF (-50 * J) (3 * (Ex + Ey - 2 * Ez))) ||
  (decide (k = 0) && (infF (50 - 50 * J) (3 * (Ex + Ey - 2 * Ez)) ||
    infF (50 + 50 * J) (-3 * (Ex + Ey - 2 * Ez)))) ||
  bernF (famA0 Ex Ey Ez J k - 12500) (famA1 Ex Ey Ez J k + 2700) (famA2 Ex Ey Ez - 729) ||
  bernF (famA0 Ex Ey Ez J k - 10000) (famA1 Ex Ey Ez J k - 1200) (famA2 Ex Ey Ez - 324)

/-- All cases `E ∈ {−2,…,2}³ ∖ 0`, `|J| ≤ 2`, `κ ∈ {−1, 0, 1}`. -/
def famAll : Bool :=
  LW5.all fun Ex => LW5.all fun Ey => LW5.all fun Ez =>
    (Ex == 0 && Ey == 0 && Ez == 0) || (LW5.all fun J => LW3.all fun k => famOK Ex Ey Ez J k)

theorem famAll_true : famAll = true := by decide +kernel

theorem infF_sound {a b : ℤ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h : infF a b = true)
    (hc : 0 < (a : ℝ) + b * t) : False := by
  simp only [infF, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : (a : ℝ) ≤ 0 := by exact_mod_cast h.1
  have h2 : (a : ℝ) + b ≤ 0 := by exact_mod_cast h.2
  have : (a : ℝ) + b * t = a * (1 - t) + (a + b) * t := by ring
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 (by linarith : (0 : ℝ) ≤ 1 - t),
    mul_nonpos_of_nonpos_of_nonneg h2 ht0]

theorem bernF_sound {c0 c1 c2 : ℤ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h : bernF c0 c1 c2 = true) :
    0 ≤ (c0 : ℝ) + c1 * t + c2 * t ^ 2 := by
  simp only [bernF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have h0' : (0 : ℝ) ≤ c0 := by exact_mod_cast h0
  have h1' : (0 : ℝ) ≤ 2 * c0 + c1 := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ c0 + c1 + c2 := by exact_mod_cast h2
  have e : (c0 : ℝ) + c1 * t + c2 * t ^ 2 =
      c0 * (1 - t) ^ 2 + (2 * c0 + c1) * (t * (1 - t)) + (c0 + c1 + c2) * t ^ 2 := by ring
  rw [e]
  have : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  positivity

/-- **Soundness of one case**: if `(E, δ, κ)` with `δ = J/2 − Q·3t/100` meets the conditions of an option and the
parity, then `10⁴|V|² ≥ 10⁴ q_a(ε)` or `≥ 10⁴ q_b(ε)`. -/
theorem famOK_sound (Ex Ey Ez J k m : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpar : J - (Ex + Ey) = 2 * m)
    (hlo : 0 < (50 * J + 100 : ℤ) + ((-3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t)
    (hhi : 0 < (100 - 50 * J : ℤ) + ((3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t)
    (hk1 : k = 1 → 0 < (50 * J : ℤ) + ((-3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t)
    (hkm : k = -1 → 0 < (-50 * J : ℤ) + ((3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t)
    (hk0 : k = 0 → 0 < (50 - 50 * J : ℤ) + ((3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t ∧
      0 < (50 + 50 * J : ℤ) + ((-3 * (Ex + Ey - 2 * Ez) : ℤ) : ℝ) * t)
    (hok : famOK Ex Ey Ez J k = true) :
    (12500 : ℝ) - 2700 * t + 729 * t ^ 2 ≤ famA0 Ex Ey Ez J k + famA1 Ex Ey Ez J k * t + famA2 Ex Ey Ez * t ^ 2 ∨
    (10000 : ℝ) + 1200 * t + 324 * t ^ 2 ≤ famA0 Ex Ey Ez J k + famA1 Ex Ey Ez J k * t + famA2 Ex Ey Ez * t ^ 2 := by
  simp only [famOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ((((((hok | hok) | hok) | ⟨hk, hok⟩) | ⟨hk, hok⟩) | ⟨hk, hok | hok⟩) | hok) | hok
  · exfalso; rw [hpar] at hok; exact hok (Int.mul_emod_right 2 m)
  · exact (infF_sound ht0 ht1 hok hlo).elim
  · exact (infF_sound ht0 ht1 hok hhi).elim
  · exact (infF_sound ht0 ht1 hok (hk1 hk)).elim
  · exact (infF_sound ht0 ht1 hok (hkm hk)).elim
  · exact (infF_sound ht0 ht1 hok (hk0 hk).1).elim
  · exact (infF_sound ht0 ht1 hok (hk0 hk).2).elim
  · left
    have := bernF_sound ht0 ht1 hok
    push_cast at this
    linarith
  · right
    have := bernF_sound ht0 ht1 hok
    push_cast at this
    linarith

end QUNetsM3
