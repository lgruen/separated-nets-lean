/-
The integer core of `prop:wnet` (2) (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# The integer core of `prop:wnet` (2)

Notation of the proof of `prop:wnet` (2): `E ∈ ℤ³` the step, `D = Δζ` the change of the halved digit,
`κ` the wrap of the digit `2ζ mod p`, so `Δg = (2D − pκ, 2D − pκ, D)`; `S = E_x + E_y`, `Q = S − 2E_z`,
`ρ = 2r + 1`, and `48r = p − θ` with `θ = p mod 48` odd (so `θ − 24 ∈ {−23, …, 23}` is the paper's `θ + 24`
up to sign). With `W = pE + Δg` (`= pV`) the claim `|V|² ≥ 281/256 − 345/(128p)` reads
`256|W|² ≥ 281p² − 690p`.

* Some `|E_c| ≥ 3`: direct.
* Otherwise `2D + ρQ = pJ` (from `D ≡ u·E`, `2(h − r) ≡ −ρ`) with `|J| ≤ 2` (`J = 2M` of the paper), and
  `48D = p(24J − Q) + (θ − 24)Q`, `24W_{x,y} = p a_{x,y} + b`, `48W_z = p a_z + b`. The finitely many
  cases `(E, θ, J, κ)` are certified by `caseW` (checked by `decide +kernel` in `allW_true`): each case is
  excluded by the parity `J ≡ Q (mod 2)`, by a range constraint (`|D|, |2D − pκ| ≤ p − 1`, `κ = sgn D` or
  `κ = 0` with `2|D| ≤ p − 1`; linear in `p`, violated for all `p ≥ 53`), or the quadratic
  `2304(256|W|² − 281p² + 690p)` has nonnegative coefficients in `p − 53`. This is the case analysis of the
  printed proof (the rules for `(M, κ)`, the long options, and the rows of `tab:wcontacts`), carried out
  exhaustively, as for `prop:twocoset`.
-/

namespace QUNetsM3

/-- The linear constraint `a p + b ≤ 0` is violated for every `p ≥ 53`. -/
def linW (a b : ℤ) : Bool := decide (0 ≤ a) && decide (0 < 53 * a + b)

/-- `A p² + B p + C` has nonnegative coefficients in `p − 53`. -/
def polyW (A B C : ℤ) : Bool :=
  decide (0 ≤ A) && decide (0 ≤ 106 * A + B) && decide (0 ≤ 2809 * A + 53 * B + C)

/-- The certificate of one case `(E_x, E_y, E_z, θ, J, κ)`. -/
def caseW (Ex Ey Ez θ J k : ℤ) : Bool :=
  let Q := Ex + Ey - 2 * Ez
  let a1 := 24 * J - Q
  let b1 := (θ - 24) * Q
  let ax := 24 * Ex + 24 * J - Q - 24 * k
  let ay := 24 * Ey + 24 * J - Q - 24 * k
  let az := 48 * Ez + 24 * J - Q
  decide ((J - Q) % 2 ≠ 0) ||
  linW (2 * a1 - 96) (2 * b1 + 96) || linW (-2 * a1 - 96) (-2 * b1 + 96) ||
  linW (2 * a1 - 48 * k - 48) (2 * b1 + 48) || linW (-2 * a1 + 48 * k - 48) (-2 * b1 + 48) ||
  (decide (k = 1) && linW (-a1) (-b1 + 48)) ||
  (decide (k = -1) && linW a1 (b1 + 48)) ||
  (decide (k = 0) && (linW (2 * a1 - 48) (2 * b1 + 48) || linW (-2 * a1 - 48) (-2 * b1 + 48))) ||
  polyW (256 * (4 * ax ^ 2 + 4 * ay ^ 2 + az ^ 2) - 2304 * 281)
    (512 * b1 * (4 * ax + 4 * ay + az) + 2304 * 690) (256 * 9 * b1 ^ 2)

theorem linW_sound {a b p : ℤ} (hp : 53 ≤ p) (h : linW a b = true) (hc : a * p + b ≤ 0) : False := by
  simp only [linW, Bool.and_eq_true, decide_eq_true_eq] at h
  nlinarith [mul_le_mul_of_nonneg_left hp h.1]

theorem caseW_sound (p r θ m Ex Ey Ez D κ J : ℤ) (hp : 53 ≤ p) (h48 : 48 * r = p - θ)
    (hθ : θ = 2 * m + 1) (hJ : 2 * D + (2 * r + 1) * (Ex + Ey - 2 * Ez) = p * J)
    (hD1 : 2 * D ≤ 2 * p - 2) (hD2 : -(2 * D) ≤ 2 * p - 2)
    (hg1 : 2 * D - p * κ ≤ p - 1) (hg2 : -(2 * D - p * κ) ≤ p - 1)
    (hκ : (κ = 0 ∧ 2 * D ≤ p - 1 ∧ -(2 * D) ≤ p - 1) ∨ (κ = 1 ∧ 0 < D) ∨ (κ = -1 ∧ D < 0))
    (hok : caseW Ex Ey Ez θ J κ = true) :
    281 * p ^ 2 - 690 * p ≤
      256 * ((p * Ex + 2 * D - p * κ) ^ 2 + (p * Ey + 2 * D - p * κ) ^ 2 + (p * Ez + D) ^ 2) := by
  have h48D : 48 * D = p * (24 * J - (Ex + Ey - 2 * Ez)) + (θ - 24) * (Ex + Ey - 2 * Ez) := by
    linear_combination 24 * hJ - (Ex + Ey - 2 * Ez) * h48
  simp only [caseW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ((((((((hok | hok) | hok) | hok) | hok) | ⟨hk, hok⟩) | ⟨hk, hok⟩) |
    ⟨hk, hok | hok⟩) | hok)
  · exfalso
    have e : J - (Ex + Ey - 2 * Ez) = 2 * (D - 24 * r * J + r * (Ex + Ey - 2 * Ez) - m * J) := by
      linear_combination -hJ + J * h48 - J * hθ
    rw [e] at hok
    exact hok (Int.mul_emod_right 2 _)
  · exact (linW_sound hp hok (by linear_combination 48 * hD1 - 2 * h48D)).elim
  · exact (linW_sound hp hok (by linear_combination 48 * hD2 + 2 * h48D)).elim
  · exact (linW_sound hp hok (by linear_combination 48 * hg1 - 2 * h48D)).elim
  · exact (linW_sound hp hok (by linear_combination 48 * hg2 + 2 * h48D)).elim
  · subst hk
    have hD : 1 ≤ D := by rcases hκ with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> omega
    exact (linW_sound hp hok (by linear_combination 48 * hD + h48D)).elim
  · subst hk
    have hD : D ≤ -1 := by rcases hκ with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> omega
    exact (linW_sound hp hok (by linear_combination 48 * hD - h48D)).elim
  · subst hk
    have hD : 2 * D ≤ p - 1 := by rcases hκ with ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact (linW_sound hp hok (by linear_combination 48 * hD - 2 * h48D)).elim
  · subst hk
    have hD : -(2 * D) ≤ p - 1 := by
      rcases hκ with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact (linW_sound hp hok (by linear_combination 48 * hD + 2 * h48D)).elim
  · simp only [polyW, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨h2, h1⟩, h0⟩ := hok
    set ax := 24 * Ex + 24 * J - (Ex + Ey - 2 * Ez) - 24 * κ
    set ay := 24 * Ey + 24 * J - (Ex + Ey - 2 * Ez) - 24 * κ
    set az := 48 * Ez + 24 * J - (Ex + Ey - 2 * Ez)
    set b1 := (θ - 24) * (Ex + Ey - 2 * Ez)
    have ex : 24 * (p * Ex + 2 * D - p * κ) = p * ax + b1 := by
      simp only [ax, b1]; linear_combination h48D
    have ey : 24 * (p * Ey + 2 * D - p * κ) = p * ay + b1 := by
      simp only [ay, b1]; linear_combination h48D
    have ez : 48 * (p * Ez + D) = p * az + b1 := by
      simp only [az, b1]; linear_combination h48D
    have hW : 2304 * ((p * Ex + 2 * D - p * κ) ^ 2 + (p * Ey + 2 * D - p * κ) ^ 2 + (p * Ez + D) ^ 2) =
        4 * (p * ax + b1) ^ 2 + 4 * (p * ay + b1) ^ 2 + (p * az + b1) ^ 2 := by
      rw [← ex, ← ey, ← ez]; ring
    set A := 256 * (4 * ax ^ 2 + 4 * ay ^ 2 + az ^ 2) - 2304 * 281
    set B := 512 * b1 * (4 * ax + 4 * ay + az) + 2304 * 690
    set C := 256 * 9 * b1 ^ 2
    have hid : 256 * (4 * (p * ax + b1) ^ 2 + 4 * (p * ay + b1) ^ 2 + (p * az + b1) ^ 2) -
        2304 * (281 * p ^ 2 - 690 * p) = A * p ^ 2 + B * p + C := by
      simp only [A, B, C]; ring
    set u := p - 53 with hu
    have hu0 : 0 ≤ u := by omega
    have hpu : p = u + 53 := by omega
    have hpoly : A * p ^ 2 + B * p + C = A * u ^ 2 + (106 * A + B) * u + (2809 * A + 53 * B + C) := by
      rw [hpu]; ring
    have : 0 ≤ A * u ^ 2 + (106 * A + B) * u + (2809 * A + 53 * B + C) := by
      have := mul_nonneg h2 (sq_nonneg u)
      have := mul_nonneg h1 hu0
      linarith
    linarith

/-- The range lists of the enumeration. -/
def LW5 : List ℤ := [-2, -1, 0, 1, 2]
def LW3 : List ℤ := [-1, 0, 1]
def LWθ : List ℤ := [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43,
  45, 47]

/-- All cases `E ∈ {−2,…,2}³ ∖ 0`, `θ ∈ {1, 3, …, 47}`, `|J| ≤ 2`, `κ ∈ {−1, 0, 1}`. -/
def allW : Bool :=
  LW5.all fun Ex => LW5.all fun Ey => LW5.all fun Ez =>
    (Ex == 0 && Ey == 0 && Ez == 0) ||
      (LWθ.all fun θ => LW5.all fun J => LW3.all fun k => caseW Ex Ey Ez θ J k)

set_option maxHeartbeats 0 in
theorem allW_true : allW = true := by decide +kernel

theorem mem_LW5 {a : ℤ} (h1 : -2 ≤ a) (h2 : a ≤ 2) : a ∈ LW5 := by
  simp only [LW5, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_LW3 {a : ℤ} (h1 : -1 ≤ a) (h2 : a ≤ 1) : a ∈ LW3 := by
  simp only [LW3, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_LWθ {θ : ℤ} (h1 : 1 ≤ θ) (h2 : θ ≤ 47) (h3 : θ % 2 = 1) : θ ∈ LWθ := by
  simp only [LWθ, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- A coordinate with `|E| ≥ 3` and `|x| ≤ p − 1` has `|pE + x| ≥ 2p + 1`. -/
theorem big_coordW (p E x : ℤ) (hp : 0 ≤ p) (hx1 : x ≤ p - 1) (hx2 : -x ≤ p - 1) (hE : 3 ≤ |E|) :
    (2 * p + 1) ^ 2 ≤ (p * E + x) ^ 2 := by
  rcases le_abs'.1 hE with h | h
  · have : p * E ≤ -(3 * p) := by nlinarith
    nlinarith
  · have : 3 * p ≤ p * E := by nlinarith
    nlinarith

/-- **The integer core of `prop:wnet` (2).** -/
theorem w_core (p r θ Ex Ey Ez D κ : ℤ) (hp : 53 ≤ p) (h48 : 48 * r = p - θ) (hθ1 : 1 ≤ θ)
    (hθ2 : θ ≤ 47) (hθo : θ % 2 = 1)
    (hdiv : p ∣ 2 * D + (2 * r + 1) * (Ex + Ey - 2 * Ez))
    (hD1 : D ≤ p - 1) (hD2 : -D ≤ p - 1)
    (hg1 : 2 * D - p * κ ≤ p - 1) (hg2 : -(2 * D - p * κ) ≤ p - 1)
    (hκ : (κ = 0 ∧ 2 * D ≤ p - 1 ∧ -(2 * D) ≤ p - 1) ∨ (κ = 1 ∧ 0 < D) ∨ (κ = -1 ∧ D < 0))
    (hE : Ex ≠ 0 ∨ Ey ≠ 0 ∨ Ez ≠ 0) :
    281 * p ^ 2 - 690 * p ≤
      256 * ((p * Ex + 2 * D - p * κ) ^ 2 + (p * Ey + 2 * D - p * κ) ^ 2 + (p * Ez + D) ^ 2) := by
  have hp0 : 0 ≤ p := by omega
  have q1 := sq_nonneg (p * Ex + 2 * D - p * κ)
  have q2 := sq_nonneg (p * Ey + 2 * D - p * κ)
  have q3 := sq_nonneg (p * Ez + D)
  have hbig : 281 * p ^ 2 - 690 * p ≤ 256 * (2 * p + 1) ^ 2 := by nlinarith [sq_nonneg p]
  by_cases h3 : 3 ≤ |Ex| ∨ 3 ≤ |Ey| ∨ 3 ≤ |Ez|
  · rcases h3 with h | h | h
    · have := big_coordW p Ex (2 * D - p * κ) hp0 hg1 hg2 h
      have e : p * Ex + (2 * D - p * κ) = p * Ex + 2 * D - p * κ := by ring
      rw [e] at this; linarith
    · have := big_coordW p Ey (2 * D - p * κ) hp0 hg1 hg2 h
      have e : p * Ey + (2 * D - p * κ) = p * Ey + 2 * D - p * κ := by ring
      rw [e] at this; linarith
    · have := big_coordW p Ez D hp0 hD1 hD2 h
      linarith
  push Not at h3
  obtain ⟨hx3, hy3, hz3⟩ := h3
  have hx : -2 ≤ Ex ∧ Ex ≤ 2 := by rw [abs_lt] at hx3; omega
  have hy : -2 ≤ Ey ∧ Ey ≤ 2 := by rw [abs_lt] at hy3; omega
  have hz : -2 ≤ Ez ∧ Ez ≤ 2 := by rw [abs_lt] at hz3; omega
  obtain ⟨J, hJ⟩ := hdiv
  obtain ⟨m, hm⟩ : ∃ m, θ = 2 * m + 1 := ⟨θ / 2, by omega⟩
  have hQ : -8 ≤ Ex + Ey - 2 * Ez ∧ Ex + Ey - 2 * Ez ≤ 8 := by omega
  have hr0 : 0 ≤ r := by omega
  have hρ0 : 0 ≤ 2 * r + 1 := by omega
  have hρQ1 : (2 * r + 1) * (Ex + Ey - 2 * Ez) ≤ (2 * r + 1) * 8 :=
    mul_le_mul_of_nonneg_left hQ.2 hρ0
  have hρQ2 : (2 * r + 1) * (-8) ≤ (2 * r + 1) * (Ex + Ey - 2 * Ez) :=
    mul_le_mul_of_nonneg_left hQ.1 hρ0
  have hJb : -2 ≤ J ∧ J ≤ 2 := by
    constructor
    · by_contra hc; push Not at hc
      have : p * J ≤ p * (-3) := mul_le_mul_of_nonneg_left (by omega) hp0
      linarith
    · by_contra hc; push Not at hc
      have : p * 3 ≤ p * J := mul_le_mul_of_nonneg_left (by omega) hp0
      linarith
  have hκb : -1 ≤ κ ∧ κ ≤ 1 := by omega
  have hall := allW_true
  simp only [allW, List.all_eq_true] at hall
  have hcase := hall Ex (mem_LW5 hx.1 hx.2) Ey (mem_LW5 hy.1 hy.2) Ez (mem_LW5 hz.1 hz.2)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcase
  rcases hcase with ⟨⟨h0, h1⟩, h2⟩ | hc
  · exfalso; rcases hE with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2
  · have := hc θ (mem_LWθ hθ1 hθ2 hθo) J (mem_LW5 hJb.1 hJb.2) κ (mem_LW3 hκb.1 hκb.2)
    exact caseW_sound p r θ m Ex Ey Ez D κ J hp h48 hm (by linear_combination hJ) (by omega) (by omega)
      hg1 hg2 hκ this

end QUNetsM3
