/-
Entry TwoCoset: the integer core of `prop:twocoset` (2) (`paper/core.tex`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# The integer core of `prop:twocoset` (2)

Notation of the proof of `prop:twocoset`: `E ∈ ℤ³` the cell difference, `Δg = (ξ, η, η)` the
change of the geometric digits (`y` and `z` share it), `S = E_y + E_z`, `T = E_y − E_z`,
`8r = p + θ`.  With `W = pE + (ξ, η, η)` (`= pV`, `V` of the paper) the claim
`|V|² ≥ 33/32 − 41/(16p)` reads `32|W|² ≥ 33p² − 82p`.

* `|E_c| ≥ 3` for some `c`, or `|T| ≥ 2`: direct (`tc_core`).
* Otherwise the integers `j`, `i` of the paper, `2ξ = jp − S`, `8η = ip + θE_x − 8T`, satisfy
  `|j| ≤ 2`, `|i| ≤ 8`, and
  `32|W|² = 8(pA − S)² + (pB + C)² + 16p²T²`, `A = 2E_x + j`, `B = 4S + i`, `C = θE_x − 8T`.
  The finitely many cases `(E, θ, j, i)` are certified by `caseOK` (checked by `decide +kernel`
  in `allOK_true`): each case is excluded by the parities `j ≡ S (mod 2)`, `i ≡ E_x (mod 8)`, or
  by one of the range constraints `|ξ|, |η| ≤ p − 1` (linear in `p`, violated for all `p ≥ 41`),
  or the quadratic `32|W|² − 33p² + 82p` has nonnegative coefficients in `u = p − 41`.  This is
  the case analysis (a)–(f) of the paper, carried out exhaustively.
-/

namespace QUNetsM3

/-- The linear constraint `a p + b ≤ 0` is violated for every `p ≥ 41`. -/
def linInf (a b : ℤ) : Bool := decide (0 ≤ a) && decide (0 < 41 * a + b)

/-- `8(pA − S)² + (pB + C)² + 16p²T² − 33p² + 82p` has nonnegative coefficients in `p − 41`. -/
def polyOK (A B C S T : ℤ) : Bool :=
  decide (0 ≤ 8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) &&
  decide (0 ≤ 82 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) + (-16 * A * S + 2 * B * C + 82)) &&
  decide (0 ≤ 1681 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) +
    41 * (-16 * A * S + 2 * B * C + 82) + (8 * S ^ 2 + C ^ 2))

/-- The certificate of one case `(E_x, E_y, E_z, θ, j, i)`. -/
def caseOK (Ex Ey Ez θ j i : ℤ) : Bool :=
  decide ((j * θ + (Ey + Ez)) % 2 ≠ 0) || decide ((θ * Ex - i * θ) % 8 ≠ 0) ||
  linInf (j - 2) (-(Ey + Ez) + 2) || linInf (-j - 2) ((Ey + Ez) + 2) ||
  linInf (i - 8) ((θ * Ex - 8 * (Ey - Ez)) + 8) || linInf (-i - 8) (-(θ * Ex - 8 * (Ey - Ez)) + 8) ||
  polyOK (2 * Ex + j) (4 * (Ey + Ez) + i) (θ * Ex - 8 * (Ey - Ez)) (Ey + Ez) (Ey - Ez)

theorem linInf_sound {a b p : ℤ} (hp : 41 ≤ p) (h : linInf a b = true) (hc : a * p + b ≤ 0) :
    False := by
  simp only [linInf, Bool.and_eq_true, decide_eq_true_eq] at h
  nlinarith [mul_le_mul_of_nonneg_left hp h.1]

theorem caseOK_sound (p r θ Ex Ey Ez ξ η j i : ℤ) (hp : 41 ≤ p) (h8 : 8 * r = p + θ)
    (hξ : |ξ| ≤ p - 1) (hη : |η| ≤ p - 1) (hj : 2 * ξ = j * p - (Ey + Ez))
    (hi : 8 * η = i * p + (θ * Ex - 8 * (Ey - Ez))) (hok : caseOK Ex Ey Ez θ j i = true) :
    33 * p ^ 2 - 82 * p ≤ 32 * ((p * Ex + ξ) ^ 2 + (p * Ey + η) ^ 2 + (p * Ez + η) ^ 2) := by
  rw [abs_le] at hξ hη
  simp only [caseOK, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ((((((hok | hok) | hok) | hok) | hok) | hok) | hok)
  · exfalso
    have e : j * θ + (Ey + Ez) = 2 * (4 * j * r - ξ) := by linear_combination hj - j * h8
    rw [e] at hok
    exact hok (Int.mul_emod_right 2 _)
  · exfalso
    have e : θ * Ex - i * θ = 8 * (η - i * r + (Ey - Ez)) := by linear_combination -hi + i * h8
    rw [e] at hok
    exact hok (Int.mul_emod_right 8 _)
  · exact (linInf_sound hp hok (by nlinarith)).elim
  · exact (linInf_sound hp hok (by nlinarith)).elim
  · exact (linInf_sound hp hok (by nlinarith)).elim
  · exact (linInf_sound hp hok (by nlinarith)).elim
  · simp only [polyOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨h2, h1⟩, h0⟩ := hok
    set A := 2 * Ex + j
    set B := 4 * (Ey + Ez) + i
    set C := θ * Ex - 8 * (Ey - Ez)
    set S := Ey + Ez
    set T := Ey - Ez
    have hW : 32 * ((p * Ex + ξ) ^ 2 + (p * Ey + η) ^ 2 + (p * Ez + η) ^ 2) =
        8 * (p * A - S) ^ 2 + (p * B + C) ^ 2 + 16 * p ^ 2 * T ^ 2 := by
      have e1 : 2 * (p * Ex + ξ) = p * A - S := by simp only [A, S]; linear_combination hj
      have e2 : 4 * ((p * Ey + η) + (p * Ez + η)) = p * B + C := by
        simp only [B, C]; linear_combination hi
      have e3 : (p * Ey + η) - (p * Ez + η) = p * T := by simp only [T]; ring
      have : 32 * ((p * Ex + ξ) ^ 2 + (p * Ey + η) ^ 2 + (p * Ez + η) ^ 2) =
          8 * (2 * (p * Ex + ξ)) ^ 2 + (4 * ((p * Ey + η) + (p * Ez + η))) ^ 2 +
            16 * ((p * Ey + η) - (p * Ez + η)) ^ 2 := by ring
      rw [this, e1, e2, e3]; ring
    rw [hW]
    set u := p - 41 with hu
    have hu0 : 0 ≤ u := by omega
    have hpu : p = u + 41 := by omega
    have key : 8 * (p * A - S) ^ 2 + (p * B + C) ^ 2 + 16 * p ^ 2 * T ^ 2 - (33 * p ^ 2 - 82 * p) =
        (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) * u ^ 2 +
        (82 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) + (-16 * A * S + 2 * B * C + 82)) * u +
        (1681 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) +
          41 * (-16 * A * S + 2 * B * C + 82) + (8 * S ^ 2 + C ^ 2)) := by
      rw [hpu]; ring
    have : 0 ≤ (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) * u ^ 2 +
        (82 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) + (-16 * A * S + 2 * B * C + 82)) * u +
        (1681 * (8 * A ^ 2 + B ^ 2 + 16 * T ^ 2 - 33) +
          41 * (-16 * A * S + 2 * B * C + 82) + (8 * S ^ 2 + C ^ 2)) := by
      have := mul_nonneg h2 (sq_nonneg u)
      have := mul_nonneg h1 hu0
      linarith
    linarith

/-- The range lists of the enumeration. -/
def L5 : List ℤ := [-2, -1, 0, 1, 2]
def Lθ : List ℤ := [-3, -1, 1, 3]
def L17 : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- All cases `E ∈ {−2,…,2}³ ∖ 0` with `|E_y − E_z| ≤ 1`, `θ ∈ {±1, ±3}`, `|j| ≤ 2`, `|i| ≤ 8`. -/
def allOK : Bool :=
  L5.all fun Ex => L5.all fun Ey => L5.all fun Ez =>
    ((Ex == 0 && Ey == 0 && Ez == 0) || decide (1 < |Ey - Ez|)) ||
      (Lθ.all fun θ => L5.all fun j => L17.all fun i => caseOK Ex Ey Ez θ j i)

theorem allOK_true : allOK = true := by decide +kernel

theorem mem_L5 {a : ℤ} (h1 : -2 ≤ a) (h2 : a ≤ 2) : a ∈ L5 := by
  simp only [L5, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_L17 {a : ℤ} (h1 : -8 ≤ a) (h2 : a ≤ 8) : a ∈ L17 := by
  simp only [L17, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_Lθ {θ : ℤ} (h : θ = -3 ∨ θ = -1 ∨ θ = 1 ∨ θ = 3) : θ ∈ Lθ := by
  simp only [Lθ, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- A coordinate with `|E| ≥ 3` and `|x| ≤ p − 1` has `|pE + x| ≥ 2p + 1`. -/
theorem big_coord (p E x : ℤ) (hp : 0 ≤ p) (hx : |x| ≤ p - 1) (hE : 3 ≤ |E|) :
    (2 * p + 1) ^ 2 ≤ (p * E + x) ^ 2 := by
  rw [abs_le] at hx
  rcases le_abs'.1 hE with h | h
  · have : p * E ≤ -(3 * p) := by nlinarith
    nlinarith
  · have : 3 * p ≤ p * E := by nlinarith
    nlinarith

/-- **The integer core of `prop:twocoset` (2).** -/
theorem tc_core (p r θ Ex Ey Ez ξ η : ℤ) (hp : 41 ≤ p)
    (hθ : θ = -3 ∨ θ = -1 ∨ θ = 1 ∨ θ = 3) (h8 : 8 * r = p + θ)
    (hξ : |ξ| ≤ p - 1) (hη : |η| ≤ p - 1)
    (hcj : p ∣ 2 * ξ + (Ey + Ez)) (hci : p ∣ 8 * η - (θ * Ex - 8 * (Ey - Ez)))
    (hE : Ex ≠ 0 ∨ Ey ≠ 0 ∨ Ez ≠ 0) :
    33 * p ^ 2 - 82 * p ≤ 32 * ((p * Ex + ξ) ^ 2 + (p * Ey + η) ^ 2 + (p * Ez + η) ^ 2) := by
  have hp0 : 0 ≤ p := by omega
  have q1 := sq_nonneg (p * Ex + ξ)
  have q2 := sq_nonneg (p * Ey + η)
  have q3 := sq_nonneg (p * Ez + η)
  have hbig : 33 * p ^ 2 - 82 * p ≤ 32 * (2 * p + 1) ^ 2 := by nlinarith
  by_cases h3 : 3 ≤ |Ex| ∨ 3 ≤ |Ey| ∨ 3 ≤ |Ez|
  · rcases h3 with h | h | h
    · nlinarith [big_coord p Ex ξ hp0 hξ h]
    · nlinarith [big_coord p Ey η hp0 hη h]
    · nlinarith [big_coord p Ez η hp0 hη h]
  push Not at h3
  obtain ⟨hx3, hy3, hz3⟩ := h3
  by_cases hT : 2 ≤ |Ey - Ez|
  · have hT2 : 4 ≤ (Ey - Ez) ^ 2 := by
      have := sq_abs (Ey - Ez); nlinarith
    have : p ^ 2 * (Ey - Ez) ^ 2 ≤ 2 * ((p * Ey + η) ^ 2 + (p * Ez + η) ^ 2) := by
      nlinarith [sq_nonneg (p * Ey + η + (p * Ez + η))]
    nlinarith
  push Not at hT
  have hx : -2 ≤ Ex ∧ Ex ≤ 2 := by rw [abs_lt] at hx3; omega
  have hy : -2 ≤ Ey ∧ Ey ≤ 2 := by rw [abs_lt] at hy3; omega
  have hz : -2 ≤ Ez ∧ Ez ≤ 2 := by rw [abs_lt] at hz3; omega
  have hT1 : -1 ≤ Ey - Ez ∧ Ey - Ez ≤ 1 := by rw [abs_lt] at hT; omega
  obtain ⟨j, hj⟩ := hcj
  obtain ⟨i, hi⟩ := hci
  rw [abs_le] at hξ hη
  have hjb : -2 ≤ j ∧ j ≤ 2 := by
    constructor
    · by_contra hc; push Not at hc
      have : p * j ≤ -3 * p := by nlinarith
      omega
    · by_contra hc; push Not at hc
      have : 3 * p ≤ p * j := by nlinarith
      omega
  have hθb : -3 ≤ θ ∧ θ ≤ 3 := by omega
  have hC : -14 ≤ θ * Ex - 8 * (Ey - Ez) ∧ θ * Ex - 8 * (Ey - Ez) ≤ 14 := by
    rcases hθ with h | h | h | h <;> subst h <;> omega
  have hib : -8 ≤ i ∧ i ≤ 8 := by
    constructor
    · by_contra hc; push Not at hc
      have : p * i ≤ -9 * p := by nlinarith
      omega
    · by_contra hc; push Not at hc
      have : 9 * p ≤ p * i := by nlinarith
      omega
  have hall := allOK_true
  simp only [allOK, List.all_eq_true] at hall
  have hcase := hall Ex (mem_L5 hx.1 hx.2) Ey (mem_L5 hy.1 hy.2) Ez (mem_L5 hz.1 hz.2)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hcase
  rcases hcase with (⟨⟨h0, h1⟩, h2⟩ | hc) | hc
  · exfalso; rcases hE with h | h | h <;> contradiction
  · exfalso; rw [lt_abs] at hc; omega
  · have := hc θ (mem_Lθ hθ) j (mem_L5 hjb.1 hjb.2) i (mem_L17 hib.1 hib.2)
    exact caseOK_sound p r θ Ex Ey Ez ξ η j i hp h8 (abs_le.2 hξ) (abs_le.2 hη)
      (by linear_combination hj) (by linear_combination hi) this

end QUNetsM3
