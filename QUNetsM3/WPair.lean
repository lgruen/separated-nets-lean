/-
`prop:wnet` (3): the explicit pair of `𝒲_p`, its bound, `δN^{1/3}` and the limit `√281/16`
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WSep
public import QUNetsM3.TCPair

@[expose] public section

/-!
# `prop:wnet` (3)

The cells `(1,0,0)` (index `p²`) and `(2,0,p−1)` (index `2p² + p − 1`): second digits `(p−ρ, p−ρ, h−r)` and
`(p−4ρ, p−4ρ, p−2ρ)`, third digits `(0,1,0)` and `(p−2,1,0)`, so the difference is
`(p² − (6r+2)p − 2, −(6r+3)p, p³ − (h+3r+2)p)`, and the translate `t = (0,0,−1)` is the toroidal one.
The bound `d_*/p² < √281/16 + 5/(2p)`: with `48r = p − θ'`, `θ' = p mod 48`,
`(√281 p² + 40p)² − 256 d_*² ≥ (40326/25 − 30θ')p³ + (−9θ'² + 368θ' − 1408)p² + (128θ' − 2048)p − 1024 > 0`
(using `√281 > 16.763`), checked for each odd `θ' < 48` with nonnegative coefficients in `p − 53`.
-/

namespace QUNetsM3

open Matrix Filter Topology

variable {p : ℕ}

theorem digits_p2 (hp : 2 ≤ p) : digits p (p ^ 2) = ![1, 0, 0] := by
  have hp0 : 0 < p := by omega
  funext c
  fin_cases c
  · simp only [digits]
    rw [Nat.div_self (by positivity)]; simp
  · simp only [digits]
    rw [show p ^ 2 / p = p by rw [pow_two, Nat.mul_div_cancel _ hp0]]; simp
  · simp only [digits]
    push_cast; simp

theorem digits_pair2 (hp : 2 ≤ p) : digits p (2 * p ^ 2 + p - 1) = ![2, 0, -1] := by
  have hp0 : 0 < p := by omega
  have hA : (2 * p ^ 2 + p - 1) / p ^ 2 = 2 := by
    apply Nat.div_eq_of_lt_le
    · have : p ≤ p ^ 2 := by nlinarith
      omega
    · have : p + 1 ≤ p ^ 2 := by nlinarith
      generalize p ^ 2 = q at this ⊢
      omega
  have hB : (2 * p ^ 2 + p - 1) / p = 2 * p := by
    apply Nat.div_eq_of_lt_le
    · have : 2 * p * p = 2 * p ^ 2 := by ring
      omega
    · have : (2 * p + 1) * p = 2 * p ^ 2 + p := by ring
      omega
  have hC : ((2 * p ^ 2 + p - 1 : ℕ) : ZMod p) = -1 := by
    have : 2 * p ^ 2 + p - 1 + 1 = p * (2 * p + 1) := by
      have : 1 ≤ 2 * p ^ 2 + p := by nlinarith
      rw [Nat.sub_add_cancel this]; ring
    have h1 : ((2 * p ^ 2 + p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      have := congrArg (fun k : ℕ => (k : ZMod p)) this
      push_cast at this
      rw [this]; simp
    linear_combination h1
  funext c
  fin_cases c
  · simp only [digits]
    rw [hA]; simp
  · simp only [digits]
    rw [hB]; push_cast; simp
  · simp only [digits]
    exact hC

/-- `X² ≤ (X + N t)²` for `2|X| ≤ N`. -/
theorem near_zero (X N t : ℤ) (h1 : 2 * X ≤ N) (h2 : -(2 * X) ≤ N) : X ^ 2 ≤ (X + N * t) ^ 2 := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have : N * t ≤ -N := by nlinarith
    nlinarith
  · rw [ht]; ring_nf; exact le_refl _
  · have : N ≤ N * t := by nlinarith
    nlinarith

theorem rW_small (hp53 : 53 ≤ p) : 48 * rW p ≤ p ∧ 1 ≤ rW p := by
  unfold rW; omega

/-- The coordinates of the two points of `prop:wnet` (3). -/
theorem w_pair_pts (hp : p.Prime) (hp53 : 53 ≤ p) :
    (digitalPt p (genW p) (p ^ 2) 0 : ℤ) = p ^ 2 + (p - (2 * rW p + 1)) * p ∧
    (digitalPt p (genW p) (p ^ 2) 1 : ℤ) = (p - (2 * rW p + 1)) * p + 1 ∧
    (digitalPt p (genW p) (p ^ 2) 2 : ℤ) = ((hW p : ℤ) - rW p) * p ∧
    (digitalPt p (genW p) (2 * p ^ 2 + p - 1) 0 : ℤ) = 2 * p ^ 2 + (p - 4 * (2 * rW p + 1)) * p + (p - 2) ∧
    (digitalPt p (genW p) (2 * p ^ 2 + p - 1) 1 : ℤ) = (p - 4 * (2 * rW p + 1)) * p + 1 ∧
    (digitalPt p (genW p) (2 * p ^ 2 + p - 1) 2 : ℤ) = (p - 1) * p ^ 2 + (p - 2 * (2 * rW p + 1)) * p := by
  have : NeZero p := ⟨by omega⟩
  have : Fact (1 < p) := ⟨by omega⟩
  have hodd := odd_of_prime5 hp (by omega)
  obtain ⟨h48, hr1⟩ := rW_small hp53
  set r := rW p
  have hρlt : 2 * r + 1 < p := by omega
  have h4ρ : 4 * (2 * r + 1) < p := by omega
  have hhr : r < hW p := by unfold hW; omega
  have hhrp : hW p - r < p := by unfold hW; omega
  have h2hr := two_hr (p := p) hodd r
  have v1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have v2 : (2 : ZMod p).val = 2 := by
    have := ZMod.val_natCast (n := p) 2; rw [Nat.mod_eq_of_lt (by omega)] at this; exact_mod_cast this
  have vneg : ∀ k : ℕ, 0 < k → k < p → (-(k : ZMod p)).val = p - k := fun k h0 h => val_neg_nat h0 h
  have vρ : (-rhoZ p r).val = p - (2 * r + 1) := vneg _ (by omega) hρlt
  have v4ρ : (-(4 * rhoZ p r)).val = p - 4 * (2 * r + 1) := by
    have := vneg (4 * (2 * r + 1)) (by omega) h4ρ
    rw [← this]; unfold rhoZ; push_cast; ring_nf
  have v2ρ : (-(2 * rhoZ p r)).val = p - 2 * (2 * r + 1) := by
    have := vneg (2 * (2 * r + 1)) (by omega) (by omega)
    rw [← this]; unfold rhoZ; push_cast; ring_nf
  have vneg1 : (-(1 : ZMod p)).val = p - 1 := by
    have := vneg 1 (by norm_num) (by omega); rwa [Nat.cast_one] at this
  have vneg2 : (-(2 : ZMod p)).val = p - 2 := by
    have := vneg 2 (by norm_num) (by omega); rwa [Nat.cast_ofNat] at this
  have vhr : ((hW p : ZMod p) - r).val = hW p - r := by
    rw [← Nat.cast_sub hhr.le, ZMod.val_natCast, Nat.mod_eq_of_lt hhrp]
  have d1 := digits_p2 (p := p) (by omega)
  have d2 := digits_pair2 (p := p) (by omega)
  simp only [digitalPt_eq, coord_def, d1, d2, genW]
  rw [genWr_x0, genWr_x1, genWr_x2, genWr_y0, genWr_y1, genWr_y2, genWr_z0, genWr_z1, genWr_z2,
    genWr_x0, genWr_x1, genWr_x2, genWr_y0, genWr_y1, genWr_y2, genWr_z0, genWr_z1, genWr_z2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  have e1 : rhoZ p r * (-(1 : ZMod p) - 0 + 2 * 0) = -rhoZ p r := by ring
  have e2 : rhoZ p r * (-(2 : ZMod p) - 0 + 2 * -1) = -(4 * rhoZ p r) := by ring
  have e3 : ((hW p : ZMod p) - r) * (1 + 0) + rhoZ p r * 0 = (hW p : ZMod p) - r := by ring
  have e4 : ((hW p : ZMod p) - r) * (2 + 0) + rhoZ p r * -1 = -(2 * rhoZ p r) := by
    linear_combination h2hr
  have e5 : (0 : ZMod p) + 2 * 0 = 0 := by ring
  have e6 : (0 : ZMod p) + 2 * -1 = -2 := by ring
  have e7 : (1 : ZMod p) + 0 = 1 := by ring
  have e8 : (2 : ZMod p) + -1 = 1 := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  simp only [ZMod.val_zero, vρ, v4ρ, v2ρ, vneg1, vneg2, vhr, v1, v2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast [Nat.cast_sub hρlt.le, Nat.cast_sub h4ρ.le,
    Nat.cast_sub (show 2 * (2 * r + 1) ≤ p by omega), Nat.cast_sub hhr.le,
    Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub (show 2 ≤ p by omega)] <;> ring

/-- **`prop:wnet` (3), the pair** (proof of `W_pair`). -/
theorem w_pair (hp : p.Prime) (hp53 : 53 ≤ p) :
    sepSqG p (genW p) (p ^ 2) (2 * p ^ 2 + p - 1) ![0, 0, -1] = dstarSqW p ∧
    ∀ t : Fin 3 → ℤ, dstarSqW p ≤ sepSqG p (genW p) (p ^ 2) (2 * p ^ 2 + p - 1) t := by
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ := w_pair_pts hp hp53
  obtain ⟨h48, hr1⟩ := rW_small hp53
  have hodd := odd_of_prime5 hp (by omega)
  have hh : 2 * (hW p : ℤ) + 1 = p := by unfold hW; omega
  have hpZ : (53 : ℤ) ≤ p := by exact_mod_cast hp53
  have hrZ : 48 * (rW p : ℤ) ≤ p := by exact_mod_cast h48
  have hr1Z : (1 : ℤ) ≤ rW p := by exact_mod_cast hr1
  have hsep : ∀ t : Fin 3 → ℤ, sepSqG p (genW p) (p ^ 2) (2 * p ^ 2 + p - 1) t =
      ((p : ℤ) ^ 2 - (6 * rW p + 2) * p - 2 + (p : ℤ) ^ 3 * t 0) ^ 2 +
      (-((6 * (rW p : ℤ) + 3) * p) + (p : ℤ) ^ 3 * t 1) ^ 2 +
      ((p : ℤ) ^ 3 - ((hW p : ℤ) + 3 * rW p + 2) * p + (p : ℤ) ^ 3 * t 2) ^ 2 := by
    intro t
    unfold sepSqG
    rw [Fin.sum_univ_three, a0, a1, a2, b0, b1, b2]
    ring
  constructor
  · rw [hsep]; unfold dstarSqW
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  · intro t
    rw [hsep]; unfold dstarSqW
    have hp2 : (p : ℤ) ^ 2 ≥ 2809 := by nlinarith
    have hp3 : (p : ℤ) ^ 3 = p * p ^ 2 := by ring
    have c0 := near_zero ((p : ℤ) ^ 2 - (6 * rW p + 2) * p - 2) ((p : ℤ) ^ 3) (t 0)
      (by nlinarith) (by nlinarith)
    have c1 := near_zero (-((6 * (rW p : ℤ) + 3) * p)) ((p : ℤ) ^ 3) (t 1) (by nlinarith) (by nlinarith)
    have c2 := near_top ((p : ℤ) ^ 3 - ((hW p : ℤ) + 3 * rW p + 2) * p) ((p : ℤ) ^ 3) (t 2)
      (by nlinarith) (by nlinarith)
    have e2 : ((p : ℤ) ^ 3 - ((hW p : ℤ) + 3 * rW p + 2) * p - (p : ℤ) ^ 3) ^ 2 =
        ((hW p : ℤ) + 3 * rW p + 2) ^ 2 * (p : ℤ) ^ 2 := by ring
    have e1 : (-((6 * (rW p : ℤ) + 3) * p)) ^ 2 = (6 * (rW p : ℤ) + 3) ^ 2 * (p : ℤ) ^ 2 := by ring
    rw [e2] at c2; rw [e1] at c1
    linarith

/-- `√281 > 16.763`. -/
theorem sqrt281_gt : 16.763 < Real.sqrt 281 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt281_lt : Real.sqrt 281 < 16.764 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The polynomial of the bound of `prop:wnet` (3) is positive for `p ≥ 53` (`u = p − 53`), for every odd
`θ' < 48`. -/
theorem w_poly_pos (θ : ℕ) (hθ : θ < 48) (hodd : θ % 2 = 1) (u : ℝ) (hu : 0 ≤ u) :
    0 < (40326 / 25 - 30 * (θ : ℝ)) * (u + 53) ^ 3 + (-9 * (θ : ℝ) ^ 2 + 368 * θ - 1408) * (u + 53) ^ 2 +
      (128 * (θ : ℝ) - 2048) * (u + 53) - 1024 := by
  have hu2 := pow_nonneg hu 2
  have hu3 := pow_nonneg hu 3
  interval_cases θ <;> first | omega | (push_cast; ring_nf; linarith)

/-- **`prop:wnet` (3), the bound** (proof of `W_pair_lt`). -/
theorem w_pair_lt (hp : p.Prime) (hp53 : 53 ≤ p) :
    Real.sqrt (dstarSqW p : ℝ) / (p : ℝ) ^ 2 < Real.sqrt 281 / 16 + 5 / (2 * p) := by
  have hodd := odd_of_prime5 hp (by omega)
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp53
  have h0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt 281 with hs
  have hs2 : s ^ 2 = 281 := Real.sq_sqrt (by norm_num)
  have hsl := sqrt281_gt
  set θ : ℕ := p % 48 with hθ
  have hθ48 : θ < 48 := Nat.mod_lt _ (by norm_num)
  have hθodd : θ % 2 = 1 := by omega
  have hr : ((rW p : ℕ) : ℝ) = ((p : ℝ) - θ) / 48 := by
    have : 48 * rW p + θ = p := by unfold rW; omega
    have : (48 : ℝ) * (rW p : ℝ) + θ = p := by exact_mod_cast this
    linarith
  have hh : ((hW p : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
    have : 2 * hW p + 1 = p := by unfold hW; omega
    have : (2 : ℝ) * (hW p : ℝ) + 1 = p := by exact_mod_cast this
    linarith
  have hdR : (dstarSqW p : ℝ) = ((p : ℝ) ^ 2 - (6 * (((p : ℝ) - θ) / 48) + 2) * p - 2) ^ 2 +
      (6 * (((p : ℝ) - θ) / 48) + 3) ^ 2 * (p : ℝ) ^ 2 +
      (((p : ℝ) - 1) / 2 + 3 * (((p : ℝ) - θ) / 48) + 2) ^ 2 * (p : ℝ) ^ 2 := by
    unfold dstarSqW; push_cast; rw [hr, hh]
  have hpos : 0 < s / 16 + 5 / (2 * p) := by positivity
  have hd0 : (0 : ℝ) ≤ dstarSqW p := by rw [hdR]; positivity
  rw [div_lt_iff₀ (by positivity)]
  have key : (dstarSqW p : ℝ) < ((s / 16 + 5 / (2 * p)) * (p : ℝ) ^ 2) ^ 2 := by
    have hexp : ((s / 16 + 5 / (2 * p)) * (p : ℝ) ^ 2) ^ 2 = (s * p ^ 2 + 40 * p) ^ 2 / 256 := by
      field_simp; ring
    rw [hexp, hdR, lt_div_iff₀ (by norm_num)]
    have hF : (s * p ^ 2 + 40 * p) ^ 2 - (((p : ℝ) ^ 2 - (6 * (((p : ℝ) - θ) / 48) + 2) * p - 2) ^ 2 +
        (6 * (((p : ℝ) - θ) / 48) + 3) ^ 2 * (p : ℝ) ^ 2 +
        (((p : ℝ) - 1) / 2 + 3 * (((p : ℝ) - θ) / 48) + 2) ^ 2 * (p : ℝ) ^ 2) * 256 =
        80 * (s - 16.763) * p ^ 3 + ((40326 / 25 - 30 * (θ : ℝ)) * p ^ 3 +
          (-9 * (θ : ℝ) ^ 2 + 368 * θ - 1408) * p ^ 2 + (128 * (θ : ℝ) - 2048) * p - 1024) := by
      linear_combination (p : ℝ) ^ 4 * hs2
    have hp3 : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    have hsp : 0 ≤ 80 * (s - 16.763) * (p : ℝ) ^ 3 := by
      have : 0 ≤ s - 16.763 := by linarith
      positivity
    have hpoly : 0 < (40326 / 25 - 30 * (θ : ℝ)) * p ^ 3 +
        (-9 * (θ : ℝ) ^ 2 + 368 * θ - 1408) * p ^ 2 + (128 * (θ : ℝ) - 2048) * p - 1024 := by
      have := w_poly_pos θ hθ48 hθodd ((p : ℝ) - 53) (by linarith)
      rwa [show (p : ℝ) - 53 + 53 = p by ring] at this
    linarith
  have := Real.sqrt_lt_sqrt hd0 key
  rwa [Real.sqrt_sq (by positivity)] at this

/-! ## `δ N^{1/3}` and the limit -/

/-- `c_W(p) ≤ δ N^{1/3} ≤ d_*/p²` (proof of `W_delta`). -/
theorem w_delta (hp : p.Prime) (hp53 : 53 ≤ p) :
    cW p ≤ deltaW p ∧ deltaW p ≤ Real.sqrt (dstarSqW p : ℝ) / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  unfold deltaW deltaG
  constructor
  · apply le_csInf
    · exact ⟨_, 0, 1, 0, by omega, h3, by norm_num, rfl⟩
    · rintro d ⟨x, x', t, hx, hx', hne, rfl⟩
      rw [le_div_iff₀ hp0]
      have := Real.le_sqrt_of_sq_le (w_sep hp hp53 x x' hx hx' hne t)
      linarith
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro d ⟨x, x', t, -, -, -, rfl⟩
      positivity
    · have hp2 : 2 ≤ p := by omega
      refine ⟨p ^ 2, 2 * p ^ 2 + p - 1, ![0, 0, -1], by nlinarith, ?_, ?_, ?_⟩
      · have : 2 * p ^ 2 + p < p ^ 3 := by nlinarith
        omega
      · have : p ≤ p ^ 2 := by nlinarith
        omega
      · rw [(w_pair hp hp53).1]

/-- `c_W(p) > √281/16 − 5/p` for `p ≥ 53`. -/
theorem cW_ge (hp53 : 53 ≤ p) : Real.sqrt 281 / 16 - 5 / p < cW p := by
  unfold cW
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp53
  have h0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt 281 / 16 with hs
  have hs2 : s ^ 2 = 281 / 256 := by
    rw [hs, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs1 : 1.04 < s := by
    rw [hs, lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  set x := 345 / (128 * (p : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 16 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have key : s - x ≤ Real.sqrt (281 / 256 - x) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hxp : x = (345 / 128) / p := by rw [hx]; field_simp
  have h3 : Real.sqrt 3 < 1.7320509 := sqrt3_lt_W
  have hlt : (345 / 128) / (p : ℝ) + Real.sqrt 3 / p < 5 / p := by
    rw [← add_div]; exact div_lt_div_of_pos_right (by linarith) h0
  linarith

/-- **`prop:wnet` (3), the limit** (proof of `W_limit`). -/
theorem w_limit : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
    |deltaW p - Real.sqrt 281 / 16| < ε := by
  intro ε hε
  refine ⟨max 53 (⌈5 / ε⌉₊ + 1), fun p hp hP => ?_⟩
  have h53 : 53 ≤ p := le_of_max_le_left hP
  have hc : ⌈5 / ε⌉₊ + 1 ≤ p := le_of_max_le_right hP
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  obtain ⟨hlo, hhi⟩ := w_delta hp h53
  have hup := w_pair_lt hp h53
  have hge := cW_ge h53
  have hpe : 5 / ε < p := by
    have := Nat.le_ceil (5 / ε)
    have : ((⌈5 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hc
    push_cast at this
    linarith
  have hsmall : 5 / (p : ℝ) < ε := by
    rw [div_lt_iff₀ hpR]; rw [div_lt_iff₀ hε] at hpe; linarith
  have h2 : 5 / (2 * (p : ℝ)) ≤ 5 / p := by
    apply div_le_div_of_nonneg_left (by norm_num) hpR; linarith
  rw [abs_lt]; constructor <;> linarith

end QUNetsM3
