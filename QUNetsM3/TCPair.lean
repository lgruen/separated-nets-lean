/-
Entry TwoCoset: `prop:twocoset` (2) numerics and (3), the explicit pair and the limit
(`paper/core.tex`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.TCSep

@[expose] public section

/-!
# `prop:twocoset`: the constants of (2), the pair of (3) and the limit `√66/8`
-/

namespace QUNetsM3

open Matrix Filter Topology

variable {p : ℕ}

/-! ## The constant `c(p) = √(33/32 − 41/(16p)) − √3/p` -/

theorem sqrt3_lt_TC : Real.sqrt 3 < 1.7320509 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt3_gt_TC : 1.7320508 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem cTC_mono {p p' : ℕ} (hp : 41 ≤ p) (hle : p ≤ p') : cTC p ≤ cTC p' := by
  unfold cTC
  have hpR : (41 : ℝ) ≤ p := by exact_mod_cast hp
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) ≤
      Real.sqrt (33 / 32 - 41 / (16 * (p' : ℝ))) := by
    apply Real.sqrt_le_sqrt
    have : 41 / (16 * (p' : ℝ)) ≤ 41 / (16 * (p : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith
  have h2 : Real.sqrt 3 / p' ≤ Real.sqrt 3 / p :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg 3) h0 hle'
  linarith

/-- `√66/8 = √(33/32)`. -/
theorem sqrt66_div8 : Real.sqrt 66 / 8 = Real.sqrt (33 / 32) := by
  rw [show (33 / 32 : ℝ) = 66 / 8 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 8 ^ 2),
    Real.sqrt_sq (by norm_num)]

theorem cTC_ge83 (hp : 83 ≤ p) : Real.sqrt 66 / 8 - 3.014 / p < cTC p := by
  unfold cTC
  have hpR : (83 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt 66 / 8 with hs
  have hs2 : s ^ 2 = 33 / 32 := by
    rw [hs, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs1 : 1.01 < s := by
    rw [hs, lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num
  set x := 41 / (16 * (p : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 32 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have key : s - x / 2 ≤ Real.sqrt (33 / 32 - x) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hxp : x / 2 = (41 / 32) / p := by rw [hx]; field_simp; norm_num
  have h3 : Real.sqrt 3 < 1.7320509 := sqrt3_lt_TC
  have hlt : (41 / 32) / (p : ℝ) + Real.sqrt 3 / p < 3.014 / p := by
    rw [← add_div]; exact div_lt_div_of_pos_right (by linarith) h0
  linarith

theorem cTC_197 : 1.0002 < cTC 197 ∧ cTC 197 < 1.0003 := by
  unfold cTC
  have h3l := sqrt3_gt_TC
  have h3u := sqrt3_lt_TC
  push_cast
  constructor
  · have : 1.0002 + Real.sqrt 3 / 197 < Real.sqrt (33 / 32 - 41 / (16 * 197)) := by
      rw [Real.lt_sqrt (by positivity)]
      nlinarith
    linarith
  · have : Real.sqrt (33 / 32 - 41 / (16 * 197)) < 1.0003 + Real.sqrt 3 / 197 := by
      rw [Real.sqrt_lt' (by positivity)]
      nlinarith
    linarith

theorem cTC_193 : cTC 193 < 1 := by
  unfold cTC
  have h3l := sqrt3_gt_TC
  push_cast
  have : Real.sqrt (33 / 32 - 41 / (16 * 193)) < 1 + Real.sqrt 3 / 193 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  linarith

theorem cTC_gt1 (hp : 197 ≤ p) : 1 < cTC p := by
  have := cTC_mono (p := 197) (by norm_num) hp
  have := cTC_197.1
  linarith

/-! ## The pair of (3) -/

theorem val_neg_nat [NeZero p] {k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    (-(k : ZMod p)).val = p - k := by
  have hne : (k : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by omega) hk
  rw [ZMod.neg_val, if_neg hne, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem digits_top (hp : 2 ≤ p) : digits p (p ^ 3 - 1) = fun _ => -1 := by
  have h1 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hA : (p ^ 3 - 1) / p ^ 2 = p - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (p - 1) * p ^ 2 + p ^ 2 = p ^ 3 := by
        have : p - 1 + 1 = p := by omega
        calc (p - 1) * p ^ 2 + p ^ 2 = (p - 1 + 1) * p ^ 2 := by ring
          _ = p ^ 3 := by rw [this]; ring
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    · have : (p - 1 + 1) * p ^ 2 = p ^ 3 := by
        have : p - 1 + 1 = p := by omega
        rw [this]; ring
      omega
  have hB : (p ^ 3 - 1) / p = p ^ 2 - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (p ^ 2 - 1) * p + p = p ^ 3 := by
        have hq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
        have : p ^ 2 - 1 + 1 = p ^ 2 := by omega
        calc (p ^ 2 - 1) * p + p = (p ^ 2 - 1 + 1) * p := by ring
          _ = p ^ 3 := by rw [this]; ring
      omega
    · have hq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      have : (p ^ 2 - 1 + 1) * p = p ^ 3 := by
        have : p ^ 2 - 1 + 1 = p ^ 2 := by omega
        rw [this]; ring
      omega
  have hq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  funext c
  fin_cases c
  · simp only [digits, Matrix.cons_val_zero]
    rw [hA, Nat.cast_sub (by omega)]; simp
  · simp only [digits, Matrix.cons_val_one, Matrix.head_cons]
    rw [hB, Nat.cast_sub hq]; simp
  · simp only [digits, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [Nat.cast_sub h1]; simp

theorem digitalPt_zero [NeZero p] (c : Fin 3) : digitalPt p (genTC p) 0 c = 0 := by
  have : digits p 0 = 0 := by funext i; fin_cases i <;> simp [digits]
  rw [digitalPt_eq, this, Matrix.mulVec_zero]
  simp [coord]

/-- The three coordinates of the point of the cell `(p − 1)𝟙`. -/
theorem digitalPt_top (hp : p.Prime) (hp7 : 7 ≤ p) :
    digitalPt p (genTC p) (p ^ 3 - 1) 0 = (p - 1) * p ^ 2 + 1 * p + (p - 3) ∧
    digitalPt p (genTC p) (p ^ 3 - 1) 1 = (p - 1) * p ^ 2 + (p - rTC p) * p + (p - 4) ∧
    digitalPt p (genTC p) (p ^ 3 - 1) 2 = (p - 1) * p ^ 2 + (p - rTC p) * p + (p - 6) := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hodd := odd_of_prime5 hp (by omega)
  have hd := digits_top (p := p) (by omega)
  have v1 : (-(1 : ZMod p)).val = p - 1 := by
    have h := val_neg_nat (p := p) (k := 1) (by norm_num) (by omega); rwa [Nat.cast_one] at h
  have hr0 := rTC_pos (p := p) (by omega)
  have hrl := rTC_lt (p := p) (by omega)
  have vr : (-(rTC p : ZMod p)).val = p - rTC p := val_neg_nat (by omega) hrl
  have v3 : (-(3 : ZMod p)).val = p - 3 := by
    have h := val_neg_nat (p := p) (k := 3) (by norm_num) (by omega); rwa [Nat.cast_ofNat] at h
  have v4 : (-(4 : ZMod p)).val = p - 4 := by
    have h := val_neg_nat (p := p) (k := 4) (by norm_num) (by omega); rwa [Nat.cast_ofNat] at h
  have v6 : (-(6 : ZMod p)).val = p - 6 := by
    have h := val_neg_nat (p := p) (k := 6) (by norm_num) (by omega); rwa [Nat.cast_ofNat] at h
  have vone : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h2h := two_hTC hodd
  have x0 : (genTC p 0 *ᵥ (fun _ => (-1 : ZMod p))) 0 = -1 := by rw [genTC_x0]
  have x1 : (genTC p 0 *ᵥ (fun _ => (-1 : ZMod p))) 1 = 1 := by rw [genTC_x1]; linear_combination -h2h
  have x2 : (genTC p 0 *ᵥ (fun _ => (-1 : ZMod p))) 2 = -3 := by rw [genTC_x2]; ring
  have y0 : (genTC p 1 *ᵥ (fun _ => (-1 : ZMod p))) 0 = -1 := by rw [genTC_y0]
  have y1 : (genTC p 1 *ᵥ (fun _ => (-1 : ZMod p))) 1 = -(rTC p : ZMod p) := by rw [genTC_y1]; ring
  have y2 : (genTC p 1 *ᵥ (fun _ => (-1 : ZMod p))) 2 = -4 := by rw [genTC_y2]; ring
  have z0 : (genTC p 2 *ᵥ (fun _ => (-1 : ZMod p))) 0 = -1 := by rw [genTC_z0]
  have z1 : (genTC p 2 *ᵥ (fun _ => (-1 : ZMod p))) 1 = -(rTC p : ZMod p) := by rw [genTC_z1]; ring
  have z2 : (genTC p 2 *ᵥ (fun _ => (-1 : ZMod p))) 2 = -6 := by rw [genTC_z2]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [digitalPt_eq, coord_def, hd, x0, x1, x2, v1, v3, vone]
  · rw [digitalPt_eq, coord_def, hd, y0, y1, y2, v1, vr, v4]
  · rw [digitalPt_eq, coord_def, hd, z0, z1, z2, v1, vr, v6]

/-- `(X − N)² ≤ (X + N t)²` for `N/2 ≤ X ≤ N`. -/
theorem near_top (X N t : ℤ) (h1 : N ≤ 2 * X) (h2 : X ≤ N) : (X - N) ^ 2 ≤ (X + N * t) ^ 2 := by
  rcases le_or_gt 0 t with ht | ht
  · have : 0 ≤ N * t := by nlinarith
    nlinarith
  · have ht' : t ≤ -1 := by omega
    have : N * t ≤ -N := by nlinarith
    nlinarith

/-- **`prop:twocoset` (3), the pair** (proof of `TC_pair`). -/
theorem tc_pair' (hp : p.Prime) (hp7 : 7 ≤ p) :
    sepSqG p (genTC p) 0 (p ^ 3 - 1) (fun _ => -1) = dstarSqTC p ∧
    ∀ t : Fin 3 → ℤ, dstarSqTC p ≤ sepSqG p (genTC p) 0 (p ^ 3 - 1) t := by
  have := Fact.mk hp
  obtain ⟨hx, hy, hz⟩ := digitalPt_top hp hp7
  have hr0 := rTC_pos (p := p) (by omega)
  have hrl := rTC_lt (p := p) (by omega)
  have hP : ∀ c, (digitalPt p (genTC p) (p ^ 3 - 1) c : ℤ) = (if c = 0 then
      ((p : ℤ) - 1) * p ^ 2 + p + (p - 3) else if c = 1 then
      ((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 4) else
      ((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 6)) := by
    intro c
    fin_cases c
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; rw [hx]; push_cast [Nat.cast_sub (show 1 ≤ p by omega),
        Nat.cast_sub (show 3 ≤ p by omega)]; ring
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; rw [hy]
      push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub hrl.le,
        Nat.cast_sub (show 4 ≤ p by omega)]; ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte]; rw [hz]
      push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub hrl.le,
        Nat.cast_sub (show 6 ≤ p by omega)]; ring
  have hsep : ∀ t : Fin 3 → ℤ, sepSqG p (genTC p) 0 (p ^ 3 - 1) t =
      ∑ c : Fin 3, ((digitalPt p (genTC p) (p ^ 3 - 1) c : ℤ) + (p : ℤ) ^ 3 * t c) ^ 2 := by
    intro t
    unfold sepSqG
    simp [digitalPt_zero]
  have hpZ : (7 : ℤ) ≤ p := by exact_mod_cast hp7
  have hrZ : (1 : ℤ) ≤ rTC p := by exact_mod_cast hr0
  have hrZ' : (rTC p : ℤ) < p := by exact_mod_cast hrl
  constructor
  · rw [hsep, Fin.sum_univ_three, hP, hP, hP]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq]
    unfold dstarSqTC
    ring
  · intro t
    rw [hsep, Fin.sum_univ_three, hP, hP, hP]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Fin.reduceEq]
    unfold dstarSqTC
    have hp2 : (p : ℤ) ^ 2 ≥ 49 := by nlinarith
    have hp3 : (p : ℤ) ^ 3 = p * p ^ 2 := by ring
    have a0 := near_top (((p : ℤ) - 1) * p ^ 2 + p + (p - 3)) ((p : ℤ) ^ 3) (t 0)
      (by nlinarith) (by nlinarith)
    have a1 := near_top (((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 4)) ((p : ℤ) ^ 3) (t 1)
      (by nlinarith) (by nlinarith)
    have a2 := near_top (((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 6)) ((p : ℤ) ^ 3) (t 2)
      (by nlinarith) (by nlinarith)
    have e0 : (((p : ℤ) - 1) * p ^ 2 + p + (p - 3) - (p : ℤ) ^ 3) ^ 2 =
        ((p : ℤ) ^ 2 - 2 * p + 3) ^ 2 := by ring
    have e1 : (((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 4) - (p : ℤ) ^ 3) ^ 2 =
        (((rTC p : ℤ) - 1) * p + 4) ^ 2 := by ring
    have e2 : (((p : ℤ) - 1) * p ^ 2 + (p - rTC p) * p + (p - 6) - (p : ℤ) ^ 3) ^ 2 =
        (((rTC p : ℤ) - 1) * p + 6) ^ 2 := by ring
    rw [e0] at a0; rw [e1] at a1; rw [e2] at a2
    linarith

/-- **`prop:twocoset` (3), the bound** (proof of `TC_pair_lt`). -/
theorem tc_pair_lt' (hp : p.Prime) (hp53 : 53 ≤ p) :
    Real.sqrt (dstarSqTC p : ℝ) / (p : ℝ) ^ 2 < Real.sqrt 66 / 8 - 2 / p := by
  have hodd := odd_of_prime5 hp (by omega)
  have hθ := thetaTC_cases hodd
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp53
  have h0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt 66 with hs
  have hs2 : s ^ 2 = 66 := Real.sq_sqrt (by norm_num)
  have hsl : 8.1240384 < s := by rw [hs, Real.lt_sqrt (by norm_num)]; norm_num
  have hsu : s < 8.1240385 := by rw [hs, Real.sqrt_lt' (by norm_num)]; norm_num
  set θ : ℝ := (thetaTC p : ℝ) with hθR
  have hr : ((rTC p : ℕ) : ℝ) = ((p : ℝ) + θ) / 8 := by
    have : θ = 8 * ((rTC p : ℕ) : ℝ) - p := by rw [hθR]; unfold thetaTC; push_cast; ring
    linarith
  have hdR : (dstarSqTC p : ℝ) = ((p : ℝ) ^ 2 - 2 * p + 3) ^ 2 +
      ((((p : ℝ) + θ) / 8 - 1) * p + 4) ^ 2 + ((((p : ℝ) + θ) / 8 - 1) * p + 6) ^ 2 := by
    unfold dstarSqTC; push_cast; rw [← hr]
  have hpos : 0 < s / 8 - 2 / p := by
    have : 2 / (p : ℝ) ≤ 2 / 53 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith
  have hd0 : (0 : ℝ) ≤ dstarSqTC p := by rw [hdR]; positivity
  rw [div_lt_iff₀ (by positivity)]
  have key : (dstarSqTC p : ℝ) < ((s / 8 - 2 / p) * (p : ℝ) ^ 2) ^ 2 := by
    have hexp : ((s / 8 - 2 / p) * (p : ℝ) ^ 2) ^ 2 = (s * p ^ 2 - 16 * p) ^ 2 / 64 := by
      field_simp; ring
    rw [hexp, hdR, lt_div_iff₀ (by norm_num)]
    have hF : (s * p ^ 2 - 16 * p) ^ 2 - (((p : ℝ) ^ 2 - 2 * p + 3) ^ 2 +
        ((((p : ℝ) + θ) / 8 - 1) * p + 4) ^ 2 + ((((p : ℝ) + θ) / 8 - 1) * p + 6) ^ 2) * 64 =
        (288 - 4 * θ - 32 * s) * p ^ 3 - (672 - 32 * θ + 2 * θ ^ 2) * p ^ 2 +
          (2048 - 160 * θ) * p - 3904 := by
      linear_combination (p : ℝ) ^ 4 * hs2
    have hθ' : θ = -3 ∨ θ = -1 ∨ θ = 1 ∨ θ = 3 := by
      rcases hθ with h | h | h | h <;> rw [hθR, h] <;> norm_num
    have hp3 : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    have hsp : s * (p : ℝ) ^ 3 ≤ 8.1240385 * (p : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hsu.le hp3
    set u := (p : ℝ) - 53 with hu
    have hu0 : 0 ≤ u := by linarith
    have hpu : (p : ℝ) = u + 53 := by linarith
    have hu2 := pow_nonneg hu0 2
    have hu3 := pow_nonneg hu0 3
    rw [hpu] at hF hsp ⊢
    rcases hθ' with h | h | h | h <;> rw [h] at hF ⊢ <;> linarith
  have := Real.sqrt_lt_sqrt hd0 key
  rwa [Real.sqrt_sq (by positivity)] at this

/-! ## `δ N^{1/3}` and the limit -/

theorem tc_delta' (hp : p.Prime) (hp41 : 41 ≤ p) :
    cTC p ≤ deltaTC p ∧ deltaTC p ≤ Real.sqrt (dstarSqTC p : ℝ) / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  constructor
  · apply le_csInf
    · exact ⟨_, 0, 1, 0, by omega, h3, by norm_num, rfl⟩
    · rintro d ⟨x, x', t, hx, hx', hne, rfl⟩
      rw [le_div_iff₀ hp0]
      have := Real.le_sqrt_of_sq_le (tc_sep' hp hp41 x x' hx hx' hne t)
      unfold cTC; linarith
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro d ⟨x, x', t, -, -, -, rfl⟩
      positivity
    · refine ⟨0, p ^ 3 - 1, fun _ => -1, by positivity, by omega, by omega, ?_⟩
      rw [(tc_pair' hp (by omega)).1]

theorem tc_limit' : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
    |deltaTC p - Real.sqrt 66 / 8| < ε := by
  intro ε hε
  refine ⟨max 83 (⌈3.014 / ε⌉₊ + 1), fun p hp hP => ?_⟩
  have h83 : 83 ≤ p := le_of_max_le_left hP
  have hc : ⌈3.014 / ε⌉₊ + 1 ≤ p := le_of_max_le_right hP
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  obtain ⟨hlo, hhi⟩ := tc_delta' hp (by omega)
  have hup := tc_pair_lt' hp (by omega)
  have hge := cTC_ge83 h83
  have h2 : 0 < 2 / (p : ℝ) := by positivity
  have hpe : 3.014 / ε < p := by
    have := Nat.le_ceil (3.014 / ε)
    have : ((⌈3.014 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hc
    push_cast at this
    linarith
  have hsmall : 3.014 / (p : ℝ) < ε := by
    rw [div_lt_iff₀ hpR]; rw [div_lt_iff₀ hε] at hpe; linarith
  rw [abs_lt]; constructor <;> linarith

end QUNetsM3
