/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `thm:allm` and its proof ("Constants").
Entry Dim3 (`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3Rem
public import Z3Net.KNBsep

@[expose] public section

/-!
# Entry Dim3, part 2: `thm:allm` (real form, `ρ` maximal, constants)

* `g(ρ) = q(a(ρ))` with `a(ρ) = (ρ-2)/(ρ+1)` (increasing) and `q(a) = a³(4-a)/3` (increasing on
  `(0, 1]`), which gives `gB1_strictMonoOn` without derivatives, and `g → q(1) = 1`.
* With `p < (ρ+1)²(ρ+2)` (maximality of `ρ`), `c³ = (ρ²-4)³/p² > g(ρ)`; since `0 ≤ c ≤ 1`,
  `g(ρ) < c³ ≤ c ≤ 1`, which squeezes `c → 1`.
-/

namespace Z3NetKN.Proofs.D3

open Finset Filter Topology

/-! ## `ρ` maximal -/

lemma rhoB1_spec (p : ℕ) : rhoB1 p ^ 2 * (rhoB1 p + 1) ≤ p :=
  Nat.findGreatest_spec (P := fun ρ => ρ ^ 2 * (ρ + 1) ≤ p) (Nat.zero_le p) (by simp)

lemma rhoB1_gt (p : ℕ) : p < (rhoB1 p + 1) ^ 2 * (rhoB1 p + 2) := by
  rcases Nat.eq_zero_or_pos p with h0 | hp
  · subst h0; positivity
  · have hs := rhoB1_spec p
    have hlt : rhoB1 p < p := by
      by_contra h
      have hρ : 1 ≤ rhoB1 p := by omega
      have : rhoB1 p * 1 < rhoB1 p ^ 2 * (rhoB1 p + 1) := by nlinarith
      omega
    have := Nat.findGreatest_is_greatest (P := fun ρ => ρ ^ 2 * (ρ + 1) ≤ p)
      (Nat.lt_succ_self (rhoB1 p)) hlt
    simp only [not_le] at this
    exact this

lemma rhoB1_ge (p n : ℕ) (h : n ^ 2 * (n + 1) ≤ p) : n ≤ rhoB1 p := by
  refine Nat.le_findGreatest (P := fun ρ => ρ ^ 2 * (ρ + 1) ≤ p) ?_ h
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · omega
  · have : n * 1 ≤ n ^ 2 * (n + 1) := by nlinarith
    omega

/-! ## Real-form helpers -/

lemma rpow_mix (p : ℝ) (hp : 0 < p) (a : ℝ) (n : ℕ) :
    p ^ (-a) * (p ^ n) ^ (-(1 / (3 : ℝ))) = p ^ (-(a + (n : ℝ) / 3)) := by
  rw [← Real.rpow_natCast p n, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]; congr 1; ring

lemma rpow_neg_nat (p : ℝ) (hp : 0 < p) (n : ℕ) : p ^ (-(n : ℝ)) = (p ^ n)⁻¹ := by
  rw [Real.rpow_neg hp.le, Real.rpow_natCast]

/-- The real toroidal distance as `√(torusDist2)/N`. -/
lemma sqrt_cres_sum (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) :
    Real.sqrt (∑ c, ((cres N ((x c : ℤ) - (y c : ℤ)) : ℝ) / (N : ℝ)) ^ 2) =
      Real.sqrt (torusDist2 N x y : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (∑ c, ((cres N ((x c : ℤ) - (y c : ℤ)) : ℝ) / (N : ℝ)) ^ 2) =
      (torusDist2 N x y : ℝ) / (N : ℝ) ^ 2 := by
    unfold torusDist2; push_cast
    rw [Finset.sum_div]; congr 1; ext c; rw [div_pow]
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN'.le]

end Z3NetKN.Proofs.D3

namespace Z3NetKN.Proofs

open Finset Filter Topology D3

/-- **`thm:allm`, `ρ` maximal.** -/
theorem B1_rho_spec (p : ℕ) (hp : 12 ≤ p) :
    2 ≤ rhoB1 p ∧ rhoB1 p ^ 2 * (rhoB1 p + 1) ≤ p ∧ p < (rhoB1 p + 1) ^ 2 * (rhoB1 p + 2) :=
  ⟨rhoB1_ge p 2 (by norm_num; omega), rhoB1_spec p, rhoB1_gt p⟩

/-- **`thm:allm`, separation (real form).** -/
theorem B1_sep_real (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (-(2 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 1)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 1))
          ((digPoint p (3 * k + 1) C v c : ℤ) - (digPoint p (3 * k + 1) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 1)) ^ 2) := by
  have hZ := B1_sep p k ρ hp hk hρ hρp C hC v w hvw
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : 0 < p ^ (3 * k + 1) := pow_pos hp.pos _
  have hs := sqrt_cres_sum (p ^ (3 * k + 1)) hN (digPoint p (3 * k + 1) C v)
    (digPoint p (3 * k + 1) C w)
  push_cast at hs
  rw [hs, mul_assoc, rpow_mix _ hp0,
    show -(2 / (3 : ℝ) + ((3 * k + 1 : ℕ) : ℝ) / 3) = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
    rpow_neg_nat _ hp0, le_div_iff₀ (by positivity)]
  have h4 : (4 : ℝ) ≤ (ρ : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
    nlinarith
  have hcast : (((ρ ^ 2 - 4 : ℕ) : ℝ)) = (ρ : ℝ) ^ 2 - 4 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have hZr : ((ρ : ℝ) ^ 2 - 4) ^ 2 * (p : ℝ) ^ (4 * k) ≤
      (torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) : ℝ) := by
    rw [← hcast]; exact_mod_cast hZ
  have hle : ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k) ≤
      Real.sqrt (torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v)
        (digPoint p (3 * k + 1) C w) : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    calc (((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k)) ^ 2
        = ((ρ : ℝ) ^ 2 - 4) ^ 2 * (p : ℝ) ^ (4 * k) := by ring
      _ ≤ _ := hZr
  calc ((ρ : ℝ) ^ 2 - 4) * ((p : ℝ) ^ (k + 1))⁻¹ * (p : ℝ) ^ (3 * k + 1)
      = ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k) := by
        field_simp; ring
    _ ≤ _ := hle

/-! ## `g` -/

namespace D3

/-- `a(ρ) = (ρ - 2)/(ρ + 1)`. -/
noncomputable def aG (x : ℝ) : ℝ := (x - 2) / (x + 1)

lemma gB1_eq (x : ℝ) (hx : 0 < x + 1) : gB1 x = aG x ^ 3 * (4 - aG x) / 3 := by
  unfold gB1 aG
  have : x + 1 ≠ 0 := hx.ne'
  push_cast
  field_simp
  ring

lemma aG_lt (x y : ℝ) (hx : 0 < x + 1) (hxy : x < y) : aG x < aG y := by
  unfold aG
  rw [div_lt_div_iff₀ hx (by linarith)]; nlinarith

lemma aG_le_one (x : ℝ) (hx : 0 < x + 1) : aG x < 1 := by
  unfold aG; rw [div_lt_one hx]; linarith

lemma aG_pos (x : ℝ) (hx : 2 < x) : 0 < aG x := by
  unfold aG; apply div_pos <;> linarith

/-- `q(a) = a³(4 - a)` is strictly increasing on `(0, 1]`. -/
lemma q_lt (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) :
    a ^ 3 * (4 - a) < b ^ 3 * (4 - b) := by
  have key : b ^ 3 * (4 - b) - a ^ 3 * (4 - a) =
      (b - a) * (4 * (b ^ 2 + a * b + a ^ 2) - (a + b) * (a ^ 2 + b ^ 2)) := by ring
  have h1 : 0 < b - a := by linarith
  have h2 : (a + b) * (a ^ 2 + b ^ 2) ≤ 2 * (a ^ 2 + b ^ 2) := by
    have : a + b ≤ 2 := by linarith
    nlinarith [sq_nonneg a, sq_nonneg b]
  have h3 : 0 < 4 * (b ^ 2 + a * b + a ^ 2) - (a + b) * (a ^ 2 + b ^ 2) := by
    nlinarith [mul_pos ha (show 0 < b by linarith), sq_nonneg (a + b)]
  nlinarith

end D3

/-- **`thm:allm`, "Constants": `g` increases for `ρ ≥ 3`.** -/
theorem gB1_strictMonoOn : StrictMonoOn gB1 (Set.Ici 3) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rw [gB1_eq x (by linarith), gB1_eq y (by linarith)]
  have := q_lt (aG x) (aG y) (aG_pos x (by linarith)) (aG_lt x y (by linarith) hxy)
    (aG_le_one y (by linarith)).le
  linarith

/-- **`thm:allm`, "Constants": `g` tends to `1`.** -/
theorem gB1_tendsto : Filter.Tendsto gB1 Filter.atTop (nhds 1) := by
  have ha : Tendsto aG atTop (𝓝 1) := by
    have e : ∀ x : ℝ, 0 < x + 1 → aG x = 1 - 3 / (x + 1) := by
      intro x hx; unfold aG; field_simp; ring
    have h3 : Tendsto (fun x : ℝ => 3 / (x + 1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h1 : Tendsto (fun x : ℝ => 1 - 3 / (x + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (e x (by linarith)).symm
  have hq : Tendsto (fun x : ℝ => aG x ^ 3 * (4 - aG x) / 3) atTop (𝓝 1) := by
    have := ((ha.pow 3).mul ((tendsto_const_nhds (x := (4 : ℝ))).sub ha)).div_const 3
    convert this using 2; norm_num
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gB1_eq x (by linarith)).symm

/-- **`thm:allm`, "Constants": `c³ > g(ρ)`.** -/
theorem B1_g_lt (p : ℕ) (h3 : 3 ≤ rhoB1 p) : gB1 (rhoB1 p) < bndB1 p ^ 3 := by
  set ρ := rhoB1 p with hρ
  have hs := rhoB1_spec p
  have hg := rhoB1_gt p
  rw [← hρ] at hs hg
  have hp : 0 < p := by
    have : 0 < ρ ^ 2 * (ρ + 1) := by positivity
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hR3' : (3 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h3
  have hgR' : (p : ℝ) < ((ρ : ℝ) + 1) ^ 2 * ((ρ : ℝ) + 2) := by exact_mod_cast hg
  set R : ℝ := (ρ : ℝ) with hR
  have hR3 : (3 : ℝ) ≤ R := hR3'
  have hgR : (p : ℝ) < (R + 1) ^ 2 * (R + 2) := hgR'
  have hcube : bndB1 p ^ 3 = (R ^ 2 - 4) ^ 3 / (p : ℝ) ^ 2 := by
    unfold bndB1
    rw [← hρ, mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ _) 3, ← Real.rpow_mul hp0.le]
    push_cast
    rw [show -(2 / (3 : ℝ)) * 3 = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_nat _ hp0, div_eq_mul_inv]
  rw [hcube]
  unfold gB1
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hfac : (R ^ 2 - 4) ^ 3 = (R - 2) ^ 3 * (R + 2) ^ 3 := by ring
  rw [hfac]
  have hpos : 0 < (R - 2) ^ 3 * (R + 2) := by
    have : 0 < R - 2 := by linarith
    positivity
  have hsq : (p : ℝ) ^ 2 < ((R + 1) ^ 2 * (R + 2)) ^ 2 := by
    apply pow_lt_pow_left₀ hgR hp0.le (by norm_num)
  calc (R - 2) ^ 3 * (R + 2) * (p : ℝ) ^ 2 < (R - 2) ^ 3 * (R + 2) * ((R + 1) ^ 2 * (R + 2)) ^ 2 :=
        mul_lt_mul_of_pos_left hsq hpos
    _ = (R - 2) ^ 3 * (R + 2) ^ 3 * (R + 1) ^ 4 := by ring

/-- `c ≤ 1` and `0 ≤ c` for `ρ = rhoB1 p ≥ 2`. -/
lemma D3.bndB1_le_one (p : ℕ) (h2 : 2 ≤ rhoB1 p) : 0 ≤ bndB1 p ∧ bndB1 p ≤ 1 := by
  set ρ := rhoB1 p with hρ
  have hs := rhoB1_spec p
  rw [← hρ] at hs
  have hp : 0 < p := by
    have : 0 < ρ ^ 2 * (ρ + 1) := by positivity
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hR2 : (2 : ℝ) ≤ ρ := by exact_mod_cast h2
  have hsR : (ρ : ℝ) ^ 2 * ((ρ : ℝ) + 1) ≤ p := by exact_mod_cast hs
  have h4 : (0 : ℝ) ≤ (ρ : ℝ) ^ 2 - 4 := by nlinarith
  unfold bndB1
  rw [← hρ]
  push_cast
  refine ⟨by positivity, ?_⟩
  -- `(ρ² - 4) p^(-2/3) ≤ 1` iff `(ρ² - 4)³ ≤ p²`
  have hx : (p : ℝ) ^ (-(2 / (3 : ℝ))) = ((p : ℝ) ^ (2 : ℕ)) ^ (-(1 / (3 : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  rw [hx]
  apply mul_rpow_neg_third_le _ _ _ (by positivity) (by norm_num)
  have h6 : ((ρ : ℝ) ^ 2 - 4) ^ 3 ≤ ((ρ : ℝ) ^ 3) ^ 2 := by
    have h1 : ((ρ : ℝ) ^ 2 - 4) ^ 3 ≤ ((ρ : ℝ) ^ 2) ^ 3 := by
      apply pow_le_pow_left₀ h4; linarith
    nlinarith
  have h7 : ((ρ : ℝ) ^ 3) ^ 2 ≤ (p : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); nlinarith
  nlinarith

/-- **`thm:allm`: with `ρ` maximal the bound tends to `1`.** -/
theorem B1_tendsto : Filter.Tendsto bndB1 Filter.atTop (nhds 1) := by
  have hρ : Tendsto (fun p : ℕ => (rhoB1 p : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop_atTop.2 fun n => ⟨n ^ 2 * (n + 1), fun p hp => rhoB1_ge p n hp⟩
  have hg : Tendsto (fun p : ℕ => gB1 (rhoB1 p)) atTop (𝓝 1) := gB1_tendsto.comp hρ
  have hev : ∀ᶠ p : ℕ in atTop, 3 ≤ rhoB1 p := by
    filter_upwards [eventually_ge_atTop 36] with p hp
    exact rhoB1_ge p 3 (by norm_num; omega)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds
  · filter_upwards [hev] with p hp
    have h1 := B1_g_lt p hp
    obtain ⟨h0, hle⟩ := bndB1_le_one p (by omega)
    have : bndB1 p ^ 3 ≤ bndB1 p := by
      calc bndB1 p ^ 3 = bndB1 p * bndB1 p ^ 2 := by ring
        _ ≤ bndB1 p * 1 := by
          apply mul_le_mul_of_nonneg_left _ h0
          nlinarith
        _ = bndB1 p := mul_one _
    linarith
  · filter_upwards [hev] with p hp
    exact (bndB1_le_one p (by omega)).2

/-- **`thm:allm`, "Constants": `ρ ≥ 27` iff `p ≥ 20412`.** -/
theorem B1_rho27 (p : ℕ) : 27 ≤ rhoB1 p ↔ 20412 ≤ p := by
  constructor
  · intro h
    have hs := rhoB1_spec p
    have h1 : 27 ^ 2 ≤ rhoB1 p ^ 2 := Nat.pow_le_pow_left h 2
    have h2 : 27 ^ 2 * 28 ≤ rhoB1 p ^ 2 * (rhoB1 p + 1) := Nat.mul_le_mul h1 (by omega)
    norm_num at h2
    omega
  · intro h; exact rhoB1_ge p 27 (by norm_num; omega)

lemma D3.gB1_27_val : gB1 27 = 453125 / 614656 := by
  unfold gB1; norm_num

/-- **`thm:allm`: the bound exceeds `0.9` whenever `ρ ≥ 27`, i.e. for every prime `p ≥ 20431`.** -/
theorem B1_gt09 :
    (∀ p : ℕ, 27 ≤ rhoB1 p → 0.9 < bndB1 p) ∧ (∀ p : ℕ, p.Prime → 20431 ≤ p → 0.9 < bndB1 p) ∧
    Nat.Prime 20431 ∧ (∀ p : ℕ, p.Prime → 20412 ≤ p → 20431 ≤ p) := by
  have h1 : ∀ p : ℕ, 27 ≤ rhoB1 p → 0.9 < bndB1 p := by
    intro p h
    have hlt := B1_g_lt p (by omega)
    have hmono : gB1 27 ≤ gB1 (rhoB1 p) := by
      apply gB1_strictMonoOn.monotoneOn (by norm_num) (by simp; exact_mod_cast (by omega : 3 ≤ rhoB1 p))
      exact_mod_cast h
    rw [gB1_27_val] at hmono
    obtain ⟨h0, -⟩ := bndB1_le_one p (by omega)
    by_contra hc
    push Not at hc
    have : bndB1 p ^ 3 ≤ 0.9 ^ 3 := pow_le_pow_left₀ h0 hc 3
    norm_num at this
    linarith
  refine ⟨h1, ?_, by norm_num, ?_⟩
  · intro p _ hp
    exact h1 p ((B1_rho27 p).2 (by omega))
  · intro p hp h
    by_contra hc
    push Not at hc
    interval_cases p <;> norm_num at hp

/-- **`thm:allm`, "Constants": `g(27)^(1/3) = 0.9033…`.** -/
theorem gB1_27 : 0.9033 < gB1 27 ^ ((1 : ℝ) / 3) ∧ gB1 27 ^ ((1 : ℝ) / 3) < 0.9034 := by
  rw [gB1_27_val]
  have hx : (0 : ℝ) ≤ 453125 / 614656 := by norm_num
  have hc := rpow_third_cube (453125 / 614656 : ℝ) hx
  have hpos : (0 : ℝ) ≤ (453125 / 614656 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  constructor
  · apply lt_of_pow_lt_pow_left₀ 3 hpos
    rw [hc]; norm_num
  · apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
    rw [hc]; norm_num

end Z3NetKN.Proofs
