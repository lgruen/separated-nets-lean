/-
`rem:wstar` (reaching `μ*`): the nets `𝒲*_p` (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WFamOne
public import QUNetsM3.WFour

@[expose] public section

/-!
# `rem:wstar`

`𝒲*_p` is `genWr` at `r = ⌊pε*⌋`. As printed: `ρ = 2r + 1` is the odd integer nearest to `2pε*` (`pε*` is not an
integer, as `ε*` is irrational), so `|ε_p − ε*| < 1/(2p)`; the net property needs only `1 ≤ ρ < p`, `1 ≤ h − r < p`;
the layer is `𝐰uᵀ` with `u/p = (½ − ε_p, ½ − ε_p, 2ε_p)` (`w_layer`, also for `𝒲_p`); `ε_p ≤ 3/100` for `p ≥ 17`; so
`prop:wfamily` (1), (2) give the value `min(q_a(ε_p), q_b(ε_p))` without the third digits, and the tangent lines of
the convex `q_a`, `q_b` at `ε*` (with `q_b'(ε*) < |q_a'(ε*)| = 2K`) give `> μ*² − K/p`. The limit and the
thresholds `67`, `97`, `9791`, `17737` of the remark are proved here too (exact rational bounds on the roots).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-! ## The layer -/

/-- **The layer of `genWr p r`** (`𝒲_p`, `𝒲*_p`): `genWr p r = genWfam p u T` with `u = (h − r, h − r, ρ)` and the
third rows of `prop:wnet`, for odd `p`. -/
theorem w_layer (hodd : p % 2 = 1) (r : ℕ) : genWr p r = genWfam p (uW p r) (thirdW p) := by
  have h2 := two_hr (p := p) hodd r
  funext c
  ext i j
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [genWr, genWfam, uW, thirdW] <;>
    first | linear_combination h2 | linear_combination 2 * h2 | linear_combination (-1 : ZMod p) * h2

/-- `u/p = (½ − ε, ½ − ε, 2ε)` with `ε = ρ/(2p)`, for odd `p` and `r < h`. -/
theorem w_layer_tau (hodd : p % 2 = 1) {r : ℕ} (hr : r < hW p) :
    tauOf p (uW p r) = tauEps ((2 * (r : ℝ) + 1) / (2 * p)) := by
  have hp : 0 < p := by omega
  have : NeZero p := ⟨by omega⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hhr : hW p - r < p := by unfold hW at hr ⊢; omega
  have hρ : 2 * r + 1 < p := by unfold hW at hr; omega
  have hh : (2 : ℝ) * (hW p : ℝ) + 1 = p := by
    have : 2 * hW p + 1 = p := by unfold hW; omega
    exact_mod_cast this
  have v1 : ((hW p : ZMod p) - r).val = hW p - r := by
    rw [← Nat.cast_sub hr.le, ZMod.val_natCast, Nat.mod_eq_of_lt hhr]
  have v2 : (rhoZ p r).val = 2 * r + 1 := by
    unfold rhoZ; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hρ]
  funext c
  fin_cases c <;> simp only [tauOf, uW, tauEps] <;> simp [v1, v2] <;>
    push_cast [Nat.cast_sub hr.le] <;> field_simp <;> linarith

/-! ## `ε*`, `ρ`, `ε_p` -/

theorem epsStar_lt48 : epsStar < 1 / 48 := by
  have := sqrt31_gt; unfold epsStar; linarith

/-- `√31` is irrational. -/
theorem sqrt31_irr : Irrational (Real.sqrt 31) := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 31 by norm_num)
  simpa using this

/-- `pε*` is not an integer (`p ≥ 1`). -/
theorem pEps_ne (hp : 0 < p) (r : ℕ) : (p : ℝ) * epsStar ≠ r := by
  intro h
  apply sqrt31_irr
  refine ⟨(13 - 90 * (r : ℚ) / p) / 2, ?_⟩
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [← h]
  unfold epsStar
  field_simp
  ring

theorem rStar_le (p : ℕ) : rStar p ≤ p / 48 := by
  unfold rStar
  have h1 : (p : ℝ) * epsStar ≤ (p : ℝ) / 48 := by
    have := epsStar_lt48
    have : (0 : ℝ) ≤ p := by positivity
    nlinarith
  calc ⌊(p : ℝ) * epsStar⌋₊ ≤ ⌊(p : ℝ) / 48⌋₊ := Nat.floor_le_floor h1
    _ = p / 48 := by exact_mod_cast Nat.floor_div_eq_div p 48

theorem rStar_param (hp5 : 5 ≤ p) : WParamOK p (rStar p) := by
  have := rStar_le p
  exact ⟨by omega, by unfold hW; omega⟩

/-- **`rem:wstar`, the net** (proof of `Wstar_net`): `𝒲*_p` is a `(0,3,3)`-net for every prime `p ≥ 5`. -/
theorem wstar_net (hp : p.Prime) (hp5 : 5 ≤ p) : IsDigitalNet033 p (genWstar p) :=
  w_net_gen hp hp5 (rStar_param hp5)

/-- `r ≤ pε* < r + 1` with `pε* ≠ r`. -/
theorem rStar_bounds (hp : 0 < p) :
    (rStar p : ℝ) < p * epsStar ∧ (p : ℝ) * epsStar < rStar p + 1 := by
  have he : 0 ≤ (p : ℝ) * epsStar := mul_nonneg (Nat.cast_nonneg _) (by linarith [epsStar_bounds.1])
  refine ⟨lt_of_le_of_ne (Nat.floor_le he) (pEps_ne hp _).symm, Nat.lt_floor_add_one _⟩

/-- **`ρ` and `ε_p`** (proof of `Wstar_rho`): `ρ = 2⌊pε*⌋ + 1` is the odd integer nearest to `2pε*`
(`|ρ − 2pε*| < 1 ≤ |o − 2pε*|` for every other odd `o`), and `|ε_p − ε*| < 1/(2p)`. -/
theorem wstar_rho (hp : 0 < p) :
    |(2 * (rStar p : ℝ) + 1) - 2 * p * epsStar| < 1 ∧
    (∀ o : ℤ, Odd o → |(2 * (rStar p : ℝ) + 1) - 2 * p * epsStar| ≤ |(o : ℝ) - 2 * p * epsStar|) ∧
    |epsP p - epsStar| < 1 / (2 * p) := by
  obtain ⟨h1, h2⟩ := rStar_bounds hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hA : |(2 * (rStar p : ℝ) + 1) - 2 * p * epsStar| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  refine ⟨hA, ?_, ?_⟩
  · rintro o ⟨m, rfl⟩
    rcases lt_trichotomy m (rStar p) with h | h | h
    · have : (m : ℝ) + 1 ≤ rStar p := by exact_mod_cast (show m + 1 ≤ (rStar p : ℤ) by omega)
      refine le_trans hA.le ?_
      rw [abs_sub_comm, le_abs]; left; push_cast; linarith
    · subst h; push_cast; exact le_refl _
    · have : (rStar p : ℝ) + 1 ≤ m := by exact_mod_cast (show (rStar p : ℤ) + 1 ≤ m by omega)
      refine le_trans hA.le ?_
      rw [le_abs]; left; push_cast; linarith
  · unfold epsP
    rw [show (2 * (rStar p : ℝ) + 1) / (2 * p) - epsStar =
      ((2 * (rStar p : ℝ) + 1) - 2 * p * epsStar) / (2 * p) by field_simp]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * p)]
    exact div_lt_div_of_pos_right hA (by positivity)

/-- **`ε_p ≤ 3/100` for `p ≥ 17`** (proof of `Wstar_eps`): `ε_p = 1/(2p)` for `p ≤ 47`, `ε_p ≤ 3/(2p)` for
`48 ≤ p ≤ 58`, and `ε_p < ε* + 1/118 < 3/100` for `p ≥ 59`; also `ε_p > 0`. -/
theorem wstar_eps (hp : p.Prime) (h17 : 17 ≤ p) : 0 < epsP p ∧ epsP p ≤ 3 / 100 := by
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast h17
  have hp0 : (0 : ℝ) < p := by linarith
  have he := epsStar_bounds
  obtain ⟨h1, h2⟩ := rStar_bounds (show 0 < p by omega)
  refine ⟨by unfold epsP; positivity, ?_⟩
  unfold epsP
  rw [div_le_iff₀ (by positivity)]
  rcases lt_or_ge p 49 with h | h
  · -- `r = 0`
    have hr : (rStar p : ℝ) < 1 := by
      have : (p : ℝ) ≤ 48 := by exact_mod_cast (show p ≤ 48 by omega)
      nlinarith
    have h1' : rStar p < 1 := by exact_mod_cast hr
    have h0 : rStar p = 0 := by omega
    rw [h0]; push_cast; linarith
  · rcases lt_or_ge p 59 with h' | h'
    · -- `49 ≤ p ≤ 58`, `p ≠ 49`: `r ≤ 1`
      have h50 : 50 ≤ p := by
        rcases eq_or_lt_of_le h with h49 | h49
        · exact absurd (h49 ▸ hp) (by norm_num)
        · omega
      have hr : (rStar p : ℝ) < 2 := by
        have : (p : ℝ) ≤ 58 := by exact_mod_cast (show p ≤ 58 by omega)
        nlinarith
      have : rStar p ≤ 1 := by
        have : (rStar p : ℝ) < 2 := hr
        have : rStar p < 2 := by exact_mod_cast this
        omega
      have : (rStar p : ℝ) ≤ 1 := by exact_mod_cast this
      have : (50 : ℝ) ≤ p := by exact_mod_cast h50
      nlinarith
    · -- `p ≥ 59`
      have : (59 : ℝ) ≤ p := by exact_mod_cast h'
      nlinarith

/-! ## The bound with `K` -/

/-- `K > 0` and `q_b'(ε*)/2 < K`. -/
theorem KW_facts : 0 < KW ∧ 2 + 36 * epsStar < KW := by
  have := sqrt31_gt; have := sqrt31_lt
  unfold KW epsStar; constructor <;> linarith

/-- The tangent lines: `min(q_a(ε), q_b(ε)) > μ*² − K/p` for `|ε − ε*| < 1/(2p)`. -/
theorem min_tangent {ε : ℝ} (hp : 0 < (p : ℝ)) (hε : |ε - epsStar| < 1 / (2 * p)) :
    muStarSq - KW / p < min (qaW ε) (qbW ε) := by
  obtain ⟨hK, hKb⟩ := KW_facts
  have hqa := qaW_star
  have hqb := qbW_star
  have hKe : KW = (9 - 162 * epsStar) / 2 := by
    unfold KW epsStar; ring
  rw [abs_lt] at hε
  have hd : 1 / (2 * (p : ℝ)) * (2 * KW) = KW / p := by field_simp
  apply lt_min
  · -- `q_a(ε) − μ*² = 81(ε − ε*)² − 2K(ε − ε*)`
    have e : qaW ε - muStarSq = 81 * (ε - epsStar) ^ 2 - 2 * KW * (ε - epsStar) := by
      rw [← hqa, hKe]; unfold qaW; ring
    have : 2 * KW * (ε - epsStar) < 2 * KW * (1 / (2 * p)) := by
      apply mul_lt_mul_of_pos_left hε.2; positivity
    nlinarith [sq_nonneg (ε - epsStar)]
  · -- `q_b(ε) − μ*² = 36(ε − ε*)² + 2K_b(ε − ε*)`, `K_b < K`
    have e : qbW ε - muStarSq = 36 * (ε - epsStar) ^ 2 + 2 * (2 + 36 * epsStar) * (ε - epsStar) := by
      rw [← hqb]; unfold qbW; ring
    have hb : 0 < 2 + 36 * epsStar := by have := epsStar_bounds; linarith
    rcases le_or_gt 0 (ε - epsStar) with h | h
    · have : 0 < KW / p := by positivity
      nlinarith [sq_nonneg (ε - epsStar)]
    · have h1 : -(2 * (2 + 36 * epsStar)) * (1 / (2 * p)) < 2 * (2 + 36 * epsStar) * (ε - epsStar) := by
        nlinarith
      have h2 : 2 * (2 + 36 * epsStar) * (1 / (2 * p)) ≤ 2 * KW * (1 / (2 * p)) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [sq_nonneg (ε - epsStar)]

/-- **`rem:wstar`, the bound** (proof of `Wstar_bound`): for every prime `p ≥ 17`,
`δN^{1/3}(𝒲*_p) > √(μ*² − K/p) − √3/p`, `K = (9√31 − 36)/5`. -/
theorem wstar_bound (hp : p.Prime) (h17 : 17 ≤ p) :
    Real.sqrt (muStarSq - KW / p) - Real.sqrt 3 / p < deltaG p (genWstar p) := by
  have hodd := odd_of_prime5 hp (by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr := (rStar_param (p := p) (by omega)).r_lt
  have hlay : genWstar p = genWfam p (uW p (rStar p)) (thirdW p) := w_layer hodd _
  have htau := w_layer_tau hodd hr
  obtain ⟨he0, he1⟩ := wstar_eps hp h17
  have hFp : FpW p (uW p (rStar p)) = min (qaW (epsP p)) (qbW (epsP p)) := by
    rw [wfam_FpW hp (by omega), htau]
    exact wfam_two (by unfold epsP at he0; exact he0) he1
  have hmin := min_tangent hpR (wstar_rho hp.pos).2.2
  have hδ := wfam_delta hp (uW p (rStar p)) (thirdW p)
  rw [abs_lt] at hδ
  rw [hlay]
  have : Real.sqrt (muStarSq - KW / p) ≤ Real.sqrt (FpW p (uW p (rStar p))) := by
    apply Real.sqrt_le_sqrt; rw [hFp]; exact hmin.le
  linarith

/-- **`rem:wstar`, the limit** (proof of `Wstar_limit`): `δN^{1/3}(𝒲*_p) → μ*` as the prime `p → ∞`. -/
theorem wstar_limit : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
    |deltaG p (genWstar p) - muStar| < ε := by
  intro ε hε
  refine ⟨max 17 (⌈5 / ε⌉₊ + 1), fun p hp hP => ?_⟩
  have h17 : 17 ≤ p := le_of_max_le_left hP
  have hc : ⌈5 / ε⌉₊ + 1 ≤ p := le_of_max_le_right hP
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast h17
  have hp0 : (0 : ℝ) < p := by linarith
  have hlo := wstar_bound hp h17
  have hodd := odd_of_prime5 hp (by omega)
  have hup : deltaG p (genWstar p) < muStar + Real.sqrt 3 / p := by
    rw [genWstar, w_layer hodd]; exact (wfam_three_net hp (by omega) _ _).2
  have hμ := muStarSq_bounds
  obtain ⟨hK, -⟩ := KW_facts
  have hK3 : KW < 3 := by have := sqrt31_lt; unfold KW; linarith
  have hμ1 : 1 < muStar := by
    unfold muStar; rw [Real.lt_sqrt (by norm_num)]; linarith
  have hμsq := muStar_sq
  -- `√(μ*² − x) ≥ μ* − x/μ*`
  set x := KW / p
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 3 / 17 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; nlinarith
  have key : muStar - x ≤ Real.sqrt (muStarSq - x) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hs3 : Real.sqrt 3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hxp : x ≤ 3 / p := by
    simp only [x]; exact div_le_div_of_nonneg_right hK3.le hp0.le
  have hpe : 5 / ε < p := by
    have := Nat.le_ceil (5 / ε)
    have : ((⌈5 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hc
    push_cast at this
    linarith
  have hsmall : 5 / (p : ℝ) < ε := by
    rw [div_lt_iff₀ hp0]; rw [div_lt_iff₀ hε] at hpe; linarith
  have h3p : Real.sqrt 3 / p ≤ 2 / p := div_le_div_of_nonneg_right hs3.le hp0.le
  have h5 : 3 / (p : ℝ) + 2 / p = 5 / p := by ring
  rw [abs_lt]; constructor <;> linarith

/-! ## The thresholds of `rem:wstar` -/

theorem fStar_mono {p p' : ℕ} (hp : 17 ≤ p) (hle : p ≤ p') : fStar p ≤ fStar p' := by
  unfold fStar
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have h0 : (0 : ℝ) < p := by linarith
  obtain ⟨hK, -⟩ := KW_facts
  have h1 : Real.sqrt (muStarSq - KW / p) ≤ Real.sqrt (muStarSq - KW / p') := by
    apply Real.sqrt_le_sqrt
    have : KW / p' ≤ KW / p := div_le_div_of_nonneg_left hK.le h0 hle'
    linarith
  have h2 : Real.sqrt 3 / p' ≤ Real.sqrt 3 / p := div_le_div_of_nonneg_left (Real.sqrt_nonneg 3) h0 hle'
  linarith

/-- Square-root bounds for the thresholds. -/
theorem sqrt31_lt' : Real.sqrt 31 < 5.5677643628301 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem sqrt3_lt' : Real.sqrt 3 < 1.7320508075689 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem sqrt281_lt' : Real.sqrt 281 < 16.763054614241 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem sqrt843_lt' : Real.sqrt 843 < 29.034462281916 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem sqrt66_lt' : Real.sqrt 66 < 8.1240384046360 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `T + √3/p₀ < √(μ*² − K/p₀)` from `(T + √3/p₀)² < μ*² − K/p₀`. -/
theorem fStar_gt_of {T : ℝ} {p₀ : ℕ} (hp : 0 < p₀) (hT : 0 ≤ T)
    (h : (T + Real.sqrt 3 / p₀) ^ 2 < muStarSq - KW / p₀) : T < fStar p₀ := by
  unfold fStar
  have : T + Real.sqrt 3 / p₀ < Real.sqrt (muStarSq - KW / p₀) := by
    rw [Real.lt_sqrt (by positivity)]; exact h
  linarith

/-- **The thresholds of `rem:wstar`** (proof of `Wstar_thresholds`): the bound `f(p) = √(μ*² − K/p) − √3/p`
increases with `p`; it exceeds `1` for `p ≥ 67`, `√66/8` for `p ≥ 97`, `√281/16` for `p ≥ 9791`, and
`√281/16 + 5/(2p)` for `p ≥ 17737`. -/
theorem wstar_thresholds :
    (∀ p p' : ℕ, 17 ≤ p → p ≤ p' → fStar p ≤ fStar p') ∧
    (∀ p : ℕ, 67 ≤ p → 1 < fStar p) ∧ (∀ p : ℕ, 97 ≤ p → Real.sqrt 66 / 8 < fStar p) ∧
    (∀ p : ℕ, 9791 ≤ p → Real.sqrt 281 / 16 < fStar p) ∧
    (∀ p : ℕ, 17737 ≤ p → Real.sqrt 281 / 16 + 5 / (2 * p) < fStar p) := by
  have s31 := sqrt31_lt'
  have s3 := sqrt3_lt'
  have s281 := sqrt281_lt'
  have s843 := sqrt843_lt'
  have s66 := sqrt66_lt'
  have q3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have q281 : Real.sqrt 281 ^ 2 = 281 := Real.sq_sqrt (by norm_num)
  have q66 : Real.sqrt 66 ^ 2 = 66 := Real.sq_sqrt (by norm_num)
  have p843 : Real.sqrt 281 * Real.sqrt 3 = Real.sqrt 843 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have p66 : Real.sqrt 66 * Real.sqrt 3 = Real.sqrt 198 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have s198 : Real.sqrt 198 < 14.071247279471 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have n3 := Real.sqrt_nonneg 3
  have n281 := Real.sqrt_nonneg 281
  have n66 := Real.sqrt_nonneg 66
  refine ⟨fun p p' h h' => fStar_mono h h', ?_, ?_, ?_, ?_⟩
  · intro p hp
    refine lt_of_lt_of_le ?_ (fStar_mono (by norm_num) hp)
    refine fStar_gt_of (by norm_num) (by norm_num) ?_
    unfold muStarSq KW; push_cast; nlinarith
  · intro p hp
    refine lt_of_lt_of_le ?_ (fStar_mono (by norm_num) hp)
    refine fStar_gt_of (by norm_num) (by positivity) ?_
    unfold muStarSq KW; push_cast
    have e : (Real.sqrt 66 / 8 + Real.sqrt 3 / 97) ^ 2 =
        Real.sqrt 66 ^ 2 / 64 + Real.sqrt 66 * Real.sqrt 3 / 388 + Real.sqrt 3 ^ 2 / 9409 := by ring
    rw [e, q66, q3, p66]; linarith
  · intro p hp
    refine lt_of_lt_of_le ?_ (fStar_mono (by norm_num) hp)
    refine fStar_gt_of (by norm_num) (by positivity) ?_
    unfold muStarSq KW; push_cast
    have e : (Real.sqrt 281 / 16 + Real.sqrt 3 / 9791) ^ 2 =
        Real.sqrt 281 ^ 2 / 256 + Real.sqrt 281 * Real.sqrt 3 / (8 * 9791) + Real.sqrt 3 ^ 2 / 9791 ^ 2 := by ring
    rw [e, q281, q3, p843]; linarith
  · intro p hp
    have hpR : (17737 : ℝ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := by linarith
    -- `f(p) − 5/(2p)` increases with `p`
    have hmono : fStar 17737 - 5 / (2 * 17737) ≤ fStar p - 5 / (2 * p) := by
      have := fStar_mono (p := 17737) (by norm_num) hp
      have : 5 / (2 * (p : ℝ)) ≤ 5 / (2 * 17737) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
      linarith
    have h0 : Real.sqrt 281 / 16 + 5 / (2 * 17737) < fStar 17737 := by
      refine fStar_gt_of (by norm_num) (by positivity) ?_
      unfold muStarSq KW; push_cast
      have e : (Real.sqrt 281 / 16 + 5 / (2 * 17737) + Real.sqrt 3 / 17737) ^ 2 =
          Real.sqrt 281 ^ 2 / 256 + Real.sqrt 281 * Real.sqrt 3 / (8 * 17737) +
            Real.sqrt 3 ^ 2 / 17737 ^ 2 + 5 * Real.sqrt 281 / (16 * 17737) +
            2 * (5 / (2 * 17737)) * Real.sqrt 3 / 17737 + (5 / (2 * 17737)) ^ 2 := by ring
      rw [e, q281, q3, p843]; linarith
    linarith

/-- **`𝒲*_p` provably ahead of `𝒲_p`** (proof of `Wstar_ahead`): for every prime `p ≥ 17737`,
`δN^{1/3}(𝒲_p) ≤ d_*/p² < √281/16 + 5/(2p) < f(p) < δN^{1/3}(𝒲*_p)`. -/
theorem wstar_ahead (hp : p.Prime) (h : 17737 ≤ p) : deltaW p < deltaG p (genWstar p) := by
  have h1 := (w_delta hp (by omega)).2
  have h2 := w_pair_lt hp (by omega)
  have h3 := wstar_thresholds.2.2.2.2 p h
  have h4 := wstar_bound hp (by omega)
  unfold fStar at h3
  linarith

end QUNetsM3
