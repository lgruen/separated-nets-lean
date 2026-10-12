/-
Proof module of entry U (stage 6): the constants `a_3, a_4, a_5` of `thm:U`, the lower bound
`L_s ≤ a_s`, and the growth of `a_s` and of the bound `L_s (s² + 2^(s-2))`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SUBound

@[expose] public section

/-!
# Entry U, stage 6: `a_3 = 4`, `a_4 = 63`, `a_5 = 17407`; growth of `a_s`

* `U_a3`, `U_a4`, `U_a5` — kernel evaluation (`decide +kernel`) of the Challenge definition `aU`.
* `U_aLower` — `L_s ≤ a_s` (the `∞` column of any finite row contributes `L_s`).
* `U_growth` — for every `ε > 0`, eventually in `s`:
  `(log 2 - ε) s² ≤ log a_s` and `log (L_s (s² + 2^(s-2))) ≤ (log 4 + ε) s²`
  (Chebyshev's bounds `ψ(n) ≥ n log 2 - log(n+1)` and `ψ(x) ≤ x log 4 + 2 √x log x` of Mathlib;
  `log L_s = (s-1) ψ(s-2)`).
-/

namespace Z3NetU.Proofs

open Finset Z3NetU Filter Real

theorem U_a3 : aU 3 = 4 := by decide +kernel

theorem U_a4 : aU 4 = 63 := by decide +kernel

theorem U_a5 : aU 5 = 17407 := by decide +kernel

lemma acoef_ge_L (s : ℕ) (hs : 3 ≤ s) : Lcst s ≤ acoef s ⟨1, by omega⟩ := by
  unfold acoef
  have h0 : (⟨0, by omega⟩ : Fin s) ∈ univ.filter (fun d : Fin s => d ≠ ⟨1, by omega⟩) := by
    simp [Fin.ext_iff]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)
  refine le_trans ?_ (Finset.le_sup (f := fun j => (Msum s j ⟨1, by omega⟩ ⟨0, by omega⟩).natAbs)
    (mem_range.mpr (show 0 < s - 1 by omega)))
  have : Msum s 0 ⟨1, by omega⟩ ⟨0, by omega⟩ = (Lcst s : ℤ) := by
    have h1 : ¬ (s - 1 ≤ 0) := by omega
    simp [Msum, Foff]
    omega
  rw [this, Int.natAbs_natCast]

theorem U_aLower (s : ℕ) (hs : 3 ≤ s) : Lcst s ≤ aU s :=
  le_trans (acoef_ge_L s hs) (Finset.le_sup (f := acoef s) (mem_univ _))

lemma Lcst_eq (s : ℕ) : Lcst s = (Nat.lcmUpto (s - 2)) ^ (s - 1) := rfl

lemma log_Lcst (s : ℕ) : Real.log (Lcst s : ℝ) = (s - 1 : ℕ) * Chebyshev.psi ((s - 2 : ℕ) : ℝ) := by
  rw [Lcst_eq, Nat.cast_pow, Real.log_pow, Chebyshev.psi_eq_log_lcmUpto]

/-- `√x log x = o(x)`. -/
lemma sqrt_log_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 2 * √x * Real.log x ≤ ε * x := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound (c := ε / 2) (by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  have hs : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  rw [hs] at hx
  have hsq : √x * √x = x := Real.mul_self_sqrt hx0
  have : 0 ≤ √x := Real.sqrt_nonneg x
  nlinarith

/-- `x log x = o(x²)`. -/
lemma log_small (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * x := by
  have h := isLittleO_log_id_atTop.bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (by simp; linarith)] at hx
  simpa using hx

lemma sq_add_pow_le (s : ℕ) (hs : 6 ≤ s) : s ^ 2 + 2 ^ (s - 2) ≤ 2 ^ s := by
  have h3 : ∀ t : ℕ, (t + 6) ^ 2 ≤ 3 * 2 ^ (t + 6 - 2) := by
    intro t
    induction t with
    | zero => norm_num
    | succ n ih =>
      have e : 3 * 2 ^ (n + 1 + 6 - 2) = 2 * (3 * 2 ^ (n + 6 - 2)) := by
        rw [show n + 1 + 6 - 2 = (n + 6 - 2) + 1 by omega, pow_succ]; ring
      have h2 : (n + 1 + 6) ^ 2 ≤ 2 * (n + 6) ^ 2 := by ring_nf; nlinarith [Nat.zero_le n]
      rw [e]; omega
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 6 := ⟨s - 6, by omega⟩
  have := h3 t
  have h4 : 2 ^ (t + 6) = 4 * 2 ^ (t + 6 - 2) := by
    rw [show t + 6 = (t + 6 - 2) + 2 by omega, pow_add]; norm_num; ring_nf
  omega

lemma nat_eventually {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P x) :
    ∀ᶠ s : ℕ in atTop, P ((s : ℝ)) :=
  tendsto_natCast_atTop_atTop.eventually h

/-- **Growth of `a_s`** (the provable form of `e^{Θ(s²)}`; the constant `1` of the paper's
`e^{(1+o(1))s²}` needs the prime number theorem, which is not in Mathlib): for every `ε > 0`,
eventually `(log 2 - ε) s² ≤ log a_s` and `log (L_s (s² + 2^(s-2))) ≤ (log 4 + ε) s²`. -/
theorem U_growth (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℕ in atTop, (Real.log 2 - ε) * (s : ℝ) ^ 2 ≤ Real.log (aU s : ℝ) ∧
      Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) ≤ (Real.log 4 + ε) * (s : ℝ) ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- lower bound ingredients
  have e1 := nat_eventually (log_small (ε / 2) (by positivity))
  have e2 := nat_eventually (sqrt_log_small (ε / 4) (by positivity))
  have e3 := nat_eventually (log_small (ε / 8) (by positivity))
  have e4 : ∀ᶠ s : ℕ in atTop, (3 * Real.log 2 + 4 * Real.log 4 + 8) / ε ≤ (s : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have e5 := nat_eventually (sqrt_log_small (ε / 4) (by positivity))
  filter_upwards [e1, e2, e3, e4, eventually_ge_atTop 6,
    (tendsto_sub_atTop_nat 2).eventually e5] with s h1 h2 h3 h4 hs5 h5
  have hs : (6 : ℝ) ≤ s := by exact_mod_cast hs5
  have hcs : ((s - 2 : ℕ) : ℝ) = s - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hcs1 : ((s - 1 : ℕ) : ℝ) = s - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hL1 : (1 : ℝ) ≤ Lcst s := by exact_mod_cast Lcst_pos s
  constructor
  · -- `log a_s ≥ log L_s = (s-1) ψ(s-2) ≥ (s-1)((s-2) log 2 - log(s-1))`
    have ha : (Lcst s : ℝ) ≤ aU s := by exact_mod_cast U_aLower s (by omega)
    have hlog : Real.log (Lcst s : ℝ) ≤ Real.log (aU s : ℝ) :=
      Real.log_le_log (by linarith) ha
    refine le_trans ?_ hlog
    rw [log_Lcst, hcs1, hcs]
    have hpsi := Chebyshev.psi_ge (s - 2)
    rw [hcs, show (s : ℝ) - 2 + 1 = s - 1 by ring] at hpsi
    -- `log (s-1) ≤ log s ≤ (ε/2) s`
    have hls : Real.log ((s : ℝ) - 1) ≤ Real.log s := Real.log_le_log (by linarith) (by linarith)
    have hb : (s - 1) * ((s - 2) * Real.log 2 - Real.log (s - 1)) ≤
        (s - 1) * Chebyshev.psi (s - 2) := mul_le_mul_of_nonneg_left hpsi (by linarith)
    refine le_trans ?_ hb
    have h4' : 3 * Real.log 2 + 4 * Real.log 4 + 8 ≤ ε * s := by
      rw [div_le_iff₀ hε] at h4; linarith
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have a1 : ((s : ℝ) - 1) * Real.log ((s : ℝ) - 1) ≤ ((s : ℝ) - 1) * (ε / 2 * s) :=
      mul_le_mul_of_nonneg_left (hls.trans h1) (by linarith)
    have a2 : 6 * Real.log 2 ≤ ε * s := by linarith
    have a3 : 6 * Real.log 2 * s ≤ ε * s * s := mul_le_mul_of_nonneg_right a2 (by linarith)
    nlinarith
  · -- upper bound
    have hpos : (0 : ℝ) < (s : ℝ) ^ 2 + 2 ^ (s - 2) := by positivity
    rw [Real.log_mul (by linarith) hpos.ne', log_Lcst, hcs1]
    -- `ψ(s-2) ≤ (s-2) log 4 + 2 √(s-2) log(s-2) ≤ (s-2) (log 4 + ε/4)`
    have hpsi := Chebyshev.psi_le (x := ((s - 2 : ℕ) : ℝ)) (by rw [hcs]; linarith)
    have h5' : 2 * √((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) ≤ ε / 4 * ((s - 2 : ℕ) : ℝ) := h5
    rw [hcs] at hpsi h5'
    -- `s² + 2^(s-2) ≤ 2^s`, so its log is at most `s log 2 ≤ (ε/8) s log 2 ...`
    have hpow : (s : ℝ) ^ 2 + 2 ^ (s - 2) ≤ 2 ^ s := by
      have hn : s ^ 2 + 2 ^ (s - 2) ≤ 2 ^ s := sq_add_pow_le s hs5
      exact_mod_cast hn
    have hlogp : Real.log ((s : ℝ) ^ 2 + 2 ^ (s - 2)) ≤ s * Real.log 2 := by
      calc Real.log ((s : ℝ) ^ 2 + 2 ^ (s - 2)) ≤ Real.log ((2 : ℝ) ^ s) :=
            Real.log_le_log hpos hpow
        _ = s * Real.log 2 := by rw [Real.log_pow]
    have h4' : 3 * Real.log 2 + 4 * Real.log 4 + 8 ≤ ε * s := by
      rw [div_le_iff₀ hε] at h4; linarith
    have hps : Chebyshev.psi ((s : ℝ) - 2) ≤ ((s : ℝ) - 2) * (Real.log 4 + ε / 4) := by
      nlinarith
    have : ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) ≤
        ((s : ℝ) - 1) * (((s : ℝ) - 2) * (Real.log 4 + ε / 4)) :=
      mul_le_mul_of_nonneg_left hps (by linarith)
    rw [hcs]
    have b1 : ε * 6 ≤ ε * s := mul_le_mul_of_nonneg_left hs hε.le
    have b2 : 8 * s ≤ ε * s * s := by nlinarith
    have hl42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    nlinarith

end Z3NetU.Proofs
