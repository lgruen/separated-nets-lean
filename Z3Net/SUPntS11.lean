/-
Proof module of entry PPInvU (stage 11): `log a_s = (1+o(1)) s²` of `thm:U`, as a reduction to
the prime number theorem `ψ(x) ~ x` (an explicit hypothesis `PNTpsi`; not in Mathlib).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SUS6
public import Z3Net.SUPntDefs

@[expose] public section

/-!
# Entry PPInvU, stage 11: `log a_s = (1+o(1)) s²` given the prime number theorem

* `U_logA_psi` — unconditional, `s ≥ 6`:
  `(s-1) ψ(s-2) ≤ log a_s ≤ log (L_s (s² + 2^(s-2))) ≤ (s-1) ψ(s-2) + s log 2`
  (`log L_s = (s-1) ψ(s-2)`, `L_s ≤ a_s ≤ L_s (s² + 2^(s-2))`, `s² + 2^(s-2) ≤ 2^s`).
* `U_growth_pnt`, `U_bound_growth_pnt` — given `PNTpsi` (`ψ(x)/x → 1`, the prime number theorem,
  an external theorem not in Mathlib), `log a_s / s² → 1` and `log (L_s (s² + 2^(s-2))) / s² → 1`:
  `(s-1) ψ(s-2) / s² = (1 - 1/s)(1 - 2/s) · ψ(s-2)/(s-2) → 1`, `s log 2 / s² → 0`, and squeeze.

`PNTpsi` is a verbatim copy of the Challenge definition, in `Z3Net/SUPntDefs.lean` (stage 13b).
-/

namespace Z3NetU

namespace ProofsS11

open Filter Real

/-- The three inequalities of `U_logA_psi`. -/
theorem logA_psi (s : ℕ) (hs : 6 ≤ s) :
    ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) ≤ Real.log (aU s : ℝ) ∧
      Real.log (aU s : ℝ) ≤ Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) ∧
      Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) ≤
        ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) + s * Real.log 2 := by
  have hcs : ((s - 2 : ℕ) : ℝ) = s - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hcs1 : ((s - 1 : ℕ) : ℝ) = s - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hLL : Real.log (Lcst s : ℝ) = ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) := by
    rw [Proofs.log_Lcst, hcs1, hcs]
  have hL1 : (1 : ℝ) ≤ Lcst s := by exact_mod_cast Proofs.Lcst_pos s
  have hpos : (0 : ℝ) < (s : ℝ) ^ 2 + 2 ^ (s - 2) := by positivity
  have ha : (Lcst s : ℝ) ≤ aU s := by exact_mod_cast Proofs.U_aLower s (by omega)
  have hb : (aU s : ℝ) ≤ (Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2)) := by
    exact_mod_cast Proofs.U_aBound s (by omega)
  have hpow : (s : ℝ) ^ 2 + 2 ^ (s - 2) ≤ 2 ^ s := by
    have hn : s ^ 2 + 2 ^ (s - 2) ≤ 2 ^ s := Proofs.sq_add_pow_le s hs
    exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLL]; exact Real.log_le_log (by linarith) ha
  · exact Real.log_le_log (by linarith) hb
  · rw [Real.log_mul (by linarith) hpos.ne', hLL]
    have : Real.log ((s : ℝ) ^ 2 + 2 ^ (s - 2)) ≤ s * Real.log 2 := by
      calc Real.log ((s : ℝ) ^ 2 + 2 ^ (s - 2)) ≤ Real.log ((2 : ℝ) ^ s) :=
            Real.log_le_log hpos hpow
        _ = s * Real.log 2 := by rw [Real.log_pow]
    linarith

/-- Given `ψ(x)/x → 1`: `(s-1) ψ(s-2) / s² → 1` along `s ∈ ℕ`. -/
theorem main_term (hpnt : PNTpsi) :
    Tendsto (fun s : ℕ => ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) / (s : ℝ) ^ 2)
      atTop (nhds 1) := by
  have hsub : Tendsto (fun s : ℕ => (s : ℝ) - 2) atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_natCast_atTop_atTop
    simpa [sub_eq_add_neg] using this
  have hq : Tendsto (fun s : ℕ => Chebyshev.psi ((s : ℝ) - 2) / ((s : ℝ) - 2)) atTop (nhds 1) :=
    hpnt.comp hsub
  have h1 : Tendsto (fun s : ℕ => (1 : ℝ) - 1 / (s : ℝ)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun s : ℕ => (1 : ℝ) - 2 / (s : ℝ)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat 2)
  have hprod := (h1.mul h2).mul hq
  rw [show ((1 : ℝ) - 0) * (1 - 0) * 1 = 1 by norm_num] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with s hs
  have hs' : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have h0 : (s : ℝ) ≠ 0 := by positivity
  have h2' : (s : ℝ) - 2 ≠ 0 := by intro h; linarith
  field_simp

/-- `s log 2 / s² → 0`. -/
theorem small_term :
    Tendsto (fun s : ℕ => (s : ℝ) * Real.log 2 / (s : ℝ) ^ 2) atTop (nhds 0) := by
  refine (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with s hs
  have h1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h0 : (s : ℝ) ≠ 0 := by positivity
  field_simp

/-- Squeeze: a sequence between `(s-1) ψ(s-2)` and `(s-1) ψ(s-2) + s log 2` (eventually), divided
by `s²`, tends to `1`. -/
theorem squeeze (hpnt : PNTpsi) (f : ℕ → ℝ)
    (hf : ∀ᶠ s : ℕ in atTop, ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) ≤ f s ∧
      f s ≤ ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) + s * Real.log 2) :
    Tendsto (fun s : ℕ => f s / (s : ℝ) ^ 2) atTop (nhds 1) := by
  have hm := main_term hpnt
  have hu := hm.add small_term
  rw [add_zero] at hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hu ?_ ?_
  · filter_upwards [hf] with s hs
    exact div_le_div_of_nonneg_right hs.1 (by positivity)
  · filter_upwards [hf] with s hs
    rw [← add_div]
    exact div_le_div_of_nonneg_right hs.2 (by positivity)

end ProofsS11

/-! ## Restatements of the Challenge theorems (namespace `Z3NetU`) -/

/-- **`thm:U`, proof: `log a_s` in terms of Chebyshev's function.** For `s ≥ 6`,
`(s-1) ψ(s-2) ≤ log a_s ≤ log (L_s (s² + 2^(s-2))) ≤ (s-1) ψ(s-2) + s log 2`
(`log L_s = (s-1) ψ(s-2)`; the `O(s)` of the paper made explicit). -/
theorem U_logA_psi (s : ℕ) (hs : 6 ≤ s) :
    ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) ≤ Real.log (aU s : ℝ) ∧
      Real.log (aU s : ℝ) ≤ Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) ∧
      Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) ≤
        ((s : ℝ) - 1) * Chebyshev.psi ((s : ℝ) - 2) + s * Real.log 2 :=
  ProofsS11.logA_psi s hs

/-- **`thm:U`, `log a_s = (1+o(1)) s²`, reduction to the prime number theorem.** Given `PNTpsi`
(`ψ(x) ~ x`, not proved here), `log a_s / s² → 1`. -/
theorem U_growth_pnt (hpnt : PNTpsi) :
    Filter.Tendsto (fun s : ℕ => Real.log (aU s : ℝ) / (s : ℝ) ^ 2) Filter.atTop (nhds 1) :=
  ProofsS11.squeeze hpnt _ ((Filter.eventually_ge_atTop 6).mono fun s hs =>
    ⟨(ProofsS11.logA_psi s hs).1,
      (ProofsS11.logA_psi s hs).2.1.trans (ProofsS11.logA_psi s hs).2.2⟩)

/-- **`thm:U`, `L_s (s² + 2^(s-2)) = e^{(1+o(1)) s²}`, reduction to the prime number theorem.**
Given `PNTpsi` (`ψ(x) ~ x`, not proved here), `log (L_s (s² + 2^(s-2))) / s² → 1`. -/
theorem U_bound_growth_pnt (hpnt : PNTpsi) :
    Filter.Tendsto (fun s : ℕ => Real.log ((Lcst s : ℝ) * ((s : ℝ) ^ 2 + 2 ^ (s - 2))) / (s : ℝ) ^ 2)
      Filter.atTop (nhds 1) :=
  ProofsS11.squeeze hpnt _ ((Filter.eventually_ge_atTop 6).mono fun s hs =>
    ⟨(ProofsS11.logA_psi s hs).1.trans (ProofsS11.logA_psi s hs).2.1,
      (ProofsS11.logA_psi s hs).2.2⟩)

end Z3NetU
