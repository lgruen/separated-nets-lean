/-
`rem:accounting` (first-order accounting): assembly, of the manuscript *Low-discrepancy quasi-uniform digital nets in
every dimension* (`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.AcctCert

@[expose] public section

/-!
# V14 stage S13′: `rem:accounting`, assembly

`acct_upper_core` (`Z3Net/AcctUp.lean`) and `acct_lower_core` (`Z3Net/AcctLow.lean`) give
`(√5/2)(1 − 2dj/(5p)) − C/p² ≤ δN^{1/5} ≤ (√5/2)(1 − 2dr/(5p)) + C/p²`; here they are turned into the bounds for
`K_eff(p) = (5p/2)(1 − δN^{1/5}/(√5/2))` (`acct_main_core`, `acct_liminf_core`), the exact expansion when
`dj = dr` (`acct_exact_core`) and the instance `𝒬*_p` (`acct_qstar_core`).
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs Filter

noncomputable section

lemma sepN_spec_core (p : ℕ) (hp : 2 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) :
    (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y → sepN p X ≤ (p : ℝ) * Real.sqrt (∑ c,
      ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧ sepN p X = (p : ℝ) * Real.sqrt (∑ c,
      ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2) :=
  ⟨fun x y h => sepN_le p X x y h, sepN_attained p hp X⟩

lemma ell2_eq_halfEllInf_core (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    (ell2 F2 E c : ℝ) = 2 * halfEllInf F2 E c := by
  rw [halfEllInf_eq, ell2_eq]; unfold dotR; ring

/-- `K_eff` in terms of `δN^{1/5}`: with `a = √5/2`, `K_eff = (5p/2)(1 − δ/a)`; a lower bound
`δ ≥ a(1 − K/(5p)) − C/p²` gives `K_eff ≤ K/2 + 5C/(2ap)`, an upper bound `δ ≤ a(1 − K/(5p)) + C/p²` gives
`K_eff ≥ K/2 − 5C/(2ap)`. -/
lemma keff_le (p : ℕ) (hp : 1 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (K C : ℝ)
    (h : Real.sqrt 5 / 2 * (1 - K / (5 * p)) - C / (p : ℝ) ^ 2 ≤ sepN p X) :
    Keff p X ≤ K / 2 + 5 * C / (2 * (Real.sqrt 5 / 2) * p) := by
  have ha1 := one_le_a
  have ha0 : 0 < Real.sqrt 5 / 2 := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold Keff
  have e : 5 * (p : ℝ) / 2 * (1 - sepN p X / (Real.sqrt 5 / 2)) =
      5 * (p : ℝ) / 2 - 5 * p / (2 * (Real.sqrt 5 / 2)) * sepN p X := by field_simp
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 5 * p / (2 * (Real.sqrt 5 / 2)))
  have e2 : 5 * (p : ℝ) / (2 * (Real.sqrt 5 / 2)) * (Real.sqrt 5 / 2 * (1 - K / (5 * p)) - C / (p : ℝ) ^ 2) =
      5 * (p : ℝ) / 2 - K / 2 - 5 * C / (2 * (Real.sqrt 5 / 2) * p) := by field_simp; try ring
  rw [e2] at h2
  linarith

lemma le_keff (p : ℕ) (hp : 1 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (K C : ℝ)
    (h : sepN p X ≤ Real.sqrt 5 / 2 * (1 - K / (5 * p)) + C / (p : ℝ) ^ 2) :
    K / 2 - 5 * C / (2 * (Real.sqrt 5 / 2) * p) ≤ Keff p X := by
  have ha1 := one_le_a
  have ha0 : 0 < Real.sqrt 5 / 2 := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold Keff
  have e : 5 * (p : ℝ) / 2 * (1 - sepN p X / (Real.sqrt 5 / 2)) =
      5 * (p : ℝ) / 2 - 5 * p / (2 * (Real.sqrt 5 / 2)) * sepN p X := by field_simp
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 5 * p / (2 * (Real.sqrt 5 / 2)))
  have e2 : 5 * (p : ℝ) / (2 * (Real.sqrt 5 / 2)) * (Real.sqrt 5 / 2 * (1 - K / (5 * p)) + C / (p : ℝ) ^ 2) =
      5 * (p : ℝ) / 2 - K / 2 + 5 * C / (2 * (Real.sqrt 5 / 2) * p) := by field_simp; try ring
  rw [e2] at h2
  linarith

/-- `5|C|/(2ap) ≤ ε` for `p ≥ ⌈5|C|/ε⌉ + 1`. -/
lemma small_of_large (C ε : ℝ) (hε : 0 < ε) (p : ℕ) (hp : ⌈5 * |C| / ε⌉₊ + 1 ≤ p) :
    5 * |C| / (2 * (Real.sqrt 5 / 2) * p) ≤ ε := by
  have ha1 := one_le_a
  have hp0 : (0 : ℝ) < p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    linarith
  have h1 : 5 * |C| / ε ≤ p := by
    have := Nat.le_ceil (5 * |C| / ε)
    have : ((⌈5 * |C| / ε⌉₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast (show ⌈5 * |C| / ε⌉₊ ≤ p by omega)
    linarith
  rw [div_le_iff₀ hε] at h1
  rw [div_le_iff₀ (by positivity)]
  have : 0 ≤ ε * p := by positivity
  nlinarith

theorem acct_main_core (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      (drift2 F2 : ℝ) / 2 - ε ≤ Keff p (halfNet p F2 D) ∧
        Keff p (halfNet p F2 D) ≤ (dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 + ε := by
  obtain ⟨C1, P1, h1⟩ := acct_upper_core F2 D hodd hΛ
  obtain ⟨C2, P2, h2⟩ := acct_lower_core F2 D hodd hdet
  refine ⟨P1 + P2 + ⌈5 * |C1| / ε⌉₊ + ⌈5 * |C2| / ε⌉₊ + 1, fun p hp hPp => ⟨?_, ?_⟩⟩
  · have := le_keff p hp.one_lt.le _ _ _ (h2 p hp (by omega))
    have hs := small_of_large C2 ε hε p (by omega)
    have : 5 * C2 / (2 * (Real.sqrt 5 / 2) * p) ≤ 5 * |C2| / (2 * (Real.sqrt 5 / 2) * p) := by
      have ha1 := one_le_a
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      apply div_le_div_of_nonneg_right (by linarith [le_abs_self C2]) (by positivity)
    linarith
  · have := keff_le p hp.one_lt.le _ _ _ (h1 p hp (by omega))
    have hs := small_of_large C1 ε hε p (by omega)
    have : 5 * C1 / (2 * (Real.sqrt 5 / 2) * p) ≤ 5 * |C1| / (2 * (Real.sqrt 5 / 2) * p) := by
      have ha1 := one_le_a
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      apply div_le_div_of_nonneg_right (by linarith [le_abs_self C1]) (by positivity)
    linarith

theorem acct_exact_core (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) (heq : dj2 F2 (fun c d => D c 1 d) = drift2 F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      |sepN p (halfNet p F2 D) - Real.sqrt 5 / 2 * (1 - (drift2 F2 : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  obtain ⟨C1, P1, h1⟩ := acct_upper_core F2 D hodd hΛ
  obtain ⟨C2, P2, h2⟩ := acct_lower_core F2 D hodd hdet
  refine ⟨max C1 C2, P1 + P2, fun p hp hPp => ?_⟩
  have u := h1 p hp (by omega)
  have l := h2 p hp (by omega)
  rw [heq] at u
  have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp0 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have m1 : C1 / (p : ℝ) ^ 2 ≤ max C1 C2 / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right (le_max_left _ _) hp0.le
  have m2 : C2 / (p : ℝ) ^ 2 ≤ max C1 C2 / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right (le_max_right _ _) hp0.le
  rw [abs_le]; constructor <;> linarith

/-! ## The `liminf`/`limsup` form -/

/-- The filter "`p → ∞` along the primes". -/
abbrev primesAtTop : Filter ℕ := atTop ⊓ 𝓟 {p | p.Prime}

instance primesAtTop_neBot : primesAtTop.NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hU
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes N
  exact ⟨q, hN q hq, hqp⟩

lemma eventually_primes (P : ℕ) (Q : ℕ → Prop) (h : ∀ p, p.Prime → P ≤ p → Q p) : ∀ᶠ p in primesAtTop, Q p := by
  rw [Filter.Eventually, Filter.mem_inf_principal]
  filter_upwards [Filter.eventually_ge_atTop P] with p hp hpr using h p hpr hp

theorem acct_liminf_core (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) :
    (drift2 F2 : ℝ) / 2 ≤ Filter.liminf (fun p => Keff p (halfNet p F2 D)) (atTop ⊓ 𝓟 {p | p.Prime}) ∧
      Filter.liminf (fun p => Keff p (halfNet p F2 D)) (atTop ⊓ 𝓟 {p | p.Prime}) ≤
        Filter.limsup (fun p => Keff p (halfNet p F2 D)) (atTop ⊓ 𝓟 {p | p.Prime}) ∧
      Filter.limsup (fun p => Keff p (halfNet p F2 D)) (atTop ⊓ 𝓟 {p | p.Prime}) ≤
        (dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 := by
  set f : ℕ → ℝ := fun p => Keff p (halfNet p F2 D) with hf
  have hb : ∀ ε > 0, ∀ᶠ p in primesAtTop, (drift2 F2 : ℝ) / 2 - ε ≤ f p ∧
      f p ≤ (dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 + ε := fun ε hε => by
    obtain ⟨P, hP⟩ := acct_main_core F2 D hodd hdet hΛ ε hε
    exact eventually_primes P _ hP
  have hb1 := hb 1 one_pos
  have hbdd : IsBoundedUnder (· ≤ ·) primesAtTop f :=
    ⟨(dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 + 1, Filter.eventually_map.mpr (hb1.mono fun p h => h.2)⟩
  have hbdd' : IsBoundedUnder (· ≥ ·) primesAtTop f :=
    ⟨(drift2 F2 : ℝ) / 2 - 1, Filter.eventually_map.mpr (hb1.mono fun p h => h.1)⟩
  refine ⟨?_, Filter.liminf_le_limsup hbdd hbdd', ?_⟩
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have := Filter.le_liminf_of_le hbdd.isCoboundedUnder_ge ((hb ε hε).mono fun p h => h.1)
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact Filter.limsup_le_of_le hbdd'.isCoboundedUnder_le ((hb ε hε).mono fun p h => h.2)

/-! ## `𝒬*_p` -/

lemma D1_of_Dstar : (fun c d => Dstar c 1 d) = D1star := by
  funext c d; simp [Dstar]

theorem acct_qstar_core : drift2 F2star = 17 ∧ dj2 F2star D1star = 17 ∧ (Matrix.of F2star).det = -880 ∧
    (∀ E ∈ halfSteps 5, E ∉ bind5 → 8 ≤ ∑ c, ell2 F2star E c ^ 2) ∧ LamHyp F2star ∧
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      |sepN p (Qstar p) - Real.sqrt 5 / 2 * (1 - 17 / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  have hΛ : LamHyp F2star := fun E hE hnb => by have := lam_star8 E hE hnb; omega
  refine ⟨TD.F2star_drift, dj2_star, det_star, lam_star8, hΛ, ?_⟩
  obtain ⟨C, P, h⟩ := acct_exact_core F2star Dstar TD.F2star_odd (by rw [det_star]; norm_num) hΛ
    (by rw [D1_of_Dstar, dj2_star, TD.F2star_drift])
  refine ⟨C, P, fun p hp hPp => ?_⟩
  have := h p hp hPp
  rw [TD.F2star_drift] at this
  push_cast at this
  exact this

theorem acct_counterexample_core : (∀ c d, Odd (F2cex c d)) ∧ B2D F2cex ∧ DisjMinors F2cex ∧
    (Matrix.of F2cex).det = 560 ∧ ![1, -1, -2, -1, -1] ∈ halfSteps 5 ∧ ![1, -1, -2, -1, -1] ∉ bind5 ∧
    (fun c => dotR F2cex ![1, -1, -2, -1, -1] c) = ![4, -6, -2, -2, -2] ∧
    ∑ c, ell2 F2cex ![1, -1, -2, -1, -1] c ^ 2 = 4 ∧ ¬ LamHyp F2cex :=
  ⟨F2cex_odd, F2cex_B2, F2cex_disj, det_cex, cex_step.1, cex_step.2.1, cex_step.2.2.1, cex_step.2.2.2,
    cex_not_lam⟩

end

end Z3NetHL.Proofs.Acct
