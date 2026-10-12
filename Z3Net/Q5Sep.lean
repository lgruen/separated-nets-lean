/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Q5ScanR2_0
public import Z3Net.Q5ScanR2_1
public import Z3Net.Q5ScanR2_2
public import Z3Net.Q5ScanR2_3
public import Z3Net.Q5ScanR2_4
public import Z3Net.Q5ScanHk_0
public import Z3Net.Q5ScanHk_1
public import Z3Net.Q5ScanHk_2
public import Z3Net.Q5ScanTail
public import Z3Net.HalfSep
public import Z3Net.TDNorm

@[expose] public section

/-!
# V14 stage S11′: `prop:half5` (the layer `𝒬*`), assembly

* (1) `qstar_net`: the `126` integer box determinants (layer row doubled) divide `360 = 2³·3²·5`
  (`chkDetQ`, kernel `decide`), so `𝒬*_p` is a `(0,5,5)`-net for every prime `p ≥ 7` (`lem:nie`,
  `halfPhi_net_of_int`).
* (2) `qstar_sep`: `max|2β| ≤ 22`, `max|v| ≤ 24` (`abs_beta2_le`), so `lem:R2` (`R2_sep_core`) applies for `p ≥ 37`;
  `LB₂(p) > 1` for the primes `37 ≤ p < 200` by the exact scans (`Z3Net/Q5ScanR2_*.lean`) and for `p ≥ 200` by the
  monotone bound: `LB₂*(200)² > 1` (`r2s_200`) and `P² · 2b*_c(q) ≥ q² · 2b*_c(P)` for `q ≥ P` (`bR2s_mono`).
  `qstar_bounds`, `qstar_limit`: `λ(F₀*) = √5/2` (`lam_star`, a check over the `5⁵ − 1` steps), then `half_sep`,
  `half_LB2_ge` (`δN^{1/5} ≥ √5/2 − 12√5/p`, the bound `λ − √5(2A+1)/p` of the proof) and `half_upper`
  (`δN^{1/5} ≤ √5/2 + 4√5/p` for `p > 32`, `prop:Hk`(3) with `C = 3/2`).
* (3) `qstar_hk`: `prop:Hk`(1) at `k = 1` (`GF_relax_core`) for every graph form with first offset rows `F₀*`;
  `LB(p) > 1` for the primes `53 ≤ p < 200` by the exact scans (`Z3Net/Q5ScanHk_*.lean`) and for `p ≥ 200` by
  `LB*(200)² > 1` (`hks_200`) and `P · 2b*_c(q) ≥ q · 2b*_c(P)` (`bHks_mono`).
-/

namespace Z3NetHL.Proofs.Q5

open Finset Matrix Z3NetHL Z3NetHL.Proofs

set_option maxRecDepth 100000

/-! ## (1) The net -/

def okDetQ (d : Fin 5 → ℕ) : Bool :=
  decide ((detL 5 (boxMatrix (halfIntGen F2star Dstar) d)).natAbs ∣ 360)

/-- All compositions `(a, …)` of `5`, split by `a`. -/
def chkDetQ (a : ℕ) : Bool :=
  (List.range 6).all fun b => (List.range 6).all fun c => (List.range 6).all fun d =>
    (List.range 6).all fun e => decide (a + b + c + d + e ≠ 5) || okDetQ ![a, b, c, d, e]

set_option maxHeartbeats 0 in
theorem chkDetQ_all : ∀ a ∈ List.range 6, chkDetQ a = true := by
  intro a ha
  simp only [List.mem_range] at ha
  interval_cases a <;> decide +kernel

lemma detQ_dvd (d : Fin 5 → ℕ) (hd : ∑ c, d c = 5) :
    (boxMatrix (halfIntGen F2star Dstar) d).det.natAbs ∣ 360 := by
  rw [Fin.sum_univ_five] at hd
  have m : ∀ c, d c ∈ List.range 6 := fun c => by
    rw [List.mem_range]
    fin_cases c <;> simp <;> omega
  have h := chkDetQ_all (d 0) (m 0)
  simp only [chkDetQ, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [hd, ne_eq, not_true_eq_false, decide_false, Bool.false_or, okDetQ,
    decide_eq_true_eq] at h'
  have e : ![d 0, d 1, d 2, d 3, d 4] = d := by
    funext c; fin_cases c <;> rfl
  rw [e, detL_eq] at h'
  exact h'

lemma prime_dvd_360 {p : ℕ} (hp : p.Prime) (h : p ∣ 360) : p ≤ 5 := by
  have h360 : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
  rw [h360] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact (prime_dvd_pow_eq hp Nat.prime_two h).le.trans (by norm_num)
    · exact (prime_dvd_pow_eq hp Nat.prime_three h).le.trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) h

/-- **`prop:half5`(1)**: `𝒬*_p` is a digital `(0,5,5)`-net for every prime `p ≥ 7`. -/
theorem qstar_net (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) : IsNet0 5 p (5 * 1) (Qstar p) := by
  refine halfPhi_net_of_int 5 p hp (by omega) F2star Dstar fun d hd hdvd => ?_
  rw [Int.natCast_dvd] at hdvd
  have := prime_dvd_360 hp (hdvd.trans (detQ_dvd d hd))
  omega

/-! ## Bounds on `β` and `v` -/

lemma halfA2_F2star : halfA2 F2star = 11 := by decide +kernel
lemma halfA2_D1star : halfA2 D1star = 12 := by decide +kernel
lemma C2max_F2star : C2max 5 (fun _ => F2star) = 3 := by decide +kernel

lemma beta_le (E : Fin 5 → ℤ) (hE : ∀ d, |E d| ≤ 2) (c : Fin 5) : |dotR F2star E c| ≤ 22 := by
  have := abs_beta2_le F2star E hE c; rw [halfA2_F2star] at this; exact this

lemma v_le (E : Fin 5 → ℤ) (hE : ∀ d, |E d| ≤ 2) (c : Fin 5) : |dotR D1star E c| ≤ 24 := by
  have := abs_beta2_le D1star E hE c; rw [halfA2_D1star] at this; exact this

lemma row1_star (p : ℕ) : Row1Design 5 p (halfPhi 5 p F2star Dstar) D1star := by
  intro c d r hr
  simp [halfPhi, Dstar, hr]

/-! ## (2) `lem:R2` for `𝒬*` -/

lemma r2_small : ∀ p ∈ ([37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] : List ℕ), ∀ E ∈ halfSteps 5,
    (2 * (p : ℤ) ^ 2) ^ 2 < ∑ c, bR2 p F2star D1star E c ^ 2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [fun E hE => lt_of_eq_of_lt (by norm_num) (r2_37 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_41 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_43 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_47 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_53 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_59 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_61 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_67 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_71 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_73 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_79 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_83 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_89 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_97 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_101 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_103 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_107 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_109 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_113 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_127 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_131 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_137 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_139 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_149 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_151 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_157 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_163 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_167 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_173 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_179 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_181 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_191 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_193 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_197 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (r2_199 E hE)]

lemma r2_prime_list (p : ℕ) (hp : p.Prime) (h1 : 37 ≤ p) (h2 : p < 200) : p ∈ ([37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] : List ℕ) := by
  interval_cases p <;> first | decide | (exfalso; norm_num at hp)

/-- `(2p²)² < ∑_c (2b_c)²` on every step, for every prime `p ≥ 37` (exact for `p < 200`, monotone tail). -/
theorem r2_all (p : ℕ) (hp : p.Prime) (h37 : 37 ≤ p) :
    ∀ E ∈ halfSteps 5, (2 * (p : ℤ) ^ 2) ^ 2 < ∑ c, bR2 p F2star D1star E c ^ 2 := by
  by_cases h200 : p < 200
  · exact r2_small p (r2_prime_list p hp h37 h200)
  intro E hE
  set o := decide ((∑ d, E d) % 2 = 1)
  have hs := r2s_200 E hE
  have key : ∀ c, (p : ℤ) ^ 4 * bR2s 200 o (E c) (dotR F2star E c) (dotR D1star E c) ^ 2 ≤
      200 ^ 4 * bR2 p F2star D1star E c ^ 2 := by
    intro c
    have h1 := bR2s_mono 200 p (by norm_num) (by omega) o (E c) (dotR F2star E c) (dotR D1star E c)
    have h2 : bR2s p o (E c) (dotR F2star E c) (dotR D1star E c) ≤ bR2 p F2star D1star E c := by
      rw [bR2_eq]; exact bR2s_le _ _ _ _ _
    have h0 := bR2s_nonneg 200 o (E c) (dotR F2star E c) (dotR D1star E c)
    have h0' := bR2s_nonneg p o (E c) (dotR F2star E c) (dotR D1star E c)
    calc (p : ℤ) ^ 4 * bR2s 200 o (E c) (dotR F2star E c) (dotR D1star E c) ^ 2
        = ((p : ℤ) ^ 2 * bR2s 200 o (E c) (dotR F2star E c) (dotR D1star E c)) ^ 2 := by ring
      _ ≤ (((200 : ℕ) : ℤ) ^ 2 * bR2s p o (E c) (dotR F2star E c) (dotR D1star E c)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ (((200 : ℕ) : ℤ) ^ 2 * bR2 p F2star D1star E c) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h2 (by positivity)) 2
      _ = 200 ^ 4 * bR2 p F2star D1star E c ^ 2 := by push_cast; ring
  have hsum : (p : ℤ) ^ 4 * ∑ c, bR2s 200 o (E c) (dotR F2star E c) (dotR D1star E c) ^ 2 ≤
      200 ^ 4 * ∑ c, bR2 p F2star D1star E c ^ 2 := by
    rw [mul_sum, mul_sum]; exact sum_le_sum fun c _ => key c
  have hp4 : (0 : ℤ) < (p : ℤ) ^ 4 := by positivity
  have := mul_lt_mul_of_pos_left hs hp4
  nlinarith

/-- `LB₂(p) > 1` for every prime `p ≥ 37`. -/
theorem one_lt_LB2R (p : ℕ) (hp : p.Prime) (h37 : 37 ≤ p) : 1 < LB2R p F2star D1star := by
  unfold LB2R
  haveI : Nonempty (halfSteps 5) := (halfSteps_nonempty (by norm_num)).to_subtype
  obtain ⟨E0, hE0⟩ := Finite.exists_min (fun E : halfSteps 5 =>
    Real.sqrt (∑ c, ((bR2 p F2star D1star (E : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hval : 1 < Real.sqrt (∑ c, ((bR2 p F2star D1star (E0 : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2) /
      (2 * (p : ℝ) ^ 2) := by
    have h := r2_all p hp h37 E0.1 E0.2
    rw [lt_div_iff₀ (by positivity), one_mul, Real.lt_sqrt (by positivity)]
    exact_mod_cast h
  exact lt_min (by norm_num) (hval.trans_le (le_ciInf hE0))

/-- **`prop:half5`(2)**: `δ N^(1/5) > 1` (toroidal) for every prime `p ≥ 37`. -/
theorem qstar_sep (p : ℕ) (hp : p.Prime) (h37 : 37 ≤ p) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp' : (37 : ℤ) ≤ p := by exact_mod_cast h37
  have h := R2_sep_core 5 p (halfPhi 5 p F2star Dstar) F2star D1star (by norm_num) hodd
    (halfPhi_row 5 p (by norm_num) hodd F2star Dstar) (row1_star p) TD.F2star_odd
    (fun E c hE => by have := beta_le E hE c; omega) (fun E c hE => by have := v_le E hE c; omega) x y hxy
  have hN : (0 : ℝ) < ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have h1 := one_lt_LB2R p hp h37
  calc ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) < LB2R p F2star D1star * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
        nlinarith
    _ ≤ _ := h

/-! ## `λ(F₀*) = √5/2`, the bounds and the limit -/

def okLam (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  (fun o : Bool => decide (5 ≤ hLinf o e0 (fF 0 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e1 (fF 1 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e2 (fF 2 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e3 (fF 3 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e4 (fF 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkLam (e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okLam e0 e1 e2 e3 e4

set_option maxHeartbeats 0 in
theorem chkLam_all : ∀ e0 ∈ vals5, chkLam e0 = true :=
  forall_vals5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `λ(F₀*) = min(√5/2, √2)` (`= √5/2`; `|ℓ(E)|² ≥ 5/4` on all steps). -/
theorem lam_star : halfLam F2star = min (Real.sqrt 5 / 2) (Real.sqrt 2) := by
  refine le_antisymm (by exact_mod_cast half_lam_le 5 (by norm_num) F2star) ?_
  haveI : Nonempty (halfSteps 5) := (halfSteps_nonempty (by norm_num)).to_subtype
  refine le_ciInf fun E => (min_le_left _ _).trans ?_
  have hE := E.2
  have m := vals5_of E.1 hE
  have h := chkLam_all (E.1 0) (m 0)
  simp only [chkLam, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okLam, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact absurd h' (ne_zero5 E.1 (halfSteps_mem hE).1)
  · have hc : ((5 : ℕ) : ℤ) ≤ ∑ c, hLinf (oddB E.1) (E.1 c) (∑ d, F2star c d * E.1 d) ^ 2 := by
      have e : ∀ c, (∑ d, F2star c d * E.1 d) = dotR F2star E.1 c := fun c => rfl
      simp only [Fin.sum_univ_five, e, dotF, oddB, odd5]
      exact_mod_cast h'
    have := le_sqrt_inf_of_cert F2star E.1 5 hc
    exact_mod_cast this

lemma min_star : min (Real.sqrt 5 / 2) (Real.sqrt 2) = Real.sqrt 5 / 2 := by
  refine min_eq_left ?_
  rw [div_le_iff₀ (by norm_num), show Real.sqrt 2 * 2 = Real.sqrt 8 by
    rw [show (8 : ℝ) = 2 * 2 ^ 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **`prop:half5`(2), the limit, explicit**: for every prime `p > 32`,
`√5/2 − 12√5/p ≤ δN^{1/5}` (toroidal) and `δN^{1/5} ≤ √5/2 + 4√5/p` (Euclidean, hence toroidal). -/
theorem qstar_bounds (p : ℕ) (hp : p.Prime) (h32 : 32 < p) :
    (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
      (Real.sqrt 5 / 2 - 12 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
        ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
            (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
      Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
        ≤ (Real.sqrt 5 / 2 + 4 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hrow := halfPhi_row 5 p (by norm_num) hodd F2star Dstar
  have hN : (0 : ℝ) ≤ ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by positivity
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have h := half_sep 5 p (by norm_num) hp (by omega) F2star TD.F2star_odd
      (by rw [halfA2_F2star]; omega) _ hrow x y hxy
    have hge := half_LB2_ge 5 p (by norm_num) hp.pos F2star
    rw [lam_star, min_star, halfA2_F2star] at hge
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hN) h
    have : Real.sqrt (5 : ℕ) * (((11 : ℕ) : ℝ) + 1) / p = 12 * Real.sqrt 5 / p := by push_cast; ring
    rw [this] at hge; exact hge
  · obtain ⟨x, y, hxy, h⟩ := half_upper 5 p (by norm_num) hp F2star TD.F2star_odd
      (by rw [C2max_F2star]; omega) _ hrow
    refine ⟨x, y, hxy, h.trans (le_of_eq ?_)⟩
    rw [C2max_F2star]; push_cast; rw [min_star]; ring

/-- **`prop:half5`(2), the limit**: `δN^{1/5} → √5/2` as `p → ∞` (toroidal lower bound, Euclidean upper bound). -/
theorem qstar_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
        (Real.sqrt 5 / 2 - ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
              (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
      ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
        Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
          ≤ (Real.sqrt 5 / 2 + ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
  obtain ⟨P, hP⟩ := half_limit 5 (by norm_num) F2star TD.F2star_odd (by exact_mod_cast lam_star) ε hε
  refine ⟨max P 3, fun p hp hPp => ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h := hP p hp (le_of_max_le_left hPp) _ (halfPhi_row 5 p (by norm_num) hodd F2star Dstar)
  rw [show ((5 : ℕ) : ℝ) = 5 by norm_num, min_star] at h
  exact h

/-! ## (3) `prop:Hk`(1) for `F₀*` -/

/-- `LB(p)` of `prop:Hk`(1) at `k = 1` for `F₀*`. -/
noncomputable def LBHk (p : ℕ) : ℝ :=
  min 2 (⨅ E : halfSteps 5,
    Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2star) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p))

lemma hk_small : ∀ p ∈ ([53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] : List ℕ), ∀ E ∈ halfSteps 5,
    (2 * (p : ℤ)) ^ 2 < ∑ c, bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [fun E hE => lt_of_eq_of_lt (by norm_num) (hk_53 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_59 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_61 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_67 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_71 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_73 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_79 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_83 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_89 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_97 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_101 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_103 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_107 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_109 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_113 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_127 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_131 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_137 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_139 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_149 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_151 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_157 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_163 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_167 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_173 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_179 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_181 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_191 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_193 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_197 E hE),
      fun E hE => lt_of_eq_of_lt (by norm_num) (hk_199 E hE)]

lemma hk_prime_list (p : ℕ) (hp : p.Prime) (h1 : 53 ≤ p) (h2 : p < 200) : p ∈ ([53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] : List ℕ) := by
  interval_cases p <;> first | decide | (exfalso; norm_num at hp)

theorem hk_all (p : ℕ) (hp : p.Prime) (h53 : 53 ≤ p) :
    ∀ E ∈ halfSteps 5, (2 * (p : ℤ)) ^ 2 < ∑ c, bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by
  by_cases h200 : p < 200
  · exact hk_small p (hk_prime_list p hp h53 h200)
  intro E hE
  set o := decide ((∑ d, E d) % 2 = 1)
  have hs := hks_200 E hE
  have key : ∀ c, (p : ℤ) ^ 2 * bHks 200 o (E c) (dotR F2star E c) ^ 2 ≤
      200 ^ 2 * bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by
    intro c
    have h1 := bHks_mono 200 p (by omega) o (E c) (dotR F2star E c)
    have h2 : bHks p o (E c) (dotR F2star E c) ≤ bOpt2 p (fun _ => F2star) E (fun _ => 0) c := by
      rw [bOpt2_eq]; exact bHks_le _ _ _ _
    have h0 := bHks_nonneg 200 o (E c) (dotR F2star E c)
    have h0' := bHks_nonneg p o (E c) (dotR F2star E c)
    calc (p : ℤ) ^ 2 * bHks 200 o (E c) (dotR F2star E c) ^ 2
        = ((p : ℤ) * bHks 200 o (E c) (dotR F2star E c)) ^ 2 := by ring
      _ ≤ (((200 : ℕ) : ℤ) * bHks p o (E c) (dotR F2star E c)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ (((200 : ℕ) : ℤ) * bOpt2 p (fun _ => F2star) E (fun _ => 0) c) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h2 (by positivity)) 2
      _ = 200 ^ 2 * bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by push_cast; ring
  have hsum : (p : ℤ) ^ 2 * ∑ c, bHks 200 o (E c) (dotR F2star E c) ^ 2 ≤
      200 ^ 2 * ∑ c, bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by
    rw [mul_sum, mul_sum]; exact sum_le_sum fun c _ => key c
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
  have := mul_lt_mul_of_pos_left hs hp2
  nlinarith

theorem one_lt_LBHk (p : ℕ) (hp : p.Prime) (h53 : 53 ≤ p) : 1 < LBHk p := by
  unfold LBHk
  haveI : Nonempty (halfSteps 5) := (halfSteps_nonempty (by norm_num)).to_subtype
  obtain ⟨E0, hE0⟩ := Finite.exists_min (fun E : halfSteps 5 =>
    Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2star) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hval : 1 < Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2star) (E0 : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) /
      (2 * p) := by
    have h := hk_all p hp h53 E0.1 E0.2
    rw [lt_div_iff₀ (by positivity), one_mul, Real.lt_sqrt (by positivity)]
    exact_mod_cast h
  exact lt_min (by norm_num) (hval.trans_le (le_ciInf hE0))

/-- **`prop:half5`(3)**: for every prime `p ≥ 53`, every graph form over `𝔽_p` with depths `(1, …, 1)` and first
offset rows `F₀*` (deeper rows arbitrary) has `δ N^(1/5) > 1` (toroidal). -/
theorem qstar_hk (p : ℕ) (hp : p.Prime) (h53 : 53 ≤ p)
    (Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 5 p 1 Φ (fun _ => F2star)) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((GFpoint 5 p 1 Φ x c : ℤ) - (GFpoint 5 p 1 Φ y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp' : (53 : ℤ) ≤ p := by exact_mod_cast h53
  have hJ : ∀ J : Fin 5 → ℕ, (∀ d, J d < min 1 (5 - 1)) → J = fun _ => 0 := fun J hJ =>
    funext fun d => by have := hJ d; omega
  have h := GF_relax_core 5 p 1 Φ (fun _ => F2star) (by norm_num) hodd le_rfl hrow
    (fun c d => TD.F2star_odd c d) (fun x c d h1 h2 => by omega)
    (fun E J c hE hJ' => by
      rw [hJ J hJ', sig2_k1]; have := beta_le E hE c; omega)
    (LBHk p) (fun E J hE hne hJ' => by
      rw [hJ J hJ']
      have hmem : E ∈ halfSteps 5 := mem_halfSteps.mpr ⟨hE, fun h0 => by
        obtain ⟨d, hd⟩ := hne; exact hd (by rw [h0]; rfl)⟩
      refine min_le_min_left 2 ?_
      exact ciInf_le (f := fun E : halfSteps 5 =>
        Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2star) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p))
        ⟨0, fun _ ⟨_, h⟩ => h ▸ by positivity⟩ ⟨E, hmem⟩) x y hxy
  have hN : (0 : ℝ) < ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have h1 := one_lt_LBHk p hp h53
  calc ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) < LBHk p * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
        nlinarith
    _ ≤ _ := h

end Z3NetHL.Proofs.Q5
