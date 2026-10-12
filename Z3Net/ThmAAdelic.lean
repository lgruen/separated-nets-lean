/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmALat

@[expose] public section

/-!
# Theorem A, part 4: the adelic Chebyshev identity (`lem:adelic`) and Babai rounding (`lem:babai`)

V14 stage S4.

* The place `∞`: for any flag, `A_{j,∞} = ‖u‖/γ_j` with `u` the Gram–Schmidt vector
  (`Ainf_isLeast`); `θ = γ_j u/‖u‖²` (`adelic_inf_core`).
* The places `p`: `A_{j,p} = p^{v_p(γ_j)}` for every prime `p` (`Ap_isLeast`), and
  `γ_j = ∏_{p ∈ S} A_{j,p}` (`sunit_primes`, `adelic_gamma_core`).
* `h_j = ‖u‖` for every flag (`hS_eq`); `π_j(Λ_j) = ℤ u` (`adelic_proj_core`); `‖E‖ ≥ h_j` off
  `V_{j-1}` (`adelic_norm_core`).
* `lem:babai` (`babai_core`, `babai_growth_core`, `babai_flag_core`) and the design `U*_s`
  (`Ustar_proj_core`, `Ustar_babai_core`, `Ustar_growth_core`, `aStar_le_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

lemma natDeg_le_of_deg_lt {R : Type*} [Semiring R] (g : Polynomial R) (j : ℕ)
    (h : g.degree < ((j + 1 : ℕ) : WithBot ℕ)) : g.natDegree ≤ j := by
  by_cases h0 : g = 0
  · simp [h0]
  · have := (natDegree_lt_iff_degree_lt h0).2 h; omega

lemma flag_Ecol (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) : Flag d (Ecol d) j :=
  fun i hi => Ecol_spec hs d i (by omega)

/-! ## The place `∞` -/

lemma monic_of_u (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) :
    ∃ g : Polynomial ℝ, g.Monic ∧ g.natDegree = j ∧
      polyVecR d g = (gamS d j : ℝ)⁻¹ • uvec d B j := by
  have hu := uvec_mem hs d B j hj hB
  obtain ⟨g₀, hg₀, he⟩ := (mem_Vlt d (j + 1) _).1 hu.1
  have hnd : g₀.natDegree ≤ j := natDeg_le_of_deg_lt g₀ j hg₀
  have hγ := gam_pos hs d j hj
  have hco : g₀.coeff j = gamS d j := by
    have h1 := inner_u_poly hs d B j hj hB g₀ hnd
    rw [← he, real_inner_self_eq_norm_sq] at h1
    have hn : ‖uvec d B j‖ ^ 2 ≠ 0 := by
      have := norm_pos_iff.2 (uvec_ne_zero hs d B j hj hB); positivity
    have h2 : g₀.coeff j / gamS d j = 1 := by
      have := mul_right_cancel₀ hn (h1.symm.trans (one_mul _).symm); exact this
    field_simp at h2; linarith
  have hc1 : ((gamS d j : ℝ)⁻¹ • g₀).coeff j = 1 := by
    rw [coeff_smul, hco, smul_eq_mul, inv_mul_cancel₀ hγ.ne']
  have hnd' : ((gamS d j : ℝ)⁻¹ • g₀).natDegree = j :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_smul_le _ _).trans hnd) (by rw [hc1]; simp)
  refine ⟨(gamS d j : ℝ)⁻¹ • g₀, ?_, hnd', ?_⟩
  · rw [Monic, leadingCoeff, hnd', hc1]
  · rw [polyVecR_smul, ← he]

/-- `A_{j,∞} = ‖u‖ / γ_j`, attained (for the Gram–Schmidt vector `u` of any flag). -/
lemma Ainf_isLeast (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) : IsLeast (AinfSet d j) (‖uvec d B j‖ / gamS d j) := by
  have hγ := gam_pos hs d j hj
  have hu := norm_pos_iff.2 (uvec_ne_zero hs d B j hj hB)
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hm, hd, he⟩ := monic_of_u hs d B j hj hB
    refine ⟨g, hm, hd, ?_⟩
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hγ), div_eq_inv_mul]
  · rintro r ⟨g, hm, hd, rfl⟩
    have h1 := inner_u_poly hs d B j hj hB g hd.le
    have hc : g.coeff j = 1 := by rw [← hd]; exact hm.coeff_natDegree
    rw [hc] at h1
    have h2 := real_inner_le_norm (uvec d B j) (polyVecR d g)
    rw [h1] at h2
    have h3 : ‖uvec d B j‖ * (‖uvec d B j‖ / gamS d j) ≤ ‖uvec d B j‖ * ‖polyVecR d g‖ := by
      calc _ = 1 / gamS d j * ‖uvec d B j‖ ^ 2 := by ring
        _ ≤ _ := h2
    exact le_of_mul_le_mul_left h3 hu

lemma Ainf_eq (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) : Ainf d j = ‖uvec d B j‖ / gamS d j :=
  (Ainf_isLeast hs d B j hj hB).csInf_eq

/-! ## The places `p` -/

lemma den_not_dvd (p : ℕ) [hp : Fact p.Prime] (x : ℚ) (hx : padicNorm p x ≤ 1) :
    ¬ p ∣ x.den := by
  intro hd
  have h1 : padicNorm p (x.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).2 hd
  have hnum : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have h2 : padicNorm p (x.num : ℚ) < 1 := by
    rw [hnum, padicNorm.mul]
    calc _ ≤ 1 * padicNorm p x.den := mul_le_mul_of_nonneg_right hx (padicNorm.nonneg _)
      _ < 1 := by rw [one_mul]; exact h1
  have h3 := (padicNorm.int_lt_one_iff _).1 h2
  have h4 : p ∣ x.num.natAbs := Int.natCast_dvd.1 h3
  exact (Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp.out, h4, hd⟩) x.reduced

/-- Clearing the denominators of a `p`-integral vector by an integer prime to `p`. -/
lemma clear_den (p : ℕ) [hp : Fact p.Prime] (x : Fin s → ℚ) (hx : ∀ c, padicNorm p (x c) ≤ 1) :
    ∃ D : ℕ, 0 < D ∧ ¬ p ∣ D ∧ ∃ F : Fin s → ℤ, ∀ c, (F c : ℚ) = D * x c := by
  refine ⟨∏ c, (x c).den, prod_pos fun c _ => (x c).den_pos, ?_, ?_⟩
  · intro h
    obtain ⟨c, _, hc⟩ := (Prime.dvd_finsetProd_iff hp.out.prime _).1 h
    exact den_not_dvd p (x c) (hx c) hc
  · have hint : ∀ c, ∃ z : ℤ, (z : ℚ) = ((∏ c, (x c).den : ℕ) : ℚ) * x c := by
      intro c
      obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun c => (x c).den) (mem_univ c)
      refine ⟨(m : ℤ) * (x c).num, ?_⟩
      rw [hm]
      have h2 : ((x c).den : ℚ) ≠ 0 := by exact_mod_cast (x c).den_pos.ne'
      have h3 : ((x c).num : ℚ) = x c * (x c).den := (Rat.mul_den_eq_num _).symm
      push_cast
      rw [h3]; ring
    choose F hF using hint
    exact ⟨F, hF⟩

lemma padicNorm_pos (p : ℕ) [Fact p.Prime] {a : ℚ} (ha : a ≠ 0) : 0 < padicNorm p a :=
  lt_of_le_of_ne (padicNorm.nonneg a) (padicNorm.nonzero ha).symm

lemma padic_gam_pos (hs : 3 ≤ s) (p : ℕ) [Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < padicNorm p (gamS d j) :=
  padicNorm_pos p (gamS_spec hs d j hj).1.ne'

lemma iSup_le_bound (f : Fin s → ℚ) (b : ℚ) (h : ∀ c, f c ≤ b) : (⨆ c, (f c : ℝ)) ≤ b := by
  have : Nonempty (Fin s) := ⟨0⟩
  exact ciSup_le fun c => by exact_mod_cast h c

lemma le_iSup_val (f : Fin s → ℚ) (c : Fin s) : (f c : ℝ) ≤ ⨆ c, (f c : ℝ) :=
  le_ciSup (f := fun c => (f c : ℝ)) (Set.finite_range _).bddAbove c

/-- The lower bound at `p`: every monic `g` of degree `j` has `max_c |w_c g(y_c)|_p ≥ |γ_j|_p⁻¹`. -/
lemma Ap_lower (hs : 3 ≤ s) (p : ℕ) [hp : Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (g : Polynomial ℚ) (hg : g.Monic) (hgd : g.natDegree = j) :
    (((padicNorm p (gamS d j))⁻¹ : ℚ) : ℝ) ≤ ⨆ c, ((padicNorm p (polyVecQ d g c) : ℚ) : ℝ) := by
  set E := polyVecQ d g
  have hE0 : E d = 0 := by simp [E, polyVecQ]
  have hrep : ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d) := by
    intro c hc; simp [E, polyVecQ, hc]
  have hex : ∃ c, E c ≠ 0 := by
    by_contra h
    push Not at h
    have hz : E = 0 := funext h
    have := colPoly_eq' hs d E g hj hgd.le hrep
    rw [hz, colPoly_zero] at this
    exact hg.ne_zero this
  obtain ⟨c₁, hc₁⟩ := hex
  obtain ⟨c₀, -, hmax⟩ := exists_max_image univ (fun c => padicNorm p (E c)) univ_nonempty
  have hpos : 0 < padicNorm p (E c₀) :=
    lt_of_lt_of_le (padicNorm_pos p hc₁) (hmax c₁ (mem_univ _))
  have hE0' : E c₀ ≠ 0 := fun h => by rw [h, padicNorm.zero] at hpos; exact lt_irrefl _ hpos
  set x : Fin s → ℚ := fun c => E c / E c₀
  have hx : ∀ c, padicNorm p (x c) ≤ 1 := by
    intro c
    simp only [x, padicNorm.div]
    exact div_le_one_of_le₀ (hmax c (mem_univ _)) (padicNorm.nonneg _)
  obtain ⟨D, hD, hpD, F, hF⟩ := clear_den p x hx
  have hdeg : (C ((D : ℚ) / E c₀) * g).natDegree ≤ j := (natDegree_C_mul_le _ _).trans hgd.le
  have hrepF : ∀ c, c ≠ d → (F c : ℚ) = wQ c d * (C ((D : ℚ) / E c₀) * g).eval (yQ c d) := by
    intro c hc
    rw [hF c, eval_mul, eval_C]; simp only [x, hrep c hc]; field_simp
  have hFl : InLam d j F := by
    refine ⟨?_, _, hdeg, hrepF⟩
    have := hF d; simp only [x, hE0, zero_div, mul_zero] at this; exact_mod_cast this
  have hk : kappa d j F = (D : ℚ) / E c₀ := by
    rw [kappa_eq hs hj F _ hdeg hrepF, coeff_C_mul, ← hgd, hg.coeff_natDegree, mul_one]
  obtain ⟨z, hz⟩ := kappa_mem hs hj hFl
  rw [hk] at hz
  have hD1 : padicNorm p (D : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).2 hpD
  have h1 : padicNorm p ((D : ℚ) / E c₀) = (padicNorm p (E c₀))⁻¹ := by
    rw [padicNorm.div, hD1, one_div]
  have h2 : padicNorm p ((z : ℚ) * gamS d j) ≤ padicNorm p (gamS d j) := by
    rw [padicNorm.mul]; exact mul_le_of_le_one_left (padicNorm.nonneg _) (padicNorm.of_int z)
  rw [hz] at h1
  have h3 : (padicNorm p (E c₀))⁻¹ ≤ padicNorm p (gamS d j) := h1 ▸ h2
  have h4 : (padicNorm p (gamS d j))⁻¹ ≤ padicNorm p (E c₀) := by
    rwa [inv_le_comm₀ hpos (padic_gam_pos hs p d j hj)] at h3
  calc (((padicNorm p (gamS d j))⁻¹ : ℚ) : ℝ) ≤ ((padicNorm p (E c₀) : ℚ) : ℝ) := by
        exact_mod_cast h4
    _ ≤ _ := le_iSup_val (fun c => padicNorm p (E c)) c₀

/-- The minimum at `p` is attained at `E_{d,j}/γ_j`. -/
lemma Ap_attain (hs : 3 ≤ s) (p : ℕ) [hp : Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ g : Polynomial ℚ, g.Monic ∧ g.natDegree = j ∧
      (⨆ c, ((padicNorm p (polyVecQ d g c) : ℚ) : ℝ)) ≤ (((padicNorm p (gamS d j))⁻¹ : ℚ) : ℝ) := by
  obtain ⟨hl, hk⟩ := Ecol_spec hs d j hj
  set G := colPoly d fun c => (Ecol d j c : ℚ)
  have hγ := (gamS_spec hs d j hj).1
  have hGd : G.natDegree ≤ j := ((inLam_iff hs hj _).1 hl).2
  have hGc : G.coeff j = gamS d j := hk
  have hc1 : (C (gamS d j)⁻¹ * G).coeff j = 1 := by
    rw [coeff_C_mul, hGc, inv_mul_cancel₀ hγ.ne']
  have hnd : (C (gamS d j)⁻¹ * G).natDegree = j :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_C_mul_le _ _).trans hGd) (by rw [hc1]; simp)
  refine ⟨C (gamS d j)⁻¹ * G, by rw [Monic, leadingCoeff, hnd, hc1], hnd, ?_⟩
  refine iSup_le_bound _ _ fun c => ?_
  have hv : polyVecQ d (C (gamS d j)⁻¹ * G) c = (Ecol d j c : ℚ) / gamS d j := by
    simp only [polyVecQ]
    split_ifs with h
    · rw [h, hl.1]; simp
    · rw [colPoly_rep (by omega) d (fun c => (Ecol d j c : ℚ)) c h, eval_mul, eval_C]
      simp only [G]; field_simp
  rw [hv, padicNorm.div, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.2 (padicNorm.nonneg _)) (padicNorm.of_int _)

lemma Ap_isLeast' (hs : 3 ≤ s) (p : ℕ) [hp : Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    IsLeast (ApSet p d j) (((padicNorm p (gamS d j))⁻¹ : ℚ) : ℝ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hm, hd, hle⟩ := Ap_attain hs p d j hj
    exact ⟨g, hm, hd, le_antisymm (Ap_lower hs p d j hj g hm hd) hle⟩
  · rintro r ⟨g, hm, hd, rfl⟩
    exact Ap_lower hs p d j hj g hm hd

lemma padicNorm_inv_eq (p : ℕ) [Fact p.Prime] (a : ℚ) (ha : a ≠ 0) :
    (((padicNorm p a)⁻¹ : ℚ) : ℝ) = (p : ℝ) ^ padicValRat p a := by
  rw [padicNorm.eq_zpow_of_nonzero ha, zpow_neg, inv_inv]
  push_cast; rfl

/-- `A_{j,p} = p^{v_p(γ_j)}`, attained, for every prime `p`. -/
lemma Ap_isLeast (hs : 3 ≤ s) (p : ℕ) [hp : Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    IsLeast (ApSet p d j) ((p : ℝ) ^ padicValRat p (gamS d j)) := by
  rw [← padicNorm_inv_eq p _ (gamS_spec hs d j hj).1.ne']
  exact Ap_isLeast' hs p d j hj

lemma Ap_eq (hs : 3 ≤ s) (p : ℕ) [hp : Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    Ap p d j = (p : ℝ) ^ padicValRat p (gamS d j) :=
  (Ap_isLeast hs p d j hj).csInf_eq

/-! ## `S`-units are products over `S` -/

lemma prod_primesS (m : ℕ) (hm : m ≠ 0) (hp : ∀ p, p.Prime → p ∣ m → p ≤ s - 2) :
    ∏ p ∈ primesS s, p ^ padicValNat p m = m := by
  have h := Nat.prod_pow_prime_padicValNat m hm (m + s + 1) (by omega)
  refine Eq.trans (Finset.prod_subset (fun p hp' => ?_) (fun p hp' hnot => ?_)) h
  · simp only [primesS, mem_filter, mem_range] at hp' ⊢; exact ⟨by omega, hp'.2⟩
  · simp only [primesS, mem_filter, mem_range, not_and] at hp' hnot
    have : ¬ p ∣ m := fun hd => by
      have := hp p hp'.2 hd
      have := hp'.2.two_le
      exact hnot (by omega) hp'.2
    rw [padicValNat.eq_zero_of_not_dvd this, pow_zero]

lemma prime_le_of_dvd {a b e : ℕ} (hab : a.Coprime b) (h : a ∣ b * (s - 2).factorial ^ e)
    {p : ℕ} (hp : p.Prime) (hpa : p ∣ a) : p ≤ s - 2 := by
  have h1 : a ∣ (s - 2).factorial ^ e := hab.dvd_of_dvd_mul_left h
  exact (hp.dvd_factorial).1 (hp.dvd_of_dvd_pow (hpa.trans h1))

/-- A positive `S`-unit is `∏_{p ∈ S} p^{v_p}`. -/
lemma sunit_primes (a : ℚ) (ha : 0 < a) (hu : SUnit s a) :
    (a : ℝ) = ∏ p ∈ primesS s, (p : ℝ) ^ padicValRat p a := by
  obtain ⟨_, ⟨z, e, hz⟩, ⟨z', e', hz'⟩⟩ := hu
  set n : ℕ := (s - 2).factorial
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hnum : 0 < a.num := Rat.num_pos.2 ha
  have hden : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hnumq : (a.num : ℚ) ≠ 0 := by exact_mod_cast hnum.ne'
  have ha' : a = a.num / a.den := (Rat.num_div_den a).symm
  -- the denominator divides `n^e`, the numerator `n^{e'}`
  have e1 : (a.num : ℚ) * n ^ e = z * a.den := by
    rw [ha'] at hz; field_simp at hz; linarith [hz]
  have e2 : (a.den : ℚ) * n ^ e' = z' * a.num := by
    rw [ha', inv_div] at hz'; field_simp at hz'; linarith [hz']
  have d1 : a.den ∣ a.num.natAbs * n ^ e := by
    have : ((a.den : ℤ)) ∣ a.num * (n : ℤ) ^ e := ⟨z, by exact_mod_cast (e1.trans (mul_comm _ _))⟩
    have := Int.natAbs_dvd_natAbs.2 this
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have d2 : a.num.natAbs ∣ a.den * n ^ e' := by
    have : (a.num : ℤ) ∣ (a.den : ℤ) * (n : ℤ) ^ e' := ⟨z', by exact_mod_cast (e2.trans (mul_comm _ _))⟩
    have := Int.natAbs_dvd_natAbs.2 this
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have pden : ∀ p, p.Prime → p ∣ a.den → p ≤ s - 2 :=
    fun p hp hd => prime_le_of_dvd a.reduced.symm d1 hp hd
  have pnum : ∀ p, p.Prime → p ∣ a.num.natAbs → p ≤ s - 2 :=
    fun p hp hd => prime_le_of_dvd a.reduced d2 hp hd
  have Pn := prod_primesS (s := s) a.num.natAbs (Int.natAbs_ne_zero.2 hnum.ne') pnum
  have Pd := prod_primesS (s := s) a.den a.den_pos.ne' pden
  have hv : ∀ p, padicValRat p a = (padicValNat p a.num.natAbs : ℤ) - padicValNat p a.den :=
    fun p => rfl
  have hpz : ∀ p ∈ primesS s, (p : ℝ) ≠ 0 := by
    intro p hp
    simp only [primesS, mem_filter] at hp
    exact_mod_cast hp.2.ne_zero
  rw [prod_congr rfl fun p hp => by rw [hv p, zpow_sub₀ (hpz p hp), zpow_natCast, zpow_natCast],
    prod_div_distrib]
  have Pn' : (∏ p ∈ primesS s, (p : ℝ) ^ padicValNat p a.num.natAbs) = (a.num.natAbs : ℝ) := by
    exact_mod_cast Pn
  have Pd' : (∏ p ∈ primesS s, (p : ℝ) ^ padicValNat p a.den) = (a.den : ℝ) := by
    exact_mod_cast Pd
  rw [Pn', Pd']
  have : (a.num.natAbs : ℝ) = (a.num : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
  rw [this]
  conv_lhs => rw [ha']
  push_cast; ring

lemma prod_Ap (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p d j = (gamS d j : ℝ) := by
  rw [sunit_primes _ (gamS_spec hs d j hj).1 (sat_gamma_core hs d j hj).2.1]
  refine prod_congr rfl fun p hp => ?_
  simp only [primesS, mem_filter] at hp
  have : Fact p.Prime := ⟨hp.2⟩
  exact Ap_eq hs p d j hj

/-- `h_j = ‖u‖` for the Gram–Schmidt vector of any flag. -/
lemma hS_eq (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Flag d B j) : hS d j = ‖uvec d B j‖ := by
  rw [hS, prod_Ap hs d j hj, Ainf_eq hs d B j hj hB, div_mul_cancel₀ _ (gam_pos hs d j hj).ne']

/-! ## `lem:adelic` -/

theorem adelic_p_core (hs : 3 ≤ s) (p : ℕ) (hp : p.Prime) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    IsLeast (ApSet p d j) ((p : ℝ) ^ padicValRat p (gamS d j)) ∧
      Ap p d j = (p : ℝ) ^ padicValRat p (gamS d j) := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨Ap_isLeast hs p d j hj, Ap_eq hs p d j hj⟩

theorem adelic_gamma_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    (gamS d j : ℝ) = ∏ p ∈ primesS s, Ap p d j :=
  (prod_Ap hs d j hj).symm

lemma kappa_real (d : Fin s) (j : ℕ) (E : Fin s → ℤ) :
    ((colPoly d fun c => (E c : ℚ)).map (algebraMap ℚ ℝ)).coeff j = (kappa d j E : ℝ) := by
  rw [coeff_map]; rfl

theorem adelic_inf_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ θ : EuclideanSpace ℝ (Fin s), θ ∈ Vlt d (j + 1) ∧ θ ∈ (Vlt d j)ᗮ ∧
      (∀ g : Polynomial ℝ, g.natDegree ≤ j → inner ℝ θ (polyVecR d g) = g.coeff j) ∧
      (∀ E : Fin s → ℤ, InLam d j E → inner ℝ θ (colE E) = kappa d j E) ∧
      (∀ θ' ∈ Vlt d (j + 1),
        (∀ g : Polynomial ℝ, g.natDegree ≤ j → inner ℝ θ' (polyVecR d g) = g.coeff j) → θ' = θ) ∧
      θ ≠ 0 ∧ IsLeast (AinfSet d j) ‖θ‖⁻¹ ∧ Ainf d j = ‖θ‖⁻¹ ∧
      ∃ g : Polynomial ℝ, g.Monic ∧ g.natDegree = j ∧ polyVecR d g = (‖θ‖ ^ 2)⁻¹ • θ := by
  have hB := flag_Ecol hs d j hj
  have hγ := gam_pos hs d j hj
  have hu0 := uvec_ne_zero hs d (Ecol d) j hj hB
  have hun := norm_pos_iff.2 hu0
  set θ := (gamS d j / ‖uvec d (Ecol d) j‖ ^ 2 : ℝ) • uvec d (Ecol d) j
  have hinner : ∀ g : Polynomial ℝ, g.natDegree ≤ j → inner ℝ θ (polyVecR d g) = g.coeff j := by
    intro g hg
    rw [real_inner_smul_left, inner_u_poly hs d (Ecol d) j hj hB g hg]
    field_simp
  have hnθ : ‖θ‖ = gamS d j / ‖uvec d (Ecol d) j‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hθ0 : θ ≠ 0 := smul_ne_zero (by positivity) hu0
  have hinv : ‖θ‖⁻¹ = ‖uvec d (Ecol d) j‖ / gamS d j := by rw [hnθ, inv_div]
  have hmem := uvec_mem hs d (Ecol d) j hj hB
  refine ⟨θ, Submodule.smul_mem _ _ hmem.1, Submodule.smul_mem _ _ hmem.2, hinner, ?_, ?_, hθ0, ?_,
    ?_, ?_⟩
  · intro E hE
    rw [colE_eq_poly hs d E hE.1, hinner _ ?_, kappa_real d j E]
    rw [map_natDegree_le]; exact ((inLam_iff hs hj E).1 hE).2
  · intro θ' hθ' h'
    have hd : θ' - θ ∈ Vlt d (j + 1) := Submodule.sub_mem _ hθ' (Submodule.smul_mem _ _ hmem.1)
    obtain ⟨g, hg, hge⟩ := (mem_Vlt d (j + 1) _).1 hd
    have hgn := natDeg_le_of_deg_lt g j hg
    have h0 : inner ℝ (θ' - θ) (θ' - θ) = 0 := by
      conv_rhs => skip
      rw [show inner ℝ (θ' - θ) (θ' - θ) = inner ℝ θ' (polyVecR d g) - inner ℝ θ (polyVecR d g) by
        rw [← hge, inner_sub_left], h' g hgn, hinner g hgn, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  · rw [hinv]; exact Ainf_isLeast hs d (Ecol d) j hj hB
  · rw [hinv]; exact Ainf_eq hs d (Ecol d) j hj hB
  · obtain ⟨g, hm, hd, he⟩ := monic_of_u hs d (Ecol d) j hj hB
    refine ⟨g, hm, hd, ?_⟩
    rw [he, hnθ, smul_smul]
    congr 1
    field_simp

theorem adelic_proj_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ u : EuclideanSpace ℝ (Fin s), u ∈ lineA d j ∧ ‖u‖ = hS d j ∧
      ∀ x, (∃ E : Fin s → ℤ, InLam d j E ∧ piA d j (colE E) = x) ↔ ∃ z : ℤ, x = (z : ℝ) • u := by
  have hB := flag_Ecol hs d j hj
  have hγ := gam_pos hs d j hj
  refine ⟨uvec d (Ecol d) j, uvec_mem hs d (Ecol d) j hj hB, (hS_eq hs d (Ecol d) j hj hB).symm,
    fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨z, hz⟩ := kappa_mem hs hj hE
    refine ⟨z, ?_⟩
    have hdeg : ((colPoly d fun c => (E c : ℚ)).map (algebraMap ℚ ℝ)).natDegree ≤ j := by
      rw [map_natDegree_le]; exact ((inLam_iff hs hj E).1 hE).2
    rw [colE_eq_poly hs d E hE.1, pi_poly hs d (Ecol d) j hj hB _ hdeg, kappa_real d j E, hz]
    congr 1; push_cast; field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z • Ecol d j, inLam_zsmul z (hB j le_rfl).1, ?_⟩
    have hl := inLam_zsmul z (hB j le_rfl).1
    have hdeg : ((colPoly d fun c => ((z • Ecol d j) c : ℚ)).map (algebraMap ℚ ℝ)).natDegree ≤ j := by
      rw [map_natDegree_le]; exact ((inLam_iff hs hj _).1 hl).2
    rw [colE_eq_poly hs d _ hl.1, pi_poly hs d (Ecol d) j hj hB _ hdeg, kappa_real d j,
      kappa_zsmul, (hB j le_rfl).2]
    congr 1; push_cast; field_simp

theorem adelic_norm_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (E : Fin s → ℤ)
    (hE : InLam d j E) (hnot : colE E ∉ Vlt d j) : hS d j ≤ ‖colE E‖ := by
  have hB := flag_Ecol hs d j hj
  have hγ := gam_pos hs d j hj
  have hun := norm_pos_iff.2 (uvec_ne_zero hs d (Ecol d) j hj hB)
  have hdeg : ((colPoly d fun c => (E c : ℚ)).map (algebraMap ℚ ℝ)).natDegree ≤ j := by
    rw [map_natDegree_le]; exact ((inLam_iff hs hj E).1 hE).2
  have hk0 : kappa d j E ≠ 0 := by
    intro h0
    apply hnot
    rw [colE_eq_poly hs d E hE.1]
    refine polyVecR_mem d _ (degree_lt_of _ j hdeg ?_)
    rw [kappa_real d j E, h0]; simp
  obtain ⟨z, hz⟩ := kappa_mem hs hj hE
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; exact hk0 hz
  have h1 := inner_u_poly hs d (Ecol d) j hj hB _ hdeg
  rw [← colE_eq_poly hs d E hE.1, kappa_real d j E, hz] at h1
  have h2 := abs_real_inner_le_norm (uvec d (Ecol d) j) (colE E)
  rw [h1] at h2
  have hzq : ((((z : ℚ) * gamS d j : ℚ)) : ℝ) / (gamS d j : ℝ) = z := by
    push_cast; field_simp
  rw [hzq, abs_mul, abs_of_nonneg (sq_nonneg ‖uvec d (Ecol d) j‖)] at h2
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  rw [hS_eq hs d (Ecol d) j hj hB]
  have h4 : ‖uvec d (Ecol d) j‖ * ‖uvec d (Ecol d) j‖ ≤ ‖uvec d (Ecol d) j‖ * ‖colE E‖ := by nlinarith [h2, hz1, sq_nonneg ‖uvec d (Ecol d) j‖]
  exact le_of_mul_le_mul_left h4 hun

/-- "It suffices to give, at each place, one monic `g` of degree `j`" (proof of `thm:A`). -/
theorem hS_le_monic_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (g : Polynomial ℝ)
    (hg : g.Monic) (hgd : g.natDegree = j) (gp : ℕ → Polynomial ℚ)
    (hgp : ∀ p ∈ primesS s, (gp p).Monic ∧ (gp p).natDegree = j) :
    hS d j ≤ ‖polyVecR d g‖ *
      ∏ p ∈ primesS s, ⨆ c, ((padicNorm p (polyVecQ d (gp p) c) : ℚ) : ℝ) := by
  have hB := flag_Ecol hs d j hj
  have hA := Ainf_isLeast hs d (Ecol d) j hj hB
  rw [hS, Ainf_eq hs d (Ecol d) j hj hB]
  have hpos : ∀ p ∈ primesS s, 0 ≤ Ap p d j := by
    intro p hp
    simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    rw [Ap_eq hs p d j hj]; positivity
  refine mul_le_mul (hA.2 ⟨g, hg, hgd, rfl⟩) (Finset.prod_le_prod₀ hpos fun p hp => ?_)
    (prod_nonneg hpos) (norm_nonneg _)
  simp only [primesS, mem_filter] at hp
  have : Fact p.Prime := ⟨hp.2⟩
  rw [Ap_eq hs p d j hj]
  exact (Ap_isLeast hs p d j hj).2 ⟨gp p, (hgp p (by simp [primesS, hp.1, hp.2])).1,
    (hgp p (by simp [primesS, hp.1, hp.2])).2, rfl⟩

end

end Z3NetA.Proofs
