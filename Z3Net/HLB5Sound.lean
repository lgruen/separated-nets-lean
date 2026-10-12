module
public import Mathlib
public import Z3Net.HLB5Cert

@[expose] public section

/-!
# Entry HL, part 12: soundness of the `s = 5` certificate

* `lbq_le`: one coordinate of a relaxation configuration gives
  `2 max(0, |q E_c + Δ_c| - 1) ≥ lbq q (∑E odd) E_c S_c` (`S_c = 2σ_c`, `|S_c| < q`, `q` odd);
* `lb1_le`: on `[Smin, Smax]`, `lb1 ≤ lbq`;
* `lbq_scale`: `q₁ · lbq q ≥ q · lbq q₁` for `q ≥ q₁` (the monotone form);
* `cert_sound`: from `allE.all okE = true`, every configuration with `q ≥ 1511` (odd) satisfies
  `100000² ∑_c max(0, |q E_c + Δ_c| - 1)² ≥ 102652² q²`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## One coordinate -/

lemma lbq_le (q : ℤ) (hq : 0 < q) (hqodd : Odd q) (E Δ S : ℤ) (odd : Bool)
    (hpar : odd = true ↔ Odd S) (hdvd : q ∣ 2 * Δ - S) (hΔ : |Δ| < q) (hS : |S| < q) :
    lbq q odd E S ≤ 2 * max 0 (|q * E + Δ| - 1) := by
  obtain ⟨t, ht⟩ := hdvd
  have ht2 : -2 ≤ t ∧ t ≤ 2 := by
    rw [abs_lt] at hΔ hS
    constructor
    · by_contra h; push_neg at h
      have : q * t ≤ q * (-3) := mul_le_mul_of_nonneg_left (by omega) hq.le
      linarith
    · by_contra h; push_neg at h
      have : q * 3 ≤ q * t := mul_le_mul_of_nonneg_left (by omega) hq.le
      linarith
  have key : q * |2 * E + t| - |S| ≤ 2 * |q * E + Δ| := by
    have e : 2 * (q * E + Δ) = q * (2 * E + t) + S := by linarith
    have h1 : |q * (2 * E + t)| = q * |2 * E + t| := by rw [abs_mul, abs_of_pos hq]
    have := abs_add_le (q * (2 * E + t) + S) (-S)
    rw [add_neg_cancel_right, abs_neg, h1, ← e, abs_mul, abs_two] at this
    linarith
  have ha : aS odd E S ≤ |2 * E + t| := by
    unfold aS
    cases odd with
    | true =>
      simp only [if_true]
      have hSo : Odd S := hpar.mp rfl
      have htodd : Odd t := by
        by_contra h
        rw [Int.not_odd_iff_even] at h
        obtain ⟨r, hr⟩ := h
        obtain ⟨w, hw⟩ := hSo
        have : 2 * Δ - S = 2 * (q * r) := by rw [ht, hr]; ring
        omega
      obtain ⟨w, hw⟩ := htodd
      have : t = 1 ∨ t = -1 := by omega
      rcases this with h | h <;> subst h
      · exact min_le_left _ _
      · exact min_le_right _ _
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hSe : ¬ Odd S := fun h => by have := hpar.mpr h; simp at this
      rw [Int.not_odd_iff_even] at hSe
      obtain ⟨w, hw⟩ := hSe
      have hteven : Even t := by
        by_contra h
        rw [Int.not_even_iff_odd] at h
        have hprod : Odd (q * t) := hqodd.mul h
        rw [← ht] at hprod
        obtain ⟨r, hr⟩ := hprod
        omega
      obtain ⟨κ, hκ⟩ := hteven
      have hΔe : Δ = w + κ * q := by
        have h2 : 2 * Δ - (w + w) = 2 * (κ * q) := by rw [← hw, ht, hκ]; ring
        omega
      rw [abs_lt] at hΔ
      have hκ1 : κ = -1 ∨ κ = 0 ∨ κ = 1 := by omega
      split_ifs with h0 hpos
      · -- `S = 0`: `t = 0`
        have hw0 : w = 0 := by omega
        rcases hκ1 with h | h | h
        · subst h; rw [hΔe, hw0] at hΔ; linarith [hΔ.1]
        · subst h; rw [hκ]; simp
        · subst h; rw [hΔe, hw0] at hΔ; linarith [hΔ.2]
      · rcases hκ1 with h | h | h
        · subst h; rw [hκ]; exact (min_le_right _ _).trans (le_of_eq (by ring_nf))
        · subst h; rw [hκ]; exact (min_le_left _ _).trans (le_of_eq (by ring_nf))
        · exfalso; subst h; rw [hΔe] at hΔ; linarith [hΔ.2]
      · rcases hκ1 with h | h | h
        · exfalso; subst h; rw [hΔe] at hΔ
          have : w < 0 := by omega
          linarith [hΔ.1]
        · subst h; rw [hκ]; exact (min_le_left _ _).trans (le_of_eq (by ring_nf))
        · subst h; rw [hκ]; exact (min_le_right _ _).trans (le_of_eq (by ring_nf))
  unfold lbq
  apply max_le (by positivity)
  have h1 : q * aS odd E S ≤ q * |2 * E + t| := mul_le_mul_of_nonneg_left ha hq.le
  have := le_max_right 0 (|q * E + Δ| - 1)
  linarith

lemma a1_le (odd : Bool) (E lo hi S : ℤ) (hlo : lo ≤ S) (hhi : S ≤ hi) :
    a1 odd E lo hi ≤ aS odd E S := by
  unfold a1 aS
  cases odd with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, if_false]
    split_ifs with h1 h2 h3 h4 h5 h6 <;>
      first
      | exact le_rfl
      | omega
      | exact min_le_left _ _
      | exact (min_le_left _ _).trans (min_le_left _ _)
      | exact (min_le_left _ _).trans (min_le_right _ _)
      | exact min_le_right _ _

lemma abs_le_max_of_mem (lo hi S : ℤ) (hlo : lo ≤ S) (hhi : S ≤ hi) : |S| ≤ max |lo| |hi| := by
  rw [abs_le]
  constructor
  · have := neg_abs_le lo; have := le_max_left |lo| |hi|; linarith
  · have := le_abs_self hi; have := le_max_right |lo| |hi|; linarith

lemma aS_nonneg (odd : Bool) (E S : ℤ) : 0 ≤ aS odd E S := by
  unfold aS; split_ifs <;> positivity

lemma a1_nonneg (odd : Bool) (E lo hi : ℤ) : 0 ≤ a1 odd E lo hi := by
  unfold a1; split_ifs <;> positivity

lemma lb1_le (q : ℤ) (hq : 0 ≤ q) (odd : Bool) (E lo hi S : ℤ) (hlo : lo ≤ S) (hhi : S ≤ hi) :
    lb1 q odd E lo hi ≤ lbq q odd E S := by
  unfold lb1 lbq
  apply max_le_max le_rfl
  have h1 := mul_le_mul_of_nonneg_left (a1_le odd E lo hi S hlo hhi) hq
  have h2 := abs_le_max_of_mem lo hi S hlo hhi
  linarith

/-- The monotone form: `q₁ · max(0, a q - b) ≥ q · max(0, a q₁ - b)` for `q ≥ q₁ > 0`, `b ≥ 0`. -/
lemma max_scale (a b q q₁ : ℤ) (hq₁ : 0 < q₁) (hq : q₁ ≤ q) (hb : 0 ≤ b) :
    q * max 0 (q₁ * a - b) ≤ q₁ * max 0 (q * a - b) := by
  rcases le_or_gt (q₁ * a - b) 0 with h | h
  · rw [max_eq_left h, mul_zero]; positivity
  · rw [max_eq_right h.le]
    have ha : 0 < a := by
      by_contra ha; push_neg at ha; nlinarith
    have h2 : 0 < q * a - b := by nlinarith
    rw [max_eq_right h2.le]
    nlinarith

lemma lbq_scale (q q₁ : ℤ) (hq₁ : 0 < q₁) (hq : q₁ ≤ q) (odd : Bool) (E S : ℤ) :
    q * lbq q₁ odd E S ≤ q₁ * lbq q odd E S := by
  unfold lbq
  have := max_scale (aS odd E S) (|S| + 2) q q₁ hq₁ hq (by positivity)
  rw [show q₁ * aS odd E S - (|S| + 2) = q₁ * aS odd E S - |S| - 2 by ring,
    show q * aS odd E S - (|S| + 2) = q * aS odd E S - |S| - 2 by ring] at this
  rw [mul_comm q₁ (aS odd E S), mul_comm q (aS odd E S)] at *
  linarith

/-! ## From the configuration to the certificate data -/

lemma ctrF_bounds (d : ℕ) (E : ℤ) (J : ℕ) (hJ : J ≤ 3) (c : ℕ) :
    cminF d E c ≤ ctrF d E J c ∧ ctrF d E J c ≤ cmaxF d E c := by
  unfold cminF cmaxF
  interval_cases J <;> constructor <;> simp

lemma Icc_sum (f : ℕ → ℤ) (J : ℕ) (hJ : J ≤ 3) :
    ∑ x ∈ Finset.Icc 1 J, f x = (if 1 ≤ J then f 1 else 0) + (if 2 ≤ J then f 2 else 0) +
      (if 3 ≤ J then f 3 else 0) := by
  interval_cases J
  · simp
  · simp
  · rw [show Finset.Icc 1 2 = {1, 2} by decide]; simp
  · rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]; simp; ring

lemma contrib_eq (E : ℤ) (J : ℕ) (hJ : J ≤ 3) (c d : Fin 5) :
    E * F2B5 0 c d + E.sign * ∑ x ∈ Icc 1 J, F2B5 x c d = ctrF d E J c := by
  rw [Icc_sum (fun x => F2B5 x c d) J hJ]; rfl

lemma sig2_eq_SF (E : Fin 5 → ℤ) (J : Fin 5 → ℕ) (hJ : ∀ d, J d ≤ 3) (c : Fin 5) :
    sig2 F2B5 E J c = SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c := by
  unfold sig2 SF
  rw [Fin.sum_univ_five]
  simp only [contrib_eq _ _ (hJ _)]
  rfl

lemma SF_bounds (E : Fin 5 → ℤ) (J : Fin 5 → ℕ) (hJ : ∀ d, J d ≤ 3) (c : ℕ) :
    loF (E 0) (E 1) (E 2) (E 3) (E 4) c ≤ SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c ∧
    SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c ≤ hiF (E 0) (E 1) (E 2) (E 3) (E 4) c := by
  have h0 := ctrF_bounds 0 (E 0) (J 0) (hJ 0) c
  have h1 := ctrF_bounds 1 (E 1) (J 1) (hJ 1) c
  have h2 := ctrF_bounds 2 (E 2) (J 2) (hJ 2) c
  have h3 := ctrF_bounds 3 (E 3) (J 3) (hJ 3) c
  have h4 := ctrF_bounds 4 (E 4) (J 4) (hJ 4) c
  unfold loF hiF SF
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

lemma F2B5_odd0 : ∀ c d : Fin 5, Odd (F2B5 0 c d) := by decide +kernel

lemma F2B5_even : ∀ x : Fin 4, ∀ c d : Fin 5, 1 ≤ (x : ℕ) → Even (F2B5 x c d) := by decide +kernel

lemma F2B5_even' (x : ℕ) (c d : Fin 5) (hx : 1 ≤ x) : Even (F2B5 x c d) := by
  by_cases h : x < 4
  · exact F2B5_even ⟨x, h⟩ c d hx
  · have : F2B5 x c d = 0 := by
      have h2 := B5_design x c d
      have h1 : HLdes uB5 vB5 lamB5 gcoB5 dgB5 x c d = 0 := by
        simp [HLdes, show 5 - 1 ≤ x by omega]
      rw [h1] at h2
      have h3 : ((F2B5 x c d : ℤ) : ℚ) = 0 := by rw [← h2]; ring
      exact_mod_cast h3
    rw [this]; exact ⟨0, rfl⟩

lemma oddF_iff (E : Fin 5 → ℤ) (J : Fin 5 → ℕ) (hJ : ∀ d, J d ≤ 3) (c : Fin 5) :
    oddF (E 0) (E 1) (E 2) (E 3) (E 4) = true ↔
      Odd (SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c) := by
  have h := sig2_parity F2B5 F2B5_odd0 (fun x c d hx => F2B5_even' x c d hx) E J c
  rw [sig2_eq_SF E J hJ, Fin.sum_univ_five] at h
  unfold oddF
  rw [decide_eq_true_iff]
  obtain ⟨r, hr⟩ := h
  constructor
  · intro h1; exact ⟨r + (E 0 + E 1 + E 2 + E 3 + E 4) / 2, by omega⟩
  · rintro ⟨w, hw⟩; omega

lemma mem_vals (z : ℤ) (h : |z| ≤ 2) : z ∈ vals := by
  rw [abs_le] at h
  simp only [vals, List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma mem_jOpts (e : ℤ) (j : ℕ) (hj : j ≤ 3) : (if e = 0 then 0 else j) ∈ jOpts e := by
  unfold jOpts
  split_ifs <;> simp <;> omega

lemma ctrF_zero (d : ℕ) (J : ℕ) (c : ℕ) : ctrF d 0 J c = 0 := by simp [ctrF]

lemma SF_mask (E : Fin 5 → ℤ) (J : Fin 5 → ℕ) (c : ℕ) :
    SF (E 0) (E 1) (E 2) (E 3) (E 4) (if E 0 = 0 then 0 else J 0) (if E 1 = 0 then 0 else J 1)
      (if E 2 = 0 then 0 else J 2) (if E 3 = 0 then 0 else J 3) (if E 4 = 0 then 0 else J 4) c =
    SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c := by
  have key : ∀ (d : ℕ) (e : ℤ) (j : ℕ), ctrF d e (if e = 0 then 0 else j) c = ctrF d e j c := by
    intro d e j; by_cases h : e = 0
    · subst h; simp [ctrF_zero]
    · simp [h]
  unfold SF; simp only [key]

/-! ## Soundness -/

theorem cert_sound (hcheck : ∀ e0 ∈ vals, checkE0 e0 = true) (q : ℤ) (hq : 1511 ≤ q) (hqodd : Odd q)
    (E : Fin 5 → ℤ) (J : Fin 5 → ℕ) (Δ : Fin 5 → ℤ) (hE : ∀ c, |E c| ≤ 2) (hne : ∃ c, E c ≠ 0)
    (hJ : ∀ c, J c ≤ 3) (hdvd : ∀ c, q ∣ 2 * Δ c - sig2 F2B5 E J c) (hΔ : ∀ c, |Δ c| < q) :
    102652 ^ 2 * q ^ 2 ≤ 100000 ^ 2 * ∑ c, (max 0 (|q * E c + Δ c| - 1)) ^ 2 := by
  have hok : okEF (E 0) (E 1) (E 2) (E 3) (E 4) = true := by
    have h := hcheck (E 0) (mem_vals _ (hE 0))
    unfold checkE0 at h
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h _
      (mem_vals _ (hE 1))) _ (mem_vals _ (hE 2))) _ (mem_vals _ (hE 3))) _ (mem_vals _ (hE 4))
  unfold okEF at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
  obtain ⟨hS, hrest⟩ := hok
  unfold okSF at hS
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hS
  obtain ⟨⟨⟨⟨hS0, hS1⟩, hS2⟩, hS3⟩, hS4⟩ := hS
  have hq0 : (0 : ℤ) < q := by linarith
  set od := oddF (E 0) (E 1) (E 2) (E 3) (E 4) with hod
  set S : ℕ → ℤ := fun c => SF (E 0) (E 1) (E 2) (E 3) (E 4) (J 0) (J 1) (J 2) (J 3) (J 4) c with hSdef
  set lo : ℕ → ℤ := fun c => loF (E 0) (E 1) (E 2) (E 3) (E 4) c
  set hi : ℕ → ℤ := fun c => hiF (E 0) (E 1) (E 2) (E 3) (E 4) c
  have hSb : ∀ c, lo c ≤ S c ∧ S c ≤ hi c := fun c => SF_bounds E J hJ c
  have hSmax : ∀ c : Fin 5, max |lo c| |hi c| < q1 := by
    intro c; fin_cases c
    · exact hS0
    · exact hS1
    · exact hS2
    · exact hS3
    · exact hS4
  have hSq : ∀ c : Fin 5, |S c| < q := fun c => by
    have := abs_le_max_of_mem _ _ _ (hSb c).1 (hSb c).2
    have := hSmax c
    unfold q1 at this
    linarith
  have hsig : ∀ c : Fin 5, sig2 F2B5 E J c = S c := fun c => sig2_eq_SF E J hJ c
  -- one coordinate
  have hcoord : ∀ c : Fin 5, lbq q od (E c) (S c) ≤ 2 * max 0 (|q * E c + Δ c| - 1) := by
    intro c
    exact lbq_le q hq0 hqodd (E c) (Δ c) (S c) od (oddF_iff E J hJ c) (by rw [← hsig]; exact hdvd c)
      (hΔ c) (hSq c)
  -- the certificate at `q₁ = 1511`
  have hcert : Tq ≤ 100000 ^ 2 * ∑ c : Fin 5, lbq q1 od (E c) (S c) ^ 2 := by
    rw [Fin.sum_univ_five]
    rcases hrest with (h0 | h1) | h2
    · exfalso
      rw [decide_eq_true_iff] at h0
      obtain ⟨c, hc⟩ := hne
      fin_cases c <;> simp_all
    · unfold ok1F at h1
      rw [decide_eq_true_iff] at h1
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hl : ∀ c : Fin 5, lb1 q1 od (E c) (lo c) (hi c) ^ 2 ≤ lbq q1 od (E c) (S c) ^ 2 := fun c =>
        pow_le_pow_left₀ (le_max_left _ _)
          (lb1_le q1 (by unfold q1; norm_num) _ _ _ _ _ (hSb c).1 (hSb c).2) 2
      have := hl 0; have := hl 1; have := hl 2; have := hl 3; have := hl 4
      exact add_le_add (add_le_add (add_le_add (add_le_add (hl 0) (hl 1)) (hl 2)) (hl 3)) (hl 4)
    · unfold ok2F at h2
      have hm := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp h2 _ (mem_jOpts (E 0) (J 0) (hJ 0))) _ (mem_jOpts (E 1) (J 1) (hJ 1))) _
        (mem_jOpts (E 2) (J 2) (hJ 2))) _ (mem_jOpts (E 3) (J 3) (hJ 3))) _ (mem_jOpts (E 4) (J 4) (hJ 4))
      unfold okJF at hm
      rw [decide_eq_true_iff] at hm
      simp only [SF_mask] at hm
      exact hm
  -- scale to `q`
  have hsc : ∀ c : Fin 5, q * lbq q1 od (E c) (S c) ≤ q1 * lbq q od (E c) (S c) :=
    fun c => lbq_scale q q1 (by unfold q1; norm_num) (by unfold q1; exact hq) _ _ _
  have hlbq0 : ∀ c : Fin 5, 0 ≤ lbq q1 od (E c) (S c) := fun c => le_max_left _ _
  have hsum1 : q ^ 2 * ∑ c : Fin 5, lbq q1 od (E c) (S c) ^ 2 ≤
      q1 ^ 2 * ∑ c : Fin 5, lbq q od (E c) (S c) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have := pow_le_pow_left₀ (mul_nonneg hq0.le (hlbq0 c)) (hsc c) 2
    rw [mul_pow, mul_pow] at this
    exact this
  have hsum2 : ∑ c : Fin 5, lbq q od (E c) (S c) ^ 2 ≤ 4 * ∑ c, (max 0 (|q * E c + Δ c| - 1)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h0 : 0 ≤ lbq q od (E c) (S c) := le_max_left _ _
    have := pow_le_pow_left₀ h0 (hcoord c) 2
    rw [mul_pow] at this
    linarith
  have hT : Tq = 205304 ^ 2 * 1511 ^ 2 := rfl
  have hq1 : q1 = 1511 := rfl
  rw [hT] at hcert
  rw [hq1] at hsum1
  set A := ∑ c : Fin 5, lbq q1 od (E c) (S c) ^ 2
  set Bq := ∑ c : Fin 5, lbq q od (E c) (S c) ^ 2
  set M := ∑ c, (max 0 (|q * E c + Δ c| - 1)) ^ 2
  have h1 : 205304 ^ 2 * 1511 ^ 2 * q ^ 2 ≤ 100000 ^ 2 * A * q ^ 2 :=
    mul_le_mul_of_nonneg_right hcert (sq_nonneg q)
  have h2 : 100000 ^ 2 * (q ^ 2 * A) ≤ 100000 ^ 2 * (1511 ^ 2 * Bq) :=
    mul_le_mul_of_nonneg_left hsum1 (by norm_num)
  have h3 : 100000 ^ 2 * (1511 ^ 2 * Bq) ≤ 100000 ^ 2 * (1511 ^ 2 * (4 * M)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 (by norm_num)) (by norm_num)
  have h4 : (4 * 1511 ^ 2) * (102652 ^ 2 * q ^ 2) ≤ (4 * 1511 ^ 2) * (100000 ^ 2 * M) := by
    linear_combination h1 + h2 + h3
  exact le_of_mul_le_mul_left h4 (by norm_num)

end

end Z3NetHL.Proofs
