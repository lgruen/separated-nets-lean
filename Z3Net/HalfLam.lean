module
public import Mathlib
public import Z3Net.HalfDefs

@[expose] public section

/-!
# Entry Half, part 1: `LB₂` versus `λ(M)` (`prop:half`(1), the `p`-free part)

* `halfSteps_nonempty`, `le_halfLB2_of`, `halfLB2_le_of`, `le_halfLam_of`, `halfLam_le_of` —
  the infima over the finite nonempty index set `halfSteps s`.
* `ell_ge_inf_sub` — `ℓ_c ≥ ℓ^∞_c - (|β_c| + 1)/p` (both parities); `abs_halfBeta_le` —
  `|β_c| ≤ 2A` for `|E| ≤ 2`.
* `dom_mul_nonpos` — for a weakly dominant `M` and `|E_c|` maximal, `E_c β_c ≤ 0`;
  `ellInf_even_ge`, `ell_ge_three_halves`.
* `half_lam_le`, `half_lam_dom`, `half_LB2_ge` — `prop:half`(1).
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## The index set and the infima -/

lemma mem_halfSteps {s : ℕ} {E : Fin s → ℤ} : E ∈ halfSteps s ↔ (∀ d, |E d| ≤ 2) ∧ E ≠ 0 := by
  simp only [halfSteps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

lemma halfSteps_nonempty {s : ℕ} (hs : 1 ≤ s) : (halfSteps s).Nonempty := by
  refine ⟨fun _ => 1, mem_halfSteps.mpr ⟨fun _ => by norm_num, fun h => ?_⟩⟩
  have := congrFun h ⟨0, hs⟩
  simp at this

lemma le_halfLB2_of {s : ℕ} (p : ℕ) (M2 : Fin s → Fin s → ℤ) (v : ℝ) (hs : 1 ≤ s) (hv2 : v ≤ 2)
    (h : ∀ E ∈ halfSteps s, v ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2)) : v ≤ halfLB2 p M2 := by
  have : Nonempty (halfSteps s) := (halfSteps_nonempty hs).to_subtype
  exact le_min hv2 (le_ciInf fun E => h E.1 E.2)

lemma halfLB2_le_of {s : ℕ} (p : ℕ) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (hE : E ∈ halfSteps s) : halfLB2 p M2 ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2) :=
  (min_le_right _ _).trans
    (ciInf_le ⟨0, by rintro _ ⟨E, rfl⟩; exact Real.sqrt_nonneg _⟩ (⟨E, hE⟩ : halfSteps s))

lemma le_halfLam_of {s : ℕ} (M2 : Fin s → Fin s → ℤ) (v : ℝ) (hs : 1 ≤ s)
    (h : ∀ E ∈ halfSteps s, v ≤ Real.sqrt (∑ c, halfEllInf M2 E c ^ 2)) : v ≤ halfLam M2 := by
  have : Nonempty (halfSteps s) := (halfSteps_nonempty hs).to_subtype
  exact le_ciInf fun E => h E.1 E.2

lemma halfLam_le_of {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (hE : E ∈ halfSteps s) :
    halfLam M2 ≤ Real.sqrt (∑ c, halfEllInf M2 E c ^ 2) :=
  ciInf_le ⟨0, by rintro _ ⟨E, rfl⟩; exact Real.sqrt_nonneg _⟩ (⟨E, hE⟩ : halfSteps s)

/-! ## Coordinatewise facts -/

lemma ell_nonneg {s : ℕ} (p : ℕ) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    0 ≤ halfEll p M2 E c := le_max_left _ _

lemma ellInf_nonneg {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    0 ≤ halfEllInf M2 E c := by
  unfold halfEllInf
  split_ifs <;> exact le_min (abs_nonneg _) (abs_nonneg _)

/-- `|∑_d M2_cd E_d| ≤ 2 · 2A` for `|E| ≤ 2`. -/
lemma abs_beta2_le {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (hE : ∀ d, |E d| ≤ 2)
    (c : Fin s) : |∑ d, M2 c d * E d| ≤ 2 * (halfA2 M2 : ℤ) := by
  have h1 : |∑ d, M2 c d * E d| ≤ ∑ d, 2 * |M2 c d| :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => by
      rw [abs_mul]; nlinarith [abs_nonneg (M2 c d), hE d, abs_nonneg (E d)])
  have h2 : ∑ d, (M2 c d).natAbs ≤ halfA2 M2 :=
    Finset.le_sup (f := fun c : Fin s => ∑ d, (M2 c d).natAbs) (mem_univ c)
  have h3 : ((∑ d, (M2 c d).natAbs : ℕ) : ℤ) = ∑ d, |M2 c d| := by
    push_cast; simp
  have h4 : ((∑ d, (M2 c d).natAbs : ℕ) : ℤ) ≤ halfA2 M2 := by exact_mod_cast h2
  rw [← mul_sum] at h1
  linarith

lemma abs_halfBeta_le {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (hE : ∀ d, |E d| ≤ 2)
    (c : Fin s) : |halfBeta M2 E c| ≤ halfA2 M2 := by
  have h := abs_beta2_le M2 E hE c
  have h' : |((∑ d, M2 c d * E d : ℤ) : ℝ)| ≤ 2 * (halfA2 M2 : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr h
    push_cast at this ⊢
    exact this
  unfold halfBeta
  rw [abs_div, abs_two]
  linarith

/-- `ℓ_c ≥ ℓ^∞_c - (|β_c| + 1)/p` (both parities, every `p`). -/
lemma ell_ge_inf_sub {s : ℕ} (p : ℕ) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    halfEllInf M2 E c - (|halfBeta M2 E c| + 1) / p ≤ halfEll p M2 E c := by
  unfold halfEll halfEllInf
  refine le_trans ?_ (le_max_right _ _)
  split_ifs with h
  · exact le_refl _
  · set t := halfBeta M2 E c / p with ht
    have hta : |t| = |halfBeta M2 E c| / p := by rw [ht, abs_div, Nat.abs_cast]
    have key : ∀ a : ℝ, |a| - |t| ≤ |a + t| := by
      intro a
      have := abs_add_le (a + t) (-t)
      rw [add_neg_cancel_right, abs_neg] at this
      linarith
    have e : (|halfBeta M2 E c| + 1) / (p : ℝ) = |t| + 1 / p := by rw [hta, add_div]
    rw [e]
    have h1 := key (E c : ℝ)
    have h2 := key ((E c : ℝ) - ((Int.sign (∑ d, M2 c d * E d) : ℤ) : ℝ))
    have hm1 := min_le_left |(E c : ℝ)| |(E c : ℝ) - ((Int.sign (∑ d, M2 c d * E d) : ℤ) : ℝ)|
    have hm2 := min_le_right |(E c : ℝ)| |(E c : ℝ) - ((Int.sign (∑ d, M2 c d * E d) : ℤ) : ℝ)|
    have : min |(E c : ℝ)| |(E c : ℝ) - ((Int.sign (∑ d, M2 c d * E d) : ℤ) : ℝ)| - |t| ≤
        min |(E c : ℝ) + t| |(E c : ℝ) - ((Int.sign (∑ d, M2 c d * E d) : ℤ) : ℝ) + t| :=
      le_min (by linarith) (by linarith)
    linarith

/-- `ℓ_c ≥ ℓ^∞_c - (2A + 1)/p` for `|E| ≤ 2`, `p ≥ 1`. -/
lemma ell_ge_inf_sub_A {s : ℕ} (p : ℕ) (hp : 1 ≤ p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (hE : ∀ d, |E d| ≤ 2) (c : Fin s) :
    halfEllInf M2 E c - ((halfA2 M2 : ℝ) + 1) / p ≤ halfEll p M2 E c := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := ell_ge_inf_sub p M2 E c
  have h2 : (|halfBeta M2 E c| + 1) / (p : ℝ) ≤ ((halfA2 M2 : ℝ) + 1) / p :=
    div_le_div_of_nonneg_right (by linarith [abs_halfBeta_le M2 E hE c]) hp0.le
  linarith

/-- Integers: `1/2 ≤ |n ± 1/2|`. -/
lemma half_le_abs_add (n : ℤ) : (1 / 2 : ℝ) ≤ |(n : ℝ) + 1 / 2| := by
  rcases le_or_gt 0 n with h | h
  · have : (0 : ℝ) ≤ n := by exact_mod_cast h
    exact le_abs.mpr (Or.inl (by linarith))
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    exact le_abs.mpr (Or.inr (by linarith))

lemma half_le_abs_sub (n : ℤ) : (1 / 2 : ℝ) ≤ |(n : ℝ) - 1 / 2| := by
  rcases le_or_gt 1 n with h | h
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    exact le_abs.mpr (Or.inl (by linarith))
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast (show n ≤ 0 by omega)
    exact le_abs.mpr (Or.inr (by linarith))

lemma ellInf_odd_ge {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s)
    (hσ : (∑ d, E d) % 2 = 1) : (1 / 2 : ℝ) ≤ halfEllInf M2 E c := by
  unfold halfEllInf
  rw [if_pos hσ]
  exact le_min (half_le_abs_add _) (half_le_abs_sub _)

/-- Dominance: if `|E_c|` is maximal then `E_c · (∑_d M2_cd E_d) ≤ 0`. -/
lemma dom_mul_nonpos {s : ℕ} (M2 : Fin s → Fin s → ℤ)
    (hdom : ∀ c, M2 c c ≤ -∑ d ∈ univ.erase c, |M2 c d|) (E : Fin s → ℤ) (c : Fin s)
    (hmax : ∀ d, |E d| ≤ |E c|) : E c * (∑ d, M2 c d * E d) ≤ 0 := by
  rw [mul_sum, ← add_sum_erase _ _ (mem_univ c)]
  have h1 : ∀ d ∈ univ.erase c, E c * (M2 c d * E d) ≤ |M2 c d| * (E c) ^ 2 := by
    intro d _
    have e : |E c * (M2 c d * E d)| = |M2 c d| * (|E c| * |E d|) := by
      rw [abs_mul, abs_mul]; ring
    have h2 : |E c| * |E d| ≤ (E c) ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (E c), abs_nonneg (E d), hmax d]
    calc E c * (M2 c d * E d) ≤ |E c * (M2 c d * E d)| := le_abs_self _
      _ = |M2 c d| * (|E c| * |E d|) := e
      _ ≤ |M2 c d| * (E c) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h3 := sum_le_sum h1
  rw [← sum_mul] at h3
  have h4 := hdom c
  have e2 : E c * (M2 c c * E c) = M2 c c * (E c) ^ 2 := by ring
  have h5 := mul_nonpos_of_nonpos_of_nonneg
    (show M2 c c + ∑ d ∈ univ.erase c, |M2 c d| ≤ 0 by linarith) (sq_nonneg (E c))
  linarith

lemma int_abs_le_abs_sub_sign (x y : ℤ) (h : x * y ≤ 0) : |x| ≤ |x - Int.sign y| := by
  rcases Int.sign_trichotomy y with hs | hs | hs <;> rw [hs]
  · have hy : 0 < y := Int.sign_eq_one_iff_pos.mp hs
    have hx : x ≤ 0 := by
      by_contra hx; push_neg at hx; nlinarith [mul_pos hx hy]
    rw [abs_of_nonpos hx, abs_of_nonpos (by linarith)]; linarith
  · simp
  · have hy : y < 0 := Int.sign_eq_neg_one_iff_neg.mp hs
    have hx : 0 ≤ x := by
      by_contra hx; push_neg at hx; nlinarith [mul_pos_of_neg_of_neg hx hy]
    rw [abs_of_nonneg hx, abs_of_nonneg (by linarith)]; linarith

/-- For `σ_E` even and `E_c β_c ≤ 0`: `ℓ^∞_c = |E_c|` (at least). -/
lemma ellInf_even_ge {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s)
    (hσ : ¬ (∑ d, E d) % 2 = 1) (hc : E c * (∑ d, M2 c d * E d) ≤ 0) :
    |(E c : ℝ)| ≤ halfEllInf M2 E c := by
  unfold halfEllInf
  rw [if_neg hσ]
  refine le_min le_rfl ?_
  have h := int_abs_le_abs_sub_sign _ _ hc
  have := (Int.cast_le (R := ℝ)).mpr h
  push_cast at this ⊢
  exact this

/-- For a weakly dominant layer and a coordinate with `|E_c| = 2` maximal:
`ℓ_c ≥ 3/2 - (2A + 1)/p`. -/
lemma ell_ge_three_halves {s : ℕ} (p : ℕ) (M2 : Fin s → Fin s → ℤ)
    (hdom : ∀ c, M2 c c ≤ -∑ d ∈ univ.erase c, |M2 c d|) (E : Fin s → ℤ)
    (hE : E ∈ halfSteps s) (c : Fin s) (hc : |E c| = 2) (hmax : ∀ d, |E d| ≤ 2) (hp : 1 ≤ p) :
    3 / 2 - ((halfA2 M2 : ℝ) + 1) / p ≤ halfEll p M2 E c := by
  have hE2 := (mem_halfSteps.mp hE).1
  have h1 := ell_ge_inf_sub_A p hp M2 E hE2 c
  have h2 : (3 / 2 : ℝ) ≤ halfEllInf M2 E c := by
    by_cases hσ : (∑ d, E d) % 2 = 1
    · unfold halfEllInf
      rw [if_pos hσ]
      rcases abs_eq (show (0 : ℤ) ≤ 2 by norm_num) |>.mp hc with h | h <;> rw [h] <;>
        norm_num [abs_of_pos, abs_of_neg]
    · have hm : ∀ d, |E d| ≤ |E c| := fun d => hc ▸ hmax d
      have := ellInf_even_ge M2 E c hσ (dom_mul_nonpos M2 hdom E c hm)
      have hc' : |(E c : ℝ)| = 2 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hc
        push_cast at this
        exact this
      linarith
  linarith

/-! ## `prop:half`(1): `λ(M)` -/

lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)

/-- `λ(M) ≤ min(√s/2, √2)`. -/
theorem half_lam_le (s : ℕ) (hs : 2 ≤ s) (M2 : Fin s → Fin s → ℤ) :
    halfLam M2 ≤ min (Real.sqrt s / 2) (Real.sqrt 2) := by
  set c0 : Fin s := ⟨0, by omega⟩
  set c1 : Fin s := ⟨1, by omega⟩
  have h01 : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  apply le_min
  · -- `E = 𝟙` (`s` odd) or `𝟙 - e_0` (`s` even)
    set b : ℤ := if Even s then 1 else 0 with hb
    set E : Fin s → ℤ := fun d => 1 - (if d = c0 then b else 0) with hEdef
    have hb01 : b = 0 ∨ b = 1 := by rw [hb]; split_ifs <;> simp
    have hEv : ∀ d, E d = 0 ∨ E d = 1 := by
      intro d
      simp only [hEdef]
      split_ifs <;> omega
    have hσ : (∑ d, E d) % 2 = 1 := by
      have : ∑ d, E d = (s : ℤ) - b := by
        simp only [hEdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      rw [this, hb]
      rcases Nat.even_or_odd s with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [if_pos ⟨r, hr⟩]; subst hr; push_cast; omega
      · rw [if_neg (Nat.not_even_iff_odd.mpr ⟨r, hr⟩)]; subst hr; push_cast; omega
    have hmem : E ∈ halfSteps s := by
      refine mem_halfSteps.mpr ⟨fun d => ?_, fun h => ?_⟩
      · rcases hEv d with h | h <;> rw [h] <;> norm_num
      · rw [h] at hσ; simp at hσ
    have hval : ∀ c, halfEllInf M2 E c = 1 / 2 := by
      intro c
      unfold halfEllInf
      rw [if_pos hσ]
      rcases hEv c with h | h <;> rw [h] <;> norm_num
    refine (halfLam_le_of M2 E hmem).trans (le_of_eq ?_)
    simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (by positivity), show ((1 : ℝ) / 2) ^ 2 = (1 / 2) ^ 2 from rfl,
      Real.sqrt_sq (by norm_num)]
    ring
  · -- `E = e_0 - e_1`
    set E : Fin s → ℤ := fun d => (if d = c0 then 1 else 0) - (if d = c1 then 1 else 0) with hEdef
    have hσ : ¬ (∑ d, E d) % 2 = 1 := by
      have : ∑ d, E d = 0 := by
        simp only [hEdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
      rw [this]; norm_num
    have hmem : E ∈ halfSteps s := by
      refine mem_halfSteps.mpr ⟨fun d => ?_, fun h => ?_⟩
      · simp only [hEdef]; split_ifs <;> norm_num
      · have := congrFun h c0
        simp [hEdef, h01] at this
    refine (halfLam_le_of M2 E hmem).trans (Real.sqrt_le_sqrt ?_)
    have hpt : ∀ c, halfEllInf M2 E c ^ 2 ≤ (if c = c0 then 1 else 0) + (if c = c1 then 1 else 0) := by
      intro c
      have h0 := ellInf_nonneg M2 E c
      have hle : halfEllInf M2 E c ≤ |(E c : ℝ)| := by
        unfold halfEllInf; rw [if_neg hσ]; exact min_le_left _ _
      by_cases hc0 : c = c0
      · subst hc0
        have : E c0 = 1 := by simp [hEdef, h01]
        rw [this] at hle
        have hr : ((if c0 = c0 then (1 : ℝ) else 0) + (if c0 = c1 then 1 else 0)) = 1 := by
          simp [h01]
        rw [hr]
        norm_num at hle
        nlinarith
      · by_cases hc1 : c = c1
        · subst hc1
          have : E c1 = -1 := by simp [hEdef, Ne.symm h01]
          rw [this] at hle
          have hr : ((if c1 = c0 then (1 : ℝ) else 0) + (if c1 = c1 then 1 else 0)) = 1 := by
            simp [Ne.symm h01]
          rw [hr]
          norm_num at hle
          nlinarith
        · have : E c = 0 := by simp [hEdef, hc0, hc1]
          rw [this] at hle
          simp only [if_neg hc0, if_neg hc1]
          norm_num at hle
          nlinarith
    calc ∑ c, halfEllInf M2 E c ^ 2 ≤ ∑ c : Fin s, ((if c = c0 then (1 : ℝ) else 0) +
          (if c = c1 then 1 else 0)) := Finset.sum_le_sum fun c _ => hpt c
      _ = 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp; norm_num

/-- `λ(M) = min(√s/2, √2)` for a weakly diagonally dominant layer. -/
theorem half_lam_dom (s : ℕ) (hs : 2 ≤ s) (M2 : Fin s → Fin s → ℤ)
    (hdom : ∀ c, M2 c c ≤ -∑ d ∈ univ.erase c, |M2 c d|) :
    halfLam M2 = min (Real.sqrt s / 2) (Real.sqrt 2) := by
  refine le_antisymm (half_lam_le s hs M2) (le_halfLam_of M2 _ (by omega) fun E hE => ?_)
  obtain ⟨hE2, hE0⟩ := mem_halfSteps.mp hE
  have hnn : ∀ c ∈ (univ : Finset (Fin s)), 0 ≤ halfEllInf M2 E c ^ 2 := fun c _ => sq_nonneg _
  by_cases hσ : (∑ d, E d) % 2 = 1
  · refine (min_le_left _ _).trans ?_
    have h : ∑ _c : Fin s, (1 / 2 : ℝ) ^ 2 ≤ ∑ c, halfEllInf M2 E c ^ 2 :=
      Finset.sum_le_sum fun c _ => by
        have := ellInf_odd_ge M2 E c hσ; nlinarith
    have e : Real.sqrt (∑ _c : Fin s, (1 / 2 : ℝ) ^ 2) = Real.sqrt s / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]; ring
    rw [← e]
    exact Real.sqrt_le_sqrt h
  · refine (min_le_right _ _).trans ?_
    have : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    obtain ⟨c, -, hcmax⟩ := Finset.exists_max_image univ (fun d => |E d|) univ_nonempty
    have hcm : ∀ d, |E d| ≤ |E c| := fun d => hcmax d (mem_univ d)
    have hc1 : 1 ≤ |E c| := by
      by_contra h
      push_neg at h
      apply hE0
      funext d
      have := hcm d
      have : |E d| = 0 := by have := abs_nonneg (E d); omega
      simpa using this
    have hcl := ellInf_even_ge M2 E c hσ (dom_mul_nonpos M2 hdom E c hcm)
    have hcR : (1 : ℝ) ≤ |(E c : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr hc1; push_cast at this; exact this
    rcases lt_or_ge 1 |E c| with h2 | h1
    · -- `|E_c| = 2`
      have hcR2 : (2 : ℝ) ≤ |(E c : ℝ)| := by
        have := (Int.cast_le (R := ℝ)).mpr (show (2 : ℤ) ≤ |E c| by omega)
        push_cast at this; exact this
      have h4 : (2 : ℝ) ^ 2 ≤ ∑ c, halfEllInf M2 E c ^ 2 :=
        (by nlinarith : (2 : ℝ) ^ 2 ≤ halfEllInf M2 E c ^ 2).trans
          (Finset.single_le_sum hnn (mem_univ c))
      calc Real.sqrt 2 ≤ 2 := sqrt_two_le_two
        _ = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ _ := Real.sqrt_le_sqrt h4
    · -- `|E_c| = 1`: a second nonzero coordinate
      have hc1' : |E c| = 1 := le_antisymm h1 hc1
      obtain ⟨d, hdc, hd0⟩ : ∃ d, d ≠ c ∧ E d ≠ 0 := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ d, E d = E c :=
          Finset.sum_eq_single c (fun d _ hd => hno d hd) (fun h => absurd (mem_univ c) h)
        apply hσ
        rw [hsum]
        rcases abs_eq (show (0 : ℤ) ≤ 1 by norm_num) |>.mp hc1' with h | h <;> rw [h] <;> decide
      have hd1 : |E d| = 1 := by
        have := hcm d
        have : 0 < |E d| := abs_pos.mpr hd0
        omega
      have hdm : ∀ d', |E d'| ≤ |E d| := fun d' => hd1 ▸ hc1' ▸ hcm d'
      have hdl := ellInf_even_ge M2 E d hσ (dom_mul_nonpos M2 hdom E d hdm)
      have hdR : (1 : ℝ) ≤ |(E d : ℝ)| := by
        have := (Int.cast_le (R := ℝ)).mpr hd1.ge; push_cast at this; exact this
      have hpair : halfEllInf M2 E d ^ 2 + halfEllInf M2 E c ^ 2 ≤ ∑ c, halfEllInf M2 E c ^ 2 := by
        calc halfEllInf M2 E d ^ 2 + halfEllInf M2 E c ^ 2
              = ∑ x ∈ {d, c}, halfEllInf M2 E x ^ 2 := by rw [Finset.sum_pair hdc]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ => sq_nonneg _
      exact Real.sqrt_le_sqrt (by nlinarith)

/-! ## `prop:half`(1): `LB₂(p) ≥ λ(M) - √s (2A+1)/p` -/

/-- Triangle inequality in the form used: `0 ≤ a_c ≤ b_c + ε`, `b ≥ 0` give
`|a| ≤ |b| + √s ε`. -/
lemma sqrt_sum_sq_le_add {s : ℕ} (a b : Fin s → ℝ) (ε : ℝ) (ha : ∀ c, 0 ≤ a c)
    (hb : ∀ c, 0 ≤ b c) (hε : 0 ≤ ε) (h : ∀ c, a c ≤ b c + ε) :
    Real.sqrt (∑ c, a c ^ 2) ≤ Real.sqrt (∑ c, b c ^ 2) + Real.sqrt s * ε := by
  set B := ∑ c, b c ^ 2 with hB
  set S := ∑ c, b c with hS
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => hb c
  have hCS : S ^ 2 ≤ (s : ℝ) * B := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin s))) (f := b)
    simpa [hS, hB] using this
  have hSle : S ≤ Real.sqrt s * Real.sqrt B := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le hCS
  have hsum : ∑ c, a c ^ 2 ≤ B + 2 * ε * S + (s : ℝ) * ε ^ 2 := by
    calc ∑ c, a c ^ 2 ≤ ∑ c, (b c + ε) ^ 2 :=
          Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (ha c) (h c) 2
      _ = ∑ c, (b c ^ 2 + (2 * ε) * b c + ε ^ 2) := Finset.sum_congr rfl fun c _ => by ring
      _ = B + 2 * ε * S + (s : ℝ) * ε ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hB, hS]
  have e1 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  have e2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by positivity)
  rw [Real.sqrt_le_left (by positivity)]
  have : 0 ≤ ε * (Real.sqrt s * Real.sqrt B - S) :=
    mul_nonneg hε (by linarith)
  nlinarith

theorem half_LB2_ge (s p : ℕ) (hs : 2 ≤ s) (hp : 1 ≤ p) (M2 : Fin s → Fin s → ℤ) :
    halfLam M2 - Real.sqrt s * ((halfA2 M2 : ℝ) + 1) / p ≤ halfLB2 p M2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set ε := ((halfA2 M2 : ℝ) + 1) / p with hεdef
  have hε : 0 ≤ ε := by positivity
  have hrw : Real.sqrt s * ((halfA2 M2 : ℝ) + 1) / p = Real.sqrt s * ε := by
    rw [hεdef, mul_div_assoc]
  rw [hrw]
  apply le_halfLB2_of p M2 _ (by omega)
  · have h1 := (half_lam_le s hs M2).trans (min_le_right _ _)
    have h2 : 0 ≤ Real.sqrt s * ε := by positivity
    linarith [sqrt_two_le_two]
  · intro E hE
    have hl := halfLam_le_of M2 E hE
    have hE2 := (mem_halfSteps.mp hE).1
    have := sqrt_sum_sq_le_add (fun c => halfEllInf M2 E c) (fun c => halfEll p M2 E c) ε
      (ellInf_nonneg M2 E) (ell_nonneg p M2 E) hε
      (fun c => by
        show halfEllInf M2 E c ≤ halfEll p M2 E c + ε
        have := ell_ge_inf_sub_A p hp M2 E hE2 c; linarith)
    linarith

end

end Z3NetHL.Proofs
