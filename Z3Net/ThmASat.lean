/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmADefs
public import Z3Net.FTsk

@[expose] public section

/-!
# Theorem A, part 1: `ℤ[1/n!]`, the nodes, and `lem:sat` (the lattice of admissible columns)

V14 stage S3.

* `ι : R_S → ℚ` is injective, its range is `InRS`; the integers `0 < |a| ≤ n` are units of `R_S`;
  the places `∞, 0, …, n` are admissible over `R_S` (`placesOK`); `ι` maps the weights and nodes
  of `prop:Ns` over `R_S` to those over `ℚ`.
* `colPoly d E` is the polynomial of a column (Lagrange interpolation at the `s - 1` distinct
  nodes); `InLam d j E ↔ E d = 0 ∧ natDegree (colPoly d E) ≤ j` for `j ≤ s - 2`.
* `lem:sat` (i)–(iv): `sat_poly_core`, `sat_gamma_core`, `sat_adm_core`, `sat_basis_core`,
  `sat_coset_core`.
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

/-! ## `R_S = ℤ[1/n!]` inside `ℚ` -/

lemma nf_ne_zero (s : ℕ) : ((((s - 2).factorial : ℕ) : ℤ) : ℚ) ≠ 0 := by
  have := Nat.factorial_pos (s - 2)
  exact_mod_cast this.ne'

/-- The embedding `ℤ[1/n!] → ℚ`. -/
def ι (s : ℕ) : RS s →+* ℚ :=
  IsLocalization.Away.lift ((((s - 2).factorial : ℕ) : ℤ)) (g := Int.castRingHom ℚ)
    (by simpa using (nf_ne_zero s))

lemma ι_alg (s : ℕ) (z : ℤ) : ι s (algebraMap ℤ (RS s) z) = z := by
  unfold ι
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp

lemma ι_inj (s : ℕ) : Function.Injective (ι s) := by
  unfold ι
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    have := IsLocalization.injective (M := Submonoid.powers ((((s - 2).factorial : ℕ) : ℤ))) (RS s)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by
        have := Nat.factorial_pos (s - 2); exact_mod_cast this.ne')) h
    simp [this]
  · intro h
    have hx : (x : ℚ) = y := by simpa using h
    have : x = y := by exact_mod_cast hx
    rw [this]

lemma unit_nf (s : ℕ) : IsUnit ((((s - 2).factorial : ℕ) : ℤ) : RS s) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := RS s) ((((s - 2).factorial : ℕ) : ℤ))
  simpa using h

/-- Integers `0 < |a| ≤ s - 2` are units of `R_S`. -/
lemma unit_int (s : ℕ) (a : ℤ) (ha : a ≠ 0) (hle : a.natAbs ≤ s - 2) : IsUnit (a : RS s) := by
  have hdvd : a.natAbs ∣ (s - 2).factorial := Nat.dvd_factorial (Int.natAbs_pos.mpr ha) hle
  obtain ⟨b, hb⟩ := hdvd
  have hb' : (((s - 2).factorial : ℕ) : ℤ) = (a.natAbs : ℤ) * (b : ℤ) := by exact_mod_cast hb
  have h1 := congrArg (fun z : ℤ => (z : RS s)) hb'
  simp only [Int.cast_mul] at h1
  have hu := unit_nf s
  rw [h1] at hu
  have h2 := isUnit_of_mul_isUnit_left hu
  rcases Int.natAbs_eq a with h | h
  · rw [h]; exact h2
  · rw [h, Int.cast_neg]; exact h2.neg

lemma ι_inv (s : ℕ) (a : RS s) (h : IsUnit a) : ι s (Ring.inverse a) = (ι s a)⁻¹ := by
  have h1 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel _ h
  have h2 := congrArg (ι s) h1
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

lemma inRS_iff (s : ℕ) (a : ℚ) : InRS s a ↔ a ∈ Set.range (ι s) := by
  constructor
  · rintro ⟨z, e, rfl⟩
    refine ⟨algebraMap ℤ (RS s) z * Ring.inverse ((((s - 2).factorial : ℕ) : ℤ) : RS s) ^ e, ?_⟩
    rw [map_mul, map_pow, ι_inv s _ (unit_nf s), ι_alg]
    have : ι s ((((s - 2).factorial : ℕ) : ℤ) : RS s) = (((s - 2).factorial : ℕ) : ℚ) := by
      rw [map_intCast]; push_cast; ring
    rw [this, div_eq_mul_inv, inv_pow]
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨z, m⟩, hzm⟩ := IsLocalization.surj (Submonoid.powers ((((s - 2).factorial : ℕ) : ℤ))) r
    obtain ⟨e, he⟩ := m.prop
    refine ⟨z, e, ?_⟩
    have h := congrArg (ι s) hzm
    rw [map_mul, ι_alg, ι_alg] at h
    simp only at h
    rw [← he] at h
    have hne : ((((((s - 2).factorial : ℕ) : ℤ) ^ e : ℤ)) : ℚ) ≠ 0 := by
      have := nf_ne_zero s; exact_mod_cast pow_ne_zero e (by exact_mod_cast this)
    rw [eq_div_iff (by push_cast at hne ⊢; exact hne)]
    push_cast at h ⊢
    exact h

lemma inRS_int (s : ℕ) (z : ℤ) : InRS s (z : ℚ) := ⟨z, 0, by simp⟩

lemma inRS_mul {s : ℕ} {a b : ℚ} (ha : InRS s a) (hb : InRS s b) : InRS s (a * b) := by
  rw [inRS_iff] at *
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, map_mul _ _ _⟩

lemma inRS_add {s : ℕ} {a b : ℚ} (ha : InRS s a) (hb : InRS s b) : InRS s (a + b) := by
  rw [inRS_iff] at *
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add _ _ _⟩

/-! ## The places and the nodes -/

variable {s : ℕ} [NeZero s]

lemma placesOK (hs : 2 ≤ s) : PlacesOK (0 : Fin s) (placeA : Fin s → RS s) := by
  intro c d hc hd hcd
  have hc' : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
  have hd' : (d : ℕ) ≠ 0 := fun h => hd (Fin.ext h)
  have hcd' : (c : ℕ) ≠ (d : ℕ) := fun h => hcd (Fin.ext h)
  have e : (placeA c : RS s) - placeA d = (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) : ℤ) := by
    simp [placeA]
  rw [e]
  apply unit_int s
  · omega
  · have := c.isLt; have := d.isLt; omega

lemma ι_place (c : Fin s) : ι s (placeA c) = placeA c := by
  simp [placeA]

lemma ι_wN (hs : 2 ≤ s) (c d : Fin s) (hcd : c ≠ d) :
    ι s (wN (0 : Fin s) (placeA : Fin s → RS s) c d) = wQ c d := by
  unfold wQ wN
  split_ifs with h
  · simp
  · push Not at h
    rw [ι_inv s _ (placesOK hs c d h.1 h.2 hcd), map_sub, ι_place, ι_place, Ring.inverse_eq_inv']

lemma ι_yN (hs : 2 ≤ s) (c d : Fin s) (hcd : c ≠ d) :
    ι s (yN (0 : Fin s) (placeA : Fin s → RS s) c d) = yQ c d := by
  unfold yQ yN
  split_ifs with h1 h2
  · simp
  · exact ι_place c
  · rw [ι_inv s _ (placesOK hs c d h1 h2 hcd), map_sub, ι_place, ι_place, Ring.inverse_eq_inv']

lemma wQ_unit_RS (hs : 2 ≤ s) (c d : Fin s) (hcd : c ≠ d) :
    InRS s (wQ c d) ∧ InRS s (wQ c d)⁻¹ ∧ wQ c d ≠ 0 := by
  have hu := Z3NetF.Proofs.wN_unit (0 : Fin s) (placeA : Fin s → RS s) (placesOK hs) c d hcd
  refine ⟨(inRS_iff s _).2 ⟨_, ι_wN hs c d hcd⟩,
    (inRS_iff s _).2 ⟨Ring.inverse (wN (0 : Fin s) (placeA : Fin s → RS s) c d), ?_⟩, ?_⟩
  · rw [ι_inv s _ hu, ι_wN hs c d hcd]
  · rw [← ι_wN hs c d hcd]
    intro h
    obtain ⟨u, hu'⟩ := hu
    have := congrArg (ι s) (u.mul_inv)
    rw [map_mul, map_one, hu', h, zero_mul] at this
    exact zero_ne_one this

lemma yQ_RS (hs : 2 ≤ s) (c d : Fin s) (hcd : c ≠ d) : InRS s (yQ c d) :=
  (inRS_iff s _).2 ⟨_, ι_yN hs c d hcd⟩

lemma yQ_sub_RS (hs : 2 ≤ s) (d c c' : Fin s) (hc : c ≠ d) (hc' : c' ≠ d) (hcc' : c ≠ c') :
    InRS s (yQ c d - yQ c' d)⁻¹ ∧ yQ c d - yQ c' d ≠ 0 := by
  have hu := Z3NetF.Proofs.yN_sub_unit (0 : Fin s) (placeA : Fin s → RS s) (placesOK hs) d c c' hc hc' hcc'
  have e : ι s (yN (0 : Fin s) (placeA : Fin s → RS s) c d - yN 0 placeA c' d) = yQ c d - yQ c' d := by
    rw [map_sub, ι_yN hs c d hc, ι_yN hs c' d hc']
  refine ⟨(inRS_iff s _).2 ⟨Ring.inverse _, by rw [ι_inv s _ hu, e]⟩, ?_⟩
  rw [← e]
  intro h
  obtain ⟨u, hu'⟩ := hu
  have := congrArg (ι s) (u.mul_inv)
  rw [map_mul, map_one, hu', h, zero_mul] at this
  exact zero_ne_one this

lemma yQ_injOn (hs : 2 ≤ s) (d : Fin s) :
    Set.InjOn (fun c => yQ c d) ↑(univ.filter fun c : Fin s => c ≠ d) := by
  intro c hc c' hc' h
  by_contra hne
  simp only [coe_filter, mem_univ, true_and] at hc hc'
  exact (yQ_sub_RS hs d c c' hc hc' hne).2 (sub_eq_zero.mpr h)

lemma card_rows (d : Fin s) : (univ.filter fun c : Fin s => c ≠ d).card = s - 1 := by
  rw [Finset.filter_ne' univ d, card_erase_of_mem (mem_univ d), card_univ, Fintype.card_fin]

/-! ## The polynomial of a column -/

lemma colPoly_eval (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℚ) (c : Fin s) (hc : c ≠ d) :
    (colPoly d E).eval (yQ c d) = E c / wQ c d := by
  unfold colPoly
  exact Lagrange.eval_interpolate_at_node _ (yQ_injOn hs d) (by simpa using hc)

lemma colPoly_rep (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℚ) (c : Fin s) (hc : c ≠ d) :
    E c = wQ c d * (colPoly d E).eval (yQ c d) := by
  rw [colPoly_eval hs d E c hc, mul_div_cancel₀ _ (wQ_unit_RS hs c d hc).2.2]

lemma colPoly_degree (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℚ) :
    (colPoly d E).degree < ((s - 1 : ℕ) : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (r := fun c => E c / wQ c d) (yQ_injOn hs d)
  rwa [card_rows] at this

lemma colPoly_natDegree (hs : 3 ≤ s) (d : Fin s) (E : Fin s → ℚ) :
    (colPoly d E).natDegree ≤ s - 2 := by
  have h := colPoly_degree (by omega) d E
  by_cases h0 : colPoly d E = 0
  · rw [h0]; simp
  · rw [degree_eq_natDegree h0] at h
    have : (colPoly d E).natDegree < s - 1 := by exact_mod_cast h
    omega

/-- Uniqueness: a polynomial of degree `< s - 1` representing `E` is its polynomial. -/
lemma colPoly_eq (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℚ) (g : Polynomial ℚ)
    (hg : g.degree < ((s - 1 : ℕ) : WithBot ℕ)) (h : ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) :
    g = colPoly d E := by
  unfold colPoly
  apply Lagrange.eq_interpolate_of_eval_eq _ (yQ_injOn hs d) (by rwa [card_rows])
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc
  rw [h c hc, mul_div_cancel_left₀ _ (wQ_unit_RS hs c d hc).2.2]

lemma deg_lt_of_natDeg_le (hs : 3 ≤ s) {g : Polynomial ℚ} {j : ℕ} (hj : j ≤ s - 2)
    (hg : g.natDegree ≤ j) : g.degree < ((s - 1 : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_le_of_natDegree_le hg) ?_
  exact_mod_cast (show j < s - 1 by omega)

lemma colPoly_eq' (hs : 3 ≤ s) (d : Fin s) (E : Fin s → ℚ) (g : Polynomial ℚ) {j : ℕ}
    (hj : j ≤ s - 2) (hg : g.natDegree ≤ j) (h : ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) :
    g = colPoly d E :=
  colPoly_eq (by omega) d E g (deg_lt_of_natDeg_le hs hj hg) h

lemma colPoly_add (d : Fin s) (E F : Fin s → ℚ) :
    colPoly d (E + F) = colPoly d E + colPoly d F := by
  unfold colPoly
  rw [← map_add]
  congr 1
  funext c
  simp [add_div]

lemma colPoly_smul (d : Fin s) (a : ℚ) (E : Fin s → ℚ) :
    colPoly d (a • E) = a • colPoly d E := by
  unfold colPoly
  rw [← map_smul]
  congr 1
  funext c
  simp [mul_div_assoc]

lemma colPoly_sum (d : Fin s) (T : Finset ℕ) (u : ℕ → ℚ) (B : ℕ → Fin s → ℚ) :
    colPoly d (∑ i ∈ T, u i • B i) = ∑ i ∈ T, u i • colPoly d (B i) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    unfold colPoly
    have : (fun c : Fin s => (0 : Fin s → ℚ) c / wQ c d) = 0 := by funext c; simp
    rw [this, map_zero]
  | insert a T ha ih => rw [sum_insert ha, sum_insert ha, colPoly_add, colPoly_smul, ih]

lemma colPoly_zero (d : Fin s) : colPoly d 0 = 0 := by
  simpa using colPoly_sum d ∅ (fun _ => 0) (fun _ => 0)

/-! ## `Λ_j` and `κ_j` -/

lemma inLam_iff (hs : 3 ≤ s) {d : Fin s} {j : ℕ} (hj : j ≤ s - 2) (E : Fin s → ℤ) :
    InLam d j E ↔ E d = 0 ∧ (colPoly d fun c => (E c : ℚ)).natDegree ≤ j := by
  constructor
  · rintro ⟨h0, g, hg, hrep⟩
    refine ⟨h0, ?_⟩
    rw [← colPoly_eq' hs d _ g hj hg hrep]
    exact hg
  · rintro ⟨h0, hdeg⟩
    exact ⟨h0, _, hdeg, fun c hc => colPoly_rep (by omega) d (fun c => (E c : ℚ)) c hc⟩

lemma kappa_eq (hs : 3 ≤ s) {d : Fin s} {j : ℕ} (hj : j ≤ s - 2) (E : Fin s → ℤ)
    (g : Polynomial ℚ) (hg : g.natDegree ≤ j)
    (hrep : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)) : kappa d j E = g.coeff j := by
  unfold kappa
  rw [← colPoly_eq' hs d _ g hj hg hrep]

lemma castE_add (E F : Fin s → ℤ) :
    (fun c => ((E + F) c : ℚ)) = (fun c => (E c : ℚ)) + fun c => (F c : ℚ) := by
  funext c; simp

lemma castE_zsmul (z : ℤ) (E : Fin s → ℤ) :
    (fun c => ((z • E) c : ℚ)) = (z : ℚ) • fun c => (E c : ℚ) := by
  funext c; simp

lemma kappa_add (d : Fin s) (j : ℕ) (E F : Fin s → ℤ) :
    kappa d j (E + F) = kappa d j E + kappa d j F := by
  unfold kappa; rw [castE_add, colPoly_add, coeff_add]

lemma kappa_zsmul (d : Fin s) (j : ℕ) (z : ℤ) (E : Fin s → ℤ) :
    kappa d j (z • E) = z * kappa d j E := by
  unfold kappa; rw [castE_zsmul, colPoly_smul, coeff_smul, smul_eq_mul]

lemma kappa_sub (d : Fin s) (j : ℕ) (E F : Fin s → ℤ) :
    kappa d j (E - F) = kappa d j E - kappa d j F := by
  have := kappa_add d j (E - F) F
  rw [sub_add_cancel] at this
  linarith

lemma kappa_zero (d : Fin s) (j : ℕ) : kappa d j 0 = 0 := by
  have := kappa_add d j 0 0
  simp only [add_zero] at this
  linarith

lemma kappa_sum (d : Fin s) (j : ℕ) (T : Finset ℕ) (t : ℕ → ℤ) (B : ℕ → Fin s → ℤ) :
    kappa d j (∑ i ∈ T, t i • B i) = ∑ i ∈ T, (t i : ℚ) * kappa d j (B i) := by
  induction T using Finset.induction_on with
  | empty => simpa using kappa_zero d j
  | insert a T ha ih => rw [sum_insert ha, sum_insert ha, kappa_add, kappa_zsmul, ih]

lemma inLam_zero (d : Fin s) (j : ℕ) : InLam d j 0 :=
  ⟨rfl, 0, by simp, fun c _ => by simp⟩

lemma inLam_add {d : Fin s} {j : ℕ} {E F : Fin s → ℤ} (hE : InLam d j E) (hF : InLam d j F) :
    InLam d j (E + F) := by
  obtain ⟨h0, g, hg, hr⟩ := hE
  obtain ⟨h0', g', hg', hr'⟩ := hF
  refine ⟨by simp [h0, h0'], g + g', (natDegree_add_le _ _).trans (max_le hg hg'), fun c hc => ?_⟩
  rw [Pi.add_apply, Int.cast_add, hr c hc, hr' c hc, eval_add]
  ring

lemma inLam_zsmul {d : Fin s} {j : ℕ} (z : ℤ) {E : Fin s → ℤ} (hE : InLam d j E) :
    InLam d j (z • E) := by
  obtain ⟨h0, g, hg, hr⟩ := hE
  refine ⟨by simp [h0], C (z : ℚ) * g, (natDegree_C_mul_le _ _).trans hg, fun c hc => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul, hr c hc, eval_mul, eval_C]
  ring

lemma inLam_neg {d : Fin s} {j : ℕ} {E : Fin s → ℤ} (hE : InLam d j E) : InLam d j (-E) := by
  have := inLam_zsmul (-1) hE
  simpa using this

lemma inLam_sub {d : Fin s} {j : ℕ} {E F : Fin s → ℤ} (hE : InLam d j E) (hF : InLam d j F) :
    InLam d j (E - F) := by
  rw [sub_eq_add_neg]; exact inLam_add hE (inLam_neg hF)

lemma inLam_mono {d : Fin s} {i j : ℕ} (hij : i ≤ j) {E : Fin s → ℤ} (hE : InLam d i E) :
    InLam d j E := by
  obtain ⟨h0, g, hg, hr⟩ := hE
  exact ⟨h0, g, hg.trans hij, hr⟩

lemma inLam_sum {d : Fin s} {j : ℕ} (T : Finset ℕ) (t : ℕ → ℤ) (B : ℕ → Fin s → ℤ)
    (hB : ∀ i ∈ T, InLam d j (B i)) : InLam d j (∑ i ∈ T, t i • B i) := by
  induction T using Finset.induction_on with
  | empty => simpa using inLam_zero d j
  | insert a T ha ih =>
    rw [sum_insert ha]
    exact inLam_add (inLam_zsmul _ (hB a (mem_insert_self a T)))
      (ih fun i hi => hB i (mem_insert_of_mem hi))

/-- `κ_j` vanishes on `Λ_i`, `i < j`. -/
lemma kappa_low (hs : 3 ≤ s) {d : Fin s} {i j : ℕ} (hij : i < j) (hj : j ≤ s - 2) {E : Fin s → ℤ}
    (hE : InLam d i E) : kappa d j E = 0 := by
  have h := ((inLam_iff hs (show i ≤ s - 2 by omega) E).1 hE).2
  unfold kappa
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hij)

/-- `Λ_{j+1} ∩ ker κ_{j+1} ⊆ Λ_j`. -/
lemma inLam_of_kappa_zero (hs : 3 ≤ s) {d : Fin s} {j : ℕ} (hj : j + 1 ≤ s - 2) {E : Fin s → ℤ}
    (hE : InLam d (j + 1) E) (hk : kappa d (j + 1) E = 0) : InLam d j E := by
  rw [inLam_iff hs hj] at hE
  rw [inLam_iff hs (by omega)]
  refine ⟨hE.1, ?_⟩
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hE.2 h)
  · have : N = j + 1 := by omega
    subst this; exact hk

/-- `Λ_0 ∩ ker κ_0 = 0`. -/
lemma eq_zero_of_kappa_zero (hs : 3 ≤ s) {d : Fin s} {E : Fin s → ℤ} (hE : InLam d 0 E)
    (hk : kappa d 0 E = 0) : E = 0 := by
  rw [inLam_iff hs (by omega)] at hE
  have hc : (colPoly d fun c => (E c : ℚ)) = 0 := by
    rw [eq_C_of_natDegree_le_zero hE.2]
    unfold kappa at hk
    rw [hk, map_zero]
  funext c
  by_cases hcd : c = d
  · rw [hcd]; exact hE.1
  · have := colPoly_rep (by omega) d (fun c => (E c : ℚ)) c hcd
    rw [hc, eval_zero, mul_zero] at this
    simp only [Pi.zero_apply]
    exact_mod_cast this

/-! ## `lem:sat`(i): the coefficients lie in `R_S` -/

lemma mem_lr_C {a : ℚ} (ha : InRS s a) : C a ∈ liftsRing (ι s) := by
  obtain ⟨r, rfl⟩ := (inRS_iff s a).1 ha
  rw [← lifts_iff_liftsRing]; exact C_mem_lifts _ r

lemma colPoly_lifts (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℤ) :
    (colPoly d fun c => (E c : ℚ)) ∈ liftsRing (ι s) := by
  unfold colPoly
  rw [Lagrange.interpolate_apply]
  refine Subring.sum_mem _ fun c hc => Subring.mul_mem _ ?_ ?_
  · simp only [mem_filter, mem_univ, true_and] at hc
    apply mem_lr_C
    rw [div_eq_mul_inv]
    exact inRS_mul (inRS_int s _) (wQ_unit_RS hs c d hc).2.1
  · simp only [mem_filter, mem_univ, true_and] at hc
    unfold Lagrange.basis
    refine Subring.prod_mem _ fun c' hc' => ?_
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hc'
    unfold Lagrange.basisDivisor
    refine Subring.mul_mem _ (mem_lr_C (yQ_sub_RS hs d c c' hc hc'.2 (Ne.symm hc'.1)).1) ?_
    refine Subring.sub_mem _ ?_ (mem_lr_C (yQ_RS hs c' d hc'.2))
    rw [← lifts_iff_liftsRing]; exact X_mem_lifts _

lemma colPoly_coeff_RS (hs : 2 ≤ s) (d : Fin s) (E : Fin s → ℤ) (i : ℕ) :
    InRS s ((colPoly d fun c => (E c : ℚ)).coeff i) := by
  have h := colPoly_lifts hs d E
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at h
  exact (inRS_iff s _).2 (h i)

theorem sat_poly_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (E : Fin s → ℤ)
    (g : Polynomial ℚ) (hg : g.natDegree ≤ j)
    (hrep : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)) (i : ℕ) : InRS s (g.coeff i) := by
  rw [colPoly_eq' hs d _ g hj hg hrep]
  exact colPoly_coeff_RS (by omega) d E i

lemma kappa_RS (hs : 2 ≤ s) (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : InRS s (kappa d j E) :=
  colPoly_coeff_RS hs d E j

/-! ## `lem:sat`(ii): `κ_j(Λ_j) = γ_j ℤ` -/

/-- `κ_j` has bounded denominators: `D κ_j(E) ∈ ℤ` for one `D > 0` and all `E`. -/
lemma kappa_den (d : Fin s) (j : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ E : Fin s → ℤ, ∃ z : ℤ, (D : ℚ) * kappa d j E = z := by
  set T := univ.filter fun c : Fin s => c ≠ d
  set a : Fin s → ℚ := fun c => (wQ c d)⁻¹ * (Lagrange.basis T (fun c => yQ c d) c).coeff j
  have hk : ∀ E : Fin s → ℤ, kappa d j E = ∑ c ∈ T, (E c : ℚ) * a c := by
    intro E
    unfold kappa colPoly
    rw [Lagrange.interpolate_apply, finsetSum_coeff]
    refine sum_congr rfl fun c _ => ?_
    rw [coeff_C_mul]
    simp only [a]; ring
  refine ⟨∏ c ∈ T, (a c).den, prod_pos fun c _ => (a c).den_pos, fun E => ?_⟩
  have hint : ∀ c ∈ T, ∃ z : ℤ, ((∏ c ∈ T, (a c).den : ℕ) : ℚ) * a c = z := by
    intro c hc
    obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun c => (a c).den) hc
    refine ⟨(m : ℤ) * (a c).num, ?_⟩
    rw [hm]
    have h1 : (a c).num / ((a c).den : ℚ) = a c := Rat.num_div_den (a c)
    have h2 : ((a c).den : ℚ) ≠ 0 := by exact_mod_cast (a c).den_pos.ne'
    have h3 : ((a c).num : ℚ) = a c * (a c).den := by rw [div_eq_iff h2] at h1; exact h1
    push_cast
    rw [h3]; ring
  choose! z hz using hint
  refine ⟨∑ c ∈ T, E c * z c, ?_⟩
  rw [hk, mul_sum]
  push_cast
  refine sum_congr rfl fun c hc => ?_
  rw [← hz c hc]; push_cast; ring

/-- `n!^(j+1) (w_c y_c^j)_c` is an integer vector of `Λ_j` with `κ_j = n!^(j+1)`. -/
lemma nf_w_int (c d : Fin s) (hcd : c ≠ d) :
    ∃ z : ℤ, (z : ℚ) = (((s - 2).factorial : ℕ) : ℚ) * wQ c d := by
  unfold wQ wN
  split_ifs with h
  · exact ⟨((s - 2).factorial : ℕ), by simp⟩
  · push Not at h
    have hc' : (c : ℕ) ≠ 0 := fun e => h.1 (Fin.ext e)
    have hd' : (d : ℕ) ≠ 0 := fun e => h.2 (Fin.ext e)
    have hcd' : (c : ℕ) ≠ (d : ℕ) := fun e => hcd (Fin.ext e)
    set a : ℤ := ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)
    have ha : a ≠ 0 := by simp only [a]; omega
    have hle : a.natAbs ≤ s - 2 := by have := c.isLt; have := d.isLt; simp only [a]; omega
    have hdN := Nat.dvd_factorial (Int.natAbs_pos.mpr ha) hle
    have hdZ : a ∣ (((s - 2).factorial : ℕ) : ℤ) := Int.natAbs_dvd.mp (by exact_mod_cast hdN)
    obtain ⟨m, hm⟩ := hdZ
    have e1 : (placeA c : ℚ) - placeA d = (a : ℚ) := by simp [placeA, a]
    rw [Ring.inverse_eq_inv', e1]
    refine ⟨m, ?_⟩
    have hmq : ((((s - 2).factorial : ℕ) : ℤ) : ℚ) = (a : ℚ) * m := by exact_mod_cast hm
    have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    push_cast at hmq
    rw [hmq]; field_simp

lemma nf_y_int (c d : Fin s) (hcd : c ≠ d) :
    ∃ z : ℤ, (z : ℚ) = (((s - 2).factorial : ℕ) : ℚ) * yQ c d := by
  unfold yQ yN
  split_ifs with h1 h2
  · exact ⟨0, by simp⟩
  · exact ⟨(((s - 2).factorial : ℕ) : ℤ) * (((c : ℕ) : ℤ) - 1), by simp [placeA]⟩
  · have := nf_w_int c d hcd
    unfold wQ wN at this
    have hn : ¬ ((c = 0) ∨ (d = 0)) := by push Not; exact ⟨h1, h2⟩
    simpa only [hn, ite_false] using this

lemma nf_pow_mem (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ E : Fin s → ℤ, InLam d j E ∧ kappa d j E = (((s - 2).factorial : ℕ) : ℚ) ^ (j + 1) := by
  have hw : ∀ c, ∃ z : ℤ, c ≠ d → (z : ℚ) = (((s - 2).factorial : ℕ) : ℚ) * wQ c d := by
    intro c
    by_cases h : c = d
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := nf_w_int c d h; exact ⟨z, fun _ => hz⟩
  have hy : ∀ c, ∃ z : ℤ, c ≠ d → (z : ℚ) = (((s - 2).factorial : ℕ) : ℚ) * yQ c d := by
    intro c
    by_cases h : c = d
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := nf_y_int c d h; exact ⟨z, fun _ => hz⟩
  choose zw hzw using hw
  choose zy hzy using hy
  set g : Polynomial ℚ := C ((((s - 2).factorial : ℕ) : ℚ) ^ (j + 1)) * X ^ j
  have hg : g.natDegree ≤ j := (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le j)
  set E : Fin s → ℤ := fun c => if c = d then 0 else zw c * zy c ^ j
  have hrep : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d) := by
    intro c hc
    simp only [E, hc, ite_false, g, eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    rw [hzw c hc, hzy c hc]
    ring
  refine ⟨E, ⟨by simp [E], g, hg, hrep⟩, ?_⟩
  rw [kappa_eq hs hj E g hg hrep]
  simp only [g]
  rw [coeff_C_mul, coeff_X_pow_self, mul_one]

/-- The ideal `{D κ_j(E) : E ∈ Λ_j}` of `ℤ`. -/
def kIdeal (d : Fin s) (j D : ℕ) : Submodule ℤ ℤ where
  carrier := {z | ∃ E, InLam d j E ∧ (D : ℚ) * kappa d j E = z}
  add_mem' := by
    rintro a b ⟨E, hE, ha⟩ ⟨F, hF, hb⟩
    exact ⟨E + F, inLam_add hE hF, by rw [kappa_add, mul_add, ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨0, inLam_zero d j, by simp [kappa_zero]⟩
  smul_mem' := by
    rintro z a ⟨E, hE, h⟩
    exact ⟨z • E, inLam_zsmul z hE, by
      rw [kappa_zsmul, smul_eq_mul, show (D : ℚ) * ((z : ℚ) * kappa d j E) = z * ((D : ℚ) * kappa d j E)
        by ring, h]; push_cast; ring⟩

lemma gamma_exists (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ γ : ℚ, 0 < γ ∧ ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ := by
  obtain ⟨D, hD, hDint⟩ := kappa_den d j
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  set I := kIdeal d j D
  set g := Submodule.IsPrincipal.generator I
  have hI : ∀ z : ℤ, z ∈ I ↔ ∃ a : ℤ, a * g = z := by
    intro z
    rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton]
    simp [g]
  have hgI : ∃ E, InLam d j E ∧ (D : ℚ) * kappa d j E = g := (hI g).2 ⟨1, one_mul g⟩
  obtain ⟨Eg, hEg, hEgk⟩ := hgI
  -- `g ≠ 0`
  obtain ⟨EP, hEP, hEPk⟩ := nf_pow_mem hs d j hj
  obtain ⟨zP, hzP⟩ := hDint EP
  obtain ⟨aP, haP⟩ := (hI zP).1 ⟨EP, hEP, hzP⟩
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at haP
    rw [← haP, hEPk] at hzP
    push_cast at hzP
    exact (mul_ne_zero hDq (pow_ne_zero _ (by have := Nat.factorial_pos (s - 2); exact_mod_cast this.ne'))) hzP
  refine ⟨(|g| : ℤ) / (D : ℚ), div_pos (by exact_mod_cast abs_pos.mpr hg0) (by exact_mod_cast hD), ?_⟩
  intro t
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨z, hz⟩ := hDint E
    obtain ⟨a, ha⟩ := (hI z).1 ⟨E, hE, hz⟩
    have ht : kappa d j E = (a * g : ℤ) / (D : ℚ) := by rw [ha, ← hz]; field_simp
    rcases abs_choice g with h | h
    · exact ⟨a, by rw [ht, h]; push_cast; ring⟩
    · exact ⟨-a, by rw [ht, h]; push_cast; ring⟩
  · rintro ⟨z, rfl⟩
    have hk : kappa d j Eg = (g : ℚ) / D := by rw [← hEgk]; field_simp
    rcases abs_choice g with h | h
    · exact ⟨z • Eg, inLam_zsmul z hEg, by rw [kappa_zsmul, hk, h]⟩
    · exact ⟨(-z) • Eg, inLam_zsmul (-z) hEg, by rw [kappa_zsmul, hk, h]; push_cast; ring⟩

lemma gamS_spec (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧ ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j := by
  have h := gamma_exists hs d j hj
  unfold gamS
  simp only [h, dite_true]
  exact Classical.choose_spec h

theorem sat_gamma_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧ SUnit s (gamS d j) ∧
      ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j := by
  obtain ⟨hpos, hspec⟩ := gamS_spec hs d j hj
  refine ⟨hpos, ⟨hpos.ne', ?_, ?_⟩, hspec⟩
  · obtain ⟨E, _, hE⟩ := (hspec (gamS d j)).2 ⟨1, by simp⟩
    rw [← hE]; exact kappa_RS (by omega) d j E
  · obtain ⟨E, hE, hEk⟩ := nf_pow_mem hs d j hj
    obtain ⟨z, hz⟩ := (hspec _).1 ⟨E, hE, hEk⟩
    refine ⟨z, j + 1, ?_⟩
    have hne : (((s - 2).factorial : ℕ) : ℚ) ^ (j + 1) ≠ 0 :=
      pow_ne_zero _ (by have := Nat.factorial_pos (s - 2); exact_mod_cast this.ne')
    rw [eq_div_iff hne, hz]
    field_simp

lemma kappa_mem (hs : 3 ≤ s) {d : Fin s} {j : ℕ} (hj : j ≤ s - 2) {E : Fin s → ℤ}
    (hE : InLam d j E) : ∃ z : ℤ, kappa d j E = z * gamS d j :=
  ((gamS_spec hs d j hj).2 _).1 ⟨E, hE, rfl⟩

/-! ## `lem:sat`(iii): admissible columns -/

theorem sat_adm_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (E : Fin s → ℤ) :
    AdmCol d j E ↔ InLam d j E ∧ SUnit s (kappa d j E) := by
  constructor
  · rintro ⟨h0, g, hg, _, hlc, hrep⟩
    refine ⟨⟨h0, g, hg.le, hrep⟩, ?_⟩
    rw [kappa_eq hs hj E g hg.le hrep, ← hg]
    exact hlc
  · rintro ⟨hE, hk⟩
    have hE' := hE
    rw [inLam_iff hs hj] at hE'
    have hdeg : (colPoly d fun c => (E c : ℚ)).natDegree = j :=
      natDegree_eq_of_le_of_coeff_ne_zero hE'.2 hk.1
    refine ⟨hE'.1, _, hdeg, colPoly_coeff_RS (by omega) d E, ?_,
      fun c hc => colPoly_rep (by omega) d (fun c => (E c : ℚ)) c hc⟩
    rw [leadingCoeff, hdeg]
    exact hk

/-! ## `lem:sat`(iv): the flag basis -/

/-- The hypothesis of `lem:sat`(iv): `E_i ∈ Λ_i` with `κ_i(E_i) = γ_i`, `i ≤ j`. -/
def FlagOK (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i

lemma basis_exists (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) :
    ∀ j, j ≤ s - 2 → FlagOK d B j → ∀ F, InLam d j F →
      ∃ t : ℕ → ℤ, F = ∑ i ∈ range (j + 1), t i • B i := by
  intro j
  induction j with
  | zero =>
    intro hj hB F hF
    obtain ⟨z, hz⟩ := kappa_mem hs hj hF
    have h0 : F - z • B 0 = 0 := by
      apply eq_zero_of_kappa_zero hs (inLam_sub hF (inLam_zsmul z (hB 0 le_rfl).1))
      rw [kappa_sub, kappa_zsmul, (hB 0 le_rfl).2, hz]; ring
    exact ⟨fun _ => z, by simp [sub_eq_zero.mp h0]⟩
  | succ j ih =>
    intro hj hB F hF
    obtain ⟨z, hz⟩ := kappa_mem hs hj hF
    have hF' : InLam d j (F - z • B (j + 1)) := by
      apply inLam_of_kappa_zero hs hj (inLam_sub hF (inLam_zsmul z (hB (j + 1) le_rfl).1))
      rw [kappa_sub, kappa_zsmul, (hB (j + 1) le_rfl).2, hz]; ring
    obtain ⟨t, ht⟩ := ih (by omega) (fun i hi => hB i (by omega)) _ hF'
    refine ⟨fun i => if i = j + 1 then z else t i, ?_⟩
    have hsum : ∑ i ∈ range (j + 1 + 1), (if i = j + 1 then z else t i) • B i =
        ∑ i ∈ range (j + 1), t i • B i + z • B (j + 1) := by
      rw [sum_range_succ]
      congr 1
      · exact sum_congr rfl fun i hi => by
          simp only [mem_range] at hi; simp [show i ≠ j + 1 by omega]
      · simp
    rw [hsum, ← ht]; abel

lemma basis_indep (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) :
    ∀ j, j ≤ s - 2 → FlagOK d B j → ∀ t : ℕ → ℤ, ∑ i ∈ range (j + 1), t i • B i = 0 →
      ∀ i ≤ j, t i = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ hB t ht i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have h := congrArg (kappa d 0) ht
    rw [sum_range_one, kappa_zsmul, (hB 0 le_rfl).2, kappa_zero] at h
    have hpos := (gamS_spec hs d 0 (by omega)).1
    exact_mod_cast (mul_eq_zero.mp h).resolve_right hpos.ne'
  | succ j ih =>
    intro hj hB t ht
    have htop : t (j + 1) = 0 := by
      have h := congrArg (kappa d (j + 1)) ht
      rw [sum_range_succ, kappa_add, kappa_zsmul, (hB (j + 1) le_rfl).2, kappa_zero, kappa_sum] at h
      have hlow : ∑ i ∈ range (j + 1), (t i : ℚ) * kappa d (j + 1) (B i) = 0 :=
        sum_eq_zero fun i hi => by
          rw [kappa_low hs (show i < j + 1 by simpa using hi) hj (hB i (by simp at hi; omega)).1,
            mul_zero]
      rw [hlow, zero_add] at h
      have hpos := (gamS_spec hs d (j + 1) hj).1
      exact_mod_cast (mul_eq_zero.mp h).resolve_right hpos.ne'
    have ht' : ∑ i ∈ range (j + 1), t i • B i = 0 := by
      rw [sum_range_succ, htop, zero_smul, add_zero] at ht; exact ht
    intro i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact ih (by omega) (fun i hi => hB i (by omega)) t ht' i (by omega)
    · rw [show i = j + 1 by omega]; exact htop

theorem sat_basis_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (B : ℕ → Fin s → ℤ)
    (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) :
    (∀ F, InLam d j F ↔ ∃ t : ℕ → ℤ, F = ∑ i ∈ range (j + 1), t i • B i) ∧
      ∀ t t' : ℕ → ℤ, ∑ i ∈ range (j + 1), t i • B i = ∑ i ∈ range (j + 1), t' i • B i →
        ∀ i ≤ j, t i = t' i := by
  refine ⟨fun F => ⟨basis_exists hs d B j hj hB F, ?_⟩, ?_⟩
  · rintro ⟨t, rfl⟩
    exact inLam_sum _ t B fun i hi => inLam_mono (by simp at hi; omega) (hB i (by simp at hi; omega)).1
  · intro t t' h i hi
    have h' : ∑ i ∈ range (j + 1), (t - t') i • B i = 0 := by
      simp only [Pi.sub_apply, sub_smul, sum_sub_distrib, h, sub_self]
    have := basis_indep hs d B j hj hB (t - t') h' i hi
    simpa [sub_eq_zero] using this

theorem sat_coset_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (B : ℕ → Fin s → ℤ)
    (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) (F : Fin s → ℤ) :
    (InLam d j F ∧ kappa d j F = gamS d j) ↔
      ∃ t : ℕ → ℤ, F - B j = ∑ i ∈ range j, t i • B i := by
  constructor
  · rintro ⟨hF, hk⟩
    have hD : InLam d j (F - B j) := inLam_sub hF (hB j le_rfl).1
    have hDk : kappa d j (F - B j) = 0 := by rw [kappa_sub, hk, (hB j le_rfl).2, sub_self]
    rcases j with _ | j
    · exact ⟨fun _ => 0, by simp [eq_zero_of_kappa_zero hs hD hDk]⟩
    · exact basis_exists hs d B j (by omega) (fun i hi => hB i (by omega)) _
        (inLam_of_kappa_zero hs hj hD hDk)
  · rintro ⟨t, ht⟩
    have hF : F = B j + ∑ i ∈ range j, t i • B i := by rw [← ht]; abel
    have hsum : InLam d j (∑ i ∈ range j, t i • B i) :=
      inLam_sum _ t B fun i hi => inLam_mono (by simp at hi; omega) (hB i (by simp at hi; omega)).1
    refine ⟨by rw [hF]; exact inLam_add (hB j le_rfl).1 hsum, ?_⟩
    rw [hF, kappa_add, kappa_sum, (hB j le_rfl).2]
    have : ∑ i ∈ range j, (t i : ℚ) * kappa d j (B i) = 0 :=
      sum_eq_zero fun i hi => by
        rw [kappa_low hs (show i < j by simpa using hi) hj (hB i (by simp at hi; omega)).1, mul_zero]
    rw [this, add_zero]

end

end Z3NetA.Proofs
