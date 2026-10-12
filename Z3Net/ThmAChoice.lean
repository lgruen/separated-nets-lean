/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAThm

@[expose] public section

/-!
# The net of `def:Ns` does not depend on the choice of `U'` and `β`; uniqueness of `γ_j`

V14 stage S6b (the Palomar headline justifies its choice-defined data).

* `Ur_unique_core`: two solutions `U'`, `U''` of the residual problem (same design `F`, same
  `λ'`) agree on all entries `(n', n)` with `n', n ≤ s - 2`. Column `n` of `U'_d` solves
  `diag(λ') diag(w) V u = (F_n[c][d])_{c ≠ d}` with `V` the Vandermonde matrix of the nodes `y_c`;
  the nodes differ by units and the weights are units (`PlacesOK`), so the matrix is invertible.
* `beta_unique_core`: two `β` with the defining relation of `prop:Gs` agree for `n ≥ s - 1`,
  `i ≤ s - 2` (the uniqueness half of `prop:Gs`, `Gs_beta_core`).
* `Ux_indep_core`, `PGen_indep_core`: `U'^(k)_d` reads `U'` only there and `β` only there, so the
  generator matrices of `def:Ns` are the same for every choice.
* `Apoint_indep_core`: hence `Apoint s q k` is the net of `def:Ns` built from any solution `(U', β)`
  and reduced by any ring homomorphism `R_S → ℤ/qℤ`.
* `gamS_unique_core`: the positive generator `γ_j` of `κ_j(Λ_j)` is unique (`lem:sat`(ii)).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)

/-- Column `n ≤ s - 2` of a residual solution, written over all `n' ≤ s - 2`. -/
lemma resid_col {F : ℕ → Fin s → Fin s → R} {lam : Fin s → R} {Ur : Fin s → ℕ → ℕ → R}
    (h : Z3NetF.Residual inf x F lam Ur) (d : Fin s) (n : ℕ) (hn : n < s - 1) (c : Fin s)
    (hc : c ≠ d) :
    F n c d = ∑ n' : Fin (s - 1),
      lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (n' : ℕ)) * Ur d n' n := by
  rw [h.2.2.2 c d hc n hn, Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun n' : ℕ => lam c * (Z3NetF.wN inf x c d *
      Z3NetF.yN inf x c d ^ n') * Ur d n' n) (s - 1)]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
  · intro n' hn'
    simp only [mem_sdiff, mem_range] at hn'
    rw [h.2.1 d n' n (by omega) hn'.1, mul_zero]
  · intro n' _; ring

/-- Two solutions of the residual problem agree on the entries `(n', n)`, `n', n ≤ s - 2`. -/
theorem Ur_unique_core (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur Ur' : Fin s → ℕ → ℕ → R) (h : Z3NetF.Residual inf x F lam Ur)
    (h' : Z3NetF.Residual inf x F lam Ur') (d : Fin s) (n : ℕ) (hn : n < s - 1) :
    ∀ n' < s - 1, Ur d n' n = Ur' d n' n := by
  classical
  have hcard : Fintype.card {c : Fin s // c ≠ d} = s - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  let e : Fin (s - 1) ≃ {c : Fin s // c ≠ d} := (Fintype.equivFinOfCardEq hcard).symm
  set D : Matrix (Fin (s - 1)) (Fin (s - 1)) R :=
    diagonal (fun r => lam (e r).1) * (diagonal (fun r => Z3NetF.wN inf x (e r).1 d) *
      vandermonde (fun r => Z3NetF.yN inf x (e r).1 d)) with hD
  have hdet : IsUnit D.det := by
    rw [hD, det_mul, det_mul, det_diagonal, det_diagonal, det_vandermonde]
    refine (IsUnit.prod_univ_iff.mpr fun r => h.1 _).mul ((IsUnit.prod_univ_iff.mpr fun r =>
      wN_unit inf x hx _ d (e r).2).mul ?_)
    rw [IsUnit.prod_univ_iff]; intro r
    rw [IsUnit.prod_iff]; intro r' hr'
    have hne : (e r').1 ≠ (e r).1 := by
      intro hh; have := e.injective (Subtype.ext hh); rw [this] at hr'; simp at hr'
    exact yN_sub_unit inf x hx d _ _ (e r').2 (e r).2 hne
  have hinj : Function.Injective D.mulVec := Z3Net.Proofs.mulVec_injective_of_isUnit_det D hdet
  have key : ∀ U : Fin s → ℕ → ℕ → R, Z3NetF.Residual inf x F lam U →
      D *ᵥ (fun n' : Fin (s - 1) => U d n' n) = fun r => F n (e r).1 d := by
    intro U hU
    funext r
    rw [resid_col inf x hU d n hn _ (e r).2]
    simp only [mulVec, dotProduct, hD, diagonal_mul, vandermonde_apply]
  have := hinj ((key Ur h).trans (key Ur' h').symm)
  intro n' hn'
  exact congrFun this ⟨n', hn'⟩

/-- Two `β` with the defining relation of `prop:Gs` agree for `n ≥ s - 1`, `i ≤ s - 2`. -/
theorem beta_unique_core (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur)
    (β β' : Fin s → ℕ → ℕ → R) (hβ : Z3NetF.BetaRel inf x F lam β)
    (hβ' : Z3NetF.BetaRel inf x F lam β') (d : Fin s) (n : ℕ) (hn : s - 1 ≤ n) :
    ∀ i < s - 1, β d n i = β' d n i := by
  have hP : ∀ b : Fin s → ℕ → ℕ → R, Z3NetF.BetaRel inf x F lam b → ∀ c, c ≠ d →
      lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n) =
        ∑ i : Fin (s - 1), (fun i : Fin (s - 1) => b d n i) i * F i c d := by
    intro b hb c hc
    rw [hb d n hn c hc, Finset.sum_range]
  have := (Gs_beta_core inf x hs hx F lam Ur hres d n).unique (hP β hβ) (hP β' hβ')
  intro i hi
  exact congrFun this ⟨i, hi⟩

/-- `U'^(k)_d` (`Ux`) is the same for any two choices of `(U', β)`. -/
theorem Ux_indep_core (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur Ur' β β' : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur)
    (hres' : Z3NetF.Residual inf x F lam Ur') (hβ : Z3NetF.BetaRel inf x F lam β)
    (hβ' : Z3NetF.BetaRel inf x F lam β') (d : Fin s) (n' n : ℕ) :
    Z3NetF.Ux Ur β d n' n = Z3NetF.Ux Ur' β' d n' n := by
  unfold Z3NetF.Ux
  by_cases h1 : n < s - 1
  · simp only [h1, ↓reduceIte]
    by_cases h2 : n' < s - 1
    · simp only [h2, ↓reduceIte]
      exact Ur_unique_core inf x hx F lam Ur Ur' hres hres' d n h1 n' h2
    · simp only [h2, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h3 : n' = n
    · simp only [h3, ↓reduceIte]
    · simp only [h3, ↓reduceIte]
      by_cases h4 : n' < s - 1
      · simp only [h4, ↓reduceIte]
        congr 1
        refine sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        rw [beta_unique_core inf x hs hx F lam Ur hres β β' hβ hβ' d n (by omega) i hi,
          Ur_unique_core inf x hx F lam Ur Ur' hres hres' d i hi n' h4]
      · simp only [h4, ↓reduceIte]

/-- The generator matrices of `def:Ns` are the same for any two choices of `(U', β)`. -/
theorem PGen_indep_core (hs : 2 ≤ s) (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (Ur Ur' β β' : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur)
    (hres' : Z3NetF.Residual inf x F lam Ur') (hβ : Z3NetF.BetaRel inf x F lam β)
    (hβ' : Z3NetF.BetaRel inf x F lam β') :
    Z3NetF.PGen k inf x F lam Ur β = Z3NetF.PGen k inf x F lam Ur' β' := by
  have hU : Z3NetF.Ugauge k inf x Ur β = Z3NetF.Ugauge k inf x Ur' β' := by
    funext d
    unfold Z3NetF.Ugauge
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    exact Ux_indep_core inf x hs hx F lam Ur Ur' β β' hres hres' hβ hβ' d _ _
  have hP : Z3NetF.PPhi k inf x F lam Ur β = Z3NetF.PPhi k inf x F lam Ur' β' := by
    funext c d
    simp only [Z3NetF.PPhi, hU]
  unfold Z3NetF.PGen
  rw [hP]

end

end Z3NetF.Proofs

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

/-- `Apoint` is the net of `def:Ns` for any solution `(U', β)` and any reduction `ψ`. -/
theorem Apoint_indep_core {q : ℕ} (hs : 3 ≤ s) (k : ℕ) (ψ : RS s →+* ZMod q)
    (Ur β : Fin s → ℕ → ℕ → RS s) (hres : Residual (0 : Fin s) placeA (UstarR s) 1 Ur)
    (hβ : BetaRel (0 : Fin s) placeA (UstarR s) 1 β) :
    Apoint s q k = digPoint q (s * k) (fun c =>
      (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) := by
  rw [Apoint_eq k ψ, Z3NetF.Proofs.PGen_indep_core k (0 : Fin s) (placeA : Fin s → RS s) (by omega)
    (placesOK (by omega)) (UstarR s) 1 (UrS s) Ur (betaS s) β (Ustar_data_core hs).1 hres
    (Ustar_data_core hs).2 hβ]

/-- The positive generator `γ_j` of `κ_j(Λ_j)` is unique. -/
theorem gamS_unique_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (γ : ℚ) (hγ : 0 < γ)
    (hgen : ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ) :
    γ = gamS d j := by
  obtain ⟨hpos, hspec⟩ := gamS_spec hs d j hj
  obtain ⟨z1, hz1⟩ := (hspec γ).1 ((hgen γ).2 ⟨1, by simp⟩)
  obtain ⟨z2, hz2⟩ := (hgen (gamS d j)).1 ((hspec _).2 ⟨1, by simp⟩)
  have h12 : ((z1 * z2 : ℤ) : ℚ) = 1 := by
    have h : (z1 : ℚ) * z2 * γ = 1 * γ := by rw [mul_assoc, ← hz2, ← hz1, one_mul]
    push_cast
    exact mul_right_cancel₀ hγ.ne' h
  have h12' : z1 * z2 = 1 := by exact_mod_cast h12
  have hz1pos : (0 : ℚ) < z1 := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hz1one : z1 = 1 := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hz1pos.le) h12'
  rw [hz1, hz1one]
  simp

end

end Z3NetA.Proofs

/-! ## The compared statements (restated by name) -/

namespace Z3NetF

open Matrix Finset

/-- **`prop:Gs`, `def:Ns`**, the net does not depend on the choices: for places with unit
differences (`PlacesOK`), any two solutions `U'`, `U''` of the residual problem of a design `F`
(with the same `λ'`) and any two `β`, `β'` with the defining relation of `prop:Gs` give the same
generator matrices of `𝒫^F_k`. (`U'^(k)_d` reads `U'_d` only on `n', n ≤ s - 2`, where it is unique,
and `β_n` only for `n ≥ s - 1`, where it is unique.) -/
theorem PGen_indep {R : Type*} [CommRing R] {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (inf : Fin s)
    (x : Fin s → R) (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur Ur' β β' : Fin s → ℕ → ℕ → R) (hres : Residual inf x F lam Ur)
    (hres' : Residual inf x F lam Ur') (hβ : BetaRel inf x F lam β)
    (hβ' : BetaRel inf x F lam β') :
    PGen k inf x F lam Ur β = PGen k inf x F lam Ur' β' :=
  Proofs.PGen_indep_core k inf x hs hx F lam Ur Ur' β β' hres hres' hβ hβ'

end Z3NetF

namespace Z3NetA

open Matrix Finset Z3NetF

/-- **`thm:A`, the net is well defined**: for every ring homomorphism `ψ : R_S → ℤ/qℤ`, every solution
`U'` of the residual problem of `U*_s` with `λ' ≡ 1` and every `β` with the defining relation of
`prop:Gs`, the net of `def:Ns` built from `(U', β)` and reduced by `ψ` is `Apoint s q k`. So `Apoint`
does not depend on the choices `UrS`, `betaS` and the chosen reduction. -/
theorem Apoint_indep (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (ψ : RS s →+* ZMod q)
    (Ur β : Fin s → ℕ → ℕ → RS s) (hres : Residual (0 : Fin s) placeA (UstarR s) 1 Ur)
    (hβ : BetaRel (0 : Fin s) placeA (UstarR s) 1 β) :
    Apoint s q k = digPoint q (s * k) (fun c =>
      (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) :=
  Proofs.Apoint_indep_core hs k ψ Ur β hres hβ

/-- **`lem:sat`(ii)**, uniqueness of `γ_j`: a positive rational `γ` with `κ_j(Λ_j) = γ ℤ` is
`gamS d j` (column `d`, `j ≤ s - 2`). -/
theorem gamS_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (γ : ℚ)
    (hγ : 0 < γ)
    (hgen : ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ) :
    γ = gamS d j :=
  Proofs.gamS_unique_core hs d j hj γ hγ hgen

end Z3NetA
