/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmASat
public import Z3Net.FPropF

@[expose] public section

/-!
# Theorem A, part 2: the design `U*_s` (`def:Ustar`), dominance and reachability

V14 stage S3.

* Orthogonal projections onto the span of a flag `B_0, …, B_{j-1}` (`B_i ∈ Λ_i`, `κ_i(B_i) = γ_i`):
  the `B_i` are linearly independent over `ℚ` (`rat_indep`), the Gram system is solvable
  (`proj_exists`) with a unique solution (`proj_unique`).
* `def:Ustar`: at each level the vector is unique (`level_unique`) and is the Babai rounding of any
  `v` of the coset (`round_good`); the family exists and is unique (`Ustar_cols_core`,
  `Ustar_cols_unique_core`, `Ustar_round_core`).
* The design: partial sums (`Ustar_Msum_core`), diagonal dominance (`Ustar_dominant_core`),
  admissible columns (`Ustar_adm_core`), reachability over `R_S` via `prop:F` (`Ustar_reach_core`),
  and the data `UrS`, `betaS` of the net (`Ustar_data_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

/-! ## Orthogonal projection onto the span of a flag -/

/-- `B_i ∈ Λ_i` with `κ_i(B_i) = γ_i` for `i < j`. -/
def Below (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) : Prop :=
  ∀ i < j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i

/-- The vectors of a flag are linearly independent over `ℚ`. -/
lemma rat_indep (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) :
    ∀ j, j ≤ s - 1 → Below d B j → ∀ u : ℕ → ℚ,
      (∀ c, ∑ l ∈ range j, u l * (B l c : ℚ) = 0) → ∀ l < j, u l = 0 := by
  intro j
  induction j with
  | zero => intro _ _ _ _ l hl; omega
  | succ j ih =>
    intro hj hB u hu
    have hvec : (∑ l ∈ range (j + 1), u l • fun c => (B l c : ℚ)) = 0 := by
      funext c; simpa [Finset.sum_apply] using hu c
    have hp := colPoly_sum d (range (j + 1)) u (fun l c => (B l c : ℚ))
    rw [hvec, colPoly_zero] at hp
    have hco := congrArg (fun p => Polynomial.coeff p j) hp
    simp only [coeff_zero, finsetSum_coeff, coeff_smul, smul_eq_mul] at hco
    rw [sum_range_succ] at hco
    have hlow : ∑ l ∈ range j, u l * (colPoly d fun c => (B l c : ℚ)).coeff j = 0 :=
      sum_eq_zero fun l hl => by
        have := kappa_low hs (show l < j by simpa using hl) (by omega) (hB l (by simp at hl; omega)).1
        unfold kappa at this; rw [this, mul_zero]
    rw [hlow, zero_add] at hco
    have hk : (colPoly d fun c => (B j c : ℚ)).coeff j = gamS d j := (hB j (by omega)).2
    rw [hk] at hco
    have hpos := (gamS_spec hs d j (by omega)).1
    have huj : u j = 0 := (mul_eq_zero.mp hco.symm).resolve_right hpos.ne'
    have hu' : ∀ c, ∑ l ∈ range j, u l * (B l c : ℚ) = 0 := by
      intro c; have := hu c; rwa [sum_range_succ, huj, zero_mul, add_zero] at this
    intro l hl
    rcases Nat.lt_or_ge l j with h | h
    · exact ih (by omega) (fun i hi => hB i (by omega)) u hu' l h
    · rw [show l = j by omega]; exact huj

/-- If `W = ∑_{l<j} u_l B_l` is orthogonal to every `B_i`, then `W = 0`. -/
lemma orth_zero {j : ℕ} (B : ℕ → Fin s → ℤ) (u : ℕ → ℚ)
    (h : ∀ i < j, ∑ c, (∑ l ∈ range j, u l * (B l c : ℚ)) * (B i c : ℚ) = 0) :
    ∀ c, ∑ l ∈ range j, u l * (B l c : ℚ) = 0 := by
  set W : Fin s → ℚ := fun c => ∑ l ∈ range j, u l * (B l c : ℚ)
  have hsq : ∑ c, W c ^ 2 = 0 := by
    calc ∑ c, W c ^ 2 = ∑ c, W c * ∑ l ∈ range j, u l * (B l c : ℚ) := by
          refine sum_congr rfl fun c _ => ?_; simp only [W]; ring
      _ = ∑ l ∈ range j, u l * ∑ c, W c * (B l c : ℚ) := by
          simp only [mul_sum]; rw [sum_comm]; refine sum_congr rfl fun l _ => sum_congr rfl fun c _ => ?_
          ring
      _ = 0 := sum_eq_zero fun l hl => by
          rw [h l (by simpa using hl), mul_zero]
  have := (sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg (W c))).1 hsq
  intro c
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (this c (mem_univ c))

lemma proj_exists (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 1)
    (hB : Below d B j) (E : Fin s → ℤ) : ∃ cf : ℕ → ℚ, ProjCoef B j E cf := by
  set G : Matrix (Fin j) (Fin j) ℚ := fun i l => ∑ c, (B l c : ℚ) * (B i c : ℚ)
  have hGu : ∀ u : Fin j → ℚ, ∀ i : Fin j,
      (G.mulVec u) i = ∑ c, (∑ l ∈ range j, (fun l => if h : l < j then u ⟨l, h⟩ else 0) l *
        (B l c : ℚ)) * (B i c : ℚ) := by
    intro u i
    simp only [Matrix.mulVec, dotProduct, G, sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [Finset.sum_range (fun l => (if h : l < j then u ⟨l, h⟩ else 0) * (B l c : ℚ) * (B i c : ℚ))]
    refine sum_congr rfl fun l _ => ?_
    rw [dite_eq_left l.isLt]; ring
  have hker : ∀ u : Fin j → ℚ, G.mulVec u = 0 → u = 0 := by
    intro u hu
    have h0 : ∀ i < j, ∑ c, (∑ l ∈ range j, (fun l => if h : l < j then u ⟨l, h⟩ else 0) l *
        (B l c : ℚ)) * (B i c : ℚ) = 0 := by
      intro i hi
      have := congrFun hu ⟨i, hi⟩
      rw [hGu] at this; simpa using this
    have hz := rat_indep hs d B j hj hB _ (orth_zero B _ h0)
    funext l
    have := hz l l.isLt
    simpa [dite_eq_left l.isLt] using this
  have hinj : Function.Injective G.mulVec := by
    intro u u' huu
    have : G.mulVec (u - u') = 0 := by rw [Matrix.mulVec_sub, huu, sub_self]
    exact sub_eq_zero.mp (hker _ this)
  have hsurj : Function.Surjective G.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  obtain ⟨u, hu⟩ := hsurj fun i : Fin j => ∑ c, (E c : ℚ) * (B i c : ℚ)
  refine ⟨fun l => if h : l < j then u ⟨l, h⟩ else 0, fun i hi => ?_⟩
  have := congrFun hu ⟨i, hi⟩
  rw [hGu] at this
  simp only [sub_mul, sum_sub_distrib]
  rw [this]; ring

lemma projCoef_sub (B : ℕ → Fin s → ℤ) (j : ℕ) (E F : Fin s → ℤ) (cf cf' : ℕ → ℚ)
    (h : ProjCoef B j E cf) (h' : ProjCoef B j F cf') : ProjCoef B j (E - F) (cf - cf') := by
  intro i hi
  have e1 := h i hi
  have e2 := h' i hi
  have : ∑ c, (((E - F) c : ℤ) - ∑ l ∈ range j, (cf - cf') l * (B l c : ℚ)) * (B i c : ℚ) =
      ∑ c, (((E c : ℚ) - ∑ l ∈ range j, cf l * (B l c : ℚ)) * (B i c : ℚ)) -
        ∑ c, (((F c : ℚ) - ∑ l ∈ range j, cf' l * (B l c : ℚ)) * (B i c : ℚ)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]; push_cast; ring
  rw [this, e1, e2, sub_self]

/-- The coefficients of a vector of the span are its coordinates. -/
lemma projCoef_span (B : ℕ → Fin s → ℤ) (j : ℕ) (t : ℕ → ℤ) :
    ProjCoef B j (∑ l ∈ range j, t l • B l) (fun l => (t l : ℚ)) := by
  intro i _
  refine sum_eq_zero fun c _ => ?_
  have : ((∑ l ∈ range j, t l • B l) c : ℚ) = ∑ l ∈ range j, (t l : ℚ) * (B l c : ℚ) := by
    simp [Finset.sum_apply]
  rw [this, sub_self, zero_mul]

/-- Two coefficient vectors of the same vector agree on `l < j`. -/
lemma projCoef_unique (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 1)
    (hB : Below d B j) (E : Fin s → ℤ) (cf cf' : ℕ → ℚ) (h : ProjCoef B j E cf)
    (h' : ProjCoef B j E cf') : ∀ l < j, cf l = cf' l := by
  have hd := projCoef_sub B j E E cf cf' h h'
  have h0 : ∀ i < j, ∑ c, (∑ l ∈ range j, (cf' l - cf l) * (B l c : ℚ)) * (B i c : ℚ) = 0 := by
    intro i hi
    have e : ∀ c, ((((E - E) c : ℤ) : ℚ) - ∑ l ∈ range j, (cf - cf') l * (B l c : ℚ)) =
        ∑ l ∈ range j, (cf' l - cf l) * (B l c : ℚ) := by
      intro c
      simp only [Pi.sub_apply, sub_self, Int.cast_zero, zero_sub, ← sum_neg_distrib]
      exact sum_congr rfl fun l _ => by ring
    have := hd i hi
    simp only [e] at this
    exact this
  have hz := rat_indep hs d B j hj hB _ (orth_zero B _ h0)
  intro l hl
  have := hz l hl
  linarith

lemma projCoef_congr (B B' : ℕ → Fin s → ℤ) (j : ℕ) (hBB : ∀ i < j, B i = B' i) (E : Fin s → ℤ)
    (cf : ℕ → ℚ) : ProjCoef B j E cf ↔ ProjCoef B' j E cf := by
  unfold ProjCoef
  have hs : ∀ c, ∑ l ∈ range j, cf l * (B l c : ℚ) = ∑ l ∈ range j, cf l * (B' l c : ℚ) :=
    fun c => sum_congr rfl fun l hl => by rw [hBB l (by simpa using hl)]
  constructor
  · intro h i hi; rw [← hBB i hi]; simp only [← hs]; exact h i hi
  · intro h i hi; rw [hBB i hi]; simp only [hs]; exact h i hi

/-! ## `def:Ustar`, one level -/

/-- The properties of `E_{d,j}` relative to the earlier columns `B 0, …, B (j-1)`. -/
def Good (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (E : Fin s → ℤ) : Prop :=
  InLam d j E ∧ kappa d j E = gamS d j ∧
    ∃ cf : ℕ → ℚ, ProjCoef B j E cf ∧ ∀ i < j, -1 / 2 ≤ cf i ∧ cf i < 1 / 2

/-- Babai rounding of any `v` of the coset gives a vector with the properties. -/
lemma round_good (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Below d B j) (v : Fin s → ℤ) (hv : InLam d j v) (hvk : kappa d j v = gamS d j)
    (cf : ℕ → ℚ) (hcf : ProjCoef B j v cf) :
    Good d B j (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) := by
  have hsum : InLam d j (∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) :=
    inLam_sum _ _ B fun i hi => inLam_mono (by simp at hi; omega) (hB i (by simpa using hi)).1
  refine ⟨inLam_sub hv hsum, ?_, fun i => cf i - ⌊cf i + 1 / 2⌋, ?_, fun i _ => ?_⟩
  · rw [kappa_sub, kappa_sum, hvk]
    have : ∑ i ∈ range j, ((⌊cf i + 1 / 2⌋ : ℤ) : ℚ) * kappa d j (B i) = 0 :=
      sum_eq_zero fun i hi => by
        rw [kappa_low hs (show i < j by simpa using hi) hj (hB i (by simpa using hi)).1, mul_zero]
    rw [this, sub_zero]
  · have := projCoef_sub B j v _ cf _ hcf (projCoef_span B j fun i => ⌊cf i + 1 / 2⌋)
    exact this
  · have h1 := Int.floor_le (cf i + 1 / 2)
    have h2 := Int.lt_floor_add_one (cf i + 1 / 2)
    constructor <;> linarith

lemma level_exists (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Below d B j) : ∃ E, Good d B j E := by
  obtain ⟨v, hv, hvk⟩ := ((gamS_spec hs d j hj).2 (gamS d j)).2 ⟨1, by simp⟩
  obtain ⟨cf, hcf⟩ := proj_exists hs d B j (by omega) hB v
  exact ⟨_, round_good hs d B j hj hB v hv hvk cf hcf⟩

lemma level_unique (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ) (j : ℕ) (hj : j ≤ s - 2)
    (hB : Below d B j) (E E' : Fin s → ℤ) (hE : Good d B j E) (hE' : Good d B j E') : E = E' := by
  obtain ⟨hEl, hEk, cf, hcf, hcfb⟩ := hE
  obtain ⟨hEl', hEk', cf', hcf', hcfb'⟩ := hE'
  set B'' : ℕ → Fin s → ℤ := fun i => if i = j then E' else B i
  have hB'' : ∀ i ≤ j, InLam d i (B'' i) ∧ kappa d i (B'' i) = gamS d i := by
    intro i hi
    by_cases h : i = j
    · subst h; simp only [B'', ite_true]; exact ⟨hEl', hEk'⟩
    · simp only [B'', h, ite_false]; exact hB i (by omega)
  obtain ⟨t, ht⟩ := (sat_coset_core hs d j hj B'' hB'' E).1 ⟨hEl, hEk⟩
  have hBj : B'' j = E' := by simp [B'']
  have ht' : E - E' = ∑ i ∈ range j, t i • B i := by
    rw [← hBj, ht]
    exact sum_congr rfl fun i hi => by simp [B'', show i ≠ j by simp at hi; omega]
  have hp1 := projCoef_sub B j E E' cf cf' hcf hcf'
  have hp2 := projCoef_span B j t
  rw [← ht'] at hp2
  have hu := projCoef_unique hs d B j (by omega) hB (E - E') _ _ hp1 hp2
  have ht0 : ∀ i < j, t i = 0 := by
    intro i hi
    have h1 := hu i hi
    simp only [Pi.sub_apply] at h1
    have a1 := hcfb i hi; have a2 := hcfb' i hi
    have hlt : |(t i : ℚ)| < 1 := by rw [abs_lt]; constructor <;> linarith
    have : |t i| < 1 := by exact_mod_cast hlt
    rw [abs_lt] at this; omega
  have : E - E' = 0 := by
    rw [ht']; exact sum_eq_zero fun i hi => by rw [ht0 i (by simpa using hi), zero_smul]
  exact sub_eq_zero.mp this

lemma good_congr (d : Fin s) (B B' : ℕ → Fin s → ℤ) (j : ℕ) (hBB : ∀ i < j, B i = B' i)
    (E : Fin s → ℤ) : Good d B j E ↔ Good d B' j E := by
  unfold Good
  simp only [projCoef_congr B B' j hBB E]

/-! ## `def:Ustar`, the family -/

lemma cols_aux (hs : 3 ≤ s) (d : Fin s) :
    ∀ J, J ≤ s - 2 → ∃ B : ℕ → Fin s → ℤ, ∀ j ≤ J, Good d B j (B j) := by
  intro J
  induction J with
  | zero =>
    intro hJ
    obtain ⟨E, hE⟩ := level_exists hs d (fun _ => 0) 0 hJ (fun i hi => absurd hi (by omega))
    refine ⟨fun _ => E, fun j hj => ?_⟩
    rw [show j = 0 by omega]
    exact (good_congr d _ _ 0 (fun i hi => absurd hi (by omega)) E).1 hE
  | succ J ih =>
    intro hJ
    obtain ⟨B, hB⟩ := ih (by omega)
    have hBelow : Below d B (J + 1) := fun i hi => ⟨(hB i (by omega)).1, (hB i (by omega)).2.1⟩
    obtain ⟨E, hE⟩ := level_exists hs d B (J + 1) hJ hBelow
    refine ⟨fun i => if i = J + 1 then E else B i, fun j hj => ?_⟩
    have hcon : ∀ i < j, (fun i => if i = J + 1 then E else B i) i = B i := by
      intro i hi; simp [show i ≠ J + 1 by omega]
    rw [good_congr d _ B j hcon]
    rcases Nat.lt_or_ge j (J + 1) with h | h
    · simp only [show j ≠ J + 1 by omega, ite_false]; exact hB j (by omega)
    · rw [show j = J + 1 by omega]; simpa using hE

lemma isUstarCols_iff (d : Fin s) (B : ℕ → Fin s → ℤ) :
    IsUstarCols d B ↔ (∀ j ≤ s - 2, Good d B j (B j)) ∧ ∀ j, s - 2 < j → B j = 0 := Iff.rfl

theorem Ustar_cols_exists (hs : 3 ≤ s) (d : Fin s) : ∃ B, IsUstarCols d B := by
  obtain ⟨B, hB⟩ := cols_aux hs d (s - 2) le_rfl
  refine ⟨fun j => if j ≤ s - 2 then B j else 0, (isUstarCols_iff d _).2 ⟨fun j hj => ?_, fun j hj => ?_⟩⟩
  · have hcon : ∀ i < j, (fun j => if j ≤ s - 2 then B j else 0) i = B i := by
      intro i hi; simp [show i ≤ s - 2 by omega]
    rw [good_congr d _ B j hcon]
    simp only [hj, ite_true]; exact hB j hj
  · simp [show ¬ j ≤ s - 2 by omega]

theorem Ustar_cols_core (hs : 3 ≤ s) (d : Fin s) : IsUstarCols d (Ecol d) :=
  Classical.epsilon_spec (Ustar_cols_exists hs d)

theorem Ustar_cols_unique_core (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ)
    (hB : IsUstarCols d B) : B = Ecol d := by
  have hE := (isUstarCols_iff d _).1 (Ustar_cols_core hs d)
  rw [isUstarCols_iff] at hB
  have key : ∀ j, (∀ i < j, B i = Ecol d i) → B j = Ecol d j := by
    intro j ih
    rcases Nat.lt_or_ge (s - 2) j with h | h
    · rw [hB.2 j h, hE.2 j h]
    · have hBel : Below d (Ecol d) j :=
        fun i hi => ⟨(hE.1 i (by omega)).1, (hE.1 i (by omega)).2.1⟩
      have hg : Good d (Ecol d) j (B j) := (good_congr d B (Ecol d) j ih _).1 (hB.1 j h)
      exact level_unique hs d (Ecol d) j h hBel _ _ hg (hE.1 j h)
  have hall : ∀ j, B j = Ecol d j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih => exact key j ih
  funext j
  exact hall j

theorem Ustar_round_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (v : Fin s → ℤ)
    (hv : InLam d j v) (hvk : kappa d j v = gamS d j) (cf : ℕ → ℚ)
    (hcf : ProjCoef (Ecol d) j v cf) :
    Ecol d j = v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • Ecol d i := by
  have hE := (isUstarCols_iff d _).1 (Ustar_cols_core hs d)
  have hBel : Below d (Ecol d) j := fun i hi => ⟨(hE.1 i (by omega)).1, (hE.1 i (by omega)).2.1⟩
  exact level_unique hs d (Ecol d) j hj hBel _ _ (hE.1 j hj)
    (round_good hs d (Ecol d) j hj hBel v hv hvk cf hcf)

lemma Ecol_spec (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    InLam d j (Ecol d j) ∧ kappa d j (Ecol d j) = gamS d j :=
  ⟨((Ustar_cols_core hs d).1 j hj).1, ((Ustar_cols_core hs d).1 j hj).2.1⟩


/-! ## The span of `E_{d,0}, …, E_{d,j}` is `V_j` -/

/-- A rational vector of `V_j` has an integer multiple in `Λ_j`. -/
lemma rat_mul_inLam (d : Fin s) (j : ℕ) (E : Fin s → ℚ) (hE0 : E d = 0)
    (g : Polynomial ℚ) (hg : g.natDegree ≤ j) (hrep : ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : Fin s → ℤ, InLam d j F ∧ ∀ c, (F c : ℚ) = D * E c := by
  refine ⟨∏ c, (E c).den, prod_pos fun c _ => (E c).den_pos, ?_⟩
  have hint : ∀ c, ∃ z : ℤ, (z : ℚ) = ((∏ c, (E c).den : ℕ) : ℚ) * E c := by
    intro c
    obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun c => (E c).den) (mem_univ c)
    refine ⟨(m : ℤ) * (E c).num, ?_⟩
    rw [hm]
    have h1 : (E c).num / ((E c).den : ℚ) = E c := Rat.num_div_den (E c)
    have h2 : ((E c).den : ℚ) ≠ 0 := by exact_mod_cast (E c).den_pos.ne'
    have h3 : ((E c).num : ℚ) = E c * (E c).den := by rw [div_eq_iff h2] at h1; exact h1
    push_cast
    rw [h3]; ring
  choose F hF using hint
  refine ⟨F, ⟨?_, C ((∏ c, (E c).den : ℕ) : ℚ) * g, (natDegree_C_mul_le _ _).trans hg, fun c hc => ?_⟩,
    fun c => hF c⟩
  · have := hF d; rw [hE0, mul_zero] at this; exact_mod_cast this
  · rw [hF c, hrep c hc, eval_mul, eval_C]; ring

theorem Ustar_span_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (E : Fin s → ℚ) :
    (E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧ ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) ↔
      ∃ u : ℕ → ℚ, E = ∑ i ∈ range (j + 1), u i • fun c => (Ecol d i c : ℚ) := by
  have hflag : ∀ i ≤ j, InLam d i (Ecol d i) ∧ kappa d i (Ecol d i) = gamS d i :=
    fun i hi => Ecol_spec hs d i (by omega)
  constructor
  · rintro ⟨hE0, g, hg, hrep⟩
    obtain ⟨D, hD, F, hF, hFE⟩ := rat_mul_inLam d j E hE0 g hg hrep
    obtain ⟨t, ht⟩ := (sat_basis_core hs d j hj (Ecol d) hflag).1 F |>.1 hF
    refine ⟨fun i => (t i : ℚ) / D, ?_⟩
    funext c
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have h1 := hFE c
    rw [ht] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul] at h1 ⊢
    have : E c = (∑ x ∈ range (j + 1), (t x : ℚ) * (Ecol d x c : ℚ)) / D := by
      rw [h1]; field_simp
    rw [this, sum_div]
    exact sum_congr rfl fun i _ => by ring
  · rintro ⟨u, rfl⟩
    have hmem : ∀ i ∈ range (j + 1), ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧
        ∀ c, c ≠ d → (Ecol d i c : ℚ) = wQ c d * g.eval (yQ c d) := by
      intro i hi
      obtain ⟨_, g, hg, hr⟩ := (hflag i (by simp at hi; omega)).1
      exact ⟨g, hg.trans (by simp at hi; omega), hr⟩
    choose! G hG hGr using hmem
    refine ⟨?_, ∑ i ∈ range (j + 1), C (u i) * G i, ?_, fun c hc => ?_⟩
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact sum_eq_zero fun i hi => by rw [(hflag i (by simp at hi; omega)).1.1]; simp
    · refine (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_)
      exact (natDegree_C_mul_le _ _).trans (hG i hi)
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eval_finsetSum, eval_mul, eval_C,
        mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [hGr i hi c hc]; ring

/-! ## The design `U*_s` -/

theorem Ustar_Msum_core (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j ≤ s - 2) :
    Msum (UstarF s) j c d = Ecol d j c := by
  induction j with
  | zero => simp [Msum, UstarF, hcd, show ¬ s ≤ 1 by omega]
  | succ j ih =>
    unfold Msum at ih ⊢
    rw [sum_range_succ, ih (by omega)]
    simp only [UstarF, hcd, ite_false, show ¬ s - 1 ≤ j + 1 by omega, show j + 1 ≠ 0 by omega,
      Nat.add_sub_cancel]
    ring

theorem Ustar_diag_core (c : Fin s) :
    UstarF s 0 c c = -(alphaS c : ℤ) ∧ ∀ n, 1 ≤ n → UstarF s n c c = 0 := by
  refine ⟨by simp [UstarF], fun n hn => ?_⟩
  simp [UstarF, show n ≠ 0 by omega]

theorem Ustar_dominant_core (hs : 3 ≤ s) (c : Fin s) :
    ∑ d ∈ univ.filter (fun d => d ≠ c),
        (range (s - 1)).sup (fun j => (Msum (UstarF s) j c d).natAbs) = alphaS c ∧
      alphaS c ≤ aStar s := by
  refine ⟨?_, le_sup (f := fun c : Fin s => alphaS c) (mem_univ c)⟩
  unfold alphaS
  refine sum_congr rfl fun d hd => ?_
  simp only [mem_filter, mem_univ, true_and] at hd
  refine sup_congr rfl fun j hj => ?_
  rw [Ustar_Msum_core hs c d (Ne.symm hd) j (by simp at hj; omega)]

theorem Ustar_adm_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    AdmCol d j (fun c => if c = d then 0 else Msum (UstarF s) j c d) := by
  have hcol : (fun c => if c = d then 0 else Msum (UstarF s) j c d) = Ecol d j := by
    funext c
    by_cases h : c = d
    · rw [ite_eq_left h, h, (Ecol_spec hs d j hj).1.1]
    · rw [ite_eq_right h, Ustar_Msum_core hs c d h j hj]
  rw [hcol, sat_adm_core hs d j hj, (Ecol_spec hs d j hj).2]
  exact ⟨(Ecol_spec hs d j hj).1, (sat_gamma_core hs d j hj).2.1⟩

/-! ## Reachability over `R_S` -/

lemma rs_nontrivial (s : ℕ) : Nontrivial (RS s) := by
  refine nontrivial_of_ne 0 1 fun h => ?_
  have := congrArg (ι s) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

lemma Msum_cast (j : ℕ) (c d : Fin s) :
    Msum (UstarR s) j c d = ((Msum (UstarF s) j c d : ℤ) : RS s) := by
  simp [Msum, UstarR, Int.cast_sum]

theorem Ustar_reach_core (hs : 3 ≤ s) :
    PlacesOK (0 : Fin s) (placeA : Fin s → RS s) ∧
      ∃ Ur : Fin s → ℕ → ℕ → RS s, Residual (0 : Fin s) placeA (UstarR s) 1 Ur := by
  have := rs_nontrivial s
  refine ⟨placesOK (by omega), ?_⟩
  rw [Z3NetF.Proofs.F_poly_iff_core (0 : Fin s) (placeA : Fin s → RS s) (UstarR s) 1
    (fun _ => isUnit_one)]
  intro d j hj
  have hj' : j ≤ s - 2 := by omega
  obtain ⟨hEl, hEk⟩ := Ecol_spec hs d j hj'
  have hlift := colPoly_lifts (by omega) d (Ecol d j)
  rw [← lifts_iff_liftsRing, mem_lifts] at hlift
  obtain ⟨g, hg⟩ := hlift
  have hdeg : (colPoly d fun c => (Ecol d j c : ℚ)).natDegree = j := by
    have h1 := ((inLam_iff hs hj' _).1 hEl).2
    refine natDegree_eq_of_le_of_coeff_ne_zero h1 ?_
    have : kappa d j (Ecol d j) ≠ 0 := by rw [hEk]; exact (gamS_spec hs d j hj').1.ne'
    exact this
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [← natDegree_map_eq_of_injective (ι_inj s) g, hg, hdeg]
  · have hlc : ι s g.leadingCoeff = gamS d j := by
      rw [← leadingCoeff_map_of_injective (ι_inj s) g, hg, leadingCoeff, hdeg]
      exact hEk
    obtain ⟨r, hr⟩ := (inRS_iff s _).1 (sat_gamma_core hs d j hj').2.1.2.2
    have h1 : g.leadingCoeff * r = 1 := by
      apply ι_inj s
      rw [map_mul, hlc, hr, map_one, mul_inv_cancel₀ (gamS_spec hs d j hj').1.ne']
    exact ⟨⟨g.leadingCoeff, r, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · intro c hcd
    apply ι_inj s
    rw [Msum_cast, map_intCast, Ustar_Msum_core hs c d hcd j hj', map_mul, map_mul, Pi.one_apply,
      map_one, one_mul, ι_wN (by omega) c d hcd, ← eval₂_at_apply, ← eval_map, hg,
      ι_yN (by omega) c d hcd]
    exact colPoly_rep (by omega) d (fun c => (Ecol d j c : ℚ)) c hcd

theorem Ustar_data_core (hs : 3 ≤ s) :
    Residual (0 : Fin s) placeA (UstarR s) 1 (UrS s) ∧
      BetaRel (0 : Fin s) placeA (UstarR s) 1 (betaS s) := by
  have hres : Residual (0 : Fin s) placeA (UstarR s) 1 (UrS s) :=
    Classical.epsilon_spec (Ustar_reach_core hs).2
  refine ⟨hres, Classical.epsilon_spec ?_⟩
  have hb := fun d n => (Z3NetF.Proofs.Gs_beta_core (0 : Fin s) (placeA : Fin s → RS s) (by omega)
    (Ustar_reach_core hs).1 (UstarR s) 1 (UrS s) hres d n).exists
  choose b hb using hb
  refine ⟨fun d n i => if h : i < s - 1 then b d n ⟨i, h⟩ else 0, fun d n _ c hc => ?_⟩
  rw [hb d n c hc, Finset.sum_range]
  refine sum_congr rfl fun i _ => ?_
  dsimp only
  rw [dite_eq_left i.isLt]

end

end Z3NetA.Proofs
