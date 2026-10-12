/-
Proof module (stage 11, entry Dim34): `prop:C4` (value of the relaxation) as a compared
statement.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D4Defs
public import Z3Net.D4Case
public import Z3Net.D4CaseCheck
public import Z3Net.D4RelaxDefs

@[expose] public section

/-!
# Stage 11 addition to entry Dim34: `prop:C4`

The definitions (verbatim copies of the new definitions of `ChallengeDim34.lean`: `Mpart`,
`relaxSigma`, `relaxJit`, `relaxB`, `relaxLB`, the relaxation of `lem:Ss` for design A) are in
`Z3Net/D4RelaxDefs.lean` (moved there in stage 13b).
The lower bound `∑ b_i² ≥ K4 q` is `Z3NetD4.Proofs.key_ineq` (the kernel-checked enumeration of
`Z3Net/D4CaseCheck.lean`); it is attained at the step `e = (-1,-1,0,1)` with a carry on the second
axis (`q = 5` and `q ≥ 9`, both `L = 2, 3`) and at `e = (-1,-1,-1,-1)`, carries `(1,0,1,2)` (`q = 7`,
`L = 3`).
-/

namespace Z3NetD4

open Matrix Finset

namespace ProofsS11

lemma Mpart_apply (J : ℕ) (i d : Fin 4) : Mpart J i d = Proofs.PJ i d J := by
  unfold Mpart Proofs.PJ; rw [Matrix.sum_apply]

lemma relaxSigma_eq (L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (i : Fin 4) :
    relaxSigma L e j i = ∑ d, e d * Proofs.PJ i d (min (j d) (L - 1)) := by
  unfold relaxSigma; simp only [Mpart_apply]

/-- The minimising representative `t` of `b_i`. -/
lemma relaxB_spec (q L : ℕ) (hq : 0 < q) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (i : Fin 4) :
    ∃ t : ℤ, t ≡ relaxSigma L e j i [ZMOD q] ∧ |t| < q ∧
      0 ≤ relaxB q L e j i ∧ |e i * q + t| - relaxJit e i ≤ relaxB q L e j i := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  unfold relaxB
  set s := relaxSigma L e j i
  have h0 : 0 ≤ s % (q : ℤ) := Int.emod_nonneg _ hq'.ne'
  have h1 : s % (q : ℤ) < q := Int.emod_lt_of_pos _ hq'
  have hm : s % (q : ℤ) ≡ s [ZMOD q] := Int.mod_modEq _ _
  split_ifs with hz
  · refine ⟨0, ?_, by simpa using hq', le_max_left _ _, le_max_right _ _⟩
    rw [← hz]; exact hm
  · have hpos : 0 < s % (q : ℤ) := lt_of_le_of_ne h0 (Ne.symm hz)
    rcases min_choice (max 0 (|e i * q + s % (q : ℤ)| - relaxJit e i))
        (max 0 (|e i * q + (s % (q : ℤ) - q)| - relaxJit e i)) with h | h
    · refine ⟨s % q, hm, abs_lt.mpr ⟨by omega, h1⟩, ?_, ?_⟩ <;> rw [h]
      · exact le_max_left _ _
      · exact le_max_right _ _
    · refine ⟨s % q - q, (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩).trans hm,
        abs_lt.mpr ⟨by omega, by omega⟩, ?_, ?_⟩ <;> rw [h]
      · exact le_max_left _ _
      · exact le_max_right _ _

lemma K4i_cast (q : ℕ) : Proofs.K4i (q : ℤ) = K4 q := by
  unfold Proofs.K4i K4
  by_cases h5 : q = 5
  · subst h5; norm_num
  by_cases h7 : q = 7
  · subst h7; norm_num
  have a5 : ¬ ((q : ℤ) = 5) := by omega
  have a7 : ¬ ((q : ℤ) = 7) := by omega
  simp only [a5, a7, h5, h7, ↓reduceIte]

/-- **Lower bound**: every configuration has `∑ b_i² ≥ K4 q` (`L ≤ 3`). -/
lemma relax_lower (q L : ℕ) (hq : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q) (hL : L ≤ 3)
    (e : Fin 4 → ℤ) (he : ∀ d, e d = -1 ∨ e d = 0 ∨ e d = 1) (hne : e ≠ 0) (j : Fin 4 → ℕ) :
    K4 q ≤ ∑ i, relaxB q L e j i ^ 2 := by
  have hq0 : 0 < q := by omega
  choose t ht using fun i => relaxB_spec q L hq0 e j i
  have key := Proofs.key_ineq Proofs.checkPoly_eq Proofs.checkSmall5 Proofs.checkSmall7
    Proofs.checkSmall9 Proofs.checkSigBound_eq (q : ℤ) (by omega) e
    (fun c => by rcases he c with h | h | h <;> omega)
    (by by_contra h; exact hne (funext fun c => by by_contra hc; exact h ⟨c, hc⟩)) (fun d => min (j d) (L - 1))
    (fun c => by omega) t (fun i => relaxB q L e j i)
    (fun i => ⟨by have := (ht i).1; rw [relaxSigma_eq] at this; exact this, (ht i).2.1⟩)
    (fun i => (ht i).2.2.1)
    (fun i => by
      have := (ht i).2.2.2
      unfold relaxJit at this
      split_ifs at this ⊢ <;> linarith)
  rw [K4i_cast] at key
  rw [Fin.sum_univ_four]; exact key

/-- The attaining step for `q = 5` and `q ≥ 9`. -/
def e0 : Fin 4 → ℤ := ![-1, -1, 0, 1]
/-- Its carry lengths (a carry on the second axis). -/
def j0 : Fin 4 → ℕ := ![0, 1, 0, 0]

lemma sig0_2 : ∀ i, relaxSigma 2 e0 j0 i = ![-1, 4, -3, 1] i := by decide
lemma sig0_3 : ∀ i, relaxSigma 3 e0 j0 i = ![-1, 4, -3, 1] i := by decide
lemma jit0 : ∀ i, relaxJit e0 i = 1 := by decide

lemma emod_negsmall (a q : ℤ) (ha : 0 < a) (haq : a < q) : (-a) % q = q - a := by
  rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]; ring

lemma attain_big (q L : ℕ) (hq : 9 ≤ q) (hL : L = 2 ∨ L = 3) :
    ∑ i, relaxB q L e0 j0 i ^ 2 = ((q : ℤ) - 5) ^ 2 + 4 := by
  have hs : ∀ i, relaxSigma L e0 j0 i = ![-1, 4, -3, 1] i := by
    rcases hL with rfl | rfl
    · exact sig0_2
    · exact sig0_3
  have hq' : (9 : ℤ) ≤ q := by exact_mod_cast hq
  have m0 : (-1 : ℤ) % q = q - 1 := emod_negsmall 1 q (by norm_num) (by omega)
  have m1 : (4 : ℤ) % q = 4 := Int.emod_eq_of_lt (by norm_num) (by omega)
  have m2 : (-3 : ℤ) % q = q - 3 := emod_negsmall 3 q (by norm_num) (by omega)
  have m3 : (1 : ℤ) % q = 1 := Int.emod_eq_of_lt (by norm_num) (by omega)
  have b0 : relaxB q L e0 j0 0 = 0 := by
    unfold relaxB; rw [hs, jit0]
    rw [show e0 0 = -1 from rfl, show (![-1, 4, -3, 1] : Fin 4 → ℤ) 0 = -1 from rfl, m0]
    simp only [show ¬ ((q : ℤ) - 1 = 0) by omega, ↓reduceIte, abs_eq_max_neg]; omega
  have b1 : relaxB q L e0 j0 1 = q - 5 := by
    unfold relaxB; rw [hs, jit0]
    rw [show e0 1 = -1 from rfl, show (![-1, 4, -3, 1] : Fin 4 → ℤ) 1 = 4 from rfl, m1]
    simp only [show ¬ ((4 : ℤ) = 0) by omega, ↓reduceIte, abs_eq_max_neg]; omega
  have b2 : relaxB q L e0 j0 2 = 2 := by
    unfold relaxB; rw [hs, jit0]
    rw [show e0 2 = 0 from rfl, show (![-1, 4, -3, 1] : Fin 4 → ℤ) 2 = -3 from rfl, m2]
    simp only [show ¬ ((q : ℤ) - 3 = 0) by omega, ↓reduceIte, abs_eq_max_neg]; omega
  have b3 : relaxB q L e0 j0 3 = 0 := by
    unfold relaxB; rw [hs, jit0]
    rw [show e0 3 = 1 from rfl, show (![-1, 4, -3, 1] : Fin 4 → ℤ) 3 = 1 from rfl, m3]
    simp only [show ¬ ((1 : ℤ) = 0) by omega, ↓reduceIte, abs_eq_max_neg]; omega
  rw [Fin.sum_univ_four, b0, b1, b2, b3]; ring

lemma attain_5 : ∑ i, relaxB 5 3 e0 j0 i ^ 2 = 1 := by decide

/-- The attaining configuration for `q = 7`, `L = 3`. -/
def e7 : Fin 4 → ℤ := ![-1, -1, -1, -1]
def j7 : Fin 4 → ℕ := ![1, 0, 1, 2]

lemma attain_7 : ∑ i, relaxB 7 3 e7 j7 i ^ 2 = 5 := by decide


/-! ## Assembly -/

/-- The set of candidate values `(∑ b_i²)^(1/2) / q` (the inner minimum of `relaxLB`). -/
def relaxSet (q L : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (e : Fin 4 → ℤ) (j : Fin 4 → ℕ),
    (∀ d, e d = -1 ∨ e d = 0 ∨ e d = 1) ∧ e ≠ 0 ∧
      x = Real.sqrt (∑ i, (relaxB q L e j i : ℝ) ^ 2) / q}

lemma relaxLB_eq (q L : ℕ) : relaxLB q L = min 1 (sInf (relaxSet q L)) := rfl

lemma relaxSet_nonempty (q L : ℕ) : (relaxSet q L).Nonempty :=
  ⟨_, e0, j0, by decide, by decide, rfl⟩

lemma relaxSet_lb (q L : ℕ) (hq : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q) (hL : L ≤ 3) :
    Real.sqrt (K4 q : ℝ) / q ∈ lowerBounds (relaxSet q L) := by
  rintro x ⟨e, j, he, hne, rfl⟩
  have h := relax_lower q L hq hL e he hne j
  have h' : (K4 q : ℝ) ≤ ∑ i, (relaxB q L e j i : ℝ) ^ 2 := by exact_mod_cast h
  gcongr

lemma K4_big (q : ℕ) (hq : 9 ≤ q) : K4 q = ((q : ℤ) - 5) ^ 2 + 4 := by
  unfold K4; simp only [show q ≠ 5 by omega, show q ≠ 7 by omega, ↓reduceIte]

lemma K4_nonneg (q : ℕ) : 0 ≤ K4 q := by
  unfold K4; split_ifs <;> positivity

lemma K4_le (q : ℕ) (hq : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q) : K4 q ≤ (q : ℤ) ^ 2 := by
  rcases hq with rfl | rfl | h | h
  · decide
  · decide
  · rw [K4_big q (by omega)]; have : (9 : ℤ) ≤ q := (by exact_mod_cast h.ge); nlinarith
  · rw [K4_big q (by omega)]; have : (11 : ℤ) ≤ q := (by exact_mod_cast h); nlinarith

/-- `min(LB_3, LB_2) = √(K4 q) / q`, given a configuration of `L = 3` attaining `K4 q`. -/
lemma relax_min (q : ℕ) (hq : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ)
    (he : ∀ d, e d = -1 ∨ e d = 0 ∨ e d = 1) (hne : e ≠ 0)
    (hatt : ∑ i, relaxB q 3 e j i ^ 2 = K4 q) :
    min (relaxLB q 3) (relaxLB q 2) = Real.sqrt (K4 q : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hv1 : Real.sqrt (K4 q : ℝ) / q ≤ 1 := by
    rw [div_le_one hq0]
    have hK : (K4 q : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast K4_le q hq
    calc Real.sqrt (K4 q : ℝ) ≤ Real.sqrt ((q : ℝ) ^ 2) := Real.sqrt_le_sqrt hK
      _ = q := Real.sqrt_sq hq0.le
  have hmem : Real.sqrt (K4 q : ℝ) / q ∈ relaxSet q 3 := by
    refine ⟨e, j, he, hne, ?_⟩
    have : (∑ i, (relaxB q 3 e j i : ℝ) ^ 2) = (K4 q : ℝ) := by exact_mod_cast hatt
    rw [this]
  have hlb3 := relaxSet_lb q 3 hq le_rfl
  have h3 : sInf (relaxSet q 3) = Real.sqrt (K4 q : ℝ) / q :=
    le_antisymm (csInf_le ⟨_, hlb3⟩ hmem) (le_csInf (relaxSet_nonempty q 3) hlb3)
  have h2 : Real.sqrt (K4 q : ℝ) / q ≤ relaxLB q 2 := by
    rw [relaxLB_eq]
    exact le_min hv1 (le_csInf (relaxSet_nonempty q 2) (relaxSet_lb q 2 hq (by norm_num)))
  rw [relaxLB_eq q 3, h3, min_eq_right hv1, min_eq_left h2]

lemma sq_val (q : ℕ) : (Real.sqrt (K4 q : ℝ) / q) ^ 2 = (K4 q : ℝ) / (q : ℝ) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by exact_mod_cast K4_nonneg q)]

end ProofsS11

/-- **Proposition `prop:C4`** (value of the relaxation). For design A, the relaxation of `lem:Ss`
with `L = 3` (used for `k ≥ 3`) and with `L = 2` and `(F_0, F_1)` (used for `k = 2`) satisfies
`min(LB_3, LB_2)² = ((q-5)² + 4)/q²` for odd `q ≥ 9`, `= 1/25` for `q = 5`, `= 5/49` for `q = 7`. -/
theorem D4_relax_value :
    (∀ q : ℕ, Odd q → 9 ≤ q →
      min (relaxLB q 3) (relaxLB q 2) ^ 2 = (((q : ℝ) - 5) ^ 2 + 4) / (q : ℝ) ^ 2) ∧
    min (relaxLB 5 3) (relaxLB 5 2) ^ 2 = 1 / 25 ∧
    min (relaxLB 7 3) (relaxLB 7 2) ^ 2 = 5 / 49 := by
  refine ⟨fun q hodd hq => ?_, ?_, ?_⟩
  · have hq' : q = 9 ∨ 11 ≤ q := by obtain ⟨k, rfl⟩ := hodd; omega
    have hq'' : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q := by omega
    rw [ProofsS11.relax_min q hq'' ProofsS11.e0 ProofsS11.j0 (by decide) (by decide)
      ((ProofsS11.attain_big q 3 hq (Or.inr rfl)).trans (ProofsS11.K4_big q hq).symm),
      ProofsS11.sq_val, ProofsS11.K4_big q hq]
    push_cast; ring
  · rw [ProofsS11.relax_min 5 (Or.inl rfl) ProofsS11.e0 ProofsS11.j0 (by decide) (by decide)
      ProofsS11.attain_5, ProofsS11.sq_val]
    norm_num [K4]
  · rw [ProofsS11.relax_min 7 (Or.inr (Or.inl rfl)) ProofsS11.e7 ProofsS11.j7 (by decide) (by decide)
      ProofsS11.attain_7, ProofsS11.sq_val]
    norm_num [K4]

end Z3NetD4
