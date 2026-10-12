/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColNet2

@[expose] public section

/-!
# V14 stage S9′: `lem:drift`(3), (4)

In units of thirds, `ε_i = q w_i + 3 r_i` (`3ε_i` of the paper) and `M = max_i ε_i` (`3 max ε`).

* (3) For `q ≥ 10` and `|w_c| ≤ 2` the excess (thirds) of every step is `ε_i - 3qκ'` (`κ'` the wrap of
  the third digit), it lies in `[-½q², q²]` (the paper's `[-⅙q², ⅓q²]`), its maximum is `M`, and
  `3g = q² - M` (`gap_formula`), i.e. `d² = q⁴ - 2q²η + 3η²` with `3η = M`.
* (4) For a `(0,3,3)`-net: `∑ r_i ≥ q` (`drift_net_r`), hence `∑ ε_i ≥ 3q`, `M ≥ q`, and `M ≥ 2q` for
  `q ≡ 1 (mod 3)` (some `w_c ≥ 2`).
-/

namespace Z3NetC.Proofs

open Z3NetF Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-- `ε_i = q w_i + 3 r_i` (thirds). -/
def epsD (q : ℕ) (w ℓ : Fin 3 → ℤ) (i : Fin 3) : ℤ := (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val

lemma epsD_sum (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0) :
    ∑ i, epsD q w ℓ i = 3 * ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by
  simp only [epsD, Finset.sum_add_distrib, ← Finset.mul_sum, hw0, mul_zero, zero_add]

lemma epsD_max_nonneg (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0) :
    0 ≤ univ.sup' univ_nonempty (epsD q w ℓ) := by
  by_contra h
  push Not at h
  have hall : ∀ i, epsD q w ℓ i < 0 := fun i =>
    lt_of_le_of_lt (Finset.le_sup' (epsD q w ℓ) (mem_univ i)) h
  have h1 : ∑ i, epsD q w ℓ i < 0 := Finset.sum_neg (fun i _ => hall i) univ_nonempty
  rw [epsD_sum w ℓ hw0] at h1
  have : (0 : ℤ) ≤ ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by positivity
  linarith

/-- **`lem:drift`(3)**. -/
lemma drift_eta_core (hq : 10 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hw2 : ∀ c, |w c| ≤ 2) :
    (∀ i n, -(q : ℤ) ^ 2 ≤ 2 * excess3 q (colStep q (colPhi q w ℓ) i n) ∧
      excess3 q (colStep q (colPhi q w ℓ) i n) ≤ (q : ℤ) ^ 2) ∧
    (∀ i n, excess3 q (colStep q (colPhi q w ℓ) i n) ≤ univ.sup' univ_nonempty (epsD q w ℓ)) ∧
    (∃ i n, excess3 q (colStep q (colPhi q w ℓ) i n) = univ.sup' univ_nonempty (epsD q w ℓ)) ∧
    (colGap q (colPhi q w ℓ) : ℤ) = (q : ℤ) ^ 2 - univ.sup' univ_nonempty (epsD q w ℓ) := by
  have hq' : (10 : ℤ) ≤ q := by exact_mod_cast hq
  have ha : ∀ i, 3 * colA q w i = q + w i := fun i => Int.mul_ediv_cancel' (hw3 i)
  have hρ : ∀ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) ≤ q - 1 := fun i => by
    have := ZMod.val_lt (((ℓ i : ℤ) : ZMod q)); omega
  have hρ0 : ∀ i, (0 : ℤ) ≤ ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := fun i => by positivity
  have hwb : ∀ i, -2 * (q : ℤ) ≤ q * w i ∧ q * w i ≤ 2 * q := fun i => by
    have := abs_le.1 (hw2 i)
    constructor <;> nlinarith
  -- the excess of a step
  have hex : ∀ i n, excess3 q (colStep q (colPhi q w ℓ) i n) =
      epsD q w ℓ i - 3 * q * wrapI q (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val := by
    intro i n
    have hwr := wrapI_cases (q := q) (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val
    have hqa : 3 * ((q : ℤ) * colA q w i) = (q : ℤ) ^ 2 + q * w i := by
      rw [show 3 * ((q : ℤ) * colA q w i) = q * (3 * colA q w i) by ring, ha]; ring
    rw [excess3_eq _ _ (drift_step w ℓ i n)]
    · simp only [epsD]
      linear_combination hqa
    · have := hwb i; have := hρ i; have := hρ0 i
      rcases hwr with h | h <;> rw [h] <;> nlinarith
    · have := hwb i; have := hρ i; have := hρ0 i
      rcases hwr with h | h <;> rw [h] <;> nlinarith
  set M := univ.sup' univ_nonempty (epsD q w ℓ) with hM
  have hle : ∀ i, epsD q w ℓ i ≤ M := fun i => Finset.le_sup' _ (mem_univ i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 3)) (epsD q w ℓ)
  rw [← hM] at hi0
  have hM0 : 0 ≤ M := epsD_max_nonneg w ℓ hw0
  have hJ0 : colJ q ℓ 0 = 0 := by simp [colJ]
  refine ⟨fun i n => ?_, fun i n => ?_, ⟨i0, 0, ?_⟩, ?_⟩
  · rw [hex]
    have := hwb i; have := hρ i; have := hρ0 i
    rcases wrapI_cases (q := q) (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val with h | h <;> rw [h] <;>
      simp only [epsD] <;> constructor <;> nlinarith
  · rw [hex]
    rcases wrapI_cases (q := q) (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val with h | h <;> rw [h] <;>
      have := hle i <;> nlinarith
  · rw [hex, hJ0, ZMod.val_zero]
    have : wrapI q 0 (((ℓ i0 : ℤ) : ZMod q)).val = 0 := by
      simp [wrapI, ZMod.val_lt]
    rw [this, ← hi0]; ring
  · apply gap_formula w ℓ hw3 _ M hle i0 hi0.symm hM0
    · have := hwb i0; have := hρ i0; rw [hi0]; simp only [epsD]; nlinarith
    · intro i; have := hwb i; have := hρ0 i; nlinarith
    · intro i
      apply val_intCast_of
      · have := ha i; have := abs_le.1 (hw2 i); omega
      · have := ha i; have := abs_le.1 (hw2 i); omega

/-- **`lem:drift`(4)**. -/
lemma drift_net_core (hq : 2 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c)
    (hnet : IsNet0 3 q 3 (digPoint q 3 (colGenW q w ℓ))) :
    3 * (q : ℤ) ≤ ∑ i, epsD q w ℓ i ∧ (q : ℤ) ≤ univ.sup' univ_nonempty (epsD q w ℓ) ∧
      (q % 3 = 1 → 2 * (q : ℤ) ≤ univ.sup' univ_nonempty (epsD q w ℓ)) := by
  have hr := drift_net_r hq w ℓ hℓ hnet
  have hs : 3 * (q : ℤ) ≤ ∑ i, epsD q w ℓ i := by rw [epsD_sum w ℓ hw0]; linarith
  have hle : ∀ i, epsD q w ℓ i ≤ univ.sup' univ_nonempty (epsD q w ℓ) :=
    fun i => Finset.le_sup' _ (mem_univ i)
  refine ⟨hs, ?_, fun h => ?_⟩
  · by_contra hc
    push Not at hc
    have : ∑ i, epsD q w ℓ i < 3 * q := by
      calc ∑ i, epsD q w ℓ i < ∑ _i : Fin 3, (q : ℤ) :=
            Finset.sum_lt_sum_of_nonempty univ_nonempty fun i _ => lt_of_le_of_lt (hle i) hc
        _ = 3 * q := by simp
    linarith
  · -- some `w_c ≥ 2`
    have hw : ∃ c, 2 ≤ w c := by
      by_contra hc
      push Not at hc
      have hmod : ∀ c, w c % 3 = 2 := by
        intro c; have := hw3 c; omega
      have hneg : ∀ c, w c ≤ -1 := by
        intro c; have := hc c; have := hmod c; omega
      have : ∑ c, w c < 0 := Finset.sum_neg (fun c _ => by have := hneg c; omega) univ_nonempty
      linarith
    obtain ⟨c, hc⟩ := hw
    have := hle c
    have hρ0 : (0 : ℤ) ≤ ((((ℓ c : ℤ) : ZMod q)).val : ℤ) := by positivity
    simp only [epsD] at this
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith

end Z3NetC.Proofs
