/-
Proof module (V14 stage S16′): `thm:col`(1), the integer box minors of the boxes with depth 3, and
`lem:drift`(2), the excesses of a cycle.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ColNet

@[expose] public section

/-!
# `thm:col`(1) over `ℤ` and the excesses of `lem:drift`(2)

* `colZ_lift`, `colZ_box3`: the integer generator matrices of `𝒞_q` (rows `e_c`, `a`, `b = (-1, 1, 0)`) reduce to
  `colGen q` modulo `q`, and the box with depth `3` on `c` (the whole matrix of coordinate `c`) has the integer
  determinant `-a_z` for `c = x, y` and `a_x + a_y` for `c = z` (the `2 × 2` minors of `(a, b)` on the two other
  columns are `-a_z`, `a_z`, `a_x + a_y`).
* `drift_excess_core`: under the range hypothesis of `lem:drift`(2) (or `|w_i| ≤ 2`, `q ≥ 4`), the excess of the step
  at `n` along `e_i` (thrice: `excess3`) is `3ε_i` if the third digit does not wrap and `3ε_i − 3q` if it wraps.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

/-- The integer generator matrices of `𝒞_q`: rows `e_c`, `a`, `b = (-1, 1, 0)`. -/
abbrev colGenZ (q : ℕ) (c : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![(Pi.single c 1 : Fin 3 → ℤ), fun d => colA q (wCol q) d, ellCol]

lemma colZ_lift (q : ℕ) (c : Fin 3) : (colGenZ q c).map (Int.cast : ℤ → ZMod q) = colGen q c := by
  ext r l
  fin_cases r <;> fin_cases c <;> fin_cases l <;> simp [colGenZ, colGen, colGenW]

lemma colZ_single_three (c : Fin 3) :
    (Pi.single c 3 : Fin 3 → ℕ) = if c = 0 then ![3, 0, 0] else if c = 1 then ![0, 3, 0] else ![0, 0, 3] := by
  fin_cases c <;> funext d <;> fin_cases d <;> rfl

lemma colZ_box3 (q : ℕ) (c : Fin 3) :
    (boxMatrix (colGenZ q) (Pi.single c 3)).det =
      if c = 2 then colA q (wCol q) 0 + colA q (wCol q) 1 else -colA q (wCol q) 2 := by
  rw [colZ_single_three]
  fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ite_true, ite_false, Fin.isValue,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide] <;>
    simp only [box300, box030, box003] <;>
    rw [Matrix.det_fin_three] <;>
    simp [colGenZ, ellCol]

/-- **`lem:drift`(2)**, the excesses of a cycle: under the range hypothesis (or its instance `|w_i| ≤ 2`, `q ≥ 4`),
the excess (thrice) of the step at `n` along `e_i` is `q w_i + 3 r_i` if the third digit does not wrap and
`q w_i + 3 r_i − 3q` if it wraps. -/
lemma drift_excess_core {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (hR : (2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2) ∨
      (|w i| ≤ 2 ∧ 4 ≤ q))
    (n : Fin 3 → ZMod q) :
    excess3 q (colStep q (colPhi q w ℓ) i n) =
      (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val -
        (if (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q then (0 : ℤ) else 3 * q) := by
  have hR' : 2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 := by
    rcases hR with h | ⟨hw, hq⟩
    · exact h
    · exact drift_range w ℓ i hw hq
  set ρ := (((ℓ i : ℤ) : ZMod q)).val
  have ha : 3 * colA q w i = q + w i := Int.mul_ediv_cancel' (hw3 i)
  have hwr : wrapI q (colJ q ℓ n).val ρ = 0 ∨ wrapI q (colJ q ℓ n).val ρ = 1 := by
    unfold wrapI; split_ifs <;> simp
  have hqa : 3 * ((q : ℤ) * colA q w i) = (q : ℤ) ^ 2 + q * w i := by
    rw [show 3 * ((q : ℤ) * colA q w i) = q * (3 * colA q w i) by ring, ha]; ring
  have b1 := abs_two _ _ hR'.1
  have b2 := abs_two _ _ hR'.2
  have hite : (if (colJ q ℓ n).val + ρ < q then (0 : ℤ) else 3 * q) = 3 * q * wrapI q (colJ q ℓ n).val ρ := by
    unfold wrapI; split_ifs <;> ring
  rw [hite, excess3_eq _ _ (drift_step w ℓ i _)]
  · rw [show (3 : ℤ) * (q * colA q w i + ρ - q * wrapI q (colJ q ℓ n).val ρ) =
      3 * (q * colA q w i) + 3 * ρ - 3 * q * wrapI q (colJ q ℓ n).val ρ by ring, hqa]; ring
  · rcases hwr with h | h <;> rw [h] <;> linarith
  · rcases hwr with h | h <;> rw [h] <;> linarith

end Z3NetC.Proofs
