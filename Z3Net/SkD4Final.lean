/-
Development module (Solution side) for `cor:dim4` (entry S2). Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkD4
-- The modules proving `Z3NetF.Proofs.S2_net4` and `Z3NetF.Proofs.S2_sep4_real` (written in
-- parallel; adjust the two imports below to their final names):
public import Z3Net.SkCompS
public import Z3Net.SkSepS2Final

@[expose] public section

/-!
# `cor:dim4` (residues `m ≢ 1 (mod 4)`), final instantiation

`SkD4.dim4_of` applied to `thm:S2`(1) (`Z3NetF.Proofs.S2_net4`, `Z3NetF.Proofs.S2_sep4_real`).
-/

namespace Z3NetF.Proofs

open Matrix Finset

/-- **`cor:dim4`**, the residues `m ≢ 1 (mod 4)` (statement verbatim from `ChallengeS2.lean`). -/
theorem dim4 (p : ℕ) [Fact p.Prime] (h23 : 23 ≤ p) (h83 : p ≤ 83) :
    ∃ Cp : ℝ, ∀ m : ℕ, 3 ≤ m → m ≠ 4 → m % 4 ≠ 1 →
      ∃ C : Fin 4 → Matrix (Fin m) (Fin m) (ZMod p), IsNet0 4 p m (digPoint p m C) ∧
        (∀ v w : Fin m → ZMod p, v ≠ w →
          1 / Real.sqrt 31 * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) ≤
            Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ m) ^ 2)) ∧
        ∀ y : Fin 4 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
          Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
            Cp * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) :=
  SkD4.dim4_of p h23 h83 (fun k hk => S2_net4 p k (by omega) hk)
    (fun k hk C hC v w hvw => S2_sep4_real p k (by omega) hk C hC v w hvw)

end Z3NetF.Proofs
