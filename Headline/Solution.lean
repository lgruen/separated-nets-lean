/-
Copyright (c) 2026 Leonhard Gruenschloss. Released under the MIT license.
Author: Leonhard Gruenschloss.
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(revision 14.3), Theorem `thm:A` (results cited by `\label`, never by number).
The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude)
under the author's direction; responsibility rests with the author.
-/
module
public import Z3Net.ThmAMain
public import Z3Net.ThmAFinal
public import Z3Net.ThmAChoice

@[expose] public section

/-!
# Solution of the headline entry (`Headline/Challenge.lean`, `thm:A`)

The definitions are the proof side's own (`Z3Net/FDefs.lean` for `Z3NetF`, `Z3Net/ThmADefs.lean` for
`Z3NetA`); the Challenge holds verbatim copies of those that `theoremA` reaches
(`scripts/check_headline_identity.py`). The theorem is `Z3NetA.thmA` of the full formalization
(`Z3Net/ThmAFinal.lean`; compared in `comparator.json` against `QUNets/Statements/ThmA.lean`), which
assembles `thm:A` from the compared theorems `A_net`, `A_covering` (S3), `A_sep_real`, `A_sep_eucl`
(S3), `A_sharp_real` (S5), `aStar_three` (S4), `aStar_bound`, `aStar_bound_log` (S5).

The three theorems on the choice-defined data come from compared library theorems as well:
`ustarCols_spec` from `Ustar_cols`, `Ustar_cols_unique` (S3); `gamma_spec` from `sat_gamma` (S3) and
`gamS_unique` (S6b); `net_wellDefined` from `A_hom`, `Ustar_reach`, `Ustar_data` (S3) and
`Apoint_indep` (S6b, `Z3Net/ThmAChoice.lean`; via `Z3NetF.PGen_indep`).
-/

namespace Z3NetA

open Matrix Finset Z3NetF

theorem theoremA (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Apoint s q k) ∧
    (∀ x : Fin s → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∃ v : Fin (s * k) → ZMod q,
      Real.sqrt (∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) ≤
        Real.sqrt s * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    (5 * aStar s + 4 ≤ q → ∀ v w : Fin (s * k) → ZMod q, v ≠ w →
      (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) ∧
        (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2)) ∧
    (2 ≤ k → 5 * aStar s + 4 ≤ q → (s - 1) * aStar s < q → ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    aStar 3 = 2 ∧
    (4 ≤ s →
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) ∧
      |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
        s * Real.log s| ≤ 3 * s) :=
  thmA s q k hs hq hk

theorem ustarCols_spec {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) :
    IsUstarCols d (Ecol d) ∧ ∀ B : ℕ → Fin s → ℤ, IsUstarCols d B → B = Ecol d :=
  ⟨Ustar_cols hs d, Ustar_cols_unique hs d⟩

theorem gamma_spec {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧
      (∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j) ∧
      ∀ γ : ℚ, 0 < γ → (∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ) →
        γ = gamS d j :=
  ⟨(sat_gamma hs d j hj).1, (sat_gamma hs d j hj).2.2,
    fun γ hγ hgen => gamS_unique hs d j hj γ hγ hgen⟩

theorem net_wellDefined (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) :
    Nonempty (RS s →+* ZMod q) ∧
      (∃ Ur : Fin s → ℕ → ℕ → RS s, Residual (0 : Fin s) placeA (UstarR s) 1 Ur) ∧
      (∃ β : Fin s → ℕ → ℕ → RS s, BetaRel (0 : Fin s) placeA (UstarR s) 1 β) ∧
      ∀ (ψ : RS s →+* ZMod q) (Ur β : Fin s → ℕ → ℕ → RS s),
        Residual (0 : Fin s) placeA (UstarR s) 1 Ur → BetaRel (0 : Fin s) placeA (UstarR s) 1 β →
        Apoint s q k = digPoint q (s * k) (fun c =>
          (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) :=
  ⟨(A_hom s q hs hq).1, (Ustar_reach hs).2, ⟨betaS s, (Ustar_data hs).2⟩,
    fun ψ Ur β hres hβ => Apoint_indep s q k hs ψ Ur β hres hβ⟩

end Z3NetA

#print axioms Z3NetA.theoremA
#print axioms Z3NetA.ustarCols_spec
#print axioms Z3NetA.gamma_spec
#print axioms Z3NetA.net_wellDefined
