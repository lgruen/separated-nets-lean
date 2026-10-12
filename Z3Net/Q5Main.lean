/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.TDNorm
public import Z3Net.Q5Sep

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S11′ (`thm:D`, `lem:R2`, `prop:half5`)

The compared theorems of `scripts/v14_delta.py` (stage S11′, `NEW`), restated by name with the same statements as in
`QUNets/Statements/Split.lean`. `thm:D`: `Z3Net/TDNorm.lean` (assembly and normalization), `Z3Net/TDSkew.lean` (the
skew case, by hand), `Z3Net/TDBal.lean` (balance), `Z3Net/TDHand.lean` (diagonal, minor tax), `Z3Net/TDEnum.lean`
and the kernel runs `Z3Net/TDCert*.lean` (the normalized non-skew case). `lem:R2`: `Z3Net/R2Sep.lean`.
`prop:half5`: `Z3Net/Q5Sep.lean` (with the checkers `Z3Net/Q5CertDefs.lean` and the scans `Z3Net/Q5Scan*.lean`).
-/

namespace Z3NetHL

open Matrix Finset

/-- **`thm:D`** (the least drift), doubled (`F2 = 2F₀`): every `F₀ ∈ (½ + ℤ)^{5×5}` (`F2` odd) with (B2) and (MIN)
(`DisjMinors`: every minor of `F₀` with disjoint row and column sets is nonzero), with entries of any size, has
`dr(F₀) ≥ 17/2`: some binding step `E` (`E ∈ {-1, 0, 1}⁵`, `∑ E` odd) has `2 dr(E) ≥ 17`. -/
theorem thmD (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hB2 : B2D F2)
    (hmin : DisjMinors F2) : 17 ≤ drift2 F2 :=
  Proofs.TD.thmD_bound F2 hodd hB2 hmin

/-- **`thm:D`, attained**: the layer `F₀*` of `prop:half5` satisfies (Half), (B2) and (MIN), and
`dr(F₀*) = 17/2`. -/
theorem thmD_star : (∀ c d, Odd (F2star c d)) ∧ B2D F2star ∧ DisjMinors F2star ∧ drift2 F2star = 17 :=
  ⟨Proofs.TD.F2star_odd, Proofs.TD.F2star_B2, Proofs.TD.F2star_disj, Proofs.TD.F2star_drift⟩

/-- **`thm:D`, the skew layers** (the part of the printed proof by hand): if moreover the off-diagonal part of
`F₀` is skew-symmetric, `dr(F₀) ≥ 17/2`. -/
theorem thmD_skew (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hB2 : B2D F2)
    (hmin : DisjMinors F2) (hskew : ∀ c d, c ≠ d → F2 c d + F2 d c = 0) : 17 ≤ drift2 F2 :=
  Proofs.TD.thmD_skew_core F2 hodd hB2 hmin hskew

/-- **The symmetry of `thm:D`** (the normalization in its proof): conjugation by a permutation matrix and a diagonal
sign matrix, `F₀ ↦ (ε_c ε_d F₀[σc][σd])`, keeps `dr`. -/
theorem thmD_conj (F2 : Fin 5 → Fin 5 → ℤ) (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ℤ)
    (hε : ∀ c, ε c = 1 ∨ ε c = -1) : drift2 (fun c d => ε c * ε d * F2 (σ c) (σ d)) = drift2 F2 :=
  Proofs.TD.drift2_conj F2 σ ε hε

/-- **`lem:R2`** (the two-digit relaxation): let `q` be odd (the paper: an odd prime), `s ≥ 3`, and let a graph form
over `ℤ/qℤ` with depths `(1, …, 1)` have first offset rows `F₀ = F2/2 ∈ (½ + ℤ)^{s×s}` (`F2` odd, `½ ≡ (q+1)/2`)
and second offset rows `D₁ ∈ ℤ^{s×s}` (deeper rows arbitrary; a digital net or not). If `q > |2β_c|` and
`q > |v_c|` (`β = F₀E`, `v = D₁E`) for all `E ∈ {-2, …, 2}^s` and all `c`, then `δ N^(1/s) ≥ LB₂(q)` for the
toroidal distance (`N = q^s`; `LB₂` with the options of `prop:Hk` for the first digit and `{v_c, v_c − q sgn v_c}`
for the second). -/
theorem R2_sep (s q : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (F2 D1 : Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q)
    (hrow : RowDesign s q 1 Φ (fun _ => F2)) (hrow1 : Row1Design s q Φ D1) (hodd : ∀ c d, Odd (F2 c d))
    (hβ : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR F2 E c| < q)
    (hv : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR D1 E c| < q)
    (x y : Fin (s * 1) → ZMod q) (hxy : x ≠ y) :
    LB2R q F2 D1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * 1))
          ((GFpoint s q 1 Φ x c : ℤ) - (GFpoint s q 1 Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * 1)) ^ 2) :=
  Proofs.R2_sep_core s q Φ F2 D1 hs hqodd hrow hrow1 hodd hβ hv x y hxy

/-- **`prop:half5`(1)**: `𝒬*_p` is a digital `(0,5,5)`-net over `𝔽_p` for every prime `p ≥ 7`. -/
theorem qstar_net (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) : IsNet0 5 p (5 * 1) (Qstar p) :=
  Proofs.Q5.qstar_net p hp h7

/-- **`prop:half5`(2)**: for every prime `p ≥ 37`, `δ N^(1/5) > 1` for `𝒬*_p` (toroidal distance, `N = p⁵`). -/
theorem qstar_sep (p : ℕ) (hp : p.Prime) (h37 : 37 ≤ p) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) :=
  Proofs.Q5.qstar_sep p hp h37 x y hxy

/-- **`prop:half5`(2), the bounds of the proof of the limit**: for every prime `p > 32`, any two distinct points of
`𝒬*_p` have toroidal distance `≥ (√5/2 − 12√5/p) N^(-1/5)` (`λ − √5(2A+1)/p` with `λ = √5/2`, `A = 11/2`), and some
two distinct points have Euclidean distance `≤ (√5/2 + 4√5/p) N^(-1/5)` (`prop:Hk`(3) with `C = 3/2`). -/
theorem qstar_bounds (p : ℕ) (hp : p.Prime) (h32 : 32 < p) :
    (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
      (Real.sqrt 5 / 2 - 12 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
        ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
            (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
      Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
        ≤ (Real.sqrt 5 / 2 + 4 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) :=
  Proofs.Q5.qstar_bounds p hp h32

/-- **`prop:half5`(2), the limit**: `δ N^(1/5) → √5/2` as the prime `p → ∞`: for every `ε > 0` there is `P` such that
for every prime `p ≥ P` all distinct points of `𝒬*_p` have toroidal distance `≥ (√5/2 − ε) N^(-1/5)` and some two
distinct points have Euclidean distance `≤ (√5/2 + ε) N^(-1/5)`. -/
theorem qstar_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
        (Real.sqrt 5 / 2 - ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
              (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
      ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
        Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
          ≤ (Real.sqrt 5 / 2 + ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) :=
  Proofs.Q5.qstar_limit ε hε

/-- **`prop:half5`(3)**: for every prime `p ≥ 53`, every graph form over `𝔽_p` with depths `(1, …, 1)` and first
offset rows `F₀*` (row `0` of every block is `F₀*`, `½ ≡ (p+1)/2`; deeper rows arbitrary) has `δ N^(1/5) > 1`
(toroidal). -/
theorem qstar_hk (p : ℕ) (hp : p.Prime) (h53 : 53 ≤ p)
    (Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 5 p 1 Φ (fun _ => F2star)) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((GFpoint 5 p 1 Φ x c : ℤ) - (GFpoint 5 p 1 Φ y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) :=
  Proofs.Q5.qstar_hk p hp h53 Φ hrow x y hxy

end Z3NetHL
