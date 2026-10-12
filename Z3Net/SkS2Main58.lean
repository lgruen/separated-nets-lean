/-
Entry S2: `thm:S2`(2) as one statement (`S2_main58`), assembled from `S2_thr`, `S2_net`,
`lem:G2N1`(c) and `S2_sep`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkGThr
public import Z3Net.SkGN1
public import Z3Net.SkCompS
public import Z3Net.SkSepS2Final

@[expose] public section

namespace Z3NetF.Proofs

open Matrix Finset

theorem S2_main58 (s p k : ℕ) [Fact p.Prime] (hs5 : 5 ≤ s) (hs8 : s ≤ 8) (hp : S2pthr s ≤ p)
    (hk : 1 ≤ k) (D1 : Finset ℕ) (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2) :
    Fs s + 1 ≤ Bp s p ∧
      (∃ C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p),
        IsS2skel s p k D1 C ∧ IsNet0 s p (s * k + (s - 2)) (digPoint p (s * k + (s - 2)) C)) ∧
      ∀ C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p),
        IsS2skel s p k D1 C → ∀ v w : Fin (s * k + (s - 2)) → ZMod p, v ≠ w →
          (Bp s p - Fs s) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
            torusDist2 (p ^ (s * k + (s - 2))) (digPoint p (s * k + (s - 2)) C v)
              (digPoint p (s * k + (s - 2)) C w) := by
  have hthr := S2_thr s p hs5 hs8
  have hB : Fs s + 1 ≤ Bp s p :=
    hthr.1.2 ((hthr.2 (Fact.out : p.Prime)).2 hp)
  refine ⟨hB, S2_net s p k hs5 hk D1 hD1 hB (G2N1_c s (Bp s p) hs5 (Or.inl ⟨hs8, hB⟩)), ?_⟩
  intro C hC v w hvw
  exact S2_sep s p k hs5 hk D1 hD1 hD1c C hC v w hvw

end Z3NetF.Proofs
