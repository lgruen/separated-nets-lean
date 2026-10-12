/-
Proof module of entry Obs: the compared statements whose proofs need the instance `NeZero q`
(derived here from the hypotheses).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsK

@[expose] public section

namespace Z3NetF.Proofs

open Matrix Finset

lemma q_pos_of_sum {s q : ℕ} {σ : Fin s → ℤ} (h : ∑ c, |σ c| < q) : NeZero q :=
  ⟨by
    have : (0 : ℤ) ≤ ∑ c, |σ c| := Finset.sum_nonneg fun c _ => abs_nonneg _
    omega⟩

theorem ceils_neg {s q k : ℕ} (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : Z3NetF.Mt Φ a a ≤ -1) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - ((|Z3NetF.Mt Φ a a| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ (k - 1)) ^ 2 +
        ∑ u ∈ univ.erase a, (((|Z3NetF.Mt Φ u a| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  haveI : NeZero q := ⟨by omega⟩
  exact ObsCeil.ceils_neg hs hq hk Φ hnet a hcol ha

theorem ceils_pos {s q k : ℕ} (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : 1 ≤ Z3NetF.Mt Φ a a) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      (((((Z3NetF.Mt Φ a a + 1 : ℤ)) : ℝ) ^ 2 +
        ∑ u ∈ univ.erase a, (((|Z3NetF.Mt Φ u a| : ℤ) : ℝ) + 1) ^ 2) / (q : ℝ) ^ 2) := by
  haveI : NeZero q := ⟨by omega⟩
  exact ObsCeil.ceils_pos hs hq hk Φ hnet a hcol ha

theorem ceils_pos_C {s q k C : ℕ} (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : 1 ≤ Z3NetF.Mt Φ a a)
    (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ) (s * ((C : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  haveI : NeZero q := ⟨by omega⟩
  exact ObsCeil.ceils_pos_C hs hq hk Φ hnet a hcol ha hC

theorem P2_ceiling {s q k : ℕ} (hs : 4 ≤ s) (h3k : 3 * k + 4 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b < 0)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - ((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε b| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ 2) ^ 2 +
        ((((Z3NetF.sig (Z3NetF.Mt Φ) a b ε a + 1 : ℤ)) : ℝ) ^ 2 +
          ∑ u ∈ (univ.erase a).erase b, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε u| : ℤ) : ℝ) + 1) ^ 2) /
          (q : ℝ) ^ 2) := by
  haveI := q_pos_of_sum hsum
  exact ObsP2.P2_ceiling hs h3k Φ hnet a b hab ε hε ha hb hsum

theorem P2_forward {s q k : ℕ} (hs : 4 ≤ s) (h3k : 3 * k + 3 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : 0 < ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      (∑ c, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  haveI := q_pos_of_sum hsum
  exact ObsP2.P2_forward hs h3k Φ hnet a b hab ε hε ha hb hsum

theorem P2_forward_C {s q k C : ℕ} (hs : 4 ≤ s) (h3k : 3 * k + 3 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : 0 < ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ) (s * (2 * (C : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  haveI := q_pos_of_sum hsum
  exact ObsP2.P2_forward_C hs h3k Φ hnet a b hab ε hε ha hb hsum hC

theorem L_Kpair {s q k : ℕ} (hs : 4 ≤ s) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (hdiag : ∀ a, Z3NetF.Mt Φ a a ≠ 0) :
    Z3NetF.Kpair (Z3NetF.Mt Φ) = ⊤ ∨ ∃ K : ℕ, Z3NetF.Kpair (Z3NetF.Mt Φ) = K ∧
      Real.sqrt (((s : ℝ) - 3) / 8) ≤ K := by
  haveI : NeZero q := ⟨by omega⟩
  exact ObsL.L_Kpair hs hq hk Φ hnet hdiag

theorem L_pm1 {s q k : ℕ} (hs : 5 ≤ s) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) :
    ¬ ∀ c d, c ≠ d → Z3NetF.Mt Φ c d = 1 ∨ Z3NetF.Mt Φ c d = -1 := by
  haveI : NeZero q := ⟨by omega⟩
  exact ObsL.L_pm1 hs hq hk Φ hnet

end Z3NetF.Proofs
