/-
Proof module of entries Skel and S2 (`prop:S1E` net, `thm:S2` nets, from `prop:skelcomp`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkCompIII
public import Z3Net.SkNecBridge
public import Z3Net.SkGN1

@[expose] public section

/-!
# Entries Skel and S2: the nets of `prop:S1E` and `thm:S2`

* `S1E_net`: `prop:skelcomp`(ii) on the frame of `def:S1` (`z` at `∞`, the full coordinates at
  `0, 1, …, s-2`, distinct modulo `p` as `s - 1 ≤ p`), read through `skel_graphGen`.
* `SkComp.S2_gen`: `prop:skelcomp`(iii) with `g = (1, -1)`, `o = 0`, read through `skel_graphGen`.
* `S2_net4` (`s = 4`, `A = [[ρ, 1], [1, ρ]]`, `2 ≤ ρ ≤ p - 2`) and `S2_net` (`s ≥ 5`,
  `A = A(B(p))`, (N1) by `G2N1_b`); (N2) is `g = ±1 ≠ 0`, (N3) holds since `β_·d` is a unit vector.
-/

namespace Z3NetF.Proofs

namespace SkComp

lemma zmod_cast_inj (p : ℕ) (a b : ℕ) (ha : a < p) (hb : b < p) (h : (a : ZMod p) = b) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

lemma zmod_cast_ne_zero (p : ℕ) (a : ℕ) (ha0 : 0 < a) (ha : a < p) : (a : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd ha0 h) (by omega)

/-- `prop:skelcomp`(iii) with `g = (1, -1)`, `o = 0`, as skeleton digits (`IsSkGF` form). -/
lemma S2_gen (p : ℕ) [Fact p.Prime] (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (A β : Fin 2 → ℕ → ZMod p) (hA : ∀ i d, d < r → A i d ≠ 0)
    (hA2 : ∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0)
    (hβ : ∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) :
    ∃ C : Fin (r + 2) → Matrix (Fin ((r + 2) * k + r)) (Fin ((r + 2) * k + r)) (ZMod p),
      Z3NetF.IsSkGF (r + 2) r p k C ∧
      (∀ (i : Fin 2) (z d : Fin (r + 2)), (z : ℕ) = r + (i : ℕ) →
        ∀ l < Z3NetF.skDepth r k d, Z3NetF.ent (C z) k (Z3NetF.skOff r k (d : ℕ) + l) =
          Z3NetF.sk2Coef r k A β ![1, -1] 0 i (d : ℕ) l) ∧
      Z3NetF.IsNet0 (r + 2) p ((r + 2) * k + r) (Z3NetF.digPoint p ((r + 2) * k + r) C) := by
  have hg : ∀ i, (![1, -1] : Fin 2 → ZMod p) i ≠ 0 := by
    have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
    intro i
    fin_cases i
    · exact h1
    · show (-1 : ZMod p) ≠ 0
      exact fun h => h1 (neg_eq_zero.mp h)
  obtain ⟨inf, x, hx, H⟩ := skelcomp_iii p r hr A β ![1, -1] 0 hA hA2 hg hβ
  obtain ⟨L, U, Φ, -, -, -, hkey, hnet⟩ := H k hk
  have hB := skel_graphGen (r + 2) r p k (by omega) Φ
  refine ⟨_, hB.1, ?_, hnet⟩
  intro i z d hz l hl
  have hzz : z = Fin.natAdd r i := Fin.ext (by simp [hz])
  subst hzz
  exact (hB.2 _ d (by simp) ⟨l, hl⟩).trans (hkey i d ⟨l, hl⟩)

end SkComp

open SkComp in
/-- **`prop:S1E`, net.** -/
theorem S1E_net (p : ℕ) [Fact p.Prime] (s k : ℕ) (hs : 3 ≤ s) (hp : s - 1 ≤ p) (κ : ℕ → ZMod p)
    (hκ : ∀ d, d + 1 < s → κ d ≠ 0) :
    ∃ C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p),
      IsS1Kskel s p k κ C ∧ IsNet0 s p (s * k + (s - 1)) (digPoint p (s * k + (s - 1)) C) := by
  set inf : Fin s := ⟨s - 1, by omega⟩ with hinf
  set x : Fin s → ZMod p := fun c => ((c : ℕ) : ZMod p) with hxdef
  have hfin : ∀ c : Fin s, c ≠ inf → (c : ℕ) < s - 1 := by
    intro c hc
    have := c.isLt
    have : (c : ℕ) ≠ s - 1 := fun h => hc (Fin.ext h)
    omega
  have hx : PlacesOK inf x := by
    intro c d hc hd hcd
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    have hc' := hfin c hc
    have hd' := hfin d hd
    exact hcd (Fin.ext (zmod_cast_inj p _ _ (by omega) (by omega) (sub_eq_zero.mp h)))
  obtain ⟨L, U, Φ, -, -, -, hrow, hnet⟩ := skelcomp_ii p s k (by omega) inf x hx κ hκ
  have hB := skel_graphGen s (s - 1) p k (by omega) Φ
  refine ⟨_, ⟨hB.1, ?_⟩, hnet⟩
  intro z d hz l hl
  exact (hB.2 z d (by omega) ⟨l, hl⟩).trans (hrow z d hz ⟨l, hl⟩)

open SkComp in
/-- **`thm:S2`(1)**, net (`s = 4`). -/
theorem S2_net4 (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k) :
    ∃ C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p),
      IsS2skel 4 p k {1} C ∧ IsNet0 4 p (4 * k + 2) (digPoint p (4 * k + 2) C) := by
  set ρ := rhoT p with hρdef
  have hρ2 : 2 ≤ ρ := Nat.le_findGreatest (by omega) (by omega)
  have hρsq : ρ ^ 2 < p + 4 :=
    Nat.findGreatest_of_ne_zero (P := fun ρ => ρ ^ 2 < p + 4) rfl (by omega)
  have hρp : ρ + 2 ≤ p := by
    by_contra h
    have h1 : p - 1 ≤ ρ := by omega
    have h2 : (p - 1) ^ 2 ≤ ρ ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : p + 4 ≤ (p - 1) ^ 2 := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
      simp only [show q + 5 - 1 = q + 4 by omega]
      nlinarith
    omega
  set A : Fin 2 → ℕ → ZMod p := fun i d => ((S2A 4 p i d : ℤ) : ZMod p) with hAdef
  set β : Fin 2 → ℕ → ZMod p := fun i d => ((betaD {1} i d : ℤ) : ZMod p) with hβdef
  have hAval : ∀ (i : Fin 2) (d : ℕ), A i d = if (i : ℕ) = d then (ρ : ZMod p) else 1 := by
    intro i d
    simp only [hAdef, S2A, if_true, AT]
    split_ifs <;> simp [hρdef]
  have hρ0 : (ρ : ZMod p) ≠ 0 := zmod_cast_ne_zero p ρ (by omega) (by omega)
  have hρm1 : (ρ : ZMod p) - 1 ≠ 0 := by
    have := zmod_cast_ne_zero p (ρ - 1) (by omega) (by omega)
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
  have hρp1 : (ρ : ZMod p) + 1 ≠ 0 := by
    have := zmod_cast_ne_zero p (ρ + 1) (by omega) (by omega)
    rwa [Nat.cast_add, Nat.cast_one] at this
  have hρsq1 : (ρ : ZMod p) * ρ - 1 * 1 ≠ 0 := by
    have e : (ρ : ZMod p) * ρ - 1 * 1 = ((ρ : ZMod p) - 1) * ((ρ : ZMod p) + 1) := by ring
    rw [e]; exact mul_ne_zero hρm1 hρp1
  have hA : ∀ i d, d < 2 → A i d ≠ 0 := by
    intro i d hd
    rw [hAval]
    split_ifs
    · exact hρ0
    · exact one_ne_zero
  have hA2 : ∀ d d', d < 2 → d' < 2 → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0 := by
    intro d d' hd hd' hdd'
    rw [hAval, hAval, hAval, hAval]
    rcases (show (d = 0 ∧ d' = 1) ∨ (d = 1 ∧ d' = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hρsq1
    · intro h
      apply hρsq1
      have h' : (1 : ZMod p) * 1 - ρ * ρ = 0 := by simpa using h
      linear_combination -h'
  have hβ : ∀ d, d < 2 → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0 := by
    intro d hd
    rw [hAval, hAval]
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · have e1 : β 1 0 = 1 := by simp [hβdef, betaD]
      have e0 : β 0 0 = 0 := by simp [hβdef, betaD]
      rw [e1, e0]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, show (1 : ℕ) ≠ 0 by omega,
        if_false]
      intro h; apply hρ0; linear_combination h
    · have e1 : β 1 1 = 0 := by simp [hβdef, betaD]
      have e0 : β 0 1 = 1 := by simp [hβdef, betaD]
      rw [e1, e0]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, show (0 : ℕ) ≠ 1 by omega,
        if_false]
      intro h; apply hρ0; linear_combination -h
  obtain ⟨C, h1, h2, h3⟩ := S2_gen p 2 k (by norm_num) hk A β hA hA2 hβ
  exact ⟨C, ⟨h1, fun i z d hz l hl => h2 i z d hz l hl⟩, h3⟩

open SkComp in
/-- **`thm:S2`(2), (3)**, net (`s ≥ 5`). -/
theorem S2_net (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ Finset.range (s - 2)) (hB : Fs s + 1 ≤ Bp s p)
    (harc : ∑ j ∈ Finset.range (s - 3), Real.arctan (1 / (cG (Bp s p) j : ℝ)) < Real.pi / 2) :
    ∃ C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p),
      IsS2skel s p k D1 C ∧ IsNet0 s p (s * k + (s - 2)) (digPoint p (s * k + (s - 2)) C) := by
  have hB1 : 1 ≤ Bp s p := by unfold Fs at hB; omega
  obtain ⟨hN1a, hN1b⟩ := G2N1_b s (Bp s p) p hs hB1 (SkG.Bp_spec s p hB1) harc
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 2 := ⟨s - 2, by omega⟩
  have hs4 : r + 2 ≠ 4 := by omega
  set A : Fin 2 → ℕ → ZMod p := fun i d => ((S2A (r + 2) p i d : ℤ) : ZMod p) with hAdef
  set β : Fin 2 → ℕ → ZMod p := fun i d => ((betaD D1 i d : ℤ) : ZMod p) with hβdef
  have hAval : ∀ i d, A i d = ((AG (r + 2) (Bp (r + 2) p) i d : ℤ) : ZMod p) := by
    intro i d
    simp only [hAdef, S2A, if_neg hs4]
  have hA : ∀ i d, d < r → A i d ≠ 0 := by
    intro i d hd
    rw [hAval]
    exact hN1a i d (by omega)
  have hA2 : ∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0 := by
    intro d d' hd hd' hdd'
    rw [hAval, hAval, hAval, hAval]
    have h := hN1b d d' (by omega) (by omega) hdd'
    push_cast at h
    exact h
  have hβ : ∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0 := by
    intro d hd
    have h0 := hA 0 d hd
    have h1 := hA 1 d hd
    by_cases hdD : d ∈ D1
    · have e : β 1 d = 0 := by simp [hβdef, betaD, hdD]
      have e' : β 0 d = 1 := by simp [hβdef, betaD, hdD]
      rw [e, e']
      intro h; apply h1; linear_combination -h
    · have e : β 1 d = 1 := by simp [hβdef, betaD, hdD]
      have e' : β 0 d = 0 := by simp [hβdef, betaD, hdD]
      rw [e, e']
      intro h; apply h0; linear_combination h
  obtain ⟨C, h1, h2, h3⟩ := S2_gen p r k (by omega) hk A β hA hA2 hβ
  exact ⟨C, ⟨h1, fun i z d hz l hl => h2 i z d hz l hl⟩, h3⟩

end Z3NetF.Proofs
