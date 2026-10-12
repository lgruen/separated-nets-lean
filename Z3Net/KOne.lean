/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDeficit

@[expose] public section

/-!
# V14 stage S9′: `lem:Kone` (the relaxation stops at one)

The printed proof: the carry-free steps `e = e_a + ε e_b` (`ε = ±1`) move only `a` and `b`, so their
jitter is `1`; if for some `ε` at most one of `a`, `b` is backward, that configuration costs at least
`1` (or `+∞`). Otherwise `M_aa + ε M_ab ≤ 0` for both signs, so `M_aa ≤ -|M_ab| ≤ -1`, and the
one-axis step along `a` without carry costs `-M_aa ≥ 1`.
-/

namespace Z3NetF.Proofs.KOne

open Finset Z3NetF

set_option linter.unusedSectionVars false

variable {s : ℕ}

lemma sigma_zero (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (i : Fin s) :
    sigma F L e 0 i = ∑ d, e d * F 0 i d := by
  simp [sigma, Msum]

lemma cost_ge_one (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ)
    (x y : Fin s) (hxy : x ≠ y) (hx : e x ≠ 0) (hy : e y ≠ 0) (hcard : (bwd F L e j).card ≤ 1) :
    1 ≤ cost F L e j := by
  unfold cost
  split_ifs with h0 h1
  · exact le_top
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
    rw [hb, Finset.sum_singleton]
    have hj : jit e b = 1 := by
      unfold jit
      rw [if_neg]
      rintro ⟨-, h⟩
      by_cases hbx : b = x
      · exact hy (h y (by rw [hbx]; exact hxy.symm))
      · exact hx (h x (Ne.symm hbx))
    rw [hj]
    exact_mod_cast Nat.le_add_left 1 _
  · exfalso; omega

lemma bwd_sub (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ) (a b : Fin s)
    (he : ∀ i, i ≠ a → i ≠ b → e i = 0) : bwd F L e j ⊆ {a, b} := by
  intro i hi
  simp only [bwd, Finset.mem_filter] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_contra h; push Not at h
  exact hi.2.1 (he i h.1 h.2)

/-- **`lem:Kone`**. -/
theorem Kone (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hL : 1 ≤ L) (a b : Fin s) (hab : a ≠ b)
    (h : F 0 a b ≠ 0) : 1 ≤ Kdef F L := by
  -- the two-axis steps `e_a + ε e_b`
  obtain ⟨e, hedef⟩ : ∃ e : ℤ → Fin s → ℤ,
      e = fun ε : ℤ => (Pi.single a (1 : ℤ) + Pi.single b ε : Fin s → ℤ) := ⟨_, rfl⟩
  have hea : ∀ ε, e ε a = 1 := fun ε => by simp [hedef, Pi.single_eq_of_ne hab]
  have heb : ∀ ε, e ε b = ε := fun ε => by simp [hedef, Pi.single_eq_of_ne hab.symm]
  have he0 : ∀ ε i, i ≠ a → i ≠ b → e ε i = 0 := fun ε i hia hib => by
    simp [hedef, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
  have hsig : ∀ ε i, sigma F L (e ε) 0 i = F 0 i a + ε * F 0 i b := by
    intro ε i
    rw [sigma_zero, hedef]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    simp [Pi.single_apply]
  have hmem : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ((e ε, (0 : Fin s → ℕ)) ∈ cfgs s L) := by
    intro ε hε
    simp only [cfgs, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨⟨fun i => ?_, ⟨a, by rw [hea]; norm_num⟩⟩, fun _ => by simp; omega⟩
    by_cases hia : i = a
    · rw [hia, hea]; simp
    · by_cases hib : i = b
      · rw [hib, heb]; rcases hε with rfl | rfl <;> simp
      · rw [he0 ε i hia hib]; simp
  have hstep : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
      ¬ (a ∈ bwd F L (e ε) 0 ∧ b ∈ bwd F L (e ε) 0) → 1 ≤ Kdef F L := by
    intro ε hε hn
    have hcard : (bwd F L (e ε) 0).card ≤ 1 := by
      have hs := bwd_sub F L (e ε) 0 a b (he0 ε)
      by_cases ha' : a ∈ bwd F L (e ε) 0
      · have hb' : b ∉ bwd F L (e ε) 0 := fun hb' => hn ⟨ha', hb'⟩
        have : bwd F L (e ε) 0 ⊆ {a} := by
          intro i hi
          have := hs hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
          rcases this with rfl | rfl
          · rfl
          · exact absurd hi hb'
        exact (Finset.card_le_card this).trans (by simp)
      · have : bwd F L (e ε) 0 ⊆ {b} := by
          intro i hi
          have := hs hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
          rcases this with rfl | rfl
          · exact absurd hi ha'
          · rfl
        exact (Finset.card_le_card this).trans (by simp)
    have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have hk : cost F L (e ε) 0 ≤ Kdef F L :=
      Z3NetF.Proofs.Deficit.cost_le_Kdef F L (ej := (e ε, 0)) (hmem ε hε)
    exact (cost_ge_one F L (e ε) 0 a b hab (by rw [hea]; norm_num) (by rw [heb]; exact hεne)
      hcard).trans hk
  by_cases h1 : a ∈ bwd F L (e 1) 0 ∧ b ∈ bwd F L (e 1) 0
  · by_cases h2 : a ∈ bwd F L (e (-1)) 0 ∧ b ∈ bwd F L (e (-1)) 0
    · -- `M_aa ≤ -|M_ab| ≤ -1`: the one-axis step along `a`
      have p1 := h1.1; have p2 := h2.1
      simp only [bwd, Finset.mem_filter, hea, hsig] at p1 p2
      have hneg : F 0 a a ≤ -1 := by
        have : F 0 a a + F 0 a b ≤ 0 := by simpa using p1.2.2
        have : F 0 a a - F 0 a b ≤ 0 := by simpa [sub_eq_add_neg] using p2.2.2
        rcases lt_or_gt_of_ne h with h' | h' <;> omega
      obtain ⟨ea, headef⟩ : ∃ ea : Fin s → ℤ, ea = Pi.single a (1 : ℤ) := ⟨Pi.single a (1 : ℤ), rfl⟩
      have hma : (ea, (0 : Fin s → ℕ)) ∈ cfgs s L := by
        simp only [cfgs, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset,
          Finset.mem_range]
        refine ⟨⟨fun i => ?_, ⟨a, by simp [headef]⟩⟩, fun _ => by simp; omega⟩
        by_cases hia : i = a
        · rw [hia]; simp [headef]
        · simp [headef, Pi.single_eq_of_ne hia]
      have hsa : sigma F L ea 0 a = F 0 a a := by
        rw [sigma_zero]; simp [headef, Pi.single_apply]
      have hb : bwd F L ea 0 = {a} := by
        ext i
        simp only [bwd, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hi, -⟩
          by_contra hia; exact hi (by simp [headef, Pi.single_eq_of_ne hia])
        · rintro rfl
          refine ⟨by simp [headef], ?_⟩
          rw [hsa]; simp [headef]; omega
      have hc : cost F L ea 0 = (((F 0 a a).natAbs : ℕ) : WithTop ℕ) := by
        unfold cost
        rw [hb, if_neg (by simp), if_pos (by simp), Finset.sum_singleton, hsa]
        have : jit ea a = 0 := by
          unfold jit; rw [if_pos]; exact ⟨by simp [headef], fun d hd => by simp [headef, Pi.single_eq_of_ne hd]⟩
        rw [this, add_zero]
      have : cost F L ea 0 ≤ Kdef F L := Z3NetF.Proofs.Deficit.cost_le_Kdef F L (ej := (ea, 0)) hma
      rw [hc] at this
      refine le_trans ?_ this
      exact_mod_cast (show 1 ≤ (F 0 a a).natAbs by omega)
    · exact hstep (-1) (Or.inr rfl) h2
  · exact hstep 1 (Or.inl rfl) h1

end Z3NetF.Proofs.KOne
