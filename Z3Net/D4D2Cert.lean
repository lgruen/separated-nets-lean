/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.D4D2CertLB
public import Z3Net.FDeficit

@[expose] public section

/-!
# V14 stage S8: `prop:4D2`, the finite parts from the coded kernel certificates

* `coded`: every configuration `(e, j)` of `cfgs 4 3` has the same `σ` (hence the same `b_i`,
  backward set and cost) as a coded one (`Z3Net/D4D2CertKS.lean`: carry class `0` on the axes that
  do not move);
* `K_eq`: `K(F) = 2` (all costs `≤ 2`, the one-axis step along `∞` without carry costs `2`);
* `S_eq`: `S(F) = 7` (all `|σ_i| ≤ 7`, attained by `e = -(1,1,1,1)` at `i = ∞`);
* `B17`, `B19`, `B21`: the exact relaxation `Bmin q F 3 3 = (q - 2)²` at `q = 17, 19, 21` (all
  `∑ b_i² ≥ (q-2)²`; attained by the one-axis step along `∞`).
-/

namespace Z3NetF.Proofs.D4D2

open Finset Z3NetF

lemma sigma_canon (F : ℕ → Fin 4 → Fin 4 → ℤ) (L : ℕ) (e : Fin 4 → ℤ) (j j' : Fin 4 → ℕ)
    (hj : ∀ d, e d ≠ 0 → min (j' d) (L - 1) = min (j d) (L - 1)) (i : Fin 4) :
    sigma F L e j' i = sigma F L e j i := by
  unfold sigma
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : e d = 0
  · rw [h, zero_mul, zero_mul]
  · rw [hj d h]

/-- Every configuration of `cfgs 4 3` is a coded one up to the carry classes of the axes that do
not move (which `σ` does not see). -/
lemma coded (F : ℕ → Fin 4 → Fin 4 → ℤ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ)
    (hc : IsConfig 3 e j) :
    ∃ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
      (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) ∧
      e = eC e0 e1 e2 e3 ∧ ∀ i, sigma F 3 e (jC j0 j1 j2 j3) i = sigma F 3 e j i := by
  obtain ⟨he, hne, hj⟩ := hc
  have hc : ∀ d, ((e d + 1).toNat) < 3 := fun d => by have := he d; omega
  have hjc : ∀ d, (if e d = 0 then 0 else j d) < 3 := fun d => by
    have := hj d; split_ifs <;> omega
  set ce : Fin 4 → Fin 3 := fun d => ⟨_, hc d⟩ with hce
  set cj : Fin 4 → Fin 3 := fun d => ⟨_, hjc d⟩ with hcj
  have hce1 : ∀ d, ce d = 1 ↔ e d = 0 := fun d => by
    rw [Fin.ext_iff]; simp only [hce, Fin.val_one]; have := he d; omega
  have hcj0 : ∀ d, e d = 0 → cj d = 0 := fun d h => by
    rw [Fin.ext_iff]; simp [hcj, h]
  have hcjm : ∀ d, e d ≠ 0 → min (cj d : ℕ) (3 - 1) = min (j d) (3 - 1) := fun d h => by
    simp only [hcj, if_neg h]
  have hdisj : ∀ d, ce d ≠ 1 ∨ cj d = 0 := fun d => by
    by_cases h : e d = 0
    · exact Or.inr (hcj0 d h)
    · exact Or.inl (fun h' => h ((hce1 d).1 h'))
  have heq : e = eC (ce 0) (ce 1) (ce 2) (ce 3) := by
    funext d
    have : ∀ d, ((ce d : ℕ) : ℤ) - 1 = e d := fun d => by
      simp only [hce]; have := he d; omega
    fin_cases d <;> simp [eC, this]
  refine ⟨ce 0, ce 1, ce 2, ce 3, cj 0, cj 1, cj 2, cj 3, ⟨?_, hdisj 0, hdisj 1, hdisj 2, hdisj 3⟩,
    heq, fun i => sigma_canon F 3 e j _ (fun d hd => ?_) i⟩
  · obtain ⟨d, hd⟩ := hne
    have hd' : ce d ≠ 1 := fun h => hd ((hce1 d).1 h)
    fin_cases d
    · exact Or.inl hd'
    · exact Or.inr (Or.inl hd')
    · exact Or.inr (Or.inr (Or.inl hd'))
    · exact Or.inr (Or.inr (Or.inr hd'))
  · have := hcjm d hd
    fin_cases d <;> simpa [jC] using this

lemma cost_congr (F : ℕ → Fin 4 → Fin 4 → ℤ) (L : ℕ) (e : Fin 4 → ℤ) (j j' : Fin 4 → ℕ)
    (h : ∀ i, sigma F L e j i = sigma F L e j' i) : cost F L e j = cost F L e j' := by
  unfold cost
  rw [Z3NetF.Proofs.Deficit.bwd_congr F F L L e j j' h]
  simp only [h]

lemma bval_sum_congr (q : ℕ) (F : ℕ → Fin 4 → Fin 4 → ℤ) (L : ℕ) (e : Fin 4 → ℤ)
    (j j' : Fin 4 → ℕ) (h : ∀ i, sigma F L e j i = sigma F L e j' i) :
    ∑ i, bval q F L e j i ^ 2 = ∑ i, bval q F L e j' i ^ 2 :=
  Finset.sum_congr rfl fun i _ => by
    rw [Z3NetF.Proofs.Deficit.bval_congr q F F L L e j j' i (h i)]

set_option maxRecDepth 100000 in
/-- `K(F) = 2` (`def:K`). -/
theorem K_eq : Kdef F4D2 3 = 2 := by
  apply le_antisymm
  · refine Finset.sup_le fun ej hej => ?_
    obtain ⟨e0, e1, e2, e3, j0, j1, j2, j3, hpre, he, hs⟩ :=
      coded F4D2 ej.1 ej.2 ((Z3NetF.Proofs.RemK.mem_cfgs (s := 4) (k := 3) ej.1 ej.2).1 hej)
    rw [← cost_congr F4D2 3 ej.1 _ _ hs, he]
    exact cost_le e0 e1 e2 e3 j0 j1 j2 j3 hpre
  · have hmem : (eC 2 1 1 1, jC 0 0 0 0) ∈ cfgs 4 3 :=
      by
        rw [Z3NetF.Proofs.RemK.mem_cfgs]; unfold IsConfig; decide +kernel
    have h2 : cost F4D2 3 (eC 2 1 1 1) (jC 0 0 0 0) = 2 := by decide +kernel
    calc (2 : WithTop ℕ) = cost F4D2 3 (eC 2 1 1 1) (jC 0 0 0 0) := h2.symm
      _ ≤ Kdef F4D2 3 :=
          Finset.le_sup (f := fun ej : (Fin 4 → ℤ) × (Fin 4 → ℕ) => cost F4D2 3 ej.1 ej.2) hmem

set_option maxRecDepth 100000 in
/-- `S(F) = 7` (`def:K`). -/
theorem S_eq : Sdef F4D2 3 = 7 := by
  apply le_antisymm
  · refine Finset.sup_le fun ej hej => Finset.sup_le fun i _ => ?_
    obtain ⟨e0, e1, e2, e3, j0, j1, j2, j3, hpre, he, hs⟩ :=
      coded F4D2 ej.1 ej.2 ((Z3NetF.Proofs.RemK.mem_cfgs (s := 4) (k := 3) ej.1 ej.2).1 hej)
    rw [← hs i, he]
    exact sigma_le e0 e1 e2 e3 j0 j1 j2 j3 hpre i
  · have hmem : (eC 0 0 0 0, jC 0 0 0 0) ∈ cfgs 4 3 :=
      by
        rw [Z3NetF.Proofs.RemK.mem_cfgs]; unfold IsConfig; decide +kernel
    have h7 : (sigma F4D2 3 (eC 0 0 0 0) (jC 0 0 0 0) 0).natAbs = 7 := by decide +kernel
    calc 7 = (sigma F4D2 3 (eC 0 0 0 0) (jC 0 0 0 0) 0).natAbs := h7.symm
      _ ≤ univ.sup fun i => (sigma F4D2 3 (eC 0 0 0 0) (jC 0 0 0 0) i).natAbs :=
          Finset.le_sup (f := fun i => (sigma F4D2 3 (eC 0 0 0 0) (jC 0 0 0 0) i).natAbs)
            (mem_univ _)
      _ ≤ Sdef F4D2 3 := Finset.le_sup
          (f := fun ej : (Fin 4 → ℤ) × (Fin 4 → ℕ) =>
            univ.sup fun i => (sigma F4D2 3 ej.1 ej.2 i).natAbs) hmem

set_option maxRecDepth 100000 in
/-- From the coded bound to `Bmin q F 3 3 = (q-2)²`. -/
lemma Bmin_of (q : ℕ) (hq : 2 ≤ q)
    (hb : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
      (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
      ((q : ℤ) - 2) ^ 2 ≤ ∑ i, bval q F4D2 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2)
    (hw : ∑ i, bval q F4D2 3 (eC 2 1 1 1) (jC 0 0 0 0) i ^ 2 = ((q : ℤ) - 2) ^ 2) :
    Bmin q F4D2 3 3 = ((q : ℤ) - 2) ^ 2 := by
  apply le_antisymm
  · have hmem : (eC 2 1 1 1, jC 0 0 0 0) ∈ cfgs 4 3 :=
      by
        rw [Z3NetF.Proofs.RemK.mem_cfgs]; unfold IsConfig; decide +kernel
    exact (Finset.fold_min_le _).2 (Or.inr ⟨(eC 2 1 1 1, jC 0 0 0 0), hmem, le_of_eq hw⟩)
  · refine (Finset.le_fold_min _).2 ⟨by nlinarith, fun ej hej => ?_⟩
    obtain ⟨e0, e1, e2, e3, j0, j1, j2, j3, hpre, he, hs⟩ :=
      coded F4D2 ej.1 ej.2 ((Z3NetF.Proofs.RemK.mem_cfgs (s := 4) (k := 3) ej.1 ej.2).1 hej)
    rw [← bval_sum_congr q F4D2 3 ej.1 _ _ hs, he]
    exact hb e0 e1 e2 e3 j0 j1 j2 j3 hpre

set_option maxRecDepth 100000 in
theorem B17 : Bmin 17 F4D2 3 3 = 15 ^ 2 := by
  have := Bmin_of 17 (by norm_num) (fun e0 e1 e2 e3 j0 j1 j2 j3 h => by
    have := bnd17 e0 e1 e2 e3 j0 j1 j2 j3 h; push_cast; linarith) (by decide +kernel)
  rw [this]; norm_num

set_option maxRecDepth 100000 in
theorem B19 : Bmin 19 F4D2 3 3 = 17 ^ 2 := by
  have := Bmin_of 19 (by norm_num) (fun e0 e1 e2 e3 j0 j1 j2 j3 h => by
    have := bnd19 e0 e1 e2 e3 j0 j1 j2 j3 h; push_cast; linarith) (by decide +kernel)
  rw [this]; norm_num

set_option maxRecDepth 100000 in
theorem B21 : Bmin 21 F4D2 3 3 = 19 ^ 2 := by
  have := Bmin_of 21 (by norm_num) (fun e0 e1 e2 e3 j0 j1 j2 j3 h => by
    have := bnd21 e0 e1 e2 e3 j0 j1 j2 j3 h; push_cast; linarith) (by decide +kernel)
  rw [this]; norm_num

end Z3NetF.Proofs.D4D2
