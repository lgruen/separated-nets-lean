/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColDefs

@[expose] public section

/-!
# V14 stage S9′: `lem:shared` (shared digits)

A `(0,m,s)`-net in base `q`, digital or not, is a family `X` of `q^m` integer points (integer scale
`q^m`; the digits `0, …, m-1` of a point of `[0,1)^s` are those of `⌊q^m x⌋`) such that every
elementary box of volume `q^{-m}` holds exactly one of them (`Z3NetF.IsNet0`).

* `net_lt`: every point lies in `[0, q^m)^s` (the boxes of shape `m e_c`).
* `digit_count`: among `x < q^k` the digit with index `p < k` (from the bottom) takes each value
  `q^{k-1}` times.
* `shared_count`: the box of shape `d_a = j+1`, `d_b = m-j-1` (zero elsewhere) holds exactly one
  point, so the pair of digits with index `j` of `a` and `b` takes each value `q^{m-2}` times. (The
  printed proof uses `d_a = d_b = j+1`, the remaining depth elsewhere; for `s = 2` and
  `2(j+1) < m` there is no such shape, while `d_b = m-j-1 ≥ j+1` works for every `s ≥ 2`.)
* `shared_fun`: a functional dependence of the two digits forces `2(j+1) > m`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset

set_option linter.unusedSectionVars false

/-- Every point of a `(0,m,s)`-net lies in `[0, q^m)^s`. -/
lemma net_lt {s q m : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin s → ℕ) (hX : IsNet0 s q m X)
    (v : Fin m → ZMod q) (c : Fin s) : X v c < q ^ m := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hbox : ∀ A : Fin (q ^ m), ∃! v : Fin m → ZMod q,
      ∀ c', X v c' / q ^ (m - (Pi.single c m : Fin s → ℕ) c') =
        (Pi.single c (A : ℕ) : Fin s → ℕ) c' := by
    intro A
    apply hX
    · simp [Finset.sum_pi_single']
    · intro c'
      by_cases h : c' = c
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
  choose φ hφ hφu using hbox
  have hinj : Function.Injective φ := by
    intro A B h
    have h1 := hφ A c
    have h2 := hφ B c
    simp only [Pi.single_eq_same, Nat.sub_self, pow_zero, Nat.div_one] at h1 h2
    exact Fin.ext (by rw [← h1, ← h2, h])
  have hcard : Fintype.card (Fin (q ^ m)) = Fintype.card (Fin m → ZMod q) := by
    simp [ZMod.card]
  obtain ⟨A, rfl⟩ := ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩).2 v
  have h1 := hφ A c
  simp only [Pi.single_eq_same, Nat.sub_self, pow_zero, Nat.div_one] at h1
  rw [h1]; exact A.isLt

/-- The digit with index `p` from the bottom of `x < q^k` takes each value `q^{k-1}` times. -/
lemma digit_count (q p k β : ℕ) (hq : 0 < q) (hp : p < k) (hβ : β < q) :
    ((range (q ^ k)).filter (fun x => x / q ^ p % q = β)).card = q ^ (k - 1) := by
  have hk : q ^ k = q ^ p * q * q ^ (k - p - 1) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have hk1 : q ^ (k - 1) = q ^ p * q ^ (k - p - 1) := by rw [← pow_add]; congr 1; omega
  have hcp : (range (q ^ p) ×ˢ range (q ^ (k - p - 1))).card = q ^ p * q ^ (k - p - 1) := by simp
  rw [hk1, ← hcp]
  have hqp : 0 < q ^ p := pow_pos hq p
  apply Finset.card_bij' (fun x _ => (x % q ^ p, x / (q ^ p * q)))
    (fun lh _ => lh.1 + q ^ p * (β + q * lh.2))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hqp, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm]; rw [hk] at hx; linarith
  · intro lh hlh
    simp only [Finset.mem_product, Finset.mem_range] at hlh
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rw [hk]
      have : lh.1 + q ^ p * (β + q * lh.2) < q ^ p * (β + q * lh.2 + 1) := by nlinarith
      have h2 : β + q * lh.2 + 1 ≤ q * q ^ (k - p - 1) := by
        have : lh.2 + 1 ≤ q ^ (k - p - 1) := hlh.2
        nlinarith
      calc lh.1 + q ^ p * (β + q * lh.2) < q ^ p * (β + q * lh.2 + 1) := this
        _ ≤ q ^ p * (q * q ^ (k - p - 1)) := Nat.mul_le_mul_left _ h2
        _ = q ^ p * q * q ^ (k - p - 1) := by ring
    · rw [Nat.add_mul_div_left _ _ hqp, Nat.div_eq_of_lt hlh.1, zero_add, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hβ]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have h1 : x / q ^ p = β + q * (x / (q ^ p * q)) := by
      rw [← Nat.div_div_eq_div_mul, ← hx.2, Nat.mod_add_div]
    calc x % q ^ p + q ^ p * (β + q * (x / (q ^ p * q))) = x % q ^ p + q ^ p * (x / q ^ p) := by
          rw [h1]
      _ = x := Nat.mod_add_div x (q ^ p)
  · intro lh hlh
    simp only [Finset.mem_product, Finset.mem_range] at hlh
    ext
    · simp only
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlh.1]
    · simp only
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hqp, Nat.div_eq_of_lt hlh.1, zero_add,
        Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hβ, zero_add]

/-- **`lem:shared`**: the pair of the digits with index `j` of two coordinates takes every value
exactly `q^{m-2}` times when `2(j+1) ≤ m`. -/
lemma shared_count {s q m : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (hj : 2 * (j + 1) ≤ m)
    (α β : ℕ) (hα : α < q) (hβ : β < q) :
    (univ.filter fun v : Fin m → ZMod q =>
        X v a / q ^ (m - 1 - j) % q = α ∧ X v b / q ^ (m - 1 - j) % q = β).card = q ^ (m - 2) := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set d : Fin s → ℕ := Pi.single a (j + 1) + Pi.single b (m - j - 1) with hd
  have hda : d a = j + 1 := by simp [hd, Pi.single_eq_of_ne hab]
  have hdb : d b = m - j - 1 := by simp [hd, Pi.single_eq_of_ne hab.symm]
  have hdc : ∀ c, c ≠ a → c ≠ b → d c = 0 := by
    intro c hca hcb; simp [hd, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb]
  have hdsum : ∑ c, d c = m := by
    simp only [hd, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']; simp; omega
  -- the box of `v`
  let box : (Fin m → ZMod q) → ℕ × ℕ := fun v => (X v a / q ^ (m - j - 1), X v b / q ^ (j + 1))
  have hlt := net_lt X hX
  set S := (range (q ^ (j + 1))) ×ˢ (range (q ^ (m - j - 1))) with hS
  have hboxS : ∀ v, box v ∈ S := by
    intro v
    simp only [hS, Finset.mem_product, Finset.mem_range, box]
    constructor
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        show j + 1 + (m - j - 1) = m by omega]
      exact hlt v a
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        show m - j - 1 + (j + 1) = m by omega]
      exact hlt v b
  have ev_a : ∀ x y : ℕ, (Pi.single a x + Pi.single b y : Fin s → ℕ) a = x := by
    intro x y; simp [Pi.single_eq_of_ne hab]
  have ev_b : ∀ x y : ℕ, (Pi.single a x + Pi.single b y : Fin s → ℕ) b = y := by
    intro x y; simp [Pi.single_eq_of_ne hab.symm]
  have ev_c : ∀ x y : ℕ, ∀ c, c ≠ a → c ≠ b → (Pi.single a x + Pi.single b y : Fin s → ℕ) c = 0 := by
    intro x y c hca hcb; simp [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb]
  have hboxeq : ∀ v, ∀ c, X v c / q ^ (m - d c) =
      (Pi.single a (box v).1 + Pi.single b (box v).2 : Fin s → ℕ) c := by
    intro v c
    by_cases hca : c = a
    · rw [hca, ev_a, hda]; simp only [box]; congr 2
    · by_cases hcb : c = b
      · rw [hcb, ev_b, hdb]; simp only [box]; congr 2; omega
      · rw [ev_c _ _ c hca hcb, hdc c hca hcb, Nat.sub_zero]
        exact Nat.div_eq_of_lt (hlt v c)
  have hinj : ∀ v w, box v = box w → v = w := by
    intro v w h
    have hbd : ∀ c, (Pi.single a (box v).1 + Pi.single b (box v).2 : Fin s → ℕ) c < q ^ d c := by
      intro c
      have := hboxS v
      simp only [hS, Finset.mem_product, Finset.mem_range] at this
      by_cases hca : c = a
      · rw [hca, ev_a, hda]; exact this.1
      · by_cases hcb : c = b
        · rw [hcb, ev_b, hdb]; exact this.2
        · rw [ev_c _ _ c hca hcb]; positivity
    obtain ⟨u, -, hu⟩ := hX d hdsum _ hbd
    rw [hu v (hboxeq v), hu w (fun c => by rw [hboxeq w, h])]
  have hsurj : ∀ p ∈ S, ∃ v, box v = p := by
    intro p hp
    simp only [hS, Finset.mem_product, Finset.mem_range] at hp
    have hbd : ∀ c, (Pi.single a p.1 + Pi.single b p.2 : Fin s → ℕ) c < q ^ d c := by
      intro c
      by_cases hca : c = a
      · rw [hca, ev_a, hda]; exact hp.1
      · by_cases hcb : c = b
        · rw [hcb, ev_b, hdb]; exact hp.2
        · rw [ev_c _ _ c hca hcb]; positivity
    obtain ⟨v, hv, -⟩ := hX d hdsum _ hbd
    refine ⟨v, ?_⟩
    have h1 := hv a
    have h2 := hv b
    rw [hboxeq v a, ev_a, ev_a] at h1; rw [hboxeq v b, ev_b, ev_b] at h2
    exact Prod.ext h1 h2
  -- the digits through the box
  have hdig : ∀ v, X v a / q ^ (m - 1 - j) % q = (box v).1 % q ∧
      X v b / q ^ (m - 1 - j) % q = (box v).2 / q ^ (m - 2 * j - 2) % q := by
    intro v
    refine ⟨by simp only [box]; rw [show m - 1 - j = m - j - 1 by omega], ?_⟩
    simp only [box]
    rw [Nat.div_div_eq_div_mul, ← pow_add, show j + 1 + (m - 2 * j - 2) = m - 1 - j by omega]
  have hcount : (univ.filter fun v : Fin m → ZMod q =>
      X v a / q ^ (m - 1 - j) % q = α ∧ X v b / q ^ (m - 1 - j) % q = β).card =
      ((range (q ^ (j + 1))).filter (fun x => x / q ^ 0 % q = α) ×ˢ
        (range (q ^ (m - j - 1))).filter (fun x => x / q ^ (m - 2 * j - 2) % q = β)).card := by
    apply Finset.card_bij (fun v _ => box v)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have := hboxS v
      simp only [hS, Finset.mem_product, Finset.mem_range] at this
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, pow_zero, Nat.div_one]
      rw [(hdig v).1] at hv; rw [(hdig v).2] at hv
      exact ⟨⟨this.1, hv.1⟩, ⟨this.2, hv.2⟩⟩
    · intro v _ w _ h; exact hinj v w h
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, pow_zero,
        Nat.div_one] at hp
      obtain ⟨v, hv⟩ := hsurj p (by simp [hS, hp.1.1, hp.2.1])
      refine ⟨v, ?_, hv⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hdig v).1, (hdig v).2, hv]; exact ⟨hp.1.2, hp.2.2⟩
  rw [hcount, Finset.card_product, digit_count q 0 (j + 1) α hq (by omega) hα,
    digit_count q (m - 2 * j - 2) (m - j - 1) β hq (by omega) hβ, ← pow_add]
  congr 1; omega

/-- **`lem:shared`**, the dependence: if the digit with index `j` of `b` is a function of the digit
with index `j` of `a` at every point, then `2(j+1) > m` (base `q ≥ 2`). -/
lemma shared_fun {s q m : ℕ} [NeZero q] (hq : 2 ≤ q) (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (f : ℕ → ℕ)
    (hf : ∀ v, X v b / q ^ (m - 1 - j) % q = f (X v a / q ^ (m - 1 - j) % q)) :
    m < 2 * (j + 1) := by
  by_contra h
  push Not at h
  set β := if f 0 = 0 then 1 else 0 with hβ
  have hβq : β < q := by rw [hβ]; split_ifs <;> omega
  have hβf : β ≠ f 0 := by rw [hβ]; split_ifs with h' <;> omega
  have hc := shared_count X hX a b hab j h 0 β (by omega) hβq
  have hpos : 0 < q ^ (m - 2) := pow_pos (by omega) _
  rw [← hc] at hpos
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have := hf v
  rw [hv.1, hv.2] at this
  exact hβf this

end Z3NetC.Proofs
