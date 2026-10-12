/-
Proof module (stage 6, main entry): `rem:base2`, reading `𝒫_{k,2^j}` in base 2.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.Net

@[expose] public section

/-!
# `rem:base2`: `t ≤ 2(j-1)`

`gen_count`: a `(0,m,3)`-net in base `q` has `q^(m - ∑e)` points in every box with `e_c` digits,
`∑ e ≤ m` (refine coordinate `0`). A base-`b` box with `d_c` digits, `∑ d + 2(j-1) = jm`, is the
union of the base-`q` boxes (`q = b^j`) with `e_c = ⌈d_c/j⌉` digits that it contains, and
`∑ e_c ≤ m`; so it holds `∏ b^(j e_c - d_c) · q^(m - ∑e) = b^(2(j-1))` points.
-/

namespace Z3Net.Proofs

open Finset

noncomputable section

namespace Base2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A `(0,m,3)`-net in base `q` (as a family over a finite index type) has `q^(m - ∑ e)` points in
every box with `e_c` digits when `∑ e ≤ m`. -/
theorem gen_count (q m : ℕ) (hq : 1 ≤ q) (X : ι → Fin 3 → ℕ)
    (hnet : ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 = m → ∀ a : Fin 3 → ℕ, (∀ c, a c < q ^ d c) →
      ∃! i, ∀ c, X i c / q ^ (m - d c) = a c)
    (e : Fin 3 → ℕ) (he : e 0 + e 1 + e 2 ≤ m) (b : Fin 3 → ℕ) (hb : ∀ c, b c < q ^ e c) :
    (univ.filter fun i => ∀ c, X i c / q ^ (m - e c) = b c).card = q ^ (m - (e 0 + e 1 + e 2)) := by
  classical
  set δ := m - (e 0 + e 1 + e 2) with hδ
  set e' : Fin 3 → ℕ := fun c => if c = 0 then e 0 + δ else e c with he'
  have he'0 : e' 0 = e 0 + δ := by simp [e']
  have he'c : ∀ c, c ≠ 0 → e' c = e c := fun c hc => by simp [e', hc]
  have hsum : e' 0 + e' 1 + e' 2 = m := by
    rw [he'0, he'c 1 (by decide), he'c 2 (by decide)]; omega
  set S := univ.filter fun i => ∀ c, X i c / q ^ (m - e c) = b c
  -- the refined index of coordinate `0`
  set g : ι → ℕ := fun i => (X i 0 / q ^ (m - e 0 - δ)) % q ^ δ
  have hmaps : ∀ i ∈ S, g i ∈ range (q ^ δ) := fun i _ =>
    mem_range.mpr (Nat.mod_lt _ (pow_pos (by omega) _))
  rw [card_eq_sum_card_fiberwise hmaps]
  have hq0 : 0 < q := by omega
  have hfib : ∀ r ∈ range (q ^ δ), (S.filter fun i => g i = r).card = 1 := by
    intro r hr
    rw [mem_range] at hr
    set a' : Fin 3 → ℕ := fun c => if c = 0 then b 0 * q ^ δ + r else b c with ha'
    have ha'lt : ∀ c, a' c < q ^ e' c := by
      intro c
      by_cases hc : c = 0
      · subst hc
        simp only [ha', if_pos rfl, he'0, pow_add]
        have := hb 0
        nlinarith
      · simp only [ha', if_neg hc, he'c c hc]; exact hb c
    obtain ⟨i0, hi0, huniq⟩ := hnet e' hsum a' ha'lt
    rw [card_eq_one]
    refine ⟨i0, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton, S]
    have key : ∀ i, ((∀ c, X i c / q ^ (m - e c) = b c) ∧ g i = r) ↔
        ∀ c, X i c / q ^ (m - e' c) = a' c := by
      intro i
      have hdiv : X i 0 / q ^ (m - e 0) = X i 0 / q ^ (m - e 0 - δ) / q ^ δ := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
      constructor
      · rintro ⟨h1, h2⟩ c
        by_cases hc : c = 0
        · subst hc
          simp only [ha', if_pos rfl, he'0]
          rw [show m - (e 0 + δ) = m - e 0 - δ by omega]
          have h0 := h1 0
          rw [hdiv] at h0
          rw [← h0, ← h2]
          exact (Nat.div_add_mod' _ _).symm
        · simp only [ha', if_neg hc, he'c c hc]; exact h1 c
      · intro h
        have h0 := h 0
        simp only [ha', if_pos rfl, he'0, show m - (e 0 + δ) = m - e 0 - δ by omega] at h0
        refine ⟨fun c => ?_, ?_⟩
        · by_cases hc : c = 0
          · subst hc
            rw [hdiv, h0, add_comm, Nat.add_mul_div_right _ _ (pow_pos hq0 _),
              Nat.div_eq_of_lt hr, zero_add]
          · have := h c
            simp only [ha', if_neg hc, he'c c hc] at this; exact this
        · simp only [g]; rw [h0, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    rw [key]
    exact ⟨fun h => huniq i h, fun h => h ▸ hi0⟩
  rw [sum_congr rfl hfib]
  simp

/-- **`rem:base2`, general base**: a `(0,m,3)`-net in base `q = b^j` is a `(2(j-1), jm, 3)`-net in
base `b`. -/
theorem baseb_net (b j m : ℕ) (hb : 2 ≤ b) (hj : 1 ≤ j) (X : ι → Fin 3 → ℕ)
    (hnet : ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 = m → ∀ a : Fin 3 → ℕ, (∀ c, a c < (b ^ j) ^ d c) →
      ∃! i, ∀ c, X i c / (b ^ j) ^ (m - d c) = a c)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 + 2 * (j - 1) = j * m) (a : Fin 3 → ℕ)
    (ha : ∀ c, a c < b ^ d c) :
    (univ.filter fun i => ∀ c, X i c / b ^ (j * m - d c) = a c).card = b ^ (2 * (j - 1)) := by
  classical
  have hb0 : 0 < b := by omega
  set e : Fin 3 → ℕ := fun c => (d c + j - 1) / j with he
  have he1 : ∀ c, d c ≤ j * e c := by
    intro c; simp only [e]
    have := Nat.div_add_mod (d c + j - 1) j
    have := Nat.mod_lt (d c + j - 1) (show 0 < j by omega)
    omega
  have he2 : ∀ c, j * e c ≤ d c + j - 1 := by
    intro c; simp only [e]; exact Nat.mul_div_le _ _
  have hsum : e 0 + e 1 + e 2 ≤ m := by
    have h0 := he2 0; have h1 := he2 1; have h2 := he2 2
    have : j * (e 0 + e 1 + e 2) < j * (m + 1) := by rw [mul_add, mul_add, mul_add]; omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have hem : ∀ c, e c ≤ m := by
    intro c; fin_cases c <;> simp <;> omega
  set δ : Fin 3 → ℕ := fun c => j * e c - d c with hδ
  have hexp : ∀ c, b ^ (j * m - d c) = (b ^ j) ^ (m - e c) * b ^ δ c := by
    intro c
    rw [← pow_mul, ← pow_add]; congr 1
    have := he1 c; have := hem c
    simp only [δ]
    rw [Nat.mul_sub]
    have : j * e c ≤ j * m := Nat.mul_le_mul_left j (hem c)
    omega
  set g : ι → Fin 3 → ℕ := fun i c => X i c / (b ^ j) ^ (m - e c)
  set B := Fintype.piFinset fun c => Ico (a c * b ^ δ c) ((a c + 1) * b ^ δ c)
  set S := univ.filter fun i => ∀ c, X i c / b ^ (j * m - d c) = a c
  have hcond : ∀ i c, (X i c / b ^ (j * m - d c) = a c) ↔ g i c / b ^ δ c = a c := by
    intro i c
    rw [hexp, ← Nat.div_div_eq_div_mul]
  have hiff : ∀ (y a' t : ℕ), 0 < t → (y / t = a' ↔ y ∈ Ico (a' * t) ((a' + 1) * t)) := by
    intro y a' t ht
    rw [mem_Ico]
    constructor
    · rintro rfl
      refine ⟨Nat.div_mul_le_self y t, ?_⟩
      have := Nat.lt_div_mul_add (a := y) ht
      linarith
    · rintro ⟨h1, h2⟩; exact Nat.div_eq_of_lt_le h1 h2
  have hδpos : ∀ c, 0 < b ^ δ c := fun c => pow_pos hb0 _
  have hmaps : ∀ i ∈ S, g i ∈ B := by
    intro i hi
    simp only [S, mem_filter, mem_univ, true_and] at hi
    simp only [B, Fintype.mem_piFinset]
    intro c
    exact (hiff _ _ _ (hδpos c)).1 ((hcond i c).1 (hi c))
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ β ∈ B, (S.filter fun i => g i = β).card = (b ^ j) ^ (m - (e 0 + e 1 + e 2)) := by
    intro β hβ
    simp only [B, Fintype.mem_piFinset] at hβ
    have hβlt : ∀ c, β c < (b ^ j) ^ e c := by
      intro c
      have h1 := (mem_Ico.mp (hβ c)).2
      have h2 : (a c + 1) * b ^ δ c ≤ b ^ d c * b ^ δ c :=
        Nat.mul_le_mul_right _ (ha c)
      have h3 : b ^ d c * b ^ δ c = (b ^ j) ^ e c := by
        rw [← pow_add, ← pow_mul]; congr 1; simp only [δ]; have := he1 c; omega
      omega
    have := gen_count (b ^ j) m (Nat.one_le_pow _ _ hb0) X hnet e hsum β hβlt
    rw [← this]
    congr 1
    ext i
    simp only [S, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, rfl⟩ c; rfl
    · intro h
      have hg : g i = β := funext h
      refine ⟨fun c => (hcond i c).2 ?_, hg⟩
      rw [hg]
      exact (hiff _ _ _ (hδpos c)).2 (hβ c)
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  simp only [B, Fintype.card_piFinset, Nat.card_Ico, Fin.prod_univ_three]
  have hc : ∀ c, (a c + 1) * b ^ δ c - a c * b ^ δ c = b ^ δ c := by
    intro c; rw [add_mul, one_mul]; omega
  rw [hc 0, hc 1, hc 2, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have := he1 0; have := he1 1; have := he1 2
  simp only [δ]
  have hm : j * (m - (e 0 + e 1 + e 2)) = j * m - (j * e 0 + j * e 1 + j * e 2) := by
    rw [Nat.mul_sub, mul_add, mul_add]
  have : j * (e 0 + e 1 + e 2) ≤ j * m := Nat.mul_le_mul_left j hsum
  rw [mul_add, mul_add] at this
  rw [hm]
  omega

theorem base2_net (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    IsNetT 2 (2 * (j - 1)) (j * (3 * k)) (Ppoint (2 ^ j) k) := by
  intro d hd a ha
  have h2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  exact baseb_net 2 j (3 * k) le_rfl hj (Ppoint (2 ^ j) k) (P_net (2 ^ j) k h2 hk) d hd a ha

end Base2

end

end Z3Net.Proofs
