/-
The reduction of a pair of points of a rank-one layer `𝐰uᵀ`, `𝐰 = (2,2,1)`, to integer data
(used by `prop:wnet` (4) and `prop:wfamily`; `paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WSep

@[expose] public section

/-!
# The reduction

For generator matrices `C` with first rows `e_x, e_y, e_z` and second rows with `x` and `y` equal and
twice `z` (the layer `𝐰uᵀ`), a pair of distinct indices and a translate `t` give the step `E = n' − n + pt ≠ 0`,
`D = Δζ ≡ (C_z E)₁`, the wrap `κ` of the digit `2ζ mod p` with the necessary conditions of `lem:wwrap`
(`wrap_nec`), and the third-digit changes `F_c ≡ (C_c E)₂`, `|F_c| ≤ p − 1`; and
`sepSqG = (p²E_x + p(2D − pκ) + F_x)² + (p²E_y + p(2D − pκ) + F_y)² + (p²E_z + pD + F_z)²`.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-- The data of a pair (`w_reduce`). -/
def WRed (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (x x' : ℕ) (t : Fin 3 → ℤ)
    (E : Fin 3 → ℤ) (D κ : ℤ) (F : Fin 3 → ℤ) : Prop :=
  E ≠ 0 ∧ (∀ c, E c = (cellDigits p x' c : ℤ) - cellDigits p x c + p * t c) ∧
  ((D : ZMod p) = (C 2 *ᵥ fun c => (E c : ZMod p)) 1) ∧ D ≤ p - 1 ∧ -D ≤ p - 1 ∧
  ((κ = 0 ∧ 2 * D ≤ p - 1 ∧ -(2 * D) ≤ p - 1) ∨ (κ = 1 ∧ 0 < D) ∨ (κ = -1 ∧ D < 0)) ∧
  2 * D - p * κ ≤ p - 1 ∧ -(2 * D - p * κ) ≤ p - 1 ∧
  (∀ c, (F c : ZMod p) = (C c *ᵥ fun c => (E c : ZMod p)) 2 ∧ F c ≤ p - 1 ∧ -F c ≤ p - 1) ∧
  sepSqG p C x x' t = ((p : ℤ) ^ 2 * E 0 + p * (2 * D - p * κ) + F 0) ^ 2 +
    ((p : ℤ) ^ 2 * E 1 + p * (2 * D - p * κ) + F 1) ^ 2 + ((p : ℤ) ^ 2 * E 2 + p * D + F 2) ^ 2

/-- The cast of a difference of cells is the difference of the digit vectors. -/
theorem cell_sub_cast [NeZero p] (x : ℕ) (c : Fin 3) :
    ((cellDigits p x c : ℕ) : ZMod p) = digits p x c := by
  simp [cellDigits]

/-- **The reduction of a pair** of a rank-one layer `𝐰uᵀ`. -/
theorem w_reduce (hp : p.Prime) (hp5 : 5 ≤ p) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC0 : ∀ c s, (C c *ᵥ s) 0 = s c) (hxy : ∀ s, (C 1 *ᵥ s) 1 = (C 0 *ᵥ s) 1)
    (h2 : ∀ s, (C 0 *ᵥ s) 1 = 2 * (C 2 *ᵥ s) 1) (x x' : ℕ) (hx : x < p ^ 3) (hx' : x' < p ^ 3)
    (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ∃ E : Fin 3 → ℤ, ∃ D κ : ℤ, ∃ F : Fin 3 → ℤ, WRed p C x x' t E D κ F := by
  have := Fact.mk hp
  have hodd := odd_of_prime5 hp hp5
  set n := cellDigits p x with hn
  set n' := cellDigits p x' with hn'
  have hnb : ∀ c, n c < p := fun c => ZMod.val_lt _
  have hnb' : ∀ c, n' c < p := fun c => ZMod.val_lt _
  have hne' : n ≠ n' := cellE1_ne hx hx' hne
  set g := g2G p C
  set f := g3G p C
  have hgb : ∀ m c, g m c < p := fun m c => ZMod.val_lt _
  have hfb : ∀ m c, f m c < p := fun m c => ZMod.val_lt _
  have hgx : ∀ m, g m 0 = (2 * g m 2 + 0) % p := by
    intro m
    refine digit_eq_mod (hgb m 0) ?_
    simp only [g, g2G, ZMod.natCast_zmod_val, h2]; push_cast; ring
  have hgy : ∀ m, g m 1 = g m 0 := by
    intro m; simp only [g, g2G, hxy]
  obtain ⟨κ, hκeq, hκ0⟩ := wrap_nec hodd (c₀ := 0) (by norm_num) (hgb n 2) (hgb n' 2)
  set E : Fin 3 → ℤ := fun c => ((n' c : ℤ) - n c) + (p : ℤ) * t c with hEdef
  set D : ℤ := (g n' 2 : ℤ) - g n 2 with hDdef
  have hgx' : (g n' 0 : ℤ) - g n 0 = 2 * D - p * κ := by rw [hgx n', hgx n, hκeq]
  have hgy' : (g n' 1 : ℤ) - g n 1 = 2 * D - p * κ := by rw [hgy n', hgy n, hgx']
  -- the cast of `E` is the difference of the digit vectors
  have hEc : (fun c => (E c : ZMod p)) = (fun c => ((n' c : ℕ) : ZMod p)) - fun c => ((n c : ℕ) : ZMod p) := by
    funext c; simp only [hEdef, Pi.sub_apply]; push_cast; simp
  have hrow : ∀ (k c : Fin 3), (C c *ᵥ fun c => (E c : ZMod p)) k =
      (C c *ᵥ fun i => ((n' i : ℕ) : ZMod p)) k - (C c *ᵥ fun i => ((n i : ℕ) : ZMod p)) k := by
    intro k c; rw [hEc, Matrix.mulVec_sub]; rfl
  have hE0 : ∀ c, E c = 0 → n' c = n c := by
    intro c hc
    have h1 := hnb c
    have h2 := hnb' c
    simp only [hEdef] at hc
    rcases lt_trichotomy (t c) 0 with ht | ht | ht
    · have : (p : ℤ) * t c ≤ -(p : ℤ) := by nlinarith
      omega
    · rw [ht] at hc; omega
    · have : (p : ℤ) ≤ (p : ℤ) * t c := by nlinarith
      omega
  have hEne : E ≠ 0 := by
    intro h0
    apply hne'
    funext c
    exact (hE0 c (congrFun h0 c)).symm
  refine ⟨E, D, κ, fun c => (f n' c : ℤ) - f n c, hEne, fun c => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hDdef, g, g2G]; push_cast; simp only [ZMod.natCast_zmod_val]; rw [hrow]
  · have := hgb n' 2; omega
  · have := hgb n 2; omega
  · rcases hκ0 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, by omega⟩)
  · have := hgb n' 0; have := hgb n 0; rw [← hgx']; omega
  · have := hgb n' 0; have := hgb n 0; rw [← hgx']; omega
  · intro c
    have h1 := hfb n' c; have h2 := hfb n c
    refine ⟨?_, show (f n' c : ℤ) - f n c ≤ p - 1 by omega, show -((f n' c : ℤ) - f n c) ≤ p - 1 by omega⟩
    simp only [f, g3G]; push_cast; simp only [ZMod.natCast_zmod_val]; rw [hrow]
  · rw [sepSqG_row0 C hC0, Fin.sum_univ_three]
    have e0 : (g n' 0 : ℤ) - g n 0 = 2 * D - p * κ := hgx'
    have e1 : (g n' 1 : ℤ) - g n 1 = 2 * D - p * κ := hgy'
    rw [e0, e1]
    simp only [hEdef, hDdef, g, f, hn, hn']
    ring

end QUNetsM3
