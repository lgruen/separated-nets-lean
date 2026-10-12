/-
`rem:wshift`, the net `𝒯_p`: the bound of `prop:twocoset` (2) persists under every digital shift whose second digits
agree on the digit shared by `y` and `z` (`paper/core.tex`). V14 stage S16′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.TCSep
public import QUNetsM3.WSep

@[expose] public section

/-!
# `rem:wshift`, the two-coset net `𝒯_p`

`tc_shift`: shift `𝒯_p` digit by digit by `τ` (`digitalPtS`, which is `def:dshift` by `digitalPtS_eq_dshiftPt_core`).
The cell of index `x` is `m = digits(x) + τ_{·,0}`, and in terms of `m` the second digits are
`g_x ≡ h(m_y + m_z) + b_x`, `g_y ≡ r m_x − m_y + m_z + b_y` and `g_z ≡ g_y + (τ_{z,2} − τ_{y,2})`, with constants
`b_x, b_y` that depend on `τ` only. If `τ_{y,2} = τ_{z,2}` then `g_z = g_y` (the `y`- and `z`-digits still wrap
together), and `tc_freeJitter_gen` (`prop:twocoset` (2) with affine second digits and arbitrary third digits) gives the
bound. The first and third shift digits are arbitrary.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-- The first rows of `𝒯_p` are `e_x, e_y, e_z`. -/
theorem genTC_row0 (c : Fin 3) (s : Fin 3 → ZMod p) : (genTC p c *ᵥ s) 0 = s c := by
  fin_cases c
  · exact genTC_x0 s
  · exact genTC_y0 s
  · exact genTC_z0 s

/-- **`rem:wshift`, the net `𝒯_p`** (proof of `TC_shift`): if the second shift digits of `y` and `z` agree
(`τ_{y,2} = τ_{z,2}`), the bound of `prop:twocoset` (2) holds for every pair of distinct points of the shifted net and
every torus translate (any first and third shift digits, any second shift digit of `x`). -/
theorem tc_shift (hp : p.Prime) (hp41 : 41 ≤ p) (τ : Fin 3 → Fin 3 → ZMod p) (hyz : τ 1 1 = τ 2 1)
    (x x' : ℕ) (hx : x < p ^ 3) (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * (Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p)) ^ 2 ≤
      (sepSqGS p (genTC p) τ x x' t : ℝ) := by
  have := Fact.mk hp
  -- the cell of an index, and the digits as functions of the cell `m = d + τ_{·,0}`
  let cellS : ℕ → Fin 3 → ℕ := fun y c => (digits p y c + τ c 0).val
  let gS : (Fin 3 → ℕ) → Fin 3 → ℕ := fun m c =>
    ((genTC p c *ᵥ (fun i => (m i : ZMod p) - τ i 0)) 1 + τ c 1).val
  let fS : (Fin 3 → ℕ) → Fin 3 → ℕ := fun m c =>
    ((genTC p c *ᵥ (fun i => (m i : ZMod p) - τ i 0)) 2 + τ c 2).val
  have fj := tc_freeJitter_gen hp hp41 (τ 0 1 - hTC p * (τ 1 0 + τ 2 0))
    (τ 1 1 - ((rTC p : ZMod p) * τ 0 0 - τ 1 0 + τ 2 0)) gS fS (fun n _ c => ZMod.val_lt _)
    (by intro m _; simp only [gS, ZMod.natCast_zmod_val, genTC_x1]; ring)
    (by intro m _; simp only [gS, ZMod.natCast_zmod_val, genTC_y1]; ring)
    (by intro m _; simp only [gS, genTC_y1, genTC_z1, hyz])
    (fun n _ c => ZMod.val_lt _) (cellS x) (cellS x')
    (fun c => ZMod.val_lt _) (fun c => ZMod.val_lt _)
    (by
      intro heq
      apply hne
      have hd : digits p x = digits p x' := by
        funext c
        have := ZMod.val_injective p (congrFun heq c)
        exact add_right_cancel this
      rw [← coord_digits hx, ← coord_digits hx', hd]) t
  have hcell : ∀ y, (fun i => ((cellS y i : ℕ) : ZMod p) - τ i 0) = digits p y := by
    intro y; funext i; simp [cellS]
  have hS : sepSqGS p (genTC p) τ x x' t = ∑ c' : Fin 3,
      ((p : ℤ) ^ 2 * ((cellS x' c' : ℤ) - cellS x c') +
        p * ((gS (cellS x') c' : ℤ) - gS (cellS x) c') +
        ((fS (cellS x') c' : ℤ) - fS (cellS x) c') + (p : ℤ) ^ 3 * t c') ^ 2 := by
    unfold sepSqGS
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [digitalPtS_row0 _ genTC_row0, digitalPtS_row0 _ genTC_row0]
    simp only [gS, fS, hcell]
    push_cast
    ring
  rw [hS]
  push_cast at fj ⊢
  exact fj

end QUNetsM3
