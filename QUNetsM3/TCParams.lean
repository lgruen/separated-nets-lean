/-
Entry TwoCoset: the parameters of `prop:twocoset` (`paper/core.tex`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.TCSep

@[expose] public section

namespace QUNetsM3

variable {p : ℕ}

/-- An integer `x ≡ θ (mod 8)` with `θ ∈ {±1, ±3}` has `|x| ≥ |θ|`. -/
theorem abs_ge_of_mod8 (x θ : ℤ) (hθ : θ = -3 ∨ θ = -1 ∨ θ = 1 ∨ θ = 3) (hx : 8 ∣ x - θ) :
    |θ| ≤ |x| := by
  obtain ⟨k, hk⟩ := hx
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases θ with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2] <;> omega

theorem tc_params' (hp : p.Prime) (hp5 : 5 ≤ p) :
    (thetaTC p = -3 ∨ thetaTC p = -1 ∨ thetaTC p = 1 ∨ thetaTC p = 3) ∧
    (∀ r' : ℤ, |thetaTC p| ≤ |8 * r' - p|) ∧ 2 * hTC p = -1 ∧ 1 ≤ rTC p ∧ rTC p < p := by
  have hodd := odd_of_prime5 hp hp5
  have hθ := thetaTC_cases hodd
  refine ⟨hθ, fun r' => abs_ge_of_mod8 _ _ hθ ⟨r' - rTC p, by unfold thetaTC; ring⟩,
    two_hTC hodd, rTC_pos hp5, rTC_lt hp5⟩

end QUNetsM3
