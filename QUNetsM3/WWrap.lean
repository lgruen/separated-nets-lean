/-
`lem:wwrap` (wraps of a halved digit) and the necessary conditions on the wraps used by
`prop:wnet` (2), `prop:wfamily` and `rem:shiftshared` (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WDefs
public import QUNetsM3.TCNet

@[expose] public section

/-!
# `lem:wwrap`

`wwrap_scalar`: for odd `p ≥ 3`, `σ < p`, the pairs `(z' − z, [2z' ≥ p] − [2z ≥ p])` with `z < p`,
`z' = (z + σ) mod p` are exactly those of `WrapAllowed`. The proof of the paper: `Δζ = σ` if
`z ≤ p − 1 − σ`, else `σ − p`; for `Δζ = δ > 0`, `κ = 1` iff `z ≤ h < z + δ`, `κ = 0` iff `z + δ ≤ h` or
`z ≥ h + 1`; explicit witnesses for the converse. `wwrap`: the lift to `n ∈ 𝔽_p³` (`ζ(n + E) = (ζ(n) + σ)
mod p`, and `ζ` is onto when `σ ≠ 0`). Lean does not need `u ≠ 0` (for `u = 0`, `σ = 0`).

`wrap_nec`: for the digit `(2z + c₀) mod p` with `c₀ ∈ {0, 1}` (`c₀ = 1` is the shifted digit of
`rem:shiftshared`), the change is `2(z' − z) − pκ` with `κ ∈ {0, sgn(z' − z)}` and `κ = 0 ⇒ 2|z' − z| ≤ p − 1`.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

theorem wrapW_def (p z : ℕ) : wrapW p z = if p ≤ 2 * z then 1 else 0 := rfl

/-- The scalar form of `lem:wwrap`. -/
theorem wwrap_scalar (hodd : p % 2 = 1) (hp3 : 3 ≤ p) {σ : ℕ} (hσ : σ < p) (d k : ℤ) :
    (∃ z : ℕ, z < p ∧ ((((z + σ) % p : ℕ) : ℤ) - z = d ∧
      wrapW p ((z + σ) % p) - wrapW p z = k)) ↔ WrapAllowed p σ d k := by
  have hh : 2 * hW p + 1 = p := by unfold hW; omega
  constructor
  · rintro ⟨z, hz, hd, hk⟩
    unfold WrapAllowed
    rcases lt_or_ge (z + σ) p with h | h
    · rw [Nat.mod_eq_of_lt h] at hd hk
      simp only [wrapW_def] at hk
      by_cases h0 : σ = 0
      · left; subst h0; refine ⟨rfl, by push_cast at hd; omega, ?_⟩
        rw [← hk]; simp
      · right
        refine ⟨h0, Or.inl (by push_cast at hd; omega), ?_⟩
        have hdpos : d = σ := by push_cast at hd; omega
        rw [hdpos, Int.sign_natCast_of_ne_zero h0]
        split_ifs at hk with h1 h2 h2
        · right; refine ⟨by omega, ?_⟩; rw [abs_of_nonneg (by omega)]; omega
        · left; omega
        · omega
        · right; refine ⟨by omega, ?_⟩; rw [abs_of_nonneg (by omega)]; omega
    · have hm : (z + σ) % p = z + σ - p := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [hm] at hd hk
      simp only [wrapW_def] at hk
      right
      have h0 : σ ≠ 0 := by omega
      have hdv : d = (σ : ℤ) - p := by push_cast [Nat.cast_sub h] at hd; omega
      refine ⟨h0, Or.inr hdv, ?_⟩
      have hsg : Int.sign d = -1 := by rw [hdv]; exact Int.sign_eq_neg_one_of_neg (by omega)
      rw [hsg]
      split_ifs at hk with h1 h2 h2
      · right; refine ⟨by omega, ?_⟩; rw [hdv, abs_of_neg (by omega)]; omega
      · omega
      · left; omega
      · right; refine ⟨by omega, ?_⟩; rw [hdv, abs_of_neg (by omega)]; omega
  · intro hA
    unfold WrapAllowed at hA
    rcases hA with ⟨rfl, rfl, rfl⟩ | ⟨h0, hd | hd, hk | ⟨rfl, hdh⟩⟩
    · exact ⟨0, by omega, by simp, by simp⟩
    · -- (σ, 1)
      have hk1 : k = 1 := by rw [hk, hd, Int.sign_natCast_of_ne_zero h0]
      subst hk1
      refine ⟨if hW p + 1 ≤ σ then 0 else hW p + 1 - σ, by split_ifs <;> omega, ?_⟩
      split_ifs with hc
      · rw [Nat.mod_eq_of_lt (by omega)]
        simp only [wrapW_def]
        refine ⟨by push_cast; omega, ?_⟩
        split_ifs <;> omega
      · rw [Nat.mod_eq_of_lt (by omega)]
        simp only [wrapW_def]
        refine ⟨by push_cast [Nat.cast_sub (show σ ≤ hW p + 1 by omega)]; omega, ?_⟩
        split_ifs <;> omega
    · -- (σ, 0), σ ≤ h
      rw [hd, abs_of_nonneg (by omega)] at hdh
      refine ⟨0, by omega, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [wrapW_def]
      refine ⟨by push_cast; omega, ?_⟩
      split_ifs <;> omega
    · -- (σ − p, −1)
      have hk1 : k = -1 := by rw [hk, hd]; exact Int.sign_eq_neg_one_of_neg (by omega)
      subst hk1
      refine ⟨if hW p + 1 ≤ p - σ then p - σ else hW p + 1, by split_ifs <;> omega, ?_⟩
      split_ifs with hc
      · have hm : (p - σ + σ) % p = 0 := by rw [Nat.sub_add_cancel hσ.le, Nat.mod_self]
        rw [hm]
        simp only [wrapW_def]
        refine ⟨by push_cast [Nat.cast_sub hσ.le]; omega, ?_⟩
        split_ifs <;> omega
      · have hm : (hW p + 1 + σ) % p = hW p + 1 + σ - p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        simp only [wrapW_def]
        refine ⟨by push_cast [Nat.cast_sub (show p ≤ hW p + 1 + σ by omega)]; omega, ?_⟩
        split_ifs <;> omega
    · -- (σ − p, 0), p − σ ≤ h
      rw [hd, abs_of_neg (by omega)] at hdh
      refine ⟨p - σ, by omega, ?_⟩
      have hm : (p - σ + σ) % p = 0 := by rw [Nat.sub_add_cancel hσ.le, Nat.mod_self]
      rw [hm]
      simp only [wrapW_def]
      refine ⟨by push_cast [Nat.cast_sub hσ.le]; omega, ?_⟩
      split_ifs <;> omega

/-- `ζ(n + E) = (ζ(n) + σ) mod p`. -/
theorem zetaW_add [NeZero p] (u n : Fin 3 → ZMod p) (E : Fin 3 → ℤ) :
    zetaW p u (n + fun c => (E c : ZMod p)) = (zetaW p u n + sigmaW p u E) % p := by
  unfold zetaW sigmaW
  rw [dotProduct_add, ZMod.val_add]

/-- `ζ` takes every value if `u ≠ 0`. -/
theorem zetaW_onto [Fact p.Prime] {u : Fin 3 → ZMod p} (hu : u ≠ 0) (z : ℕ) (hz : z < p) :
    ∃ n : Fin 3 → ZMod p, zetaW p u n = z := by
  obtain ⟨c, hc⟩ : ∃ c, u c ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  refine ⟨Pi.single c ((z : ZMod p) / u c), ?_⟩
  unfold zetaW
  rw [dotProduct_single, mul_div_cancel₀ _ hc, ZMod.val_natCast, Nat.mod_eq_of_lt hz]

/-- **`lem:wwrap`** (proof of `W_wrap`). -/
theorem wwrap (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (E : Fin 3 → ℤ) (d k : ℤ) :
    (∃ n : Fin 3 → ZMod p, dZetaW p u n E = d ∧ kappaW p u n E = k) ↔
      WrapAllowed p (sigmaW p u E) d k := by
  have := Fact.mk hp
  have hodd : p % 2 = 1 := odd_of_prime5 hp hp5
  have hσ : sigmaW p u E < p := ZMod.val_lt _
  rw [← wwrap_scalar hodd (by omega) hσ]
  constructor
  · rintro ⟨n, hd, hk⟩
    refine ⟨zetaW p u n, ZMod.val_lt _, ?_, ?_⟩
    · rw [← hd]; unfold dZetaW; rw [zetaW_add]
    · rw [← hk]; unfold kappaW; rw [zetaW_add]
  · rintro ⟨z, hz, hd, hk⟩
    by_cases hs : sigmaW p u E = 0
    · -- σ = 0: every `n` gives `(0, 0)`
      refine ⟨0, ?_, ?_⟩
      · rw [← hd]; unfold dZetaW; rw [zetaW_add, hs]
        simp only [zetaW, dotProduct_zero, ZMod.val_zero, Nat.zero_mod, add_zero]
        rw [Nat.mod_eq_of_lt hz]; simp
      · rw [← hk]; unfold kappaW; rw [zetaW_add, hs]
        simp only [zetaW, dotProduct_zero, ZMod.val_zero, Nat.zero_mod, add_zero]
        rw [Nat.mod_eq_of_lt hz]; simp
    · have hu : u ≠ 0 := by
        rintro rfl; apply hs; simp [sigmaW]
      obtain ⟨n, hn⟩ := zetaW_onto hu z hz
      refine ⟨n, ?_, ?_⟩
      · rw [← hd]; unfold dZetaW; rw [zetaW_add, hn]
      · rw [← hk]; unfold kappaW; rw [zetaW_add, hn]

/-- **Necessary conditions on a wrap** of the digit `(2z + c₀) mod p`, `c₀ ∈ {0, 1}`: the change is
`2(z' − z) − pκ` with `κ = 0` and `2|z' − z| ≤ p − 1`, or `κ = sgn(z' − z) ≠ 0`. -/
theorem wrap_nec (hodd : p % 2 = 1) {c₀ z z' : ℕ} (hc : c₀ ≤ 1) (hz : z < p) (hz' : z' < p) :
    ∃ κ : ℤ, ((((2 * z' + c₀) % p : ℕ) : ℤ) - (((2 * z + c₀) % p : ℕ) : ℤ) =
        2 * ((z' : ℤ) - z) - p * κ) ∧
      ((κ = 0 ∧ 2 * ((z' : ℤ) - z) ≤ p - 1 ∧ 2 * ((z : ℤ) - z') ≤ p - 1) ∨
        (κ = 1 ∧ 0 < (z' : ℤ) - z) ∨ (κ = -1 ∧ (z' : ℤ) - z < 0)) := by
  have hm : ∀ y : ℕ, y < p → ((2 * y + c₀) % p = 2 * y + c₀ ∧ 2 * y + c₀ < p) ∨
      ((2 * y + c₀) % p = 2 * y + c₀ - p ∧ p ≤ 2 * y + c₀) := by
    intro y hy
    rcases lt_or_ge (2 * y + c₀) p with h | h
    · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
    · exact Or.inr ⟨by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)], h⟩
  rcases hm z hz with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases hm z' hz' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rw [h1, h2]
  · exact ⟨0, by push_cast; ring, Or.inl ⟨rfl, by omega, by omega⟩⟩
  · refine ⟨1, by push_cast [Nat.cast_sub h2']; ring, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩
  · refine ⟨-1, by push_cast [Nat.cast_sub h1']; ring, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩
  · refine ⟨0, by push_cast [Nat.cast_sub h1', Nat.cast_sub h2']; ring, Or.inl ⟨rfl, by omega, by omega⟩⟩

end QUNetsM3
