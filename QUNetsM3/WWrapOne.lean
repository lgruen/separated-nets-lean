/-
`rem:wshift`, the shift `t ≡ 2t′ + 1` of `𝒲_p`: the wraps of the digit `(2ζ + 1) mod p` give the same pairs as
`lem:wwrap` (`paper/core.tex`). V14 stage S16′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WWrap

@[expose] public section

/-!
# `rem:wshift`: wraps of the digit `2ζ + 1`

`wrapOne_iff`: for odd `p` the digit `2z + 1` (`z < p`) wraps, `2z + 1 ≥ p`, if and only if `z ≥ h`, one step earlier
than `2z` (`z ≥ h + 1`). `wwrap_one_scalar`: the proof of `lem:wwrap` (`wwrap_scalar`) with `h` in place of `h + 1`;
for `Δζ = d > 0`, `ω = 1` iff `z ≤ h − 1 < z + d` (always possible), `ω = 0` iff `z + d ≤ h − 1` (possible iff
`d ≤ h − 1`) or `z ≥ h` (possible iff `d ≤ h`); so the pairs are again exactly those of `WrapAllowed`.
`wwrap_one`: the lift to `n ∈ 𝔽_p³`, as in `wwrap`.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-- `[2z + 1 ≥ p]`: the digit `(2z + 1) mod p` has wrapped. -/
def wrapOne (p z : ℕ) : ℤ := if p ≤ 2 * z + 1 then 1 else 0

/-- The digit `2z + 1` wraps if and only if `z ≥ h`. -/
theorem wrapOne_iff (hodd : p % 2 = 1) (z : ℕ) : p ≤ 2 * z + 1 ↔ hW p ≤ z := by
  unfold hW; omega

/-- The scalar form: the pairs `(z' − z, [2z' + 1 ≥ p] − [2z + 1 ≥ p])` with `z < p`, `z' = (z + σ) mod p` are exactly
those of `WrapAllowed`. -/
theorem wwrap_one_scalar (hodd : p % 2 = 1) (hp3 : 3 ≤ p) {σ : ℕ} (hσ : σ < p) (d k : ℤ) :
    (∃ z : ℕ, z < p ∧ ((((z + σ) % p : ℕ) : ℤ) - z = d ∧
      wrapOne p ((z + σ) % p) - wrapOne p z = k)) ↔ WrapAllowed p σ d k := by
  have hh : 2 * hW p + 1 = p := by unfold hW; omega
  constructor
  · rintro ⟨z, hz, hd, hk⟩
    unfold WrapAllowed
    rcases lt_or_ge (z + σ) p with h | h
    · rw [Nat.mod_eq_of_lt h] at hd hk
      simp only [wrapOne] at hk
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
      simp only [wrapOne] at hk
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
    · -- (σ, 1): `z ≤ h − 1 < z + σ`
      have hk1 : k = 1 := by rw [hk, hd, Int.sign_natCast_of_ne_zero h0]
      subst hk1
      refine ⟨if hW p ≤ σ then 0 else hW p - σ, by split_ifs <;> omega, ?_⟩
      split_ifs with hc
      · rw [Nat.mod_eq_of_lt (by omega)]
        simp only [wrapOne]
        refine ⟨by push_cast; omega, ?_⟩
        split_ifs <;> omega
      · rw [Nat.mod_eq_of_lt (by omega)]
        simp only [wrapOne]
        refine ⟨by push_cast [Nat.cast_sub (show σ ≤ hW p by omega)]; omega, ?_⟩
        split_ifs <;> omega
    · -- (σ, 0), σ ≤ h: both digits at or above the wrap, `z = h`
      rw [hd, abs_of_nonneg (by omega)] at hdh
      refine ⟨hW p, by omega, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [wrapOne]
      refine ⟨by push_cast; omega, ?_⟩
      split_ifs <;> omega
    · -- (σ − p, −1)
      have hk1 : k = -1 := by rw [hk, hd]; exact Int.sign_eq_neg_one_of_neg (by omega)
      subst hk1
      refine ⟨if hW p ≤ p - σ then p - σ else hW p, by split_ifs <;> omega, ?_⟩
      split_ifs with hc
      · have hm : (p - σ + σ) % p = 0 := by rw [Nat.sub_add_cancel hσ.le, Nat.mod_self]
        rw [hm]
        simp only [wrapOne]
        refine ⟨by push_cast [Nat.cast_sub hσ.le]; omega, ?_⟩
        split_ifs <;> omega
      · have hm : (hW p + σ) % p = hW p + σ - p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        simp only [wrapOne]
        refine ⟨by push_cast [Nat.cast_sub (show p ≤ hW p + σ by omega)]; omega, ?_⟩
        split_ifs <;> omega
    · -- (σ − p, 0), p − σ ≤ h: both digits at or above the wrap, `z = p − 1`
      rw [hd, abs_of_neg (by omega)] at hdh
      refine ⟨p - 1, by omega, ?_⟩
      have hm : (p - 1 + σ) % p = σ - 1 := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      rw [hm]
      simp only [wrapOne]
      refine ⟨by push_cast [Nat.cast_sub (show 1 ≤ σ by omega), Nat.cast_sub (show 1 ≤ p by omega)]; omega, ?_⟩
      split_ifs <;> omega

/-- **`rem:wshift`, the digit `2ζ + 1`** (proof of `W_wrap_one`): it wraps iff `ζ ≥ h`, and as `n` runs over `𝔽_p³`
the pairs `(Δζ, ω)`, `ω = [2ζ(n') + 1 ≥ p] − [2ζ(n) + 1 ≥ p]`, are exactly those of `WrapAllowed`. -/
theorem wwrap_one (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (E : Fin 3 → ℤ) (d k : ℤ) :
    (∀ z : ℕ, z < p → (p ≤ 2 * z + 1 ↔ hW p ≤ z)) ∧
    ((∃ n : Fin 3 → ZMod p, dZetaW p u n E = d ∧
        (if p ≤ 2 * zetaW p u (n + fun c => (E c : ZMod p)) + 1 then (1 : ℤ) else 0) -
          (if p ≤ 2 * zetaW p u n + 1 then (1 : ℤ) else 0) = k) ↔
      WrapAllowed p (sigmaW p u E) d k) := by
  have := Fact.mk hp
  have hodd : p % 2 = 1 := odd_of_prime5 hp hp5
  refine ⟨fun z _ => wrapOne_iff hodd z, ?_⟩
  have hσ : sigmaW p u E < p := ZMod.val_lt _
  rw [← wwrap_one_scalar hodd (by omega) hσ]
  change (∃ n : Fin 3 → ZMod p, dZetaW p u n E = d ∧
      wrapOne p (zetaW p u (n + fun c => (E c : ZMod p))) - wrapOne p (zetaW p u n) = k) ↔ _
  constructor
  · rintro ⟨n, hd, hk⟩
    refine ⟨zetaW p u n, ZMod.val_lt _, ?_, ?_⟩
    · rw [← hd]; unfold dZetaW; rw [zetaW_add]
    · rw [← hk, zetaW_add]
  · rintro ⟨z, hz, hd, hk⟩
    by_cases hs : sigmaW p u E = 0
    · -- σ = 0: every `n` gives `(0, 0)`
      refine ⟨0, ?_, ?_⟩
      · rw [← hd]; unfold dZetaW; rw [zetaW_add, hs]
        simp only [zetaW, dotProduct_zero, ZMod.val_zero, Nat.zero_mod, add_zero]
        rw [Nat.mod_eq_of_lt hz]; simp
      · rw [← hk, zetaW_add, hs]
        simp only [zetaW, dotProduct_zero, ZMod.val_zero, Nat.zero_mod, add_zero]
        rw [Nat.mod_eq_of_lt hz]; simp
    · have hu : u ≠ 0 := by
        rintro rfl; apply hs; simp [sigmaW]
      obtain ⟨n, hn⟩ := zetaW_onto hu z hz
      refine ⟨n, ?_, ?_⟩
      · rw [← hd]; unfold dZetaW; rw [zetaW_add, hn]
      · rw [← hk, zetaW_add, hn]

end QUNetsM3
