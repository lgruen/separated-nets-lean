/-
Definitions (V14 stage S16′): `rem:shiftparity` (infinite deep-shift chains, frozen from every resolution).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Defs

@[expose] public section

/-!
# Definitions for `rem:shiftparity`: infinite deep-shift chains

* `IsLiftSeq b m₀ D G S`: the generator matrices `G m` and shifts `S m` at the levels `m = m₀ + 3k` form an infinite
  chain of lifts (`def:lift`): from every level `ℓ ≥ m₀` of the class, the next level is the lift of `ℓ` with shifts
  vanishing on the first `D ℓ` digits (admissibility is not required).
* `FrozenFromEvery m₀ D`: the depth parameters satisfy the hypothesis of `lem:liftsep` from every level `L` of the
  chain (`D_ℓ ≥ ⌊L/2⌋ + (ℓ − L)/3` for `ℓ ≥ L`; for instance `D_ℓ = ⌊ℓ/2⌋`), "a chain frozen from every resolution".
-/

namespace Z3NetB23

open Matrix

/-- **`rem:shiftparity`, an infinite deep-shift chain** from level `m₀`: for every level `ℓ ≥ m₀` with
`ℓ ≡ m₀ (mod 3)`, the generator matrices `G (ℓ + 3)` and the shift `S (ℓ + 3)` are those of the lift `L_{D ℓ}`
(`def:lift`) of `(G ℓ, S ℓ)`, with shifts `s_A, s_B` vanishing on the first `D ℓ` digits of each coordinate
(admissibility is not required). -/
def IsLiftSeq (b m₀ : ℕ) (D : ℕ → ℕ) (G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b))
    (S : (m : ℕ) → Fin 3 → Fin m → ZMod b) : Prop :=
  ∀ ℓ, m₀ ≤ ℓ → ℓ % 3 = m₀ % 3 → ∃ sA sB : Fin 3 → Fin ℓ → ZMod b,
    VanishTop (D ℓ) sA ∧ VanishTop (D ℓ) sB ∧ G (ℓ + 3) = liftGen (G ℓ) sA sB ∧ S (ℓ + 3) = liftShift (S ℓ)

/-- **`rem:shiftparity`, frozen from every resolution**: for every level `L ≥ m₀` of the class `m₀ (mod 3)` and every
`ℓ ≥ L`, `D ℓ ≥ ⌊L/2⌋ + (ℓ − L)/3` (the hypothesis of `lem:liftsep` from `L`). -/
def FrozenFromEvery (m₀ : ℕ) (D : ℕ → ℕ) : Prop :=
  ∀ L ℓ, m₀ ≤ L → L % 3 = m₀ % 3 → L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ

end Z3NetB23
