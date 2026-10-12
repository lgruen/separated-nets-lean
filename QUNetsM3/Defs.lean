module
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# Definitions: base-`p` digits at `m = 3`

The digit vector of an index and its inverse, used by the nets at `m = 3` (`QUNetsM3`). V14 stage S16′: split from the former `EisensteinNet/Defs.lean`; the definitions of the
Eisenstein nets are in the retired Eisenstein development (research history).
-/

namespace QUNetsM3

open Matrix

/-- Most-significant-first base-`p` digit vector of `x` (note: `digits(x)`), read in `ZMod p`:
`(⌊x / p²⌋, ⌊x / p⌋, x)` reduced mod `p`, i.e. `(⌊x/p²⌋, ⌊x/p⌋ mod p, x mod p)` for `x < p³`. -/
def digits (p x : ℕ) : Fin 3 → ZMod p :=
  ![((x / p ^ 2 : ℕ) : ZMod p), ((x / p : ℕ) : ZMod p), ((x : ℕ) : ZMod p)]

/-- Inverse packing (note: `coord`): `w ↦ w₀ p² + w₁ p + w₂` with digits taken in `[0, p)`. -/
def coord (p : ℕ) (w : Fin 3 → ZMod p) : ℕ :=
  (w 0).val * p ^ 2 + (w 1).val * p + (w 2).val

end QUNetsM3
