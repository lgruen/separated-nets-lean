module
public import QUNetsM3.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Definitions: digital `(0,3,3)`-nets from three generator matrices

The point set `digitalPt` of generator matrices `C 0, C 1, C 2` over `ℤ/pℤ`, the net property
`IsDigitalNet033` and the squared toroidal difference `sepSqG`, used by `prop:twocoset` and
`sec:wnet`. V14 stage S16′: split from the former `EisensteinNet/E1Defs.lean` (the definitions
of the former net 𝓔_p are in the retired Eisenstein development (research history)).
-/

namespace QUNetsM3

open Matrix

/-- Coordinate `c` (at integer scale `p³`) of the point with index `x` of the digital point set
with generator matrices `C 0, C 1, C 2`: `coord(C_c · digits(x))`. -/
def digitalPt (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (x : ℕ) (c : Fin 3) : ℕ :=
  coord p (C c *ᵥ digits p x)

/-- The `(0,3,3)`-net property in base `p` of the digital point set with generator matrices
`C 0, C 1, C 2`, at integer scale `p³`: for every composition `d 0 + d 1 + d 2 = 3` and every
elementary box `∏_c [b_c/p^{d_c}, (b_c+1)/p^{d_c})` exactly one index `x < p³` has its
normalized point in the box (coordinate `c` of the point at integer scale lies in
`[b_c p^{3-d_c}, (b_c+1) p^{3-d_c})`). -/
def IsDigitalNet033 (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) : Prop :=
  ∀ d : Fin 3 → ℕ, ∑ c, d c = 3 → ∀ b : Fin 3 → ℕ, (∀ c, b c < p ^ d c) →
    ∃! x : ℕ, x < p ^ 3 ∧ ∀ c, digitalPt p C x c / p ^ (3 - d c) = b c

/-- Squared length of the difference of the points with indices `x` and `x'`, translated by the
torus period vector `p³ · t`.  The squared toroidal distance is the minimum of this over
`t ∈ ℤ³`. -/
def sepSqG (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (x x' : ℕ) (t : Fin 3 → ℤ) :
    ℤ :=
  ∑ c, ((digitalPt p C x' c : ℤ) - digitalPt p C x c + (p : ℤ) ^ 3 * t c) ^ 2

end QUNetsM3
