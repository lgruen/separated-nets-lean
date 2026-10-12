/-
Development copy (Solution side) of the new definitions of `ChallengeTwoCoset.lean` (entry
TwoCoset, `prop:twocoset` of `sec:twocoset`, `paper/core.tex`). Keep in sync with
`ChallengeTwoCoset.lean` (verbatim, same order); the shared definitions `digits`, `coord`,
`digitalPt`, `IsDigitalNet033`, `sepSqG` come from `QUNetsM3.Defs` / `QUNetsM3.E1Defs`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.NetDefs

@[expose] public section

namespace QUNetsM3

open Matrix

/-- `r = ⌊(p + 4)/8⌋`, the integer nearest to `p/8` (for odd `p`; paper `prop:twocoset`). -/
def rTC (p : ℕ) : ℕ := (p + 4) / 8

/-- `θ = 8r − p` (paper `prop:twocoset`; `θ ∈ {±1, ±3}` for odd `p`). -/
def thetaTC (p : ℕ) : ℤ := 8 * (rTC p : ℤ) - p

/-- `h = (p − 1)/2 ∈ 𝔽_p` (so `2h = −1`). -/
def hTC (p : ℕ) : ZMod p := (((p - 1) / 2 : ℕ) : ZMod p)

/-- The generator matrices of `𝒯_p` (paper `prop:twocoset`), rows over `𝔽_p`:
`C_x = [e_x ; (0,h,h) ; (0,1,2)]`, `C_y = [e_y ; (r,−1,1) ; (3,0,1)]`,
`C_z = [e_z ; (r,−1,1) ; (1,5,0)]`. -/
def genTC (p : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) :=
  ![Matrix.of ![![1, 0, 0], ![0, hTC p, hTC p], ![0, 1, 2]],
    Matrix.of ![![0, 1, 0], ![(rTC p : ZMod p), -1, 1], ![3, 0, 1]],
    Matrix.of ![![0, 0, 1], ![(rTC p : ZMod p), -1, 1], ![1, 5, 0]]]

/-- The bound of `prop:twocoset` (2): `√(33/32 − 41/(16p)) − √3/p`. -/
noncomputable def cTC (p : ℕ) : ℝ :=
  Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p

/-- `d_*² = (p² − 2p + 3)² + ((r − 1)p + 4)² + ((r − 1)p + 6)²` (paper `prop:twocoset` (3)). -/
def dstarSqTC (p : ℕ) : ℤ :=
  ((p : ℤ) ^ 2 - 2 * p + 3) ^ 2 + (((rTC p : ℤ) - 1) * p + 4) ^ 2 +
    (((rTC p : ℤ) - 1) * p + 6) ^ 2

/-- The normalized toroidal minimum distance `δ N^{1/3}` of `𝒯_p` (`N = p³`): the infimum of
`√(sepSqG)/p²` over distinct indices `x ≠ x' < p³` and torus translates `t`. -/
noncomputable def deltaTC (p : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < p ^ 3 ∧ x' < p ^ 3 ∧ x ≠ x' ∧
    d = Real.sqrt (sepSqG p (genTC p) x x' t : ℝ) / (p : ℝ) ^ 2}

end QUNetsM3
