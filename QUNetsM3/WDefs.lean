/-
Definitions of `sec:wnet` (the rank-one layer at `m = 3`: `prop:wnet`, `lem:wwrap`, `prop:wfamily`,
`rem:wstar`, and the `𝒲_p` sentence of `rem:shiftshared`; `paper/core.tex`). V14 stage S12′.
The shared definitions `digits`, `coord`, `digitalPt`, `IsDigitalNet033`, `sepSqG` come from
`QUNetsM3.Defs` / `QUNetsM3.E1Defs`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.NetDefs

@[expose] public section

namespace QUNetsM3

open Matrix

/-! ## The nets `𝒲_p` and `𝒲*_p` (`prop:wnet`, `rem:wstar`) -/

/-- `h = (p − 1)/2` (so `2h = −1` in `𝔽_p` for odd `p`). -/
def hW (p : ℕ) : ℕ := (p - 1) / 2

/-- `r = ⌊p/48⌋` (paper `prop:wnet`). -/
def rW (p : ℕ) : ℕ := p / 48

/-- `ρ = 2r + 1` in `𝔽_p`. -/
def rhoZ (p r : ℕ) : ZMod p := ((2 * r + 1 : ℕ) : ZMod p)

/-- The generator matrices of `prop:wnet` with the parameter `r` free (`ρ = 2r + 1`), rows over `𝔽_p`:
`C_x = [e_x ; ρ(−1,−1,2) ; (0,1,2)]`, `C_y = [e_y ; ρ(−1,−1,2) ; (1,0,1)]`,
`C_z = [e_z ; (h−r, h−r, ρ) ; (0,1,0)]`. With `r = ⌊p/48⌋` this is `𝒲_p` (`genW`), with
`r = ⌊pε*⌋` it is `𝒲*_p` of `rem:wstar` (`genWstar`). -/
def genWr (p r : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) :=
  ![Matrix.of ![![1, 0, 0], ![-rhoZ p r, -rhoZ p r, 2 * rhoZ p r], ![0, 1, 2]],
    Matrix.of ![![0, 1, 0], ![-rhoZ p r, -rhoZ p r, 2 * rhoZ p r], ![1, 0, 1]],
    Matrix.of ![![0, 0, 1], ![(hW p : ZMod p) - r, (hW p : ZMod p) - r, rhoZ p r], ![0, 1, 0]]]

/-- The generator matrices of `𝒲_p` (paper `prop:wnet`): `genWr` at `r = ⌊p/48⌋`. -/
def genW (p : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) := genWr p (rW p)

/-- The bound of `prop:wnet` (2): `√(281/256 − 345/(128p)) − √3/p`. -/
noncomputable def cW (p : ℕ) : ℝ :=
  Real.sqrt (281 / 256 - 345 / (128 * (p : ℝ))) - Real.sqrt 3 / p

/-- `d_*² = (p² − (6r+2)p − 2)² + (6r+3)²p² + (h+3r+2)²p²` (paper `prop:wnet` (3)). -/
def dstarSqW (p : ℕ) : ℤ :=
  ((p : ℤ) ^ 2 - (6 * (rW p : ℤ) + 2) * p - 2) ^ 2 + (6 * (rW p : ℤ) + 3) ^ 2 * (p : ℤ) ^ 2 +
    ((hW p : ℤ) + 3 * (rW p : ℤ) + 2) ^ 2 * (p : ℤ) ^ 2

/-- The normalized toroidal minimum distance `δ N^{1/3}` (`N = p³`) of the digital point set with
generator matrices `C`: the infimum of `√(sepSqG)/p²` over distinct indices `x ≠ x' < p³` and torus
translates `t`. -/
noncomputable def deltaG (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) : ℝ :=
  sInf {d : ℝ | ∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < p ^ 3 ∧ x' < p ^ 3 ∧ x ≠ x' ∧
    d = Real.sqrt (sepSqG p C x x' t : ℝ) / (p : ℝ) ^ 2}

/-- `δ N^{1/3}` of `𝒲_p`. -/
noncomputable def deltaW (p : ℕ) : ℝ := deltaG p (genW p)

/-- The exact minimum distances of `𝒲_p` at the primes `17 ≤ p ≤ 89` (`prop:wnet` (4)): pairs `(p, d)`, `d` the
squared toroidal minimum distance at integer scale `p³` (so `δN^{1/3} = √d/p²`). -/
def wExactTab : List (ℕ × ℕ) :=
  [(17, 84984), (19, 132104), (23, 282360), (29, 711144), (31, 927896), (37, 1880264), (41, 2833176),
    (43, 3426920), (47, 4889304), (53, 8310350), (59, 12940355), (61, 14848318), (67, 21611220),
    (71, 27131620), (73, 30258900), (79, 41278404), (83, 50138260), (89, 66013204)]

/-! ## `lem:wwrap` -/

/-- `ζ(n) = u · n mod p ∈ {0, …, p − 1}`. -/
def zetaW (p : ℕ) (u n : Fin 3 → ZMod p) : ℕ := (u ⬝ᵥ n).val

/-- `[2ζ ≥ p]`: the digit `2ζ mod p` has wrapped. -/
def wrapW (p z : ℕ) : ℤ := if p ≤ 2 * z then 1 else 0

/-- `Δζ = ζ(n') − ζ(n)` for `n' = n + E` (`E ∈ ℤ³` reduced mod `p`). -/
def dZetaW (p : ℕ) (u n : Fin 3 → ZMod p) (E : Fin 3 → ℤ) : ℤ :=
  (zetaW p u (n + fun c => (E c : ZMod p)) : ℤ) - zetaW p u n

/-- `κ = [2ζ(n') ≥ p] − [2ζ(n) ≥ p]` for `n' = n + E`. -/
def kappaW (p : ℕ) (u n : Fin 3 → ZMod p) (E : Fin 3 → ℤ) : ℤ :=
  wrapW p (zetaW p u (n + fun c => (E c : ZMod p))) - wrapW p (zetaW p u n)

/-- `σ ∈ {0, …, p − 1}`, the residue of `u · E`. -/
def sigmaW (p : ℕ) (u : Fin 3 → ZMod p) (E : Fin 3 → ℤ) : ℕ :=
  (u ⬝ᵥ fun c => (E c : ZMod p)).val

/-- The pairs `(Δζ, κ)` of `lem:wwrap`: `(0, 0)` if `σ = 0`; if `σ ≠ 0`, for each `Δζ ∈ {σ, σ − p}` the pair
`(Δζ, sgn Δζ)`, and also `(Δζ, 0)` if `|Δζ| ≤ h`. -/
def WrapAllowed (p σ : ℕ) (d k : ℤ) : Prop :=
  (σ = 0 ∧ d = 0 ∧ k = 0) ∨
    (σ ≠ 0 ∧ (d = σ ∨ d = (σ : ℤ) - p) ∧ (k = Int.sign d ∨ (k = 0 ∧ |d| ≤ (hW p : ℤ))))

/-! ## `prop:wfamily` -/

/-- The sign of a real number, as an integer. -/
noncomputable def sgnR (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

/-- `𝐰 = (2, 2, 1)`. -/
def wW : Fin 3 → ℝ := ![2, 2, 1]

/-- `(1, 1, 0)`. -/
def oneOneW : Fin 3 → ℝ := ![1, 1, 0]

/-- An option `(E, δ, κ)` of `τ` (paper `prop:wfamily`): `δ ∈ (−1, 1)`, `δ ≡ τ · E (mod 1)`, and `κ = sgn δ`,
or `κ = 0` if `|δ| < ½`. -/
def IsOptW (τ : Fin 3 → ℝ) (E : Fin 3 → ℤ) (δ : ℝ) (κ : ℤ) : Prop :=
  -1 < δ ∧ δ < 1 ∧ (∃ k : ℤ, δ = ∑ c, τ c * (E c : ℝ) + k) ∧ (κ = sgnR δ ∨ (κ = 0 ∧ |δ| < 1 / 2))

/-- `|E + δ𝐰 − κ(1,1,0)|²`. -/
noncomputable def optValW (E : Fin 3 → ℤ) (δ : ℝ) (κ : ℤ) : ℝ :=
  ∑ c, ((E c : ℝ) + δ * wW c - (κ : ℝ) * oneOneW c) ^ 2

/-- `F(τ)` (paper `prop:wfamily`): the least value of `|E + δ𝐰 − κ(1,1,0)|²` over the steps `E ∈ ℤ³ ∖ 0` and
the options `(δ, κ)` of `τ` (an infimum; `τ ∈ ℝ³` stands for its class in `(ℝ/ℤ)³`). -/
noncomputable def Ffam (τ : Fin 3 → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ E : Fin 3 → ℤ, E ≠ 0 ∧ ∃ δ : ℝ, ∃ κ : ℤ, IsOptW τ E δ κ ∧ v = optValW E δ κ}

/-- The digital point set over `𝔽_p` in graph form with depths `(1,1,1)` whose layer is `𝐰uᵀ`,
`𝐰 = (2,2,1)`, with third rows `T`: `C_c = [e_c ; 𝐰_c u ; T_c]` (paper `prop:wfamily`). -/
def genWfam (p : ℕ) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) :
    Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) :=
  fun c => Matrix.of ![Pi.single c 1, ((![2, 2, 1] : Fin 3 → ZMod p) c) • u, T c]

/-- `F_p(u)` (paper `prop:wfamily` (1)): the squared toroidal minimum distance of the points
`p²n + p g(n)` at integer scale `p³` (the net `genWfam p u 0`, without third digits), divided by `p⁴`
(an infimum over distinct indices and torus translates). -/
noncomputable def FpW (p : ℕ) (u : Fin 3 → ZMod p) : ℝ :=
  sInf {v : ℝ | ∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < p ^ 3 ∧ x' < p ^ 3 ∧ x ≠ x' ∧
    v = (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 4}

/-- `u/p ∈ [0,1)³` (the residues of `u`, divided by `p`). -/
noncomputable def tauOf (p : ℕ) (u : Fin 3 → ZMod p) : Fin 3 → ℝ := fun c => ((u c).val : ℝ) / p

/-- `q_a(ε) = 5/4 − 9ε + 81ε²` (row (a) of `tab:wcontacts`, the diagonal contact). -/
noncomputable def qaW (ε : ℝ) : ℝ := 5 / 4 - 9 * ε + 81 * ε ^ 2

/-- `q_b(ε) = 1 + 4ε + 36ε²` (row (b) of `tab:wcontacts`, the layer step along `e_z`). -/
noncomputable def qbW (ε : ℝ) : ℝ := 1 + 4 * ε + 36 * ε ^ 2

/-- `ε* = (13 − 2√31)/90`, the smaller root of `q_a = q_b`. -/
noncomputable def epsStar : ℝ := (13 - 2 * Real.sqrt 31) / 90

/-- `μ*² = (72 − 8√31)/25`. -/
noncomputable def muStarSq : ℝ := (72 - 8 * Real.sqrt 31) / 25

/-- `μ* = √((72 − 8√31)/25)`. -/
noncomputable def muStar : ℝ := Real.sqrt muStarSq

/-- `τ_ε = (½ − ε, ½ − ε, 2ε)`. -/
noncomputable def tauEps (ε : ℝ) : Fin 3 → ℝ := ![1 / 2 - ε, 1 / 2 - ε, 2 * ε]

/-- `τ* = (½ − ε*, ½ − ε*, 2ε*)`. -/
noncomputable def tauStar : Fin 3 → ℝ := tauEps epsStar

/-- The layer vector `u = (h − r, h − r, ρ)` of `genWr p r` (`z` reads `ζ = u·n`). -/
def uW (p r : ℕ) : Fin 3 → ZMod p := ![(hW p : ZMod p) - r, (hW p : ZMod p) - r, rhoZ p r]

/-- The third rows of `prop:wnet`: `(0,1,2)`, `(1,0,1)`, `(0,1,0)`. -/
def thirdW (p : ℕ) : Fin 3 → Fin 3 → ZMod p := ![![0, 1, 2], ![1, 0, 1], ![0, 1, 0]]

/-! ## `rem:wstar` -/

/-- `r = ⌊pε*⌋` (paper `rem:wstar`). -/
noncomputable def rStar (p : ℕ) : ℕ := ⌊(p : ℝ) * epsStar⌋₊

/-- The generator matrices of `𝒲*_p`: `genWr` at `r = ⌊pε*⌋`. -/
noncomputable def genWstar (p : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) := genWr p (rStar p)

/-- `ε_p = ρ/(2p)` with `ρ = 2⌊pε*⌋ + 1`. -/
noncomputable def epsP (p : ℕ) : ℝ := (2 * (rStar p : ℝ) + 1) / (2 * p)

/-- `K = (9√31 − 36)/5 = |q_a'(ε*)|/2`. -/
noncomputable def KW : ℝ := (9 * Real.sqrt 31 - 36) / 5

/-- The bound `f(p) = √(μ*² − K/p) − √3/p` of `rem:wstar`. -/
noncomputable def fStar (p : ℕ) : ℝ := Real.sqrt (muStarSq - KW / p) - Real.sqrt 3 / p

/-! ## Digital shifts (`rem:shiftshared`) -/

/-- Coordinate `c` (at integer scale `p³`) of the point with index `x` of the digital point set with
generator matrices `C`, shifted digit by digit by `τ c` (`def:dshift`): `coord(C_c · digits(x) + τ_c)`. -/
def digitalPtS (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (τ : Fin 3 → Fin 3 → ZMod p)
    (x : ℕ) (c : Fin 3) : ℕ :=
  coord p (C c *ᵥ digits p x + τ c)

/-- `sepSqG` for the shifted point set. -/
def sepSqGS (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (τ : Fin 3 → Fin 3 → ZMod p)
    (x x' : ℕ) (t : Fin 3 → ℤ) : ℤ :=
  ∑ c, ((digitalPtS p C τ x' c : ℤ) - digitalPtS p C τ x c + (p : ℤ) ^ 3 * t c) ^ 2

end QUNetsM3
