/-
Development copy (Solution side) of the definitions of `ChallengePPInv.lean` (entry PPInv,
`lem:ppinv` of `app:perprime`, `paper/core.tex`). Keep in sync with `ChallengePPInv.lean`
(the definition section is copied verbatim, in the same order); Comparator checks that the
Solution declarations have the same types and values.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

namespace Z3NetPI

open Matrix

/-! ## The frame `Φ^F` (verbatim from `ChallengeDim3.lean` / `ChallengeKN.lean`) -/

/-- Total entry accessor: `ent A i j = A i j` if `(i, j)` is in range, `0` otherwise. -/
def ent {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) : R :=
  if h : i < a ∧ j < b then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- `τ` on `ℤ[t]_{<m}`, `(τV)(t) = (1-t)^(m-1) V(1/(1-t))` (as `tau` in `Challenge.lean`). -/
def tauD (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i l => (-1) ^ (i : ℕ) * ((m - 1 - (l : ℕ)).choose (i : ℕ) : ℤ)

/-- The frame reading of coordinate `c` (`c = 0, 1, 2`): `τ²`, `I`, `τ`. -/
def frameZD (m c : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  if c = 0 then tauD m * tauD m else if c = 1 then 1 else tauD m

/-- Coarse depth of coordinate `c` (a natural number) for `m = 3k + r`. -/
def depN (r k c : ℕ) : ℕ := if c < r then k + 1 else k

/-- First index digit of block `c`. -/
def offN (r k c : ℕ) : ℕ :=
  if c = 0 then 0 else if c = 1 then depN r k 0 else depN r k 0 + depN r k 1

/-- Block (`0, 1, 2`) of the index digit `i`. -/
def blkN (r k i : ℕ) : ℕ :=
  if i < depN r k 0 then 0 else if i < depN r k 0 + depN r k 1 then 1 else 2

/-- Box matrix of the frame for the depths `depN r k`: row `i` is digit `i - offN (blkN i)` of the
reading `blkN i`. -/
def frameBoxD (r k : ℕ) : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) ℤ :=
  fun i col => ent (frameZD (3 * k + r) (blkN r k i)) ((i : ℕ) - offN r k (blkN r k i)) col

/-- The frame's graph form `Φ^F` over `𝔽_p`: the reading `c` times the inverse box matrix. -/
noncomputable def frameGrN (r p k c : ℕ) : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p) :=
  (frameZD (3 * k + r) c).map (Int.cast : ℤ → ZMod p) *
    ((frameBoxD r k).map (Int.cast : ℤ → ZMod p))⁻¹

/-! ## Window data -/

/-- The window data of an off-diagonal block `A = Φ_cd` (rows = offset rows of `c`, columns =
levels of `d`, level `0` the most significant): its first two offset rows (the geometric rows
`ρ = 0, 1`) on its last three levels (window index `i = 0` the last level). -/
def winB {F : Type*} [Zero F] {a b : ℕ} (A : Matrix (Fin a) (Fin b) F) : Matrix (Fin 2) (Fin 3) F :=
  Matrix.of fun ρ i => ent A (ρ : ℕ) (b - 1 - (i : ℕ))

/-- The part of a row operation `L_c` (on the offset rows of `c`) acting on the first two rows. -/
def winL {F : Type*} [Zero F] {a : ℕ} (L : Matrix (Fin a) (Fin a) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun ρ ρ' => ent L (ρ : ℕ) (ρ' : ℕ)

/-- The part of a column operation `U_d` (on the levels of `d`) acting on the last three levels,
in the window index. -/
def winU {F : Type*} [Zero F] {b : ℕ} (U : Matrix (Fin b) (Fin b) F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i i' => ent U (b - 1 - (i : ℕ)) (b - 1 - (i' : ℕ))

/-- The window data of the frame `Φ^F` with depths `depN r k`: `winF r p k c d ρ i` is geometric
row `ρ` of `c` (offset digit `depN r k c + ρ`) on window column `i` of the cell of `d` (level
`depN r k d - 1 - i`; `0` if `i ≥ depN r k d`, i.e. beyond the cell). -/
noncomputable def winF (r p k : ℕ) : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) (ZMod p) :=
  fun c d => Matrix.of fun ρ i =>
    if (i : ℕ) < depN r k d then
      ent (frameGrN r p k c) (depN r k c + (ρ : ℕ)) (offN r k d + (depN r k d - 1 - (i : ℕ)))
    else 0

/-! ## `lem:ppinv`, `m ≡ 2`: the invariants `κ₁`, `κ₂` on window data

Window data `W c d ρ i`: geometric row `ρ` of `c` on window column `i` of `d`.  For `m ≡ 2`:
`X0 = W 0 · 0`, `Y0 = W 1 · 0`, `Z0 = W 2 · 0` (skeleton digit), `Z1 = W 2 · 1`; the columns
`x_k, x_{k-1}` are `W · 0 · 0, W · 0 · 1`, likewise `y_k, y_{k-1}`. -/

/-- A row on `x̃ = x_{k-1} - (Z0|x_{k-1} / Z0|x_k) x_k`. -/
def tlx2 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (c : Fin 3)
    (ρ : Fin 2) : F :=
  W c 0 ρ 1 - W 2 0 0 1 * (W 2 0 0 0)⁻¹ * W c 0 ρ 0

/-- A row on `ỹ = y_{k-1} - (Z0|y_{k-1} / Z0|y_k) y_k`. -/
def tly2 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (c : Fin 3)
    (ρ : Fin 2) : F :=
  W c 1 ρ 1 - W 2 1 0 1 * (W 2 1 0 0)⁻¹ * W c 1 ρ 0

/-- `κ₁ = (Z1|ỹ · Y0|x̃ · X0|y_k · Z0|x_k) / (Z1|x̃ · Y0|x_k · X0|ỹ · Z0|y_k)`. -/
def kapW1 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  tly2 W 2 1 * tlx2 W 1 0 * W 0 1 0 0 * W 2 0 0 0 *
    (tlx2 W 2 1 * W 1 0 0 0 * tly2 W 0 0 * W 2 1 0 0)⁻¹

/-- `κ₂ = (Z1|x_k / Z0|x_k - Z1|y_k / Z0|y_k) · (Z0|x_k · Y0|x̃) / (Z1|x̃ · Y0|x_k)`. -/
def kapW2 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  (W 2 0 1 0 * (W 2 0 0 0)⁻¹ - W 2 1 1 0 * (W 2 1 0 0)⁻¹) * (W 2 0 0 0 * tlx2 W 1 0) *
    (tlx2 W 2 1 * W 1 0 0 0)⁻¹

/-- `κ₁, κ₂` are defined: their divisors `Z0|x_k`, `Z0|y_k`, `Y0|x_k`, `Z1|x̃`, `X0|ỹ` are
nonzero. -/
def DefK {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : Prop :=
  W 2 0 0 0 ≠ 0 ∧ W 2 1 0 0 ≠ 0 ∧ W 1 0 0 0 ≠ 0 ∧ tlx2 W 2 1 ≠ 0 ∧ tly2 W 0 0 ≠ 0

/-! ## `lem:ppinv`, `m ≡ 1`: the invariants `J₁, …, J₅` on window data

`X0 = W 0 · 0`, `Y0 = W 1 · 0` (skeleton digit), `Y1 = W 1 · 1`, `Z0 = W 2 · 0` (skeleton digit),
`Z1 = W 2 · 1`; `ξ_i = x_{k-i}` is window column `i` of `x`, `η_i = y_{k-1-i}` column `i` of `y`,
`ζ_i = z_{k-1-i}` column `i` of `z`. -/

/-- `R_Y = Y1 - (Y1|ξ₀ / Y0|ξ₀) Y0` on window column `i` of `d`. -/
def RYW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (d i : Fin 3) : F :=
  W 1 d 1 i - W 1 0 1 0 * (W 1 0 0 0)⁻¹ * W 1 d 0 i

/-- `R_Z = Z1 - (Z1|ξ₀ / Z0|ξ₀) Z0` on window column `i` of `d`. -/
def RZW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (d i : Fin 3) : F :=
  W 2 d 1 i - W 2 0 1 0 * (W 2 0 0 0)⁻¹ * W 2 d 0 i

/-- `d_x = [Y0, Z0 | ξ₀, ξ₁]`. -/
def dxW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  W 1 0 0 0 * W 2 0 0 1 - W 1 0 0 1 * W 2 0 0 0

/-- A row on `ζ̃ = ζ₁ - (X0|ζ₁ / X0|ζ₀) ζ₀`, given its values `v0, v1` on `ζ₀, ζ₁`. -/
def tlzW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (v0 v1 : F) : F :=
  v1 - W 0 2 0 1 * (W 0 2 0 0)⁻¹ * v0

/-- A row on `η̃ = η₁ - (X0|η₁ / X0|η₀) η₀`, given its values `v0, v1` on `η₀, η₁`. -/
def tlyW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (v0 v1 : F) : F :=
  v1 - W 0 1 0 1 * (W 0 1 0 0)⁻¹ * v0

/-- The coefficient `a` of `ξ̃ = ξ₂ + a ξ₁ + b ξ₀` (`Y0|ξ̃ = Z0|ξ̃ = 0`, Cramer's rule). -/
def xiAW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  (W 1 0 0 0 * W 2 0 0 2 - W 1 0 0 2 * W 2 0 0 0) *
    (W 1 0 0 1 * W 2 0 0 0 - W 1 0 0 0 * W 2 0 0 1)⁻¹

/-- The coefficient `b` of `ξ̃ = ξ₂ + a ξ₁ + b ξ₀`. -/
def xiBW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  (W 1 0 0 2 * W 2 0 0 1 - W 1 0 0 1 * W 2 0 0 2) *
    (W 1 0 0 1 * W 2 0 0 0 - W 1 0 0 0 * W 2 0 0 1)⁻¹

/-- A row on `ξ̃`, given its values `v0, v1, v2` on `ξ₀, ξ₁, ξ₂`. -/
def tlxW {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (v0 v1 v2 : F) : F :=
  v2 + xiAW W * v1 + xiBW W * v0

/-- `J₁ = (R_Y|ξ₁ · Z0|ξ₀ · Y0|ζ₀) / (R_Y|ζ₀ · d_x)`. -/
def JW1 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  RYW W 0 1 * W 2 0 0 0 * W 1 2 0 0 * (RYW W 2 0 * dxW W)⁻¹

/-- `J₂ = (R_Z|ξ₁ · Y0|ξ₀ · Z0|η₀) / (R_Z|η₀ · d_x)`. -/
def JW2 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  RZW W 0 1 * W 1 0 0 0 * W 2 1 0 0 * (RZW W 1 0 * dxW W)⁻¹

/-- `J₃ = (R_Y|ζ̃ · Y0|ζ₀) / (Y0|ζ̃ · R_Y|ζ₀)`. -/
def JW3 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  tlzW W (RYW W 2 0) (RYW W 2 1) * W 1 2 0 0 * (tlzW W (W 1 2 0 0) (W 1 2 0 1) * RYW W 2 0)⁻¹

/-- `J₄ = (R_Z|η̃ · Z0|η₀) / (Z0|η̃ · R_Z|η₀)`. -/
def JW4 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  tlyW W (RZW W 1 0) (RZW W 1 1) * W 2 1 0 0 * (tlyW W (W 2 1 0 0) (W 2 1 0 1) * RZW W 1 0)⁻¹

/-- `J₅ = (R_Z|ξ̃ · Y0|ξ₀ · Z0|η₀ · R_Y|ζ₀) / (R_Y|ξ̃ · Z0|ξ₀ · Y0|ζ₀ · R_Z|η₀)`. -/
def JW5 {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : F :=
  tlxW W (RZW W 0 0) (RZW W 0 1) (RZW W 0 2) * W 1 0 0 0 * W 2 1 0 0 * RYW W 2 0 *
    (tlxW W (RYW W 0 0) (RYW W 0 1) (RYW W 0 2) * W 2 0 0 0 * W 1 2 0 0 * RZW W 1 0)⁻¹

/-- `J₁, …, J₅` are defined: the divisors `Y0|ξ₀`, `Z0|ξ₀`, `d_x`, `R_Y|ζ₀`, `R_Z|η₀`, `X0|ζ₀`,
`X0|η₀`, `Y0|ζ̃`, `Z0|η̃`, `Y0|ζ₀`, `Z0|η₀`, `R_Y|ξ̃` are nonzero. -/
def DefJ {F : Type*} [Field F] (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : Prop :=
  W 1 0 0 0 ≠ 0 ∧ W 2 0 0 0 ≠ 0 ∧ dxW W ≠ 0 ∧ RYW W 2 0 ≠ 0 ∧ RZW W 1 0 ≠ 0 ∧
    W 0 2 0 0 ≠ 0 ∧ W 0 1 0 0 ≠ 0 ∧ tlzW W (W 1 2 0 0) (W 1 2 0 1) ≠ 0 ∧
    tlyW W (W 2 1 0 0) (W 2 1 0 1) ≠ 0 ∧ W 1 2 0 0 ≠ 0 ∧ W 2 1 0 0 ≠ 0 ∧
    tlxW W (RYW W 0 0) (RYW W 0 1) (RYW W 0 2) ≠ 0

end Z3NetPI
