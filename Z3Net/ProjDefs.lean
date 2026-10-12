/-
Definitions for `rem:projlines` (the middle digits of two coordinates of `𝒫^F_{k,q}` and `𝒫_{k,q}`, and the
rescaling of one row of the generator matrices) of the manuscript *Low-discrepancy quasi-uniform digital nets in every
dimension* (`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDefs

@[expose] public section

/-!
# Definitions for `rem:projlines` (V14 stage S13′)

* `dig C v r`: digit `r` (digit `0` most significant) of the digital point with generator matrix `C` and index `v`.
* `RowRel A B r g`: digit `r` of the coordinate with generator matrix `B` is `g` times digit `r` of the coordinate with
  generator matrix `A`, plus a linear combination of the more significant digits `0, …, r-1` of both coordinates, as
  functionals of the index `v` (the relation of `rem:projlines`).
* `projSign inf a b r`: the sign of `rem:projlines` for the places of the coordinates `a`, `b` of a frame whose
  coordinate `inf` is read at `∞`: `+1` if one of the two places is `∞`, `(-1)^r` otherwise.
* `pairDepth a b r`: the depths `r + 1` at `a`, `r` at `b`, `0` elsewhere (the box used to produce the relation).
* `rowScale C r ρ`: row `r` of every generator matrix `C_c` multiplied by `ρ_c` (the remedy of `rem:projlines`).
-/

namespace Z3NetF

open Matrix Finset

/-- Digit `r` (digit `0` most significant) of the digital point with generator matrix `C` and index `v`: the entry
`(C v)_r`, and `0` for `r ≥ m`. -/
def dig {R : Type*} [CommRing R] {m : ℕ} (C : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (r : ℕ) : R :=
  if h : r < m then (C *ᵥ v) ⟨r, h⟩ else 0

/-- The relation of `rem:projlines`: digit `r` of the coordinate with generator matrix `B` equals `g` times digit `r`
of the coordinate with generator matrix `A` plus a linear combination (coefficients `α`, `β` independent of the index)
of the more significant digits `0, …, r-1` of both coordinates, for every index `v`. -/
def RowRel {R : Type*} [CommRing R] {m : ℕ} (A B : Matrix (Fin m) (Fin m) R) (r : ℕ) (g : R) : Prop :=
  ∃ α β : ℕ → R, ∀ v : Fin m → R,
    dig B v r = g * dig A v r + ∑ l ∈ range r, (α l * dig A v l + β l * dig B v l)

/-- The sign of `rem:projlines` for the coordinates `a`, `b` of a frame whose coordinate `inf` is read at `∞`: `+1` if
one of the two places is `∞`, `(-1)^r` if both are finite. -/
def projSign {s : ℕ} (inf a b : Fin s) (r : ℕ) : ℤ :=
  if a = inf ∨ b = inf then 1 else (-1) ^ r

/-- The depths `r + 1` at `a`, `r` at `b` (`a ≠ b`), `0` at the other coordinates. -/
def pairDepth {s : ℕ} (a b : Fin s) (r : ℕ) : Fin s → ℕ :=
  fun c => if c = a then r + 1 else if c = b then r else 0

/-- Row `r` of every generator matrix `C_c` multiplied by `ρ_c` (left multiplication by the diagonal matrix with entry
`ρ_c` in row `r` and `1` elsewhere). -/
def rowScale {R : Type*} [Mul R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ) (ρ : Fin s → R) :
    Fin s → Matrix (Fin m) (Fin m) R :=
  fun c i j => if (i : ℕ) = r then ρ c * C c i j else C c i j

end Z3NetF
