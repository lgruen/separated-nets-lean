/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DeficitDefs
public import Z3Net.ThmADefs

@[expose] public section

/-!
# Definitions: lower bounds for the deficit of frame designs (`sec:Lstar`)

V14 stage S7 (`lem:O`, `prop:E`, `lem:C`, `thm:Lstar`). The deficit `K(F)` is `Kdef` of
`Z3Net/DeficitDefs.lean` (`def:K`), the weights `w_cd` are `wN` of `Z3Net/FDefs.lean`
(`prop:Ns`), the places `∞, 0, 1, …, s-2` are `Z3NetA.placeA` with `inf = 0` (coordinate `0` at
`∞`, coordinate `c ≥ 1` at the place `c - 1`), and `lcm(1, …, n)` is Mathlib's
`Nat.lcmUpto n` (`Mathlib/NumberTheory/Chebyshev.lean`).

* `QK K`: `Q_K = {x/y : x, y ∈ ℤ, 1 ≤ |x|, |y| ≤ K}`.
* `tauStar x`: `τ*(x) = max_{1 ≤ m ≤ x} τ(m)`, `τ(m)` the number of divisors of `m` (`0` for
  `x = 0`).
* `homPt inf x c`: homogeneous coordinates `[α_c : β_c]` of the place of coordinate `c` of a frame
  (`[1 : 0]` at `∞`, `[a_c : 1]` at a finite place), as in the paragraph before `lem:CH`.
* `PGLImage inf x`: the places of the frame `(inf, x)` over `ℚ` are the image of the places
  `∞, 0, 1, …, s-2` under an element of `PGL₂(ℚ)` (a matrix `g` with `det g ≠ 0`, acting on
  homogeneous coordinates up to nonzero scalars), in any assignment to the coordinates (a
  permutation `π`).
-/

namespace Z3NetF

open Matrix Finset

/-- `Q_K = {x/y : x, y ∈ ℤ, 1 ≤ |x|, |y| ≤ K}` (before `lem:C`). -/
def QK (K : ℕ) : Set ℚ :=
  {z | ∃ a b : ℤ, 1 ≤ |a| ∧ |a| ≤ K ∧ 1 ≤ |b| ∧ |b| ≤ K ∧ z = (a : ℚ) / b}

/-- `τ*(x) = max_{1 ≤ m ≤ x} τ(m)`, `τ(m)` the number of divisors of `m` (before `lem:C`). -/
def tauStar (x : ℕ) : ℕ := (Icc 1 x).sup fun m => m.divisors.card

/-- Homogeneous coordinates `[α_c : β_c]` of the place of coordinate `c` of the frame `(inf, x)`:
`[1 : 0]` for `c = inf` (the place `∞`), `[a_c : 1]` otherwise. -/
def homPt {s : ℕ} (inf : Fin s) (x : Fin s → ℚ) (c : Fin s) : Fin 2 → ℚ :=
  if c = inf then ![1, 0] else ![x c, 1]

/-- The places of the frame `(inf, x)` over `ℚ` are the image of `∞, 0, 1, …, s-2` under an
element of `PGL₂(ℚ)`: there are `g ∈ GL₂(ℚ)`, a permutation `π` of the coordinates and nonzero
scalars `t_c` with `[α_c, β_c] = t_c · g [α°_{π c}, β°_{π c}]`, where `[α°_e : β°_e]` are the
homogeneous coordinates of the places `∞, 0, 1, …, s-2` on the coordinates `0, 1, …, s-1`
(`Z3NetA.placeA`, `inf = 0`). (`g = 1`, `π = id`, `t = 1` gives these places themselves.) -/
def PGLImage {s : ℕ} [NeZero s] (inf : Fin s) (x : Fin s → ℚ) : Prop :=
  ∃ (g : Matrix (Fin 2) (Fin 2) ℚ) (π : Fin s ≃ Fin s) (t : Fin s → ℚ), g.det ≠ 0 ∧
    (∀ c, t c ≠ 0) ∧ ∀ c, homPt inf x c = t c • g *ᵥ homPt (0 : Fin s) Z3NetA.placeA (π c)

end Z3NetF
