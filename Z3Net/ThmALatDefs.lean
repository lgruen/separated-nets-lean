/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmADefs

@[expose] public section

/-!
# Definitions: the lattice geometry of Theorem A (`lem:adelic`, `lem:babai`)

V14 stage S4. The notation of `Z3Net/ThmADefs.lean` (columns of index `d` are vectors
`Fin s → ℤ` with entry `0` at the row `d`; weights `wQ`, nodes `yQ`; `Λ_j` is `InLam`, `κ_j` is
`kappa`, `γ_j` is `gamS`). Real vectors live in `EuclideanSpace ℝ (Fin s)` (the standard inner
product of `ℝ^s`; the row `d` contributes `0`, so this is the paper's `ℝ^(s-1)`).

* `colE E`: an integer column as a vector of `ℝ^s`.
* `polyVecR d g`, `polyVecQ d g`: the vector `(w_c g(y_c))_{c ≠ d}` of a real or rational polynomial.
* `Vlt d J`: the real span of the vectors of the real polynomials of degree `< J`; so
  `V_j ⊗ ℝ = Vlt d (j+1)` and `V_{j-1} ⊗ ℝ = Vlt d j` (`V_{-1} = 0`).
* `lineA d j = V_j ∩ V_{j-1}^⊥` and `piA d j`, the orthogonal projection onto it (`π_j`).
* `AinfSet`, `Ainf` (`A_{j,∞}`), `ApSet`, `Ap` (`A_{j,p}`): the least size at a place of the vectors
  of the monic polynomials of degree `j` (`sec:lattice`, before `lem:adelic`).
* `primesS s` (the set `S` of primes `≤ s - 2`) and `hS d j = A_{j,∞} ∏_{p ∈ S} A_{j,p}` (`h_j`).
-/

namespace Z3NetA

open Finset Polynomial

/-- An integer column as a vector of `ℝ^s` (`EuclideanSpace`, standard inner product). -/
noncomputable def colE {s : ℕ} (E : Fin s → ℤ) : EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 fun c => (E c : ℝ)

/-- The vector `(w_c g(y_c))_{c ≠ d}` (entry `0` at the row `d`) of a real polynomial `g`
(column `d`). -/
noncomputable def polyVecR {s : ℕ} [NeZero s] (d : Fin s) (g : Polynomial ℝ) :
    EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 fun c => if c = d then 0 else (wQ c d : ℝ) * g.eval (yQ c d : ℝ)

/-- The vector `(w_c g(y_c))_{c ≠ d}` (entry `0` at the row `d`) of a rational polynomial `g`. -/
noncomputable def polyVecQ {s : ℕ} [NeZero s] (d : Fin s) (g : Polynomial ℚ) : Fin s → ℚ :=
  fun c => if c = d then 0 else wQ c d * g.eval (yQ c d)

/-- `Vlt d J`: the real span of the vectors `(w_c g(y_c))_c` of the real polynomials of degree
`< J` (column `d`). So `V_j ⊗ ℝ = Vlt d (j + 1)` and `V_{j-1} ⊗ ℝ = Vlt d j`, with `V_{-1} = 0`
(`sec:lattice`). -/
noncomputable def Vlt {s : ℕ} [NeZero s] (d : Fin s) (J : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin s)) :=
  Submodule.span ℝ {x | ∃ g : Polynomial ℝ, g.degree < J ∧ x = polyVecR d g}

/-- The line `V_j ∩ V_{j-1}^⊥` of `lem:adelic` (column `d`). -/
noncomputable def lineA {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin s)) :=
  Vlt d (j + 1) ⊓ (Vlt d j)ᗮ

/-- `π_j`: the orthogonal projection of `ℝ^s` onto the line `V_j ∩ V_{j-1}^⊥` (`lem:adelic`). -/
noncomputable def piA {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) :
    EuclideanSpace ℝ (Fin s) →L[ℝ] EuclideanSpace ℝ (Fin s) :=
  (lineA d j).starProjection

/-- The archimedean sizes `‖(w_c g(y_c))_c‖₂` of the monic real polynomials `g` of degree `j`
(column `d`); `A_{j,∞}` is their least element. -/
def AinfSet {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) : Set ℝ :=
  {r | ∃ g : Polynomial ℝ, g.Monic ∧ g.natDegree = j ∧ r = ‖polyVecR d g‖}

/-- `A_{j,∞} = min {‖E‖₂ : E ∈ V_j ⊗ ℝ, κ_j(E) = 1}` (column `d`), as the infimum of `AinfSet`
(`lem:adelic` proves the minimum is attained). -/
noncomputable def Ainf {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) : ℝ := sInf (AinfSet d j)

/-- The `p`-adic sizes `max_c |w_c g(y_c)|_p` of the monic rational polynomials `g` of degree `j`
(column `d`); `A_{j,p}` is their least element. -/
def ApSet {s : ℕ} [NeZero s] (p : ℕ) (d : Fin s) (j : ℕ) : Set ℝ :=
  {r | ∃ g : Polynomial ℚ, g.Monic ∧ g.natDegree = j ∧
    r = ⨆ c, ((padicNorm p (polyVecQ d g c) : ℚ) : ℝ)}

/-- `A_{j,p} = min {max_c |E_c|_p : E ∈ V_j, κ_j(E) = 1}` (column `d`), as the infimum of
`ApSet` (`lem:adelic` proves the minimum is attained). -/
noncomputable def Ap {s : ℕ} [NeZero s] (p : ℕ) (d : Fin s) (j : ℕ) : ℝ := sInf (ApSet p d j)

/-- The set `S` of primes `p ≤ s - 2` (`sec:lattice`). -/
def primesS (s : ℕ) : Finset ℕ := (range (s - 1)).filter Nat.Prime

/-- `h_j = A_{j,∞} ∏_{p ∈ S} A_{j,p}` (column `d`; `lem:adelic`). -/
noncomputable def hS {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) : ℝ :=
  Ainf d j * ∏ p ∈ primesS s, Ap p d j

end Z3NetA
