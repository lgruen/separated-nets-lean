/-
Development copy (Solution side) of the new definitions of `ChallengeWhyLat.lean` (entry WhyLat,
`sec:whylat` of `paper/core.tex`: `lem:hom`, `cor:linoff`, `lem:phase`, `prop:cube`).
Keep in sync with `ChallengeWhyLat.lean` (verbatim, same order); the graph-form definitions
`coord`, `digPoint`, `IsNet0`, `boxLoc`, `graphGenK` come from `Z3Net.FDefs` (entry F).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDefs

@[expose] public section

namespace Z3NetF

open Matrix

/-! ## `lem:hom` -/

/-- Digit `i` (counted from the least significant one) of `P ∈ ℤ/q^jℤ`, read from the
representative `P.val ∈ [0, q^j)`: `⌊P.val / q^i⌋ mod q`. -/
def digitAt (q j : ℕ) (P : ZMod (q ^ j)) (i : ℕ) : ZMod q := ((P.val / q ^ i : ℕ) : ZMod q)

/-- The digit functional `φ(P) = ∑_{i<j} β_i d_i(P)` of `lem:hom`. -/
def phiDig (q j : ℕ) (β : Fin j → ZMod q) (P : ZMod (q ^ j)) : ZMod q :=
  ∑ i : Fin j, β i * digitAt q j P i

/-! ## `cor:linoff` -/

/-- Reduction of an integer vector modulo `q` (its lowest base-`q` digits). -/
def modVec (q : ℕ) {s : ℕ} (Y : Fin s → ℤ) : Fin s → ZMod q := fun c => ((Y c : ℤ) : ZMod q)

/-- The representative in `[0, q)^s` of a vector over `ℤ/qℤ`, as an integer vector. -/
def liftVec (q : ℕ) {s : ℕ} (v : Fin s → ZMod q) : Fin s → ℤ := fun c => ((v c).val : ℤ)

/-- `T_B = {qℓ + (Bℓ mod q) : ℓ ∈ {0,…,q−1}^s} ⊂ (ℤ/q²ℤ)^s` (`cor:linoff` (b)). -/
def TB (q : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q)) : Set (Fin s → ZMod (q ^ 2)) :=
  Set.range fun ℓ : Fin s → ZMod q =>
    fun i => ((q * (ℓ i).val + ((B *ᵥ ℓ) i).val : ℕ) : ZMod (q ^ 2))

/-- The carry vector `(⌊(v_i + v'_i)/q⌋)_i` of two digit vectors. -/
def carryVec (q : ℕ) {s : ℕ} (v v' : Fin s → ℕ) : Fin s → ℕ := fun i => (v i + v' i) / q

/-! ## `lem:phase` -/

/-- The geometric digit `r_c(n) = (Bn)_c ∈ [0, p)` of the cell `n` (depths `(1, …, 1)`). -/
def geoR (p : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod p)) (n : Fin s → ZMod p) (c : Fin s) :
    ℕ :=
  ((B *ᵥ n) c).val

/-- `β = BE mod p ∈ [0, p)^s` for an integer step `E`. -/
def betaE (p : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod p)) (E : Fin s → ℤ) (c : Fin s) : ℕ :=
  ((B *ᵥ fun i => ((E i : ℤ) : ZMod p)) c).val

/-- The wrap indicator `κ_c = [r_c(n) + β_c ≥ p]`. -/
def wrapK (p : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod p)) (n : Fin s → ZMod p)
    (E : Fin s → ℤ) (c : Fin s) : ℕ :=
  if p ≤ geoR p B n c + betaE p B E c then 1 else 0

/-! ## `prop:cube` -/

/-- `S ⊂ ℝ^s` has exactly one point in every unit cube `n + [0,1)^s`, `n ∈ ℤ^s`. -/
def OnePerCube {s : ℕ} (S : Set (Fin s → ℝ)) : Prop :=
  ∀ n : Fin s → ℤ, ∃! σ : Fin s → ℝ, σ ∈ S ∧ ∀ c, (n c : ℝ) ≤ σ c ∧ σ c < n c + 1

/-- The translates `τ + [0,1)^s`, `τ ∈ T`, tile `ℝ^s`: every point lies in exactly one. -/
def IsCubeTiling {s : ℕ} (T : Set (Fin s → ℝ)) : Prop :=
  ∀ x : Fin s → ℝ, ∃! τ : Fin s → ℝ, τ ∈ T ∧ ∀ c, τ c ≤ x c ∧ x c < τ c + 1

/-- The unit vector `e_c`. -/
def unitVec {s : ℕ} (c : Fin s) : Fin s → ℝ := Pi.single c 1

/-- Hajós's theorem (Minkowski's conjecture) in dimension `s`: in a lattice tiling of `ℝ^s` by
unit cubes two cubes share a facet, i.e. the lattice contains a unit vector `e_c`.  Not proved
here; used as an explicit hypothesis. -/
def HajosProp (s : ℕ) : Prop :=
  ∀ L : AddSubgroup (Fin s → ℝ), IsCubeTiling (L : Set (Fin s → ℝ)) → ∃ c, unitVec c ∈ L

/-- Keller's property in dimension `s`: in every tiling of `ℝ^s` by translates of the unit cube
two cubes share a complete facet, i.e. two translation vectors differ by a unit vector `e_c`
(true for `s ≤ 7`: Perron for `s ≤ 6`, Brakensiek–Heule–Mackey–Narváez for `s = 7`).  Not
proved here; used as an explicit hypothesis. -/
def KellerProp (s : ℕ) : Prop :=
  ∀ T : Set (Fin s → ℝ), IsCubeTiling T → ∃ τ ∈ T, ∃ c, τ + unitVec c ∈ T

/-- `ℤ^s + Π`. -/
def intPlus {s : ℕ} (P : Set (Fin s → ℝ)) : Set (Fin s → ℝ) :=
  {y | ∃ n : Fin s → ℤ, ∃ π ∈ P, y = (fun c => (n c : ℝ)) + π}

/-- The minimum distance `μ(S)` (the infimum of the Euclidean distances of distinct points). -/
noncomputable def minDist {s : ℕ} (S : Set (Fin s → ℝ)) : ℝ :=
  sInf {d : ℝ | ∃ σ ∈ S, ∃ σ' ∈ S, σ ≠ σ' ∧ d = Real.sqrt (∑ c, (σ c - σ' c) ^ 2)}

end Z3NetF
