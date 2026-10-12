/-
Development copy (Solution side) of the graph-form definitions of `ChallengeWhyLat.lean` (entry
WhyLat, `cor:linoff` (c) and `lem:phase` (ii), `paper/core.tex`). Keep in sync with
`ChallengeWhyLat.lean` (verbatim, same order).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.WLDefs

@[expose] public section

namespace Z3NetF

/-- The points (integer scale `q^{sk}`) of the graph form `Φ` with depths `(k, …, k)` over
`ℤ/qℤ`: `X(v) = digPoint (graphGenK (k, …, k) Φ) v`, `v` the vector of cell digits. -/
def gfPt (q s k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (v : Fin (s * k) → ZMod q) : Fin s → ℕ :=
  digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) v

/-- The cell `⌊x / q^a⌋` of a coordinate `x` with `a` offset digits. -/
def cellPart (q a x : ℕ) : ℕ := x / q ^ a

/-- The geometric digit (the first offset digit) `⌊(x mod q^a) / q^(a−1)⌋`. -/
def geoPart (q a x : ℕ) : ℕ := x % q ^ a / q ^ (a - 1)

/-- The contribution `x mod q^(a−1)` of the deeper digits (the jitter, `f = deep / q^(a−1)`). -/
def deepPart (q a x : ℕ) : ℕ := x % q ^ (a - 1)

end Z3NetF
