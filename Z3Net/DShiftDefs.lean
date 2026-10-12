/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDefs

@[expose] public section

/-!
# Definition: digital shifts (`def:dshift`), minimal form

V14 stage S9′. A minimal definition, added for `prop:colshift` and the `m = 3` constant of
`cor:allmshift`. Stage S10′ completes `def:dshift`: `dshiftCoord`, `dshiftPt` shift an arbitrary
point set at integer scale `q^m` (digits read off the integer coordinate); `digPointShift` is the
shift of a digital point set (`Z3NetF.Proofs.digPointShift_eq_dshiftPt`, `Z3Net/DShift.lean`).

`digPointShift q m C τ v`: the point with index `v` of the digitally shifted digital point set
`P ⊕ τ` (`def:dshift`): coordinate `c` has the digit vector `C_c v + τ_c ∈ (ℤ/qℤ)^m`, the digits of
the unshifted point added digit by digit modulo `q` without carries, read as the integer
`∑_j val((C_c v + τ_c)_j) q^(m-1-j)` (integer scale `q^m`, digit `0` most significant, as
`Z3NetF.digPoint`). For `τ = 0` it is `Z3NetF.digPoint q m C`.
-/

namespace Z3NetF

open Matrix

/-- **`def:dshift`**: coordinate `c` of the point with index `v` of the digitally shifted digital
point set `P ⊕ τ`, `P` with generator matrices `C`, `τ_c ∈ (ℤ/qℤ)^m` the shift of coordinate `c`:
the digits `C_c v + τ_c` (digit by digit modulo `q`, no carries), at integer scale `q^m`. -/
def digPointShift {s : ℕ} (q m : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (v : Fin m → ZMod q) : Fin s → ℕ :=
  fun c => ∑ j : Fin m, ((C c *ᵥ v + τ c) j).val * q ^ (m - 1 - (j : ℕ))

/-- The digit vector of a coordinate of a graph form with depth `K` (`sec:prelim`): the `K` cell digits
`a` followed by the `m - K` offset digits `b` (V14 stage S10′; used to split a digital shift
`τ_c = (τ^cell_c, τ^off_c)` as in `lem:shift`). -/
def cellOff {R : Type*} {m K : ℕ} (a : Fin K → R) (b : Fin (m - K) → R) : Fin m → R :=
  fun j => if h : (j : ℕ) < K then a ⟨j, h⟩ else b ⟨(j : ℕ) - K, by omega⟩

/-- **`def:dshift`** for an arbitrary point set, one coordinate (V14 stage S10′): a coordinate
`x ∈ [0, q^m)` at integer scale `q^m` has the digit vector `(⌊x/q^(m-1-j)⌋ mod q)_{j<m}` (digit `0`
most significant); the shifted coordinate has the digits `x_j + t_j` (modulo `q`, no carries). -/
def dshiftCoord (q m : ℕ) (t : Fin m → ZMod q) (x : ℕ) : ℕ :=
  ∑ j : Fin m, ((((x / q ^ (m - 1 - (j : ℕ))) % q : ℕ) : ZMod q) + t j).val * q ^ (m - 1 - (j : ℕ))

/-- **`def:dshift`** for an arbitrary point set (V14 stage S10′): the point `X ⊕ τ`, coordinate `c`
shifted by `τ_c ∈ (ℤ/qℤ)^m` (`dshiftCoord`). -/
def dshiftPt {s : ℕ} (q m : ℕ) (τ : Fin s → Fin m → ZMod q) (X : Fin s → ℕ) : Fin s → ℕ :=
  fun c => dshiftCoord q m (τ c) (X c)

end Z3NetF
