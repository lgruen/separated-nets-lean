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
# Definitions: the design of `prop:4D2` (dimension four, deficit two)

V14 stage S8. The design `F = (F_0, F_1, F_2)` of `app:designs` ("The designs of Table
`tab:Kdesigns`", `s = 4`) on the places `∞, 0, 1, 2` with `λ' ≡ 1`, and the nets `𝒫^F_{k,q}` of
`def:Ns` built from it, as for `U*_s` in Theorem A (`Z3NetA.Apoint`):

* `F4D2 n c d`: `F_n[c][d]` for `n = 0, 1, 2` (row `c`, column `d`, coordinates in the order of the
  places `∞, 0, 1, 2`; diagonal included), `0` for `n ≥ 3`.
* `F4D2R`: the design over `R' = ℤ[1/2]`, which is `Z3NetA.RS 4 = ℤ[1/(4-2)!]`.
* `Ur4D2`, `beta4D2`: a solution `U'` of the residual problem (`sec:frames`) with `λ' ≡ 1` over
  `ℤ[1/2]` and the coefficients `β` of `prop:Gs` (chosen; they exist, `Z3Net/D4D2.lean`, and the net
  does not depend on the choice, `Z3NetF.PGen_indep`).
* `P4D2 q k v`: the integer point with index `v` (in `[0, q^(4k))^4`, `N = q^(4k)`) of
  `𝒫^F_{k,q}`: the net of `def:Ns` over `ℤ[1/2]` (`PGen`, places `Z3NetA.placeA`, coordinate `0` at
  `∞`), reduced modulo `q` by the ring homomorphism `ℤ[1/2] → ℤ/qℤ` (it exists iff `q` is odd, and
  is then unique; the junk value `0` is used otherwise).
-/

namespace Z3NetF

open Finset Z3NetA

/-- The design of `prop:4D2` as printed in `app:designs`: `F_n[c][d]` for `n = 0, 1, 2` (row `c`,
column `d`, coordinates in the order of the places `∞, 0, 1, 2`, diagonal included), `0` for
`n ≥ 3`. -/
def F4D2 (n : ℕ) : Fin 4 → Fin 4 → ℤ :=
  if n = 0 then !![-2, -2, -1, -2; 1, -2, 1, 1; 1, -2, -2, 2; 1, -1, -1, -1]
  else if n = 1 then !![0, 3, 1, 1; 0, 1, -2, -1; -1, 1, 0, -3; -2, 1, 0, 0]
  else if n = 2 then !![0, -2, -1, 0; 0, 0, 1, -1; 0, 0, 0, 0; 1, 0, 1, 0]
  else 0

/-- The design of `prop:4D2` over `R' = ℤ[1/2]` (`= Z3NetA.RS 4`). -/
noncomputable def F4D2R : ℕ → Fin 4 → Fin 4 → RS 4 := fun n c d => (F4D2 n c d : RS 4)

/-- A solution `U'` of the residual problem of the design of `prop:4D2` over `ℤ[1/2]` with
`λ' ≡ 1` (it exists: `Z3Net/D4D2.lean`). -/
noncomputable def Ur4D2 : Fin 4 → ℕ → ℕ → RS 4 :=
  Classical.epsilon fun Ur => Residual (0 : Fin 4) placeA F4D2R 1 Ur

/-- The coefficients `β` of `prop:Gs` for the design of `prop:4D2` (they exist). -/
noncomputable def beta4D2 : Fin 4 → ℕ → ℕ → RS 4 :=
  Classical.epsilon fun β => BetaRel (0 : Fin 4) placeA F4D2R 1 β

open Classical in
/-- The integer point (in `[0, q^(4k))^4`, `N = q^(4k)`) with index `v` of the net `𝒫^F_{k,q}` of
`prop:4D2`: the net `𝒫^F_k` of `def:Ns` over `ℤ[1/2]` (`PGen`, places `∞, 0, 1, 2`, `λ' ≡ 1`,
`U' = Ur4D2`, `β = beta4D2`) reduced modulo `q` by a ring homomorphism `ℤ[1/2] → ℤ/qℤ` (it exists
iff `q` is odd, and is then unique; the junk value `0` is used otherwise). -/
noncomputable def P4D2 (q k : ℕ) (v : Fin (4 * k) → ZMod q) : Fin 4 → ℕ :=
  if h : Nonempty (RS 4 →+* ZMod q) then
    let ψ : RS 4 →+* ZMod q := Classical.choice h
    digPoint q (4 * k) (fun c => (PGen k (0 : Fin 4) placeA F4D2R 1 Ur4D2 beta4D2 c).map ψ) v
  else 0

end Z3NetF
