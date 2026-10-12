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
# Definitions: the lattice of admissible columns (`lem:sat`), the design `U*_s` (`def:Ustar`) and
the nets of Theorem A (`thm:A`)

V14 stage S3. Places `∞, 0, 1, …, n` with `n = s - 2`, in this coordinate order: coordinate `0` is
read at `∞`, coordinate `c ≥ 1` at the place `c - 1` (`placeA`; the `x` of the frame package of
`Z3Net/FDefs.lean` with `inf = 0`). Row scalars `λ' ≡ 1`. `R_S = ℤ[1/n!]` is
`Localization.Away n!` (`RS`); inside `ℚ` its elements are the `z / n!^e` (`InRS`) and its units the
`S`-units (`SUnit`), `S` the primes `≤ n`.

A column `E` of column index `d` is a vector `Fin s → ℤ` (or `ℚ`) whose entry at the row `d` is `0`
(the paper's column has the `s - 1` rows `c ≠ d`). The weights and nodes of column `d` are
`w_c = wN 0 placeA c d`, `y_c = yN 0 placeA c d` over `ℚ` (`prop:Ns`): `w_c = y_c = 1/(a_c - a_d)` for
finite `c, d`; `w = 1`, `y = 0` for `c = ∞`; `w = 1`, `y = a_c` for `d = ∞`.
-/

namespace Z3NetA

open Matrix Finset Z3NetF

/-! ## The ring `R_S = ℤ[1/n!]` and the places -/

/-- `R_S = ℤ[1/n!]`, `n = s - 2` (`sec:lattice`). -/
abbrev RS (s : ℕ) : Type := Localization.Away ((((s - 2).factorial : ℕ) : ℤ))

/-- The places of Theorem A: coordinate `0` is read at `∞` (its entry is not used), coordinate
`c ≥ 1` at the place `c - 1`; so the places are `∞, 0, 1, …, s-2` in the coordinate order. -/
def placeA {R : Type*} [CommRing R] {s : ℕ} (c : Fin s) : R := ((c : ℕ) : R) - 1

/-- `a ∈ ℤ[1/n!]` (as a rational number), `n = s - 2`: `a = z / n!^e` for some `z ∈ ℤ`, `e ∈ ℕ`. -/
def InRS (s : ℕ) (a : ℚ) : Prop :=
  ∃ (z : ℤ) (e : ℕ), a = (z : ℚ) / (((s - 2).factorial : ℕ) : ℚ) ^ e

/-- `a` is an `S`-unit (a unit of `ℤ[1/n!]`, i.e. `±` a product of powers of primes `≤ n`). -/
def SUnit (s : ℕ) (a : ℚ) : Prop := a ≠ 0 ∧ InRS s a ∧ InRS s a⁻¹

/-- The admissible bases of Theorem A: `q ≥ 2` and every prime factor of `q` is at least `s - 1`. -/
def AdmBase (s q : ℕ) : Prop := 2 ≤ q ∧ ∀ p : ℕ, p.Prime → p ∣ q → s - 1 ≤ p

/-! ## Columns, `V_j`, `Λ_j`, `κ_j` (`sec:lattice`) -/

/-- The weight `w_c = w_cd` of row `c` in column `d`, over `ℚ` (`prop:Ns`). -/
noncomputable def wQ {s : ℕ} [NeZero s] (c d : Fin s) : ℚ := wN (0 : Fin s) placeA c d

/-- The node `y_c = y_cd` of row `c` in column `d`, over `ℚ` (`prop:Ns`). -/
noncomputable def yQ {s : ℕ} [NeZero s] (c d : Fin s) : ℚ := yN (0 : Fin s) placeA c d

/-- The polynomial of a column `E` of column `d`: the Lagrange interpolant of degree `≤ s - 2`
of the values `E_c / w_c` at the `s - 1` distinct nodes `y_c`, `c ≠ d`; for `E ∈ V_j` it is the
unique `g` with `E_c = w_c g(y_c)` (`colPoly_eq`). -/
noncomputable def colPoly {s : ℕ} [NeZero s] (d : Fin s) (E : Fin s → ℚ) : Polynomial ℚ :=
  Lagrange.interpolate (univ.filter fun c => c ≠ d) (fun c => yQ c d) (fun c => E c / wQ c d)

/-- `E ∈ Λ_j = V_j ∩ ℤ^(s-1)` (column `d`): `E` vanishes at the row `d`, and
`E_c = w_c g(y_c)` for every `c ≠ d` and a rational polynomial `g` of degree `≤ j`. -/
def InLam {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : Prop :=
  E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧ ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)

/-- `κ_j(E)`: the coefficient of `X^j` in the polynomial of `E`. -/
noncomputable def kappa {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : ℚ :=
  (colPoly d fun c => (E c : ℚ)).coeff j

open Classical in
/-- `γ_j` (column `d`): the positive generator of `κ_j(Λ_j) = γ_j ℤ` (`lem:sat`(ii) proves that
it exists; the junk value `0` is never used). -/
noncomputable def gamS {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) : ℚ :=
  if h : ∃ γ : ℚ, 0 < γ ∧ ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ
  then Classical.choose h else 0

/-- A column is **admissible** at level `j` (`sec:lattice`; `prop:F` with `λ' ≡ 1` over `R_S`):
it vanishes at the row `d`, and `E_c = w_c g(y_c)` (`c ≠ d`) for a polynomial `g` of degree `j`
with coefficients in `R_S` and an `S`-unit leading coefficient. -/
def AdmCol {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : Prop :=
  E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree = j ∧ (∀ i, InRS s (g.coeff i)) ∧
    SUnit s g.leadingCoeff ∧ ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)

/-! ## The design `U*_s` (`def:Ustar`) -/

/-- `cf` are the coefficients of the orthogonal projection of `E` onto the span of
`B 0, …, B (j-1)` (Euclidean inner product of `ℝ^s ⊇ ℚ^s`), in these vectors:
`E - ∑_{l<j} cf_l B_l` is orthogonal to every `B_i`, `i < j`. -/
def ProjCoef {s : ℕ} (B : ℕ → Fin s → ℤ) (j : ℕ) (E : Fin s → ℤ) (cf : ℕ → ℚ) : Prop :=
  ∀ i < j, ∑ c, ((E c : ℚ) - ∑ l ∈ range j, cf l * (B l c : ℚ)) * (B i c : ℚ) = 0

/-- The characterization of `def:Ustar` for column `d`: for `j ≤ s - 2`, `B j = E_{d,j}` is in
`Λ_j`, has `κ_j = +γ_j`, and its orthogonal projection onto the span of `B 0, …, B (j-1)` has all
its coefficients in these vectors in `[-1/2, 1/2)` (for `j = 0` the generator of `Λ_0` with
`κ_0 > 0`); `B j = 0` for `j > s - 2`. -/
def IsUstarCols {s : ℕ} [NeZero s] (d : Fin s) (B : ℕ → Fin s → ℤ) : Prop :=
  (∀ j, j ≤ s - 2 → InLam d j (B j) ∧ kappa d j (B j) = gamS d j ∧
    ∃ cf : ℕ → ℚ, ProjCoef B j (B j) cf ∧ ∀ i < j, -1 / 2 ≤ cf i ∧ cf i < 1 / 2) ∧
  ∀ j, s - 2 < j → B j = 0

/-- The columns `E_{d,0}, …, E_{d,s-2}` of `def:Ustar` (the unique family with `IsUstarCols`,
`Ustar_cols_unique`). -/
noncomputable def Ecol {s : ℕ} [NeZero s] (d : Fin s) : ℕ → Fin s → ℤ :=
  Classical.epsilon (IsUstarCols d)

/-- `α_c = ∑_{d ≠ c} max_{j ≤ s-2} |E_{d,j}[c]|` (`def:Ustar`). -/
noncomputable def alphaS {s : ℕ} [NeZero s] (c : Fin s) : ℕ :=
  ∑ d ∈ univ.filter (fun d => d ≠ c), (range (s - 1)).sup fun j => (Ecol d j c).natAbs

/-- `a*_s = max_c α_c` (`def:Ustar`). -/
noncomputable def aStar (s : ℕ) [NeZero s] : ℕ := univ.sup fun c : Fin s => alphaS c

/-- The design `U*_s = (F_0, …, F_{s-2})` (`def:Ustar`): off the diagonal the partial sums are
`M^(j)[c][d] = E_{d,j}[c]`, i.e. `F_0[c][d] = E_{d,0}[c]` and `F_n[c][d] = E_{d,n}[c] - E_{d,n-1}[c]`
(`1 ≤ n ≤ s-2`); the level-`0` diagonal is `F_0[c][c] = -α_c`, the deeper diagonal is `0`, and
`F_n = 0` for `n ≥ s - 1`. -/
noncomputable def UstarF (s : ℕ) [NeZero s] (n : ℕ) (c d : Fin s) : ℤ :=
  if c = d then (if n = 0 then -(alphaS c : ℤ) else 0)
  else if s - 1 ≤ n then 0
  else if n = 0 then Ecol d 0 c else Ecol d n c - Ecol d (n - 1) c

/-! ## The nets `𝒫^{U*_s}_{k,q}` (`def:Ns`, `thm:A`) -/

/-- `U*_s` over `R_S`. -/
noncomputable def UstarR (s : ℕ) [NeZero s] : ℕ → Fin s → Fin s → RS s :=
  fun n c d => (UstarF s n c d : RS s)

/-- A solution `U'` of the residual problem of `U*_s` over `R_S` with `λ' ≡ 1` (it exists,
`Ustar_reach`). -/
noncomputable def UrS (s : ℕ) [NeZero s] : Fin s → ℕ → ℕ → RS s :=
  Classical.epsilon fun Ur => Residual (0 : Fin s) placeA (UstarR s) 1 Ur

/-- The coefficients `β` of `prop:Gs` for `U*_s` (they exist, `Ustar_data`). -/
noncomputable def betaS (s : ℕ) [NeZero s] : Fin s → ℕ → ℕ → RS s :=
  Classical.epsilon fun β => BetaRel (0 : Fin s) placeA (UstarR s) 1 β

open Classical in
/-- The integer point (in `[0, q^(sk))^s`, `N = q^(sk)`) with index `v` of the net
`𝒫^{U*_s}_{k,q}` of `thm:A`: the net `𝒫^F_k` of `def:Ns` over `R_S` (`PGen`, places
`∞, 0, …, s-2`, design `U*_s`, `λ' ≡ 1`, `U' = UrS`, `β = betaS`) reduced modulo `q` by a ring
homomorphism `R_S → ℤ/qℤ` (it exists iff `gcd(q, (s-2)!) = 1`, and is then unique; the junk value
`0` is used otherwise). -/
noncomputable def Apoint (s q k : ℕ) [NeZero s] (v : Fin (s * k) → ZMod q) : Fin s → ℕ :=
  if h : Nonempty (RS s →+* ZMod q) then
    let ψ : RS s →+* ZMod q := Classical.choice h
    digPoint q (s * k) (fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c).map ψ) v
  else 0

end Z3NetA
