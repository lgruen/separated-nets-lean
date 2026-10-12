/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAThm

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S3 (`thm:A`(1) and the lower bound of
`thm:A`(2) with `a*_s` abstract, `lem:sat`, `def:Ustar`, reachability, dominance)

The compared theorems of `scripts/v14_delta.py` (stage S3, `NEW`), restated by name with the same
statements as in `QUNets/Statements/ThmA.lean` and closed by `Z3Net/ThmASat.lean`,
`Z3Net/ThmAUstar.lean`, `Z3Net/ThmACover.lean` and `Z3Net/ThmAThm.lean`.
Generated from `scripts/v14_delta.py` (statement texts) with the proof terms of stage S3.
-/

namespace Z3NetA

open Matrix Finset Z3NetF

/-- **`thm:A`**, the reduction modulo `q`: for `s ≥ 3` and every `q ≥ 2` all of whose prime factors
are at least `s - 1` (`AdmBase s q`), there is a ring homomorphism `R_S = ℤ[1/(s-2)!] → ℤ/qℤ`, and
it is unique. (`Apoint` reduces the net of `def:Ns` over `R_S` by it.) -/
theorem A_hom (s q : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) :
    Nonempty (RS s →+* ZMod q) ∧ ∀ ψ ψ' : RS s →+* ZMod q, ψ = ψ' :=
  Proofs.A_hom_core hs hq

/-- **`thm:A`(1)**, the net: for every `s ≥ 3`, every `q ≥ 2` all of whose prime factors are at least
`s - 1` and every `k ≥ 1`, the net `𝒫^{U*_s}_{k,q}` (`Apoint`: the net of `def:Ns` for the places
`∞, 0, 1, …, s-2` and the design `U*_s` of `def:Ustar`, `N = q^(sk)` points) is a digital
`(0,sk,s)`-net over `ℤ/qℤ`; with `d = (k, …, k)` every cell `∏_i [n_i q^(-k), (n_i+1) q^(-k))`
holds exactly one point. -/
theorem A_net (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Apoint s q k) :=
  Proofs.A_net_core s q k hs hq

/-- **`thm:A`(1)**, the covering radius `h ≤ √s N^(-1/s)`: every `x ∈ [0,1]^s` has a point of
`𝒫^{U*_s}_{k,q}` at Euclidean distance at most `√s q^(-k) = √s N^(-1/s)` (`N = q^(sk)`). -/
theorem A_covering (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k)
    (x : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (s * k) → ZMod q,
      ∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.A_covering_core s q k hs hq x hx

/-- **`thm:A`(2)**, the lower bound, exact integer form: for `q ≥ 5 a*_s + 4` (and `q` as in (1)), every
`k ≥ 1` and distinct indices `v ≠ w`, with `N = q^(sk)` and `D² = torusDist2 N X(v) X(w)` (the squared
toroidal distance times `N²`): `q^(2(sk-k)) (q - a*_s)² ≤ q² D²`, i.e. `δ ≥ (1 - a*_s/q) N^(-1/s)`.
(`a*_s = aStar s` is the constant of `def:Ustar`; its bound is stage S5.) -/
theorem A_sep (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hqa : 5 * aStar s + 4 ≤ q)
    (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (Apoint s q k v) (Apoint s q k w) : ℤ) :=
  Proofs.A_sep_core s q k hs hq hqa hk v w hvw

/-- **`thm:A`(2)**, the lower bound, real toroidal form: for `q ≥ 5 a*_s + 4` and every `k ≥ 1`, the
toroidal distance between any two distinct points of `𝒫^{U*_s}_{k,q}` (points `X / N` in `[0,1)^s`,
`N = q^(sk)`) is at least `(1 - a*_s/q) N^(-1/s)`. -/
theorem A_sep_real (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.A_sep_real_core s q k hs hq hqa hk v w hvw

/-- **`thm:A`(2)**, the lower bound, Euclidean form ("hence also Euclidean"): for `q ≥ 5 a*_s + 4` and
every `k ≥ 1`, the Euclidean distance between any two distinct points of `𝒫^{U*_s}_{k,q}` is at least
`(1 - a*_s/q) N^(-1/s)`. -/
theorem A_sep_eucl (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.A_sep_eucl_core s q k hs hq hqa hk v w hvw

/-- **`thm:A`(1)**, the covering argument for any net: if the integer points `X v` (scale `N = q^(sk)`,
`q ≥ 2`, `s ≥ 1`) form a `(0,sk,s)`-net, so that every cell of side `q^(-k)` holds a point, every
`x ∈ [0,1]^s` is within Euclidean distance `√s q^(-k)` of a point. -/
theorem covering_of_net {s q k : ℕ} (hs : 1 ≤ s) (hq : 2 ≤ q)
    (X : (Fin (s * k) → ZMod q) → Fin s → ℕ) (hX : IsNet0 s q (s * k) X) (x : Fin s → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v, ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.covering_of_net_core hs hq X hX x hx

/-- **`thm:A`**, proof, reachability: every column of partial sums of `U*_s` is admissible: for every
column `d` and level `j ≤ s - 2`, `(M^(j)[c][d])_{c ≠ d}` (`0` at the row `d`) is admissible at level
`j` (`AdmCol`, i.e. `prop:F` with `λ' ≡ 1` over `R_S`; `lem:sat`(iii)). -/
theorem Ustar_adm {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    AdmCol d j (fun c => if c = d then 0 else Msum (UstarF s) j c d) :=
  Proofs.Ustar_adm_core hs d j hj

/-- **`thm:A`**, proof, reachability: over `R_S = ℤ[1/(s-2)!]` the places `∞, 0, 1, …, s-2` are
admissible (`PlacesOK`) and the residual problem of `U*_s` is solvable with `λ' ≡ 1` (by `prop:F`,
`F_poly_iff`). -/
theorem Ustar_reach {s : ℕ} [NeZero s] (hs : 3 ≤ s) :
    PlacesOK (0 : Fin s) (placeA : Fin s → RS s) ∧
      ∃ Ur : Fin s → ℕ → ℕ → RS s, Residual (0 : Fin s) placeA (UstarR s) 1 Ur :=
  Proofs.Ustar_reach_core hs

/-- **`thm:A`**, the data of the net `Apoint`: the chosen `U' = UrS s` solves the residual problem of
`U*_s` with `λ' ≡ 1`, and the chosen `β = betaS s` the defining relation of `prop:Gs`; so `Apoint` is
the net `𝒫^F_{k,q}` of `def:Ns` for `F = U*_s`. -/
theorem Ustar_data {s : ℕ} [NeZero s] (hs : 3 ≤ s) :
    Residual (0 : Fin s) placeA (UstarR s) 1 (UrS s) ∧
      BetaRel (0 : Fin s) placeA (UstarR s) 1 (betaS s) :=
  Proofs.Ustar_data_core hs

/-- **`lem:sat`(i)**: let `s ≥ 3`, `d` a column and `j ≤ s - 2`. The polynomial `g` of degree `≤ j`
of an integer column `E` (`E_c = w_c g(y_c)` for the rows `c ≠ d`; in particular for `E ∈ Λ_j`) has
all its coefficients in `R_S = ℤ[1/(s-2)!]`. -/
theorem sat_poly {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) (g : Polynomial ℚ) (hg : g.natDegree ≤ j)
    (hrep : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)) (i : ℕ) : InRS s (g.coeff i) :=
  Proofs.sat_poly_core hs d j hj E g hg hrep i

/-- **`lem:sat`(ii)**: `κ_j(Λ_j) = γ_j ℤ` for a positive `S`-unit `γ_j` (`gamS d j`), for every
column `d` and `j ≤ s - 2`. -/
theorem sat_gamma {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧ SUnit s (gamS d j) ∧
      ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j :=
  Proofs.sat_gamma_core hs d j hj

/-- **`lem:sat`(iii)**: an integer column is admissible at level `j` iff it lies in `Λ_j` and
`κ_j(E)` is an `S`-unit; in particular every `E ∈ Λ_j` with `κ_j(E) = γ_j` is admissible. -/
theorem sat_adm {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) :
    (AdmCol d j E ↔ InLam d j E ∧ SUnit s (kappa d j E)) ∧
      (InLam d j E → kappa d j E = gamS d j → AdmCol d j E) :=
  ⟨Proofs.sat_adm_core hs d j hj E, fun hE hk => (Proofs.sat_adm_core hs d j hj E).2
    ⟨hE, by rw [hk]; exact (Proofs.sat_gamma_core hs d j hj).2.1⟩⟩

/-- **`lem:sat`(iv)**, the basis: if `E_i ∈ Λ_i` and `κ_i(E_i) = γ_i` for `i = 0, …, j`
(`j ≤ s - 2`), then `E_0, …, E_j` is a basis of `Λ_j`: every element of `Λ_j` is a unique integer
combination of them, and every such combination lies in `Λ_j`. -/
theorem sat_basis {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ) (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) :
    (∀ F, InLam d j F ↔ ∃ t : ℕ → ℤ, F = ∑ i ∈ range (j + 1), t i • B i) ∧
      ∀ t t' : ℕ → ℤ, ∑ i ∈ range (j + 1), t i • B i = ∑ i ∈ range (j + 1), t' i • B i →
        ∀ i ≤ j, t i = t' i :=
  Proofs.sat_basis_core hs d j hj B hB

/-- **`lem:sat`(iv)**, the coset: under the hypotheses of `sat_basis`,
`{E ∈ Λ_j : κ_j(E) = γ_j} = E_j + Λ_{j-1}` with `Λ_{j-1} = ⊕_{i<j} ℤ E_i` (`Λ_{-1} = 0`). -/
theorem sat_coset {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ) (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i)
    (F : Fin s → ℤ) :
    (InLam d j F ∧ kappa d j F = gamS d j) ↔ ∃ t : ℕ → ℤ, F - B j = ∑ i ∈ range j, t i • B i :=
  Proofs.sat_coset_core hs d j hj B hB F

/-- **`def:Ustar`**, existence: for `s ≥ 3` and every column `d`, the columns `E_{d,j} = Ecol d j`
have the characterizing properties of `def:Ustar` (`IsUstarCols`): `E_{d,j} ∈ Λ_j`,
`κ_j(E_{d,j}) = +γ_j`, and the coefficients of the orthogonal projection of `E_{d,j}` onto the span of
`E_{d,0}, …, E_{d,j-1}` in these vectors lie in `[-1/2, 1/2)` (`j ≤ s - 2`). -/
theorem Ustar_cols {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) : IsUstarCols d (Ecol d) :=
  Proofs.Ustar_cols_core hs d

/-- **`def:Ustar`**, uniqueness: the family with these properties is unique. -/
theorem Ustar_cols_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ)
    (hB : IsUstarCols d B) : B = Ecol d :=
  Proofs.Ustar_cols_unique_core hs d B hB

/-- **`def:Ustar`**, independence of `v`: for every `v ∈ Λ_j` with `κ_j(v) = γ_j` (`j ≤ s - 2`) the
coefficients `c_i` of the orthogonal projection of `v` onto the span of `E_{d,0}, …, E_{d,j-1}` exist,
and for any such coefficients `E_{d,j} = v - ∑_{i<j} ⌊c_i + 1/2⌋ E_{d,i}` (the vector of `lem:babai`,
ties rounded up). -/
theorem Ustar_round {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (v : Fin s → ℤ) (hv : InLam d j v) (hvk : kappa d j v = gamS d j) :
    (∃ cf : ℕ → ℚ, ProjCoef (Ecol d) j v cf) ∧
      ∀ cf : ℕ → ℚ, ProjCoef (Ecol d) j v cf →
        Ecol d j = v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • Ecol d i :=
  ⟨Proofs.proj_exists hs d (Ecol d) j (by omega)
    (fun i _ => Proofs.Ecol_spec hs d i (by omega)) v,
    fun cf hcf => Proofs.Ustar_round_core hs d j hj v hv hvk cf hcf⟩

/-- **`def:Ustar`**: the design `U*_s` has the partial sums `M^(j)[c][d] = E_{d,j}[c]` (`c ≠ d`,
`j ≤ s - 2`). -/
theorem Ustar_Msum {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) (j : ℕ)
    (hj : j ≤ s - 2) : Msum (UstarF s) j c d = Ecol d j c :=
  Proofs.Ustar_Msum_core hs c d hcd j hj

/-- **`def:Ustar`** and the proof of `thm:A`(2): `U*_s` is diagonally dominant (`prop:D`) by
construction, with the maximum over all levels: `F_0[c][c] = -α_c`, the deeper diagonal vanishes,
`α_c = ∑_{d ≠ c} max_{j ≤ s-2} |M^(j)[c][d]|`, and `α_c ≤ a*_s = max_c α_c`. -/
theorem Ustar_dominant {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c : Fin s) :
    UstarF s 0 c c = -(alphaS c : ℤ) ∧ (∀ n, 1 ≤ n → UstarF s n c c = 0) ∧
      ∑ d ∈ univ.filter (fun d => d ≠ c),
          (range (s - 1)).sup (fun j => (Msum (UstarF s) j c d).natAbs) = alphaS c ∧
      alphaS c ≤ aStar s :=
  ⟨(Proofs.Ustar_diag_core c).1, (Proofs.Ustar_diag_core c).2,
    (Proofs.Ustar_dominant_core hs c).1, (Proofs.Ustar_dominant_core hs c).2⟩

/-- **`def:Ustar`**, the projection: for `j ≤ s - 2` the rational vectors of `V_j` (vanishing at the
row `d`, `E_c = w_c g(y_c)` for `c ≠ d` with `deg g ≤ j`) are exactly the rational combinations of
`E_{d,0}, …, E_{d,j}`; so the orthogonal projection onto `V_{j-1}` of `def:Ustar` is the projection
onto the span of `E_{d,0}, …, E_{d,j-1}` used in `IsUstarCols` and `ProjCoef`. -/
theorem Ustar_span {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℚ) :
    (E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧ ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) ↔
      ∃ u : ℕ → ℚ, E = ∑ i ∈ range (j + 1), u i • fun c => (Ecol d i c : ℚ) :=
  Proofs.Ustar_span_core hs d j hj E

end Z3NetA
