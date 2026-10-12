/-
Copyright (c) 2026 Leonhard Gruenschloss. Released under the MIT license.
Author: Leonhard Gruenschloss.
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(revision 14.3), Theorem `thm:A` (results cited by `\label`, never by number).
The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude)
under the author's direction; responsibility rests with the author.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Mathlib

@[expose] public section

/-!
# Low-discrepancy quasi-uniform digital nets in every dimension (Theorem A)

**Theorem A** (`thm:A`). Let `s ≥ 3`, let `q ≥ 2` be an integer all of whose prime factors are at
least `s - 1`, and let `k ≥ 1`. Let `𝒫^{U*_s}_{k,q}` be the digital net over `ℤ/qℤ` of `def:Ns` for
the places `∞, 0, 1, …, s-2` and the design `U*_s` of `def:Ustar`, with `N = q^(sk)` points. Then:
1. `𝒫^{U*_s}_{k,q}` is a digital `(0,sk,s)`-net over `ℤ/qℤ`, every cell
   `∏_i [n_i q^(-k), (n_i+1) q^(-k))` holds exactly one point, and `h ≤ √s N^(-1/s)`;
2. if `q ≥ 5a*_s + 4`, its toroidal (hence also Euclidean) minimum distance satisfies
   `δ ≥ (1 - a*_s/q) N^(-1/s)`, for every `k ≥ 1`; for `k ≥ 2` the constant `a*_s` is first-order
   sharp for this net: `δ N^(1/s) = 1 - a*_s/q + O(q⁻²)` as `q → ∞`.

Here `a*_3 = 2`, and `a*_s ≤ 2(s-1)^(3/2) (3/2)^(s-2) (s-2)! = e^(s log s + O(s))` for `s ≥ 4`.

The formal statement is `Z3NetA.theoremA` near the end of this file. Everything it uses is defined
below, explicitly, in two parts:

* `Z3NetF` (the frame machinery of `sec:prelim` and `sec:frames`): digital point sets over `ℤ/qℤ`,
  the `(0,m,s)`-net property, the toroidal residue, graph forms, the readings of one polynomial at
  `s` places (the Faure–Hammersley frame), its graph form `Φ^F`, the gauges of `prop:Ns` and
  `prop:Gs`, and the net `𝒫^F_k` of `def:Ns` over any commutative ring.
* `Z3NetA` (`sec:lattice`, `sec:Ustar`): the places `∞, 0, …, s-2`, the ring `R_S = ℤ[1/(s-2)!]`,
  the lattices `Λ_j`, the functionals `κ_j` and their generators `γ_j`, the columns `E_{d,j}` of
  `def:Ustar` through their defining characterization, `α_c`, `a*_s`, the design `U*_s`, and the
  net `𝒫^{U*_s}_{k,q}` (`Apoint`).

**Reading the statement.** The point of index `v ∈ (ℤ/qℤ)^(sk)` is `Apoint s q k v / N ∈ [0,1)^s`
(`Apoint` gives the integer coordinates in `[0, N)`). `N^(-1/s)` is written
`((q : ℝ) ^ (s * k)) ^ (-(1 / s))` (`Real.rpow`; it equals `q^(-k)`). The toroidal distance of
two points `X/N`, `Y/N` is `√(∑_c (cres N (X_c - Y_c) / N)²)`, `cres N u` the distance from `u` to
`Nℤ`; the Euclidean one is `√(∑_c ((X_c - Y_c) / N)²)`. The covering radius `h` and the minimum
distance `δ` are not defined as a supremum and a minimum: the statement says "every `x` has a point
within …", "every pair of distinct points is at least …", and "some pair of distinct points is
closer than …".

**Choices that are not visible in the paper's wording.** Three further compared theorems, after
`theoremA`, show inside this entry that the data introduced by choice are the paper's:
* `E_{d,j}` (`Ecol`) and `γ_j` (`gamS`) are introduced by `Classical.epsilon`/`Classical.choose`
  from their defining properties. `Z3NetA.ustarCols_spec`: `Ecol d` has the properties of
  `def:Ustar` and is the only family that has them. `Z3NetA.gamma_spec`: `gamS d j` is a positive
  rational with `κ_j(Λ_j) = γ_j ℤ` (`lem:sat`(ii)), and the only one.
* The paper's net is defined over `R' = R_S` and then "reduced modulo `q`"; it also leaves the
  solution `U'` of the residual problem and the coefficients `β` of `prop:Gs` implicit. Here `U'`
  and `β` are fixed by choice (`UrS`, `betaS`) and the reduction is a chosen ring homomorphism
  `R_S → ℤ/qℤ`. `Z3NetA.net_wellDefined`: for admissible `q` such a homomorphism, such a `U'` and
  such a `β` exist, and the net built from **any** of them is `Apoint s q k`.
* The sharpness clause is stated with an explicit threshold `q > (s-1) a*_s` and the explicit
  constant `(s-1)(a*_s + 1)²` of the `O(q⁻²)`; the bound `e^(s log s + O(s))` with the explicit
  constant `3`, for every `s ≥ 4`.
* "Optimal order" (the volume bounds `δ = O(N^(-1/s))`, `h = Ω(N^(-1/s))` for every `N`-point set)
  is classical and not part of this statement; neither is the polynomial running time of
  `def:Ustar` nor the computed values `a*_4, …, a*_10` of `tab:astar`.
-/

namespace Z3NetF

open Matrix Finset

/-! ## Digital point sets over `ℤ/qℤ` (`sec:prelim`, `sec:conv`) -/

/-- Integer coordinate of the digital point with generator matrix `C` and index `v`:
`∑_j val((C v)_j) q^(m-1-j) ∈ [0, q^m)`, digit `0` the most significant. -/
def coord (q m : ℕ) (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) : ℕ :=
  ∑ j : Fin m, ((C *ᵥ v) j).val * q ^ (m - 1 - (j : ℕ))

/-- The integer point `(coord q m (C c) v)_c ∈ [0, q^m)^s` of the digital point set with
generator matrices `C c`; the point itself is this vector divided by `q^m`. -/
def digPoint {s : ℕ} (q m : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (v : Fin m → ZMod q) : Fin s → ℕ :=
  fun c => coord q m (C c) v

/-- The `(0,m,s)`-net property in base `q`: for every depth vector `d` with `∑_c d_c = m`, every
elementary box `∏_c [a_c q^(-d_c), (a_c+1) q^(-d_c))` holds exactly one point `X v / q^m`. With
`d = (k, …, k)` (`m = sk`) these boxes are the cells of `thm:A`(1). -/
def IsNet0 (s q m : ℕ) (X : (Fin m → ZMod q) → Fin s → ℕ) : Prop :=
  ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ a : Fin s → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : Fin m → ZMod q, ∀ c, X v c / q ^ (m - d c) = a c

/-- Distance from the integer `u` to `N ℤ` (the toroidal residue; adapted from Rudolph's
`GKEvenNet.cres`, MIT). -/
def cres (N : ℕ) (u : ℤ) : ℕ :=
  min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat)

/-! ## The frame of `s` places (`sec:frames`, `lem:Ts`) -/

/-- The reading at a finite place `x` (`sec:frames`): digit `i` of `V = ∑_l v_l t^l` is
`[(t - x)^i] V = ∑_l C(l, i) x^(l-i) v_l`. -/
def readAt {R : Type*} [CommRing R] (m : ℕ) (x : R) : Matrix (Fin m) (Fin m) R :=
  fun i l => (((l : ℕ).choose (i : ℕ) : ℕ) : R) * x ^ ((l : ℕ) - (i : ℕ))

/-- The reading at `∞` (`sec:frames`): digit `i` of `V` is `[t^(m-1-i)] V`. -/
def readInf {R : Type*} [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i l => if (l : ℕ) + (i : ℕ) + 1 = m then 1 else 0

/-- The frame of `s` places (the Faure–Hammersley frame): coordinate `inf` is read at `∞`,
every other coordinate `c` at the finite place `x c`. -/
def frameRead {R : Type*} [CommRing R] {s : ℕ} (m : ℕ) (inf : Fin s) (x : Fin s → R)
    (c : Fin s) : Matrix (Fin m) (Fin m) R :=
  if c = inf then readInf m else readAt m (x c)

/-- Owner of row `r` of a stacked matrix with block sizes `ds`: (block, row inside the block),
blocks numbered from `c`. -/
def boxLoc : List ℕ → ℕ → ℕ → ℕ × ℕ
  | [], c, r => (c, r)
  | x :: xs, c, r => if r < x then (c, r) else boxLoc xs (c + 1) (r - x)

/-- The box matrix for the depths `d` (`lem:nie`): the first `d 0` rows of `C 0`, then the first
`d 1` rows of `C 1`, … -/
def boxMatrix {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) : Matrix (Fin m) (Fin m) R :=
  fun r l =>
    if h : (boxLoc (List.ofFn d) 0 r).1 < s ∧ (boxLoc (List.ofFn d) 0 r).2 < m then
      C ⟨(boxLoc (List.ofFn d) 0 r).1, h.1⟩ ⟨(boxLoc (List.ofFn d) 0 r).2, h.2⟩ l
    else 0

/-- The generator matrix of coordinate `c` of the graph form `Φ` with depths `K` (`sec:prelim`,
"Graph forms"): the index is the vector of cells `n_d ∈ R^(K d)`, stacked in coordinate order.
Row `i < K c` is the unit row of level `i` of the own cell `n_c`; row `K c + r` is the offset row
`∑_d Φ_cd[r, ·] n_d`. -/
def graphGenK {R : Type*} [Zero R] [One R] {s m : ℕ} (K : Fin s → ℕ)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) :
    Matrix (Fin m) (Fin m) R :=
  fun i j =>
    if hb : (boxLoc (List.ofFn K) 0 j).1 < s then
      if hl : (boxLoc (List.ofFn K) 0 j).2 < K ⟨(boxLoc (List.ofFn K) 0 j).1, hb⟩ then
        if hi : (i : ℕ) < K c then
          (if (boxLoc (List.ofFn K) 0 j).1 = (c : ℕ) ∧ (boxLoc (List.ofFn K) 0 j).2 = (i : ℕ)
            then 1 else 0)
        else Φ c ⟨(boxLoc (List.ofFn K) 0 j).1, hb⟩
          ⟨(i : ℕ) - K c, Nat.sub_lt_sub_right (Nat.le_of_not_lt hi) i.isLt⟩
          ⟨(boxLoc (List.ofFn K) 0 j).2, hl⟩
      else 0
    else 0

/-- The graph form `Φ^F` of the frame with depths `(k, …, k)` (`sec:frames`): `Φ^F_cd[r, l]` is
entry `(k + r, d k + l)` of `C^F_c G⁻¹`, `G` the `(k, …, k)` box matrix of the frame (a unit by
`lem:Ts` when the differences of the finite places are units). -/
noncomputable def frameGraph (R : Type*) [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s)
    (x : Fin s → R) (c d : Fin s) : Matrix (Fin (s * k - k)) (Fin k) R :=
  fun r l => (frameRead (s * k) inf x c * (boxMatrix (frameRead (s * k) inf x) (fun _ => k))⁻¹)
    ⟨k + (r : ℕ), Nat.add_lt_of_lt_sub' r.isLt⟩
    ⟨(d : ℕ) * k + (l : ℕ), Nat.lt_of_lt_of_le (Nat.add_lt_add_left l.isLt ((d : ℕ) * k))
      ((Nat.succ_mul (d : ℕ) k).symm.trans_le (Nat.mul_le_mul_right k d.isLt))⟩

/-! ## The normal form and the all-`k` gauge (`prop:Ns`, `prop:Gs`) -/

/-- `Q_c = ∏_{b finite, b ≠ c} (a_c - a_b)`, `Q_∞ = 1` (`sec:frames`). -/
def Qf {R : Type*} [CommRing R] {s : ℕ} (inf : Fin s) (x : Fin s → R) (c : Fin s) : R :=
  if c = inf then 1 else ∏ b ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ c), (x c - x b)

/-- The series of the Toeplitz column gauge `U^0_d` of `prop:Ns`: `Π_d(d + x) = ∏_{b finite, b ≠ d}
(a_d - a_b + x)^k` for finite `d`, and `∏_{b finite} (1 - a_b x)^k` for `d = ∞`. -/
noncomputable def uN {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
    (d : Fin s) : Polynomial R :=
  if d = inf then ∏ b ∈ univ.filter (fun b => b ≠ inf), (1 - Polynomial.C (x b) * Polynomial.X) ^ k
  else ∏ b ∈ univ.filter (fun b => b ≠ inf ∧ b ≠ d),
    (Polynomial.C (x d - x b) + Polynomial.X) ^ k

/-- `w_cd` of `prop:Ns`: `1/(a_c - a_d)` for finite `c, d`; `1` if `c = ∞` or `d = ∞`. -/
noncomputable def wN {R : Type*} [CommRing R] {s : ℕ} (inf : Fin s) (x : Fin s → R)
    (c d : Fin s) : R :=
  if c = inf ∨ d = inf then 1 else Ring.inverse (x c - x d)

/-- `y_cd` of `prop:Ns`: `1/(a_c - a_d)` for finite `c, d`; `0` for `c = ∞`; `a_c` for `d = ∞`. -/
noncomputable def yN {R : Type*} [CommRing R] {s : ℕ} (inf : Fin s) (x : Fin s → R)
    (c d : Fin s) : R :=
  if c = inf then 0 else if d = inf then x c else Ring.inverse (x c - x d)

/-- `Toep(u)` (`sec:frames`): the lower-triangular Toeplitz matrix of `u`, level-indexed. -/
def toep {R : Type*} [CommRing R] (k : ℕ) (u : Polynomial R) : Matrix (Fin k) (Fin k) R :=
  fun i j => if j ≤ i then u.coeff ((i : ℕ) - (j : ℕ)) else 0

/-- The row gauge `diag(sc, 1, …, 1)`. -/
def Lgauge {R : Type*} [CommRing R] (n : ℕ) (sc : R) : Matrix (Fin n) (Fin n) R :=
  diagonal fun r => if (r : ℕ) = 0 then sc else 1

/-- The residual problem (`sec:frames`, before `prop:Gs`) of a design `F` (`F n c d = F_n[c][d]`,
the target of the `x`-index `n`, i.e. level `k-1-n`, of row `0` of block `(c, d)`): units `λ'_c`, and for each `d` an
upper-triangular `(s-1) × (s-1)` matrix `U'_d` in the `x`-index with unit diagonal, such that
`F_n[c][d] = λ'_c ∑_{n' ≤ n} w_cd y_cd^(n') U'_d[n', n]` for `c ≠ d`, `n ≤ s-2`. -/
def Residual {R : Type*} [CommRing R] {s : ℕ} (inf : Fin s) (x : Fin s → R)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) : Prop :=
  (∀ c, IsUnit (lam c)) ∧ (∀ d n' n, n < n' → n' < s - 1 → Ur d n' n = 0) ∧
    (∀ d n, n < s - 1 → IsUnit (Ur d n n)) ∧
    ∀ c d, c ≠ d → ∀ n, n < s - 1 →
      F n c d = lam c * ∑ n' ∈ range (n + 1), wN inf x c d * yN inf x c d ^ n' * Ur d n' n

/-- The defining relation of `β_n` in `prop:Gs` (`n ≥ s-1`): `λ' ⊙ v_n = ∑_{i ≤ s-2} β_{n,i} F_i[·][d]`
on the rows `c ≠ d`, where `v_n = (w_cd y_cd^n)_c`. -/
def BetaRel {R : Type*} [CommRing R] {s : ℕ} (inf : Fin s) (x : Fin s → R)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (β : Fin s → ℕ → ℕ → R) : Prop :=
  ∀ d n, s - 1 ≤ n → ∀ c, c ≠ d →
    lam c * (wN inf x c d * yN inf x c d ^ n) = ∑ i ∈ range (s - 1), β d n i * F i c d

/-- `U'^(k)_d` of `prop:Gs` in the `x`-index (row `n'`, column `n`): `U'_d` on `n', n < s-1`; for
`n ≥ s-1` the column `e_n - ∑_{i ≤ s-2} β_{n,i} (column i of U'_d)`. -/
def Ux {R : Type*} [CommRing R] {s : ℕ} (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
    (d : Fin s) (n' n : ℕ) : R :=
  if n < s - 1 then (if n' < s - 1 then Ur d n' n else 0)
  else if n' = n then 1
  else if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0

/-- The column gauge `U_d = U^0_d U'^(k)_d` of `prop:Gs`, level-indexed (`U^0_d = Toep(uN_d)`; the
`x`-index `n` is level `k-1-n`). -/
noncomputable def Ugauge {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) (d : Fin s) : Matrix (Fin k) (Fin k) R :=
  toep k (uN k inf x d) *
    Matrix.of (fun i j : Fin k => Ux Ur β d (k - 1 - (i : ℕ)) (k - 1 - (j : ℕ)))

/-- The row gauge `L_c = diag(λ'_c Q_c^(-k), 1, …, 1)` of `prop:Gs`. -/
noncomputable def Lmat {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
    (lam : Fin s → R) (c : Fin s) : Matrix (Fin (s * k - k)) (Fin (s * k - k)) R :=
  Lgauge (s * k - k) (lam c * Ring.inverse (Qf inf x c ^ k))

/-! ## The net `𝒫^F_k` (`def:Ns`) -/

/-- **`def:Ns`**, the blocks: `Φ'_cd = L_c Φ^F_cd U_d` (`c ≠ d`); `Φ'_cc` has row `0` equal to
`(F_{s-2}[c][c], …, F_0[c][c])` on the levels `(k-s+1, …, k-1)` (truncated if `k < s-1`) and all
other entries `0`. -/
noncomputable def PPhi {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (c d : Fin s) : Matrix (Fin (s * k - k)) (Fin k) R :=
  if c = d then fun r l => if (r : ℕ) = 0 ∧ k - 1 - (l : ℕ) < s - 1 then F (k - 1 - (l : ℕ)) c c
    else 0
  else Lmat k inf x lam c * frameGraph R k inf x c d * Ugauge k inf x Ur β d

/-- **`def:Ns`**: the generator matrices of `𝒫^F_k` over `R`, the graph form with depths
`(k, …, k)` and the blocks `PPhi`. -/
noncomputable def PGen {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) : Fin s → Matrix (Fin (s * k)) (Fin (s * k)) R :=
  graphGenK (m := s * k) (fun _ => k) (PPhi k inf x F lam Ur β)

end Z3NetF

namespace Z3NetA

open Matrix Finset Z3NetF

/-! ## The places, `R_S`, and the lattices `Λ_j` (`sec:lattice`) -/

/-- `R_S = ℤ[1/n!]`, `n = s - 2` (`sec:lattice`). -/
abbrev RS (s : ℕ) : Type := Localization.Away ((((s - 2).factorial : ℕ) : ℤ))

/-- The places of `thm:A`: coordinate `0` is read at `∞` (its value is not used), coordinate
`c ≥ 1` at the place `c - 1`; so the places are `∞, 0, 1, …, s-2` in the coordinate order. -/
def placeA {R : Type*} [CommRing R] {s : ℕ} (c : Fin s) : R := ((c : ℕ) : R) - 1

/-- The bases of `thm:A`: `q ≥ 2`, and every prime factor of `q` is at least `s - 1`. -/
def AdmBase (s q : ℕ) : Prop := 2 ≤ q ∧ ∀ p : ℕ, p.Prime → p ∣ q → s - 1 ≤ p

/-- The weight `w_c = w_cd` of row `c` in column `d` (`sec:lattice`, from `prop:Ns`), over `ℚ`:
`1/(c-d)` for finite `c, d`; `1` if `c` or `d` is `∞`. -/
noncomputable def wQ {s : ℕ} [NeZero s] (c d : Fin s) : ℚ := wN (0 : Fin s) placeA c d

/-- The node `y_c = y_cd` of row `c` in column `d` (`sec:lattice`, from `prop:Ns`), over `ℚ`:
`1/(c-d)` for finite `c, d`; `0` for `c = ∞`; `c` for `d = ∞`. -/
noncomputable def yQ {s : ℕ} [NeZero s] (c d : Fin s) : ℚ := yN (0 : Fin s) placeA c d

/-- "The polynomial `g` of a vector of `V_j`" (`sec:lattice`): the Lagrange interpolant, of degree
`≤ s - 2`, of the values `E_c / w_c` at the `s - 1` distinct nodes `y_c`, `c ≠ d`. -/
noncomputable def colPoly {s : ℕ} [NeZero s] (d : Fin s) (E : Fin s → ℚ) : Polynomial ℚ :=
  Lagrange.interpolate (univ.filter fun c => c ≠ d) (fun c => yQ c d) (fun c => E c / wQ c d)

/-- `E ∈ Λ_j = V_j ∩ ℤ^(s-1)` (column `d`; `sec:lattice`): an integer column, written as a vector
indexed by all `s` coordinates with entry `0` at the row `d`, such that `E_c = w_c g(y_c)` for all
`c ≠ d` and a rational polynomial `g` of degree `≤ j`. -/
def InLam {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : Prop :=
  E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧ ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)

/-- `κ_j(E)` (`sec:lattice`): the coefficient of `X^j` in the polynomial of `E`. -/
noncomputable def kappa {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) (E : Fin s → ℤ) : ℚ :=
  (colPoly d fun c => (E c : ℚ)).coeff j

open Classical in
/-- `γ_j` (column `d`; `lem:sat`(ii)): the positive rational with `κ_j(Λ_j) = γ_j ℤ`. It exists
and is unique (`Z3NetA.gamma_spec` below); the junk value `0` is never used. -/
noncomputable def gamS {s : ℕ} [NeZero s] (d : Fin s) (j : ℕ) : ℚ :=
  if h : ∃ γ : ℚ, 0 < γ ∧ ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ
  then Classical.choose h else 0

/-! ## The design `U*_s` (`def:Ustar`) -/

/-- `cf` are the coefficients, in the vectors `B 0, …, B (j-1)`, of the orthogonal projection of
`E` onto their span (standard inner product of `ℚ^s`): `E - ∑_{l<j} cf_l B_l ⊥ B_i` for `i < j`. -/
def ProjCoef {s : ℕ} (B : ℕ → Fin s → ℤ) (j : ℕ) (E : Fin s → ℤ) (cf : ℕ → ℚ) : Prop :=
  ∀ i < j, ∑ c, ((E c : ℚ) - ∑ l ∈ range j, cf l * (B l c : ℚ)) * (B i c : ℚ) = 0

/-- **`def:Ustar`, the columns** (column `d`): `B j = E_{d,j}` for `j ≤ s - 2` iff `B j ∈ Λ_j`,
`κ_j(B j) = +γ_j`, and the orthogonal projection of `B j` onto `V_{j-1}` (the span of
`B 0, …, B (j-1)`) has all its coefficients in that basis in `[-1/2, 1/2)`. For `j = 0` this says
that `B 0` is the generator of `Λ_0` with `κ_0 > 0`. `B j = 0` for `j > s - 2` (normalization). -/
def IsUstarCols {s : ℕ} [NeZero s] (d : Fin s) (B : ℕ → Fin s → ℤ) : Prop :=
  (∀ j, j ≤ s - 2 → InLam d j (B j) ∧ kappa d j (B j) = gamS d j ∧
    ∃ cf : ℕ → ℚ, ProjCoef B j (B j) cf ∧ ∀ i < j, -1 / 2 ≤ cf i ∧ cf i < 1 / 2) ∧
  ∀ j, s - 2 < j → B j = 0

/-- The columns `E_{d,0}, …, E_{d,s-2}` of `def:Ustar`: the family with `IsUstarCols d`. It exists
and is unique (`Z3NetA.ustarCols_spec` below). -/
noncomputable def Ecol {s : ℕ} [NeZero s] (d : Fin s) : ℕ → Fin s → ℤ :=
  Classical.epsilon (IsUstarCols d)

/-- `α_c = ∑_{d ≠ c} max_{j ≤ s-2} |E_{d,j}[c]|` (`def:Ustar`). -/
noncomputable def alphaS {s : ℕ} [NeZero s] (c : Fin s) : ℕ :=
  ∑ d ∈ univ.filter (fun d => d ≠ c), (range (s - 1)).sup fun j => (Ecol d j c).natAbs

/-- `a*_s = max_c α_c` (`def:Ustar`). -/
noncomputable def aStar (s : ℕ) [NeZero s] : ℕ := univ.sup fun c : Fin s => alphaS c

/-- **`def:Ustar`, the design** `U*_s = (F_0, …, F_{s-2})`: off the diagonal the partial sums are
`M^(j)[c][d] = E_{d,j}[c]`, i.e. `F_0[c][d] = E_{d,0}[c]` and `F_n[c][d] = E_{d,n}[c] - E_{d,n-1}[c]`;
the level-`0` diagonal is `F_0[c][c] = -α_c`, the deeper diagonal is `0`; `F_n = 0` for `n ≥ s-1`. -/
noncomputable def UstarF (s : ℕ) [NeZero s] (n : ℕ) (c d : Fin s) : ℤ :=
  if c = d then (if n = 0 then -(alphaS c : ℤ) else 0)
  else if s - 1 ≤ n then 0
  else if n = 0 then Ecol d 0 c else Ecol d n c - Ecol d (n - 1) c

/-! ## The net `𝒫^{U*_s}_{k,q}` (`def:Ns` with the design `U*_s`, `thm:A`) -/

/-- `U*_s` over `R_S`. -/
noncomputable def UstarR (s : ℕ) [NeZero s] : ℕ → Fin s → Fin s → RS s :=
  fun n c d => (UstarF s n c d : RS s)

/-- A solution `U'` of the residual problem of `U*_s` over `R_S` with `λ' ≡ 1` (it exists, and the
net does not depend on the choice: `Z3NetA.net_wellDefined` below). -/
noncomputable def UrS (s : ℕ) [NeZero s] : Fin s → ℕ → ℕ → RS s :=
  Classical.epsilon fun Ur => Residual (0 : Fin s) placeA (UstarR s) 1 Ur

/-- Coefficients `β` of `prop:Gs` for `U*_s` over `R_S` (they exist, and the net does not depend on
the choice: `Z3NetA.net_wellDefined` below). -/
noncomputable def betaS (s : ℕ) [NeZero s] : Fin s → ℕ → ℕ → RS s :=
  Classical.epsilon fun β => BetaRel (0 : Fin s) placeA (UstarR s) 1 β

open Classical in
/-- **The net `𝒫^{U*_s}_{k,q}` of `thm:A`**: the integer point (in `[0, N)^s`, `N = q^(sk)`) with
index `v ∈ (ℤ/qℤ)^(sk)`. The generator matrices are those of `𝒫^F_k` (`def:Ns`, `PGen`) over
`R_S` for the places `∞, 0, …, s-2`, the design `U*_s`, `λ' ≡ 1`, `U' = UrS s`, `β = betaS s`,
mapped to `ℤ/qℤ` by a ring homomorphism `R_S → ℤ/qℤ` ("reduced modulo `q`"). Such a homomorphism
exists iff `gcd(q, (s-2)!) = 1`, in particular for every admissible `q`; the junk value `0` is used
otherwise. For admissible `q` the result does not depend on the choices (`Z3NetA.net_wellDefined`). -/
noncomputable def Apoint (s q k : ℕ) [NeZero s] (v : Fin (s * k) → ZMod q) : Fin s → ℕ :=
  if h : Nonempty (RS s →+* ZMod q) then
    let ψ : RS s →+* ZMod q := Classical.choice h
    digPoint q (s * k) (fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c).map ψ) v
  else 0

/-! ## Theorem A -/

/-- **Theorem A** (`thm:A`). Let `s ≥ 3`, let `q ≥ 2` be an integer all of whose prime factors are
at least `s - 1` (`AdmBase s q`), and let `k ≥ 1`; `N = q^(sk)`, and the points of
`𝒫^{U*_s}_{k,q}` are `Apoint s q k v / N`, `v ∈ (ℤ/qℤ)^(sk)`. Then:
1. `𝒫^{U*_s}_{k,q}` is a `(0, sk, s)`-net in base `q` (with depths `(k, …, k)`: every cell holds
   exactly one point), and every `x ∈ [0,1]^s` lies within Euclidean distance `√s N^(-1/s)` of a
   point of the net (`h ≤ √s N^(-1/s)`);
2. if `q ≥ 5a*_s + 4`, any two distinct points have toroidal distance, and Euclidean distance, at
   least `(1 - a*_s/q) N^(-1/s)`, for every `k ≥ 1`; if moreover `k ≥ 2` and `q > (s-1) a*_s`, some
   two distinct points have toroidal and Euclidean distance `< (1 - a*_s/q + (s-1)(a*_s+1)²/q²) N^(-1/s)`
   (first-order sharpness, `δ N^(1/s) = 1 - a*_s/q + O(q⁻²)`, with an explicit constant);
3. `a*_3 = 2`; and for `s ≥ 4`, `a*_s ≤ 2(s-1)^(3/2) (3/2)^(s-2) (s-2)!` and
   `|log(2(s-1)^(3/2) (3/2)^(s-2) (s-2)!) - s log s| ≤ 3s`, i.e. the bound is `e^(s log s + O(s))`. -/
theorem theoremA (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Apoint s q k) ∧
    (∀ x : Fin s → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∃ v : Fin (s * k) → ZMod q,
      Real.sqrt (∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) ≤
        Real.sqrt s * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    (5 * aStar s + 4 ≤ q → ∀ v w : Fin (s * k) → ZMod q, v ≠ w →
      (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) ∧
        (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2)) ∧
    (2 ≤ k → 5 * aStar s + 4 ≤ q → (s - 1) * aStar s < q → ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    aStar 3 = 2 ∧
    (4 ≤ s →
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) ∧
      |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
        s * Real.log s| ≤ 3 * s) := by
  sorry

/-! ## The choice-defined data are the paper's -/

/-- **`def:Ustar`, the columns exist and are unique**: for `s ≥ 3` and every column `d`, the chosen
family `Ecol d` has the characterizing properties of `def:Ustar` (`IsUstarCols`), and every family
with these properties is `Ecol d`. So `Ecol d j` is the paper's `E_{d,j}`. -/
theorem ustarCols_spec {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) :
    IsUstarCols d (Ecol d) ∧ ∀ B : ℕ → Fin s → ℤ, IsUstarCols d B → B = Ecol d := by
  sorry

/-- **`lem:sat`(ii), `γ_j` exists and is unique**: for `s ≥ 3`, every column `d` and `j ≤ s - 2`,
`gamS d j` is positive and `κ_j(Λ_j) = gamS d j · ℤ`, and every positive rational `γ` with
`κ_j(Λ_j) = γ ℤ` is `gamS d j`. So `gamS d j` is the paper's `γ_j`. -/
theorem gamma_spec {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧
      (∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j) ∧
      ∀ γ : ℚ, 0 < γ → (∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ) →
        γ = gamS d j := by
  sorry

/-- **`def:Ns`, `prop:Gs`, `thm:A`: the net does not depend on the choices.** For `s ≥ 3` and
admissible `q`: a ring homomorphism `ψ : R_S → ℤ/qℤ` ("reduction modulo `q`"), a solution `U'` of
the residual problem of `U*_s` with `λ' ≡ 1`, and coefficients `β` with the defining relation of
`prop:Gs` exist; and for **every** such `ψ`, `U'`, `β` the digital net with the generator matrices
of `𝒫^{U*_s}_k` (`PGen`) built from `(U', β)` and reduced by `ψ` is `Apoint s q k`. So the net of
`theoremA` is the paper's `𝒫^{U*_s}_{k,q}`, whatever solution and reduction the paper's
construction is carried out with. -/
theorem net_wellDefined (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) :
    Nonempty (RS s →+* ZMod q) ∧
      (∃ Ur : Fin s → ℕ → ℕ → RS s, Residual (0 : Fin s) placeA (UstarR s) 1 Ur) ∧
      (∃ β : Fin s → ℕ → ℕ → RS s, BetaRel (0 : Fin s) placeA (UstarR s) 1 β) ∧
      ∀ (ψ : RS s →+* ZMod q) (Ur β : Fin s → ℕ → ℕ → RS s),
        Residual (0 : Fin s) placeA (UstarR s) 1 Ur → BetaRel (0 : Fin s) placeA (UstarR s) 1 β →
        Apoint s q k = digPoint q (s * k) (fun c =>
          (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) := by
  sorry

end Z3NetA
