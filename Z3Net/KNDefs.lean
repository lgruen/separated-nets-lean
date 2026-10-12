/-
Paper: Well-separated (0,3k,3)-nets in every base q ≥ 4: one linear scramble of the
Faure–Hammersley net (draft, revision 4, 2026-10-07) — Remark on m ≡ 1, 2 (mod 3)
(`core.tex`, the `m ≡ 1, 2` paragraph of the Remarks and Appendix `app:verify`) and the
supporting notes the research notes.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Mathlib

@[expose] public section

/-!
# Definitions of the second entry (verbatim copy of the definitions in `ChallengeKN.lean`)

Keep in sync with `ChallengeKN.lean`; Comparator checks that the Solution declarations have the
same types and values.

# Challenge (second entry): well-separated digital `(0,m,3)`-nets for `m ≢ 0 (mod 3)`

Throughout `m = 3k + r` with `r ∈ {1, 2}`, digits are indexed `0, …, m-1` (digit `0` most
significant) and the coordinates are `Fin 3` (`0 = x`, `1 = y`, `2 = z`).  The basic
definitions (`coord`, `digPoint`, `IsNet0`, `cres`, `torusDist2`, `ent`) are verbatim copies of
those of the first entry (`Challenge.lean`), in the namespace `Z3NetKN`.

**Graph form with unequal depths.**  The coarse depths are `K_c = k + 1` for the first `r`
coordinates and `K_c = k` for the others (`depth r k c`); `K_x + K_y + K_z = m`.  A digital net
`C` is in graph form if its index digits are the coarse digits: digit `j < K_c` of coordinate `c`
is index digit `off r k c + j` (block `c`, level `j`, level `0` most significant).  The remaining
digits of `c` (its *offsets*) are linear forms in the index: offset row `i` of `c` is row
`K_c + i` of `C c`.  For a *skeleton* coordinate (`c ≥ r`, depth `k`) offset digit `0` is the
*skeleton digit* and offset digit `1` the *jitter digit*; a *full* coordinate (`c < r`, depth
`k + 1`) has no skeleton digit and offset digit `0` is its jitter digit (`jrow`).

A design `Rows` lists, for every coordinate `c` and block `d`, the coefficients `sk c d i`,
`jt c d i` of the skeleton / jitter digit of `c` on level `K_d - 1 - i` of block `d`
(`i = 0` is the last coarse level); they are prescribed on the last `win r d` levels
(`4` for the `x`-block when `r = 1`, else `3`) and are `0` on all higher levels (`winEntry`).
`IsKNskel` prescribes the coarse rows and the skeleton rows; `IsKN` additionally prescribes the
jitter rows and requires all *deeper* rows of `c` (below its jitter row) to vanish on `c`'s own
block.  These are exactly the data the certificate of `kn2_cert.cpp` reads off a net.

**Main declarations** (see the statement-review notes (research repository)):

* `KN1_net`, `KN1_sep` — `m ≡ 1`: for each of the 20 primes `5 ≤ p ≤ 79` in `table1`, and every
  `m = 3k + 1 ≥ 10`, there is a `(0,m,3)`-net over `𝔽_p` with the certified rows, and every net
  with these rows has toroidal separation `δ ≥ c_p N^(-1/3)`, `c_p = √T_p · p^(-5/3)`
  (exact integer form `T_p · p^(4k-2) ≤ N² δ²`).
* `KN2_net`, `KN2_sep` — `m ≡ 2`, the 17 primes of `table2` (`5 ≤ p ≤ 61` and `79`), every
  `m = 3k + 2 ≥ 8`, `c_p = √T_p · p^(-4/3)` (`T_p · p^(4k) ≤ N² δ²`).
* `B1_net`, `B1_sep`, `B2_net`, `B2_sep` — explicit families for **all** primes: skeleton rows
  `skB1 ρ`, `skB2 ρ` (index-`p²` resp. index-`p` lattices with parameters `ρ, ρ²`); separation
  `δ ≥ (ρ² - 4) p^(-2/3) N^(-1/3)` (`m ≡ 1`, `ρ²(ρ+1) ≤ p`) resp.
  `δ ≥ (ρ - 1) p^(-1/3) N^(-1/3)` (`m ≡ 2`, `ρ(1+ρ+ρ²) ≤ p`); with `ρ ≈ p^(1/3)` both
  constants tend to `1` as `p → ∞`.
-/

namespace Z3NetKN

open Matrix

/-! ## Digital nets, elementary boxes, distances (verbatim from `Challenge.lean`) -/

/-- Integer coordinate of the digital point with generator matrix `C` and index `v`:
the digits are `d = C v ∈ (ℤ/qℤ)^m` (digit `0` most significant) and
`coord q m C v = ∑_j val(d_j) · q^(m-1-j) ∈ [0, q^m)`. -/
def coord (q m : ℕ) (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) : ℕ :=
  ∑ j : Fin m, ((C *ᵥ v) j).val * q ^ (m - 1 - (j : ℕ))

/-- The integer point (three coordinates) of the digital net with generator matrices
`C 0, C 1, C 2` at index `v`. -/
def digPoint (q m : ℕ) (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) :
    Fin 3 → ℕ :=
  fun c => coord q m (C c) v

/-- `(0,m,3)`-net property in base `q` of the family of integer points `X v ∈ [0,q^m)^3`
indexed by `v ∈ (ℤ/qℤ)^m`: for every `d` with `d 0 + d 1 + d 2 = m` and every elementary box
`∏_c [a_c q^(-d_c), (a_c+1) q^(-d_c))` (`a_c < q^(d_c)`), exactly one index `v` has its point
`X v / q^m` in the box.  (`X / q^(m-d) = a` in `ℕ` is `a q^(-d) ≤ X / q^m < (a+1) q^(-d)`.) -/
def IsNet0 (q m : ℕ) (X : (Fin m → ZMod q) → Fin 3 → ℕ) : Prop :=
  ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 = m → ∀ a : Fin 3 → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : Fin m → ZMod q, ∀ c, X v c / q ^ (m - d c) = a c

/-- Distance from the integer `u` to the lattice `N ℤ`: `min (u mod N) (N - u mod N)`.
(Adapted from `GKEvenNet.cres`.) -/
def cres (N : ℕ) (u : ℤ) : ℕ :=
  min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat)

/-- Squared toroidal distance, at integer scale `N`, between the integer points `x, y`
(i.e. `N²` times the squared distance of `x / N`, `y / N` on the torus `(ℝ/ℤ)³`). -/
def torusDist2 (N : ℕ) (x y : Fin 3 → ℕ) : ℕ :=
  ∑ c, cres N ((x c : ℤ) - (y c : ℤ)) ^ 2

/-- Total entry accessor: `ent A i j = A i j` if `(i, j)` is in range, `0` otherwise. -/
def ent {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) : R :=
  if h : i < a ∧ j < b then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-! ## Graph form with unequal coarse depths -/

/-- Coarse depth of coordinate `c` for `m = 3k + r`: `k + 1` for `c < r`, else `k`. -/
def depth (r k : ℕ) (c : Fin 3) : ℕ := if (c : ℕ) < r then k + 1 else k

/-- First index digit of block `c` (blocks `x, y, z` in this order). -/
def off (r k : ℕ) (c : Fin 3) : ℕ :=
  if (c : ℕ) = 0 then 0 else if (c : ℕ) = 1 then depth r k 0 else depth r k 0 + depth r k 1

/-- Number of trailing levels of block `d` on which the designed rows may be nonzero:
`4` for the `x`-block when `r = 1`, otherwise `3`. -/
def win (r : ℕ) (d : Fin 3) : ℕ := if r = 1 ∧ (d : ℕ) = 0 then 4 else 3

/-- Row of `C c` holding the jitter digit: `K_c` for a full coordinate, `K_c + 1` for a skeleton
coordinate (whose row `K_c` is the skeleton digit). -/
def jrow (r k : ℕ) (c : Fin 3) : ℕ := if (c : ℕ) < r then depth r k c else depth r k c + 1

/-- Entry of a designed row at level `l` of a block of depth `K` with window `L`:
`row (K - 1 - l)` on the last `L` levels (`K - 1 - l < L`), `0` on the higher levels. -/
def winEntry (row : Fin 4 → ℤ) (L K l : ℕ) : ℤ :=
  if h : K - 1 - l < 4 then (if K - 1 - l < L then row ⟨K - 1 - l, h⟩ else 0) else 0

/-- A design: skeleton rows `sk c d i` and jitter rows `jt c d i`
(coefficient of level `K_d - 1 - i` of block `d` in the skeleton / jitter digit of `c`). -/
structure Rows where
  sk : Fin 3 → Fin 3 → Fin 4 → ℤ
  jt : Fin 3 → Fin 3 → Fin 4 → ℤ

/-- `C` is in graph form with depths `depth r k` and its skeleton rows are the designed `sk`. -/
def IsKNskel (r p k : ℕ) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) : Prop :=
  (∀ c : Fin 3, ∀ j col : ℕ, j < depth r k c → col < 3 * k + r →
      ent (C c) j col = if col = off r k c + j then 1 else 0) ∧
  (∀ c d : Fin 3, r ≤ (c : ℕ) → ∀ l : ℕ, l < depth r k d →
      ent (C c) (depth r k c) (off r k d + l) =
        ((winEntry (sk c d) (win r d) (depth r k d) l : ℤ) : ZMod p))

/-- `C` is a KN net with design `R`: graph form, designed skeleton and jitter rows, and all rows
of `C c` below its jitter row vanish on `c`'s own block. -/
def IsKN (r p k : ℕ) (R : Rows)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) : Prop :=
  IsKNskel r p k R.sk C ∧
  (∀ c d : Fin 3, ∀ l : ℕ, l < depth r k d →
      ent (C c) (jrow r k c) (off r k d + l) =
        ((winEntry (R.jt c d) (win r d) (depth r k d) l : ℤ) : ZMod p)) ∧
  (∀ c : Fin 3, ∀ i l : ℕ, jrow r k c < i → i < 3 * k + r → l < depth r k c →
      ent (C c) i (off r k c + l) = 0)

/-! ## The certified designs (rows read from the witness matrices of `witnesses` (research repository)) -/

/-- Rows of the `m ≡ 1` net at `p = 5` (read from `witnesses/kn2/kn2_r1_p5_m10.txt`). -/
def rows1_5 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![2, 1, 0, 0], ![0, 0, 0, 0], ![-2, 0, 0, 0]],
      ![![-1, -1, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![1, 1, 0, 0]],
      ![![0, 2, -1, -1], ![0, 0, 0, 0], ![1, -1, 1, 0]],
      ![![0, -2, -1, 1], ![1, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 7` (read from `witnesses/kn2/kn2_r1_p7_m10.txt`). -/
def rows1_7 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 1, 0, 0], ![0, 0, 0, 0], ![-3, 0, 0, 0]],
      ![![-2, 0, 0, 0], ![-1, 0, 0, 0], ![2, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, 1, 0, 0], ![1, -1, 0, 0]],
      ![![-3, -3, -1, 1], ![0, 0, 0, 0], ![-3, 1, -1, 0]],
      ![![0, -3, -2, -1], ![-1, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 11` (read from `witnesses/kn2/kn2_r1_p11_m10.txt`). -/
def rows1_11 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![-2, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
      ![![-4, -1, 0, 0], ![1, 0, 0, 0], ![4, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 0]],
      ![![2, -3, -1, 1], ![0, 0, 0, 0], ![-1, -1, 1, 0]],
      ![![0, 1, -4, 1], ![1, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 13` (read from `witnesses/kn2/kn2_r1_p13_m10.txt`). -/
def rows1_13 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![5, 1, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![-3, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![1, 1, 0, 0], ![-1, -1, 0, 0]],
      ![![-5, -2, 1, -1], ![0, 0, 0, 0], ![0, 1, 1, 0]],
      ![![0, -2, -2, 1], ![-1, 1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 17` (read from `witnesses/kn2/kn2_r1_p17_m10.txt`). -/
def rows1_17 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 1, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![6, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, -1, 0, 0], ![1, 1, 0, 0]],
      ![![-3, 0, -1, -1], ![1, 0, 0, 0], ![2, -1, 1, 0]],
      ![![-6, -2, -2, 1], ![-2, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 19` (read from `witnesses/kn2/kn2_r1_p19_m10.txt`). -/
def rows1_19 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 1, 0, 0], ![4, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![6, 1, 0, 0], ![6, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![-4, -7, 1, -1], ![-4, 0, 0, 0], ![2, 1, 1, 0]],
      ![![0, -8, 5, -1], ![-1, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 23` (read from `witnesses/kn2/kn2_r1_p23_m10.txt`). -/
def rows1_23 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 0, 0, 0], ![-3, 0, 0, 0], ![-3, 0, 0, 0]],
      ![![9, -1, 0, 0], ![-9, 0, 0, 0], ![-9, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, 1, 0, 0], ![1, 1, 0, 0]],
      ![![0, -5, -1, -1], ![0, 0, 0, 0], ![1, -1, 1, 0]],
      ![![-9, 6, -1, 1], ![10, 1, -1, 0], ![9, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 29` (read from `witnesses/kn2/kn2_r1_p29_m10.txt`). -/
def rows1_29 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 1, 0, 0], ![0, 0, 0, 0], ![3, 0, 0, 0]],
      ![![9, 1, 0, 0], ![1, 0, 0, 0], ![9, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![0, 3, -1, -1], ![0, 0, 0, 0], ![1, -1, 1, 0]],
      ![![0, -2, 9, -1], ![-1, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 31` (read from `witnesses/kn2/kn2_r1_p31_m10.txt`). -/
def rows1_31 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 1, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 0]],
      ![![-11, 0, 0, 0], ![1, 0, 0, 0], ![-11, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 0]],
      ![![0, -15, -1, -1], ![0, 0, 0, 0], ![-1, 1, -1, 0]],
      ![![0, -14, 3, -1], ![1, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 37` (read from `witnesses/kn2/kn2_r1_p37_m10.txt`). -/
def rows1_37 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![13, 0, 0, 0], ![-13, 0, 0, 0], ![-13, 0, 0, 0]],
      ![![-16, -1, 0, 0], ![16, 0, 0, 0], ![16, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, 1, 0, 0], ![1, 1, 0, 0]],
      ![![-13, -7, 1, -1], ![13, 0, 0, 0], ![14, -1, -1, 0]],
      ![![16, 8, 1, 1], ![-15, 1, -1, 0], ![-16, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 41` (read from `witnesses/kn2/kn2_r1_p41_m10.txt`). -/
def rows1_41 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![7, 0, 0, 0], ![-7, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![10, 1, 0, 0], ![-10, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![1, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![0, 13, -1, -1], ![0, 0, 0, 0], ![-1, -1, -1, 0]],
      ![![-10, 3, -6, 1], ![9, -1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 43` (read from `witnesses/kn2/kn2_r1_p43_m10.txt`). -/
def rows1_43 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![7, 1, 0, 0], ![7, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![11, 0, 0, 0], ![11, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![0, -1, -1, -1], ![0, 0, 0, 0], ![-1, -1, -1, 0]],
      ![![-11, 6, -6, -1], ![-12, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 47` (read from `witnesses/kn2/kn2_r1_p47_m10.txt`). -/
def rows1_47 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 1, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]],
      ![![18, -1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![0, 4, -1, -1], ![0, 0, 0, 0], ![1, -1, 1, 0]],
      ![![0, 18, -19, -1], ![1, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 53` (read from `witnesses/kn2/kn2_r1_p53_m10.txt`). -/
def rows1_53 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![13, 1, 0, 0], ![13, 0, 0, 0], ![12, 0, 0, 0]],
      ![![23, 0, 0, 0], ![23, 0, 0, 0], ![23, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![1, -1, 0, 0]],
      ![![0, -22, 1, -1], ![0, 0, 0, 0], ![-1, -1, -1, 0]],
      ![![-23, -4, -5, -1], ![-22, -1, 1, 0], ![-23, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 59` (read from `witnesses/kn2/kn2_r1_p59_m10.txt`). -/
def rows1_59 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![11, -1, 0, 0], ![0, 0, 0, 0], ![11, 0, 0, 0]],
      ![![-15, 1, 0, 0], ![1, 0, 0, 0], ![-15, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![0, 20, -1, -1], ![0, 0, 0, 0], ![-1, 1, -1, 0]],
      ![![0, 5, 15, -1], ![-1, -1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 61` (read from `witnesses/kn2/kn2_r1_p61_m10.txt`). -/
def rows1_61 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![11, 1, 0, 0], ![0, 0, 0, 0], ![11, 0, 0, 0]],
      ![![15, 1, 0, 0], ![-1, 0, 0, 0], ![15, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![0, 7, 1, -1], ![0, 0, 0, 0], ![1, -1, 1, 0]],
      ![![0, -17, -15, -1], ![1, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 67` (read from `witnesses/kn2/kn2_r1_p67_m10.txt`). -/
def rows1_67 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 0, 0, 0], ![4, 0, 0, 0], ![-3, 0, 0, 0]],
      ![![18, -1, 0, 0], ![18, 0, 0, 0], ![-18, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![-4, 10, 1, -1], ![-4, 0, 0, 0], ![4, -1, -1, 0]],
      ![![0, -26, 16, -1], ![1, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 71` (read from `witnesses/kn2/kn2_r1_p71_m10.txt`). -/
def rows1_71 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![10, 1, 0, 0], ![10, 0, 0, 0], ![1, 0, 0, 0]],
      ![![16, 0, 0, 0], ![15, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![-10, -2, -1, -1], ![-10, 0, 0, 0], ![0, 1, -1, 0]],
      ![![-16, -2, 2, -1], ![-16, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 73` (read from `witnesses/kn2/kn2_r1_p73_m10.txt`). -/
def rows1_73 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![9, 1, 0, 0], ![0, 0, 0, 0], ![9, 0, 0, 0]],
      ![![34, 1, 0, 0], ![1, 0, 0, 0], ![34, 0, 0, 0]]]
  jt := ![![![0, 0, 0, 0], ![1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![-9, -8, -1, -1], ![0, 0, 0, 0], ![-8, -1, 1, 0]],
      ![![0, 19, -34, -1], ![1, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 1` net at `p = 79` (read from `witnesses/kn2/kn2_r1_p79_m10.txt`). -/
def rows1_79 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![12, 12, 0, 0], ![-12, 0, 0, 0], ![-12, 0, 0, 0]],
      ![![16, 17, 0, 0], ![-17, 0, 0, 0], ![-16, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![-12, -17, -1, -1], ![12, 0, 0, 0], ![13, -1, -1, 0]],
      ![![-16, -3, 13, 1], ![18, 1, 1, 0], ![16, 0, 0, 0]]]

/-- The certified `m ≡ 1 (mod 3)` designs: `(p, T_p, rows)`; `c_p = √T_p · p^(-5/3)`. -/
def table1 : List (ℕ × ℕ × Rows) :=
  [(5, 85, rows1_5),
   (7, 360, rows1_7),
   (11, 2161, rows1_11),
   (13, 3794, rows1_13),
   (17, 9986, rows1_17),
   (19, 14904, rows1_19),
   (23, 30277, rows1_23),
   (29, 71485, rows1_29),
   (31, 86406, rows1_31),
   (37, 160082, rows1_37),
   (41, 215869, rows1_41),
   (43, 273203, rows1_43),
   (47, 381649, rows1_47),
   (53, 576177, rows1_53),
   (59, 838749, rows1_59),
   (61, 918186, rows1_61),
   (67, 1214947, rows1_67),
   (71, 1544201, rows1_71),
   (73, 1710627, rows1_73),
   (79, 2267461, rows1_79)]

/-- Rows of the `m ≡ 2` net at `p = 5` (read from `witnesses/kn2/kn2_r2_p5_m8.txt`). -/
def rows2_5 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![2, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-2, 0, 0, 0], ![2, -1, -1, 0], ![-1, 1, 0, 0]],
      ![![2, -1, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![-2, -1, 1, 0], ![0, 2, 0, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 7` (read from `witnesses/kn2/kn2_r2_p7_m8.txt`). -/
def rows2_7 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![2, 0, 0, 0], ![3, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![1, -1, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![2, -1, 1, 0], ![2, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 11` (read from `witnesses/kn2/kn2_r2_p11_m8.txt`). -/
def rows2_11 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![-3, 0, 0, 0], ![-5, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![2, 0, 0, 0], ![-5, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![-3, -1, 1, 0], ![5, 0, 0, 0], ![1, 0, 0, 0]],
      ![![2, -1, 0, 0], ![2, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 13` (read from `witnesses/kn2/kn2_r2_p13_m8.txt`). -/
def rows2_13 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 0, 0, 0], ![-6, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![5, -1, -1, 0], ![6, 0, 0, 0], ![1, 0, 0, 0]],
      ![![-4, -1, 0, 0], ![5, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 17` (read from `witnesses/kn2/kn2_r2_p17_m8.txt`). -/
def rows2_17 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 0, 0, 0], ![-7, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![3, 0, 0, 0], ![-6, -1, 1, 0], ![-1, 0, 0, 0]],
      ![![3, -1, 0, 0], ![-8, 0, 0, 0], ![-1, 1, 0, 0]],
      ![![-8, -1, 1, 0], ![-4, 3, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 19` (read from `witnesses/kn2/kn2_r2_p19_m8.txt`). -/
def rows2_19 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 0, 0, 0], ![7, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![2, 0, 0, 0], ![6, -1, 0, 0], ![-1, 0, 0, 0]],
      ![![3, -1, 1, 0], ![5, 0, 0, 0], ![-1, -1, 0, 0]],
      ![![-5, -1, 0, 0], ![8, -2, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 23` (read from `witnesses/kn2/kn2_r2_p23_m8.txt`). -/
def rows2_23 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 0, 0, 0], ![9, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-2, 0, 0, 0], ![1, -1, 1, 0], ![1, -1, 0, 0]],
      ![![1, -1, 1, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![-4, -1, 0, 0], ![-9, 3, 0, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 29` (read from `witnesses/kn2/kn2_r2_p29_m8.txt`). -/
def rows2_29 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![-3, 0, 0, 0], ![9, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![1, 1, 0, 0], ![-1, 1, 0, 0]],
      ![![-4, -1, 0, 0], ![8, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![1, 1, -1, 0], ![14, 12, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 31` (read from `witnesses/kn2/kn2_r2_p31_m8.txt`). -/
def rows2_31 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![3, 0, 0, 0], ![-11, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-4, 0, 0, 0], ![11, 1, -1, 0], ![1, 0, 0, 0]],
      ![![4, 1, 0, 0], ![-12, 0, 0, 0], ![-1, 1, 0, 0]],
      ![![0, -1, 1, 0], ![-6, 9, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 37` (read from `witnesses/kn2/kn2_r2_p37_m8.txt`). -/
def rows2_37 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![13, 0, 0, 0], ![4, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-14, 0, 0, 0], ![-3, -1, 0, 0], ![-1, 1, 0, 0]],
      ![![-1, -1, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![12, -1, -1, 0], ![-8, 2, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 41` (read from `witnesses/kn2/kn2_r2_p41_m8.txt`). -/
def rows2_41 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![13, 0, 0, 0], ![19, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![12, 0, 0, 0], ![19, 1, -1, 0], ![-1, -1, 0, 0]],
      ![![-13, 1, -1, 0], ![20, 0, 0, 0], ![1, 0, 0, 0]],
      ![![0, 1, 0, 0], ![-19, 1, 0, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 43` (read from `witnesses/kn2/kn2_r2_p43_m8.txt`). -/
def rows2_43 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![11, 0, 0, 0], ![7, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![10, 0, 0, 0], ![7, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![1, 1, -1, 0], ![-1, 0, 0, 0], ![1, -1, 0, 0]],
      ![![20, 1, 0, 0], ![-14, 4, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 47` (read from `witnesses/kn2/kn2_r2_p47_m8.txt`). -/
def rows2_47 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![5, 0, 0, 0], ![-13, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-1, 0, 0, 0], ![1, 1, -1, 0], ![1, -1, 0, 0]],
      ![![4, -1, -1, 0], ![-14, 0, 0, 0], ![-1, 0, 0, 0]],
      ![![-5, -1, 0, 0], ![12, 1, 0, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 53` (read from `witnesses/kn2/kn2_r2_p53_m8.txt`). -/
def rows2_53 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![4, 0, 0, 0], ![21, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![3, 0, 0, 0], ![21, 1, 0, 0], ![1, 0, 0, 0]],
      ![![4, -1, 0, 0], ![20, 0, 0, 0], ![-1, 1, 0, 0]],
      ![![-9, -1, 1, 0], ![-13, -1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 59` (read from `witnesses/kn/kn2_p59_m8.txt`). -/
def rows2_59 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![-16, 0, 0, 0], ![-4, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-18, 0, 0, 0], ![-4, 1, 0, 0], ![1, 1, 0, 0]],
      ![![-16, 1, 0, 0], ![-6, 0, 0, 0], ![1, 0, 0, 0]],
      ![![-27, 1, 1, 0], ![4, -1, 1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 61` (read from `witnesses/kn/kn2_p61_m8.txt`). -/
def rows2_61 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![-4, 0, 0, 0], ![-16, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-5, 0, 0, 0], ![-16, 1, 0, 0], ![1, 0, 0, 0]],
      ![![4, 1, 0, 0], ![15, 0, 0, 0], ![-1, -1, 0, 0]],
      ![![1, 1, 1, 0], ![20, 1, -1, 0], ![0, 0, 0, 0]]]

/-- Rows of the `m ≡ 2` net at `p = 79` (read from `witnesses/kn/kn2_p79_m8.txt`). -/
def rows2_79 : Rows where
  sk := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
      ![![11, 0, 0, 0], ![-18, 0, 0, 0], ![0, 0, 0, 0]]]
  jt := ![![![-14, 0, 0, 0], ![18, -1, -1, 0], ![-1, 0, 0, 0]],
      ![![-11, -1, -1, 0], ![15, 0, 0, 0], ![-1, -1, 0, 0]],
      ![![-21, -1, 0, 0], ![38, 1, 0, 0], ![0, 0, 0, 0]]]

/-- The certified `m ≡ 2 (mod 3)` designs: `(p, T_p, rows)`; `c_p = √T_p · p^(-4/3)`. -/
def table2 : List (ℕ × ℕ × Rows) :=
  [(5, 19, rows2_5),
   (7, 73, rows2_7),
   (11, 425, rows2_11),
   (13, 691, rows2_13),
   (17, 1312, rows2_17),
   (19, 1798, rows2_19),
   (23, 4022, rows2_23),
   (29, 7685, rows2_29),
   (31, 9019, rows2_31),
   (37, 13777, rows2_37),
   (41, 20116, rows2_41),
   (43, 22853, rows2_43),
   (47, 28556, rows2_47),
   (53, 37546, rows2_53),
   (59, 54357, rows2_59),
   (61, 58586, rows2_61),
   (79, 119786, rows2_79)]

/-! ## Skeleton rows of the all-`p` families -/

/-- Skeleton rows of the all-`p` family for `m ≡ 2`: the skeleton digit of `z` is
`ρ x_k + ρ² y_k` (last coarse levels of `x`, `y`), so the occupied fine cells form the index-`p`
lattice `{e : e_z ≡ ρ e_x + ρ² e_y (mod p)}`. -/
def skB2 (ρ : ℕ) : Fin 3 → Fin 3 → Fin 4 → ℤ :=
  ![0, 0, ![![(ρ : ℤ), 0, 0, 0], ![(ρ : ℤ) ^ 2, 0, 0, 0], 0]]

/-- Skeleton rows of the all-`p` family for `m ≡ 1`: the skeleton digit of `y` is
`ρ x_k + z_{k-1}` and that of `z` is `ρ² x_k + x_{k-1} + y_{k-1} - z_{k-1}` (index-`p²` lattice
`{e : e_y ≡ ρ e_x, e_z ≡ ρ² e_x (mod p)}` with unit faults). -/
def skB1 (ρ : ℕ) : Fin 3 → Fin 3 → Fin 4 → ℤ :=
  ![0, ![![(ρ : ℤ), 0, 0, 0], 0, ![1, 0, 0, 0]],
    ![![(ρ : ℤ) ^ 2, 1, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0]]]

/-! ## Stage 6 (entry PP): the conditions of `prop:pp2`, `prop:pp1` and the invariants of
`lem:ppinv` (verbatim copy of the definitions of `ChallengePP.lean`) -/

/-! ## `app:perprime`, `m ≡ 2`: the conditions (S2), (N2), (K) on a design -/

/-- The design entry `R|d^(i)` of a geometric row as an element of `𝔽_p`. `m ≡ 2`: `X0 = jt x`,
`Y0 = jt y` (jitter rows of the full coordinates), `Z0 = sk z` (skeleton digit), `Z1 = jt z`;
window index `i` = distance from the last coarse level (`x^(0) = x_k`, `z^(0) = z_{k-1}`). -/
def eF (p : ℕ) (row : Fin 3 → Fin 4 → ℤ) (d : Fin 3) (i : Fin 4) : ZMod p := ((row d i : ℤ) : ZMod p)

/-- The bracket `[R, R' | c, c'] = R|c R'|c' - R|c' R'|c` on two window columns of block `d`. -/
def brk (p : ℕ) (row row' : Fin 3 → Fin 4 → ℤ) (d : Fin 3) (i i' : Fin 4) : ZMod p :=
  eF p row d i * eF p row' d i' - eF p row d i' * eF p row' d i

/-- (S2) of `prop:pp2`: `Z0|x_{k-1} = Z0|x_{k-2} = Z0|y_{k-1} = Z0|y_{k-2} = 0` and
`X0|z_{k-3} = Y0|z_{k-3} = 0`. -/
def CondS2 (R : Rows) : Prop :=
  R.sk 2 0 1 = 0 ∧ R.sk 2 0 2 = 0 ∧ R.sk 2 1 1 = 0 ∧ R.sk 2 1 2 = 0 ∧ R.jt 0 2 2 = 0 ∧
    R.jt 1 2 2 = 0

/-- (N2) of `prop:pp2`: the entries `Z0|x_k`, `Z0|y_k`, `Y0|x_k`, `Y0|x_{k-1}`, `Z1|x_{k-1}`,
`X0|y_k`, `X0|y_{k-1}`, `X0|z_{k-1}`, `Y0|z_{k-1}` and the brackets
`[Y0, Z1 | x_{k-2}, x_{k-1}]`, `[X0, Z1 | y_{k-2}, y_{k-1}]`, `[X0, Y0 | z_{k-2}, z_{k-1}]` are
nonzero modulo `p`. -/
def CondN2 (p : ℕ) (R : Rows) : Prop :=
  eF p (R.sk 2) 0 0 ≠ 0 ∧ eF p (R.sk 2) 1 0 ≠ 0 ∧ eF p (R.jt 1) 0 0 ≠ 0 ∧ eF p (R.jt 1) 0 1 ≠ 0 ∧
    eF p (R.jt 2) 0 1 ≠ 0 ∧ eF p (R.jt 0) 1 0 ≠ 0 ∧ eF p (R.jt 0) 1 1 ≠ 0 ∧
    eF p (R.jt 0) 2 0 ≠ 0 ∧ eF p (R.jt 1) 2 0 ≠ 0 ∧
    brk p (R.jt 1) (R.jt 2) 0 2 1 ≠ 0 ∧ brk p (R.jt 0) (R.jt 2) 1 2 1 ≠ 0 ∧
    brk p (R.jt 0) (R.jt 1) 2 1 0 ≠ 0

/-- The entry of a row on the combination `x̃ = x_{k-1} - (Z0|x_{k-1}/Z0|x_k) x_k` (block
`d ∈ {x, y}`) of `lem:ppinv`. -/
def tilde2 (p : ℕ) (R : Rows) (row : Fin 3 → Fin 4 → ℤ) (d : Fin 3) : ZMod p :=
  eF p row d 1 - eF p (R.sk 2) d 1 * (eF p (R.sk 2) d 0)⁻¹ * eF p row d 0

/-- The invariant `κ₁` of `lem:ppinv` (`m ≡ 2`):
`(Z1|ỹ · Y0|x̃ · X0|y_k · Z0|x_k) / (Z1|x̃ · Y0|x_k · X0|ỹ · Z0|y_k)`. -/
def kap1 (p : ℕ) (R : Rows) : ZMod p :=
  tilde2 p R (R.jt 2) 1 * tilde2 p R (R.jt 1) 0 * eF p (R.jt 0) 1 0 * eF p (R.sk 2) 0 0 *
    (tilde2 p R (R.jt 2) 0 * eF p (R.jt 1) 0 0 * tilde2 p R (R.jt 0) 1 * eF p (R.sk 2) 1 0)⁻¹

/-- The invariant `κ₂` of `lem:ppinv` (`m ≡ 2`):
`(Z1|x_k/Z0|x_k - Z1|y_k/Z0|y_k) · (Z0|x_k · Y0|x̃) / (Z1|x̃ · Y0|x_k)`. -/
def kap2 (p : ℕ) (R : Rows) : ZMod p :=
  (eF p (R.jt 2) 0 0 * (eF p (R.sk 2) 0 0)⁻¹ - eF p (R.jt 2) 1 0 * (eF p (R.sk 2) 1 0)⁻¹) *
    (eF p (R.sk 2) 0 0 * tilde2 p R (R.jt 1) 0) * (tilde2 p R (R.jt 2) 0 * eF p (R.jt 1) 0 0)⁻¹

/-! ## `app:perprime`, `m ≡ 1`: the conditions (S1), (N1), (J) on a design -/

/-- The bracket `[R, R' | c, c'] = R|c R'|c' - R|c' R'|c` on two window columns `c = (d, i)`,
`c' = (d', i')`, possibly of different blocks. -/
def brk2 (p : ℕ) (row row' : Fin 3 → Fin 4 → ℤ) (d : Fin 3) (i : Fin 4) (d' : Fin 3) (i' : Fin 4) :
    ZMod p :=
  eF p row d i * eF p row' d' i' - eF p row d' i' * eF p row' d i

/-- (S1) of `prop:pp1` (`X0 = jt x`, `Y0 = sk y`, `Y1 = jt y`, `Z0 = sk z`, `Z1 = jt z`; window
index `i`: `x^(i) = x_{k-i}`, `y^(i) = y_{k-1-i}`, `z^(i) = z_{k-1-i}`): `Y0, Z0` vanish on
`x_{k-2}, x_{k-3}`; `X0, Z0` on `y_{k-3}`; `X0, Y0` on `z_{k-3}`. -/
def CondS1 (R : Rows) : Prop :=
  R.sk 1 0 2 = 0 ∧ R.sk 1 0 3 = 0 ∧ R.sk 2 0 2 = 0 ∧ R.sk 2 0 3 = 0 ∧ R.jt 0 1 2 = 0 ∧
    R.sk 2 1 2 = 0 ∧ R.jt 0 2 2 = 0 ∧ R.sk 1 2 2 = 0

/-- (N1) of `prop:pp1`: the entries `Y0|x_k`, `Z0|x_k`, `X0|y_{k-1}`, `Z0|y_{k-1}`, `X0|z_{k-1}`,
`Y0|z_{k-1}`, `Y1|x_{k-2}`, `Z1|y_{k-3}`, `Y1|z_{k-3}` and the brackets `[Y0, Z0 | x_{k-1}, x_k]`,
`[X0, Z0 | y_{k-2}, y_{k-1}]`, `[X0, Y0 | z_{k-2}, z_{k-1}]`, `[Y1, Z1 | x_{k-3}, x_{k-2}]`,
`[Y1, Y0 | x_k, z_{k-1}]`, `[Z1, Z0 | x_k, y_{k-1}]` are nonzero modulo `p`. -/
def CondN1 (p : ℕ) (R : Rows) : Prop :=
  eF p (R.sk 1) 0 0 ≠ 0 ∧ eF p (R.sk 2) 0 0 ≠ 0 ∧ eF p (R.jt 0) 1 0 ≠ 0 ∧ eF p (R.sk 2) 1 0 ≠ 0 ∧
    eF p (R.jt 0) 2 0 ≠ 0 ∧ eF p (R.sk 1) 2 0 ≠ 0 ∧ eF p (R.jt 1) 0 2 ≠ 0 ∧
    eF p (R.jt 2) 1 2 ≠ 0 ∧ eF p (R.jt 1) 2 2 ≠ 0 ∧
    brk2 p (R.sk 1) (R.sk 2) 0 1 0 0 ≠ 0 ∧ brk2 p (R.jt 0) (R.sk 2) 1 1 1 0 ≠ 0 ∧
    brk2 p (R.jt 0) (R.sk 1) 2 1 2 0 ≠ 0 ∧ brk2 p (R.jt 1) (R.jt 2) 0 3 0 2 ≠ 0 ∧
    brk2 p (R.jt 1) (R.sk 1) 0 0 2 0 ≠ 0 ∧ brk2 p (R.jt 2) (R.sk 2) 0 0 1 0 ≠ 0

/-- `R_Y = Y1 - (Y1|ξ₀/Y0|ξ₀) Y0` on the window column `(d, i)` (`ξ₀ = x_k`). -/
def RYv (p : ℕ) (R : Rows) (d : Fin 3) (i : Fin 4) : ZMod p :=
  eF p (R.jt 1) d i - eF p (R.jt 1) 0 0 * (eF p (R.sk 1) 0 0)⁻¹ * eF p (R.sk 1) d i

/-- `R_Z = Z1 - (Z1|ξ₀/Z0|ξ₀) Z0` on the window column `(d, i)`. -/
def RZv (p : ℕ) (R : Rows) (d : Fin 3) (i : Fin 4) : ZMod p :=
  eF p (R.jt 2) d i - eF p (R.jt 2) 0 0 * (eF p (R.sk 2) 0 0)⁻¹ * eF p (R.sk 2) d i

/-- `d_x = [Y0, Z0 | ξ₀, ξ₁]`. -/
def dxJ (p : ℕ) (R : Rows) : ZMod p := brk2 p (R.sk 1) (R.sk 2) 0 0 0 1

/-- A row on `ζ̃ = ζ₁ - (X0|ζ₁/X0|ζ₀) ζ₀` (block `z`), given the row's values on `ζ₀, ζ₁`. -/
def tlz (p : ℕ) (R : Rows) (v0 v1 : ZMod p) : ZMod p :=
  v1 - eF p (R.jt 0) 2 1 * (eF p (R.jt 0) 2 0)⁻¹ * v0

/-- A row on `η̃ = η₁ - (X0|η₁/X0|η₀) η₀` (block `y`). -/
def tly (p : ℕ) (R : Rows) (v0 v1 : ZMod p) : ZMod p :=
  v1 - eF p (R.jt 0) 1 1 * (eF p (R.jt 0) 1 0)⁻¹ * v0

/-- The coefficients `(a, b)` of `ξ̃ = ξ₂ + a ξ₁ + b ξ₀` with `Y0|ξ̃ = Z0|ξ̃ = 0` (Cramer's rule). -/
def xiA (p : ℕ) (R : Rows) : ZMod p :=
  (eF p (R.sk 1) 0 0 * eF p (R.sk 2) 0 2 - eF p (R.sk 1) 0 2 * eF p (R.sk 2) 0 0) *
    (eF p (R.sk 1) 0 1 * eF p (R.sk 2) 0 0 - eF p (R.sk 1) 0 0 * eF p (R.sk 2) 0 1)⁻¹

def xiB (p : ℕ) (R : Rows) : ZMod p :=
  (eF p (R.sk 1) 0 2 * eF p (R.sk 2) 0 1 - eF p (R.sk 1) 0 1 * eF p (R.sk 2) 0 2) *
    (eF p (R.sk 1) 0 1 * eF p (R.sk 2) 0 0 - eF p (R.sk 1) 0 0 * eF p (R.sk 2) 0 1)⁻¹

/-- A row on `ξ̃`, given its values on `ξ₀, ξ₁, ξ₂`. -/
def tlx (p : ℕ) (R : Rows) (v0 v1 v2 : ZMod p) : ZMod p := v2 + xiA p R * v1 + xiB p R * v0

/-- The invariants `J₁, …, J₅` of `lem:ppinv` (`m ≡ 1`). -/
def J1 (p : ℕ) (R : Rows) : ZMod p :=
  RYv p R 0 1 * eF p (R.sk 2) 0 0 * eF p (R.sk 1) 2 0 * (RYv p R 2 0 * dxJ p R)⁻¹

def J2 (p : ℕ) (R : Rows) : ZMod p :=
  RZv p R 0 1 * eF p (R.sk 1) 0 0 * eF p (R.sk 2) 1 0 * (RZv p R 1 0 * dxJ p R)⁻¹

def J3 (p : ℕ) (R : Rows) : ZMod p :=
  tlz p R (RYv p R 2 0) (RYv p R 2 1) * eF p (R.sk 1) 2 0 *
    (tlz p R (eF p (R.sk 1) 2 0) (eF p (R.sk 1) 2 1) * RYv p R 2 0)⁻¹

def J4 (p : ℕ) (R : Rows) : ZMod p :=
  tly p R (RZv p R 1 0) (RZv p R 1 1) * eF p (R.sk 2) 1 0 *
    (tly p R (eF p (R.sk 2) 1 0) (eF p (R.sk 2) 1 1) * RZv p R 1 0)⁻¹

def J5 (p : ℕ) (R : Rows) : ZMod p :=
  tlx p R (RZv p R 0 0) (RZv p R 0 1) (RZv p R 0 2) * eF p (R.sk 1) 0 0 * eF p (R.sk 2) 1 0 *
      RYv p R 2 0 *
    (tlx p R (RYv p R 0 0) (RYv p R 0 1) (RYv p R 0 2) * eF p (R.sk 2) 0 0 * eF p (R.sk 1) 2 0 *
      RZv p R 1 0)⁻¹

end Z3NetKN
