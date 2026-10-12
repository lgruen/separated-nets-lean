/-
Development copy (Solution side) of the Challenge for the paper: Well-separated (0,3k,3)-nets in every base q ≥ 4: one linear scramble of the
Faure–Hammersley net (draft, revision 4, 2026-10-07).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Mathlib

@[expose] public section

/-!
# Definitions (verbatim copy of the definitions in `Challenge.lean`)

Keep in sync with `Challenge.lean`; Comparator checks that the Solution declarations have the
same types and values.
-/

namespace Z3Net

open Matrix

/-! ## Digital nets, elementary boxes, distances -/

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

/-- Squared Euclidean distance in *cell units* between the points `x / p^(3k)` and
`y / p^(3k)` (cell side `p^(-k)`), i.e. `∑_c ((x_c - y_c) / p^(2k))²`. -/
noncomputable def cellDist2 (p k : ℕ) (x y : Fin 3 → ℕ) : ℝ :=
  ∑ c, (((x c : ℝ) - (y c : ℝ)) / (p : ℝ) ^ (2 * k)) ^ 2

/-- Box matrix of `C` for `d = (d 0, d 1, d 2)`: rows `0..d0-1` are the first `d 0` rows of
`C 0`, then the first `d 1` rows of `C 1`, then the remaining rows of `C 2`
(for `d 0 + d 1 + d 2 = m` these are the first `d 2` rows of `C 2`). -/
def boxMatrix {R : Type*} {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) R) (d : Fin 3 → ℕ) :
    Matrix (Fin m) (Fin m) R :=
  fun r =>
    if (r : ℕ) < d 0 then C 0 r
    else if (r : ℕ) < d 0 + d 1 then C 1 ⟨(r : ℕ) - d 0, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩
    else C 2 ⟨(r : ℕ) - d 0 - d 1,
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) r.isLt⟩

/-- Total entry accessor: `ent A i j = A i j` if `(i, j)` is in range, `0` otherwise. -/
def ent {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) : R :=
  if h : i < a ∧ j < b then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- Graph form (Section 2 of the paper): for generator matrices `C` of a `(0,3k,3)`-net, with
`B_kkk = boxMatrix C (k,k,k)`, the matrix `C_c B_kkk⁻¹` has rows `0..k-1` equal to the cell
digits of coordinate `c` and rows `k..3k-1` equal to the offset digits
`∑_d Φ_cd n_d`.  `graphBlock k C c d` is the `2k × k` block `Φ_cd`: rows `r` = offset digit
`k + r` of coordinate `c`, columns `l` = level `l` (most significant first) of the cell `n_d`. -/
noncomputable def graphBlock {R : Type*} [CommRing R] (k : ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R) (c d : Fin 3) :
    Matrix (Fin (2 * k)) (Fin k) R :=
  fun r l => ent (C c * (boxMatrix C (fun _ => k))⁻¹) (k + (r : ℕ)) ((d : ℕ) * k + (l : ℕ))

/-- Generator matrix of coordinate `c` of the digital net with (arbitrary) graph form
`Φ`: rows `0..k-1` are the identity on the column block `c` (index digit `c k + i` is
level `i` of the cell `n_c`), rows `k + r` are `(Φ_{c0} | Φ_{c1} | Φ_{c2})` row `r`.
Column `j` belongs to block `j / k` (always `< 3`), level `j % k`. -/
def graphGen {R : Type*} [Zero R] [One R] (k : ℕ)
    (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) R) (c : Fin 3) :
    Matrix (Fin (3 * k)) (Fin (3 * k)) R :=
  fun i j =>
    if (i : ℕ) < k then (if (j : ℕ) = (c : ℕ) * k + (i : ℕ) then 1 else 0)
    else ent (Φ c ⟨(j : ℕ) / k, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm 3 k))⟩)
      ((i : ℕ) - k) ((j : ℕ) % k)

/-! ## The construction `𝒫_{k,q}` (Definition `def:net`) -/

/-- `τ` on `ℤ[t]_{<m}`, `(τV)(t) = (1-t)^(m-1) V(1/(1-t))`: column `l` is the coefficient
vector of `(1-t)^(m-1-l)`, so `τ_{i l} = (-1)^i · C(m-1-l, i)`. -/
def tau (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i l => (-1) ^ (i : ℕ) * ((m - 1 - (l : ℕ)).choose (i : ℕ) : ℤ)

/-- `T = s_k τ` with `s_k = (-1)^(k+1)`, on `ℤ[t]_{<3k}`. -/
def T (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  ((-1 : ℤ) ^ (k + 1)) • tau (3 * k)

/-- `K`: lower-triangular Toeplitz matrix of `(1-t)^(-k)`, `K_{ij} = C(i-j+k-1, k-1)`
for `i ≥ j`. -/
def K (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j => if j ≤ i then (((i : ℕ) - j + k - 1).choose (k - 1) : ℤ) else 0

/-- `E`: the identity except in rows `k-2, k-1, k`:
`(Ed)_{k-2} = d_0 + … + d_{k-2}`, `(Ed)_{k-1} = -d_{k-1}`, `(Ed)_k = d_{k-1} + d_k`.
(For `k = 1` row `k-2` does not exist.) -/
def E (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j =>
    if (i : ℕ) + 2 = k then (if (j : ℕ) + 2 ≤ k then 1 else 0)
    else if (i : ℕ) + 1 = k then (if j = i then -1 else 0)
    else if (i : ℕ) = k then (if (j : ℕ) + 1 = k ∨ (j : ℕ) = k then 1 else 0)
    else (if j = i then 1 else 0)

/-- The scramble `L = E K`. -/
def L (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ := E k * K k

/-- Integer generator matrices `(L T², L, L T)` of `𝒫_{k,q}` (coordinates `x, y, z`). -/
def PGen (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  ![L k * T k ^ 2, L k, L k * T k]

/-- The integer point (in `[0, q^(3k))^3`) of `𝒫_{k,q}` with index `v ∈ (ℤ/qℤ)^(3k)`;
the generator matrices are reduced mod `q`. -/
def Ppoint (q k : ℕ) (v : Fin (3 * k) → ZMod q) : Fin 3 → ℕ :=
  digPoint q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) v

/-! ## The two-digit nets `𝒬_{k,p}` (Definition `def:Q`) -/

/-- The frame `(T², I, T)`. -/
def frameGen (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  ![T k ^ 2, 1, T k]

/-- `B = Φ^F_{c,c+1}` (taken at `c = x`): graph-form block of the frame over `ℤ`. -/
noncomputable def frameB (k : ℕ) : Matrix (Fin (2 * k)) (Fin k) ℤ := graphBlock k (frameGen k) 0 1

/-- `C = Φ^F_{c,c+2}` (taken at `c = x`): graph-form block of the frame over `ℤ`. -/
noncomputable def frameC (k : ℕ) : Matrix (Fin (2 * k)) (Fin k) ℤ := graphBlock k (frameGen k) 0 2

/-- `R = I_{2k} + (k-1) E_{1,0}` (add `k-1` times row `0` to row `1`). -/
def Rmat (k : ℕ) : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ :=
  fun i j => if i = j then 1 else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then (k : ℤ) - 1 else 0

/-- `U_0 = U_{(1-t)^(k+1)}`: lower-triangular Toeplitz, `(U_0)_{ij} = (-1)^(i-j) C(k+1, i-j)`. -/
def U0 (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => if j ≤ i then (-1) ^ ((i : ℕ) - j) * ((k + 1).choose ((i : ℕ) - j) : ℤ) else 0

/-- `V`: the identity except `V_{k-1,k-1} = -1`, `V_{k-3,k-3} = -2`, `V_{k-4,k-4} = 4`,
`V_{k-3,k-4} = -2`, and `V_{k-4,j} = -1` for `j ≤ k-5` (entries with a negative index are
omitted). -/
def Vmat (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if (i : ℕ) + 1 = k ∧ (j : ℕ) + 1 = k then -1
    else if (i : ℕ) + 3 = k ∧ (j : ℕ) + 3 = k then -2
    else if (i : ℕ) + 4 = k ∧ (j : ℕ) + 4 = k then 4
    else if (i : ℕ) + 3 = k ∧ (j : ℕ) + 4 = k then -2
    else if (i : ℕ) + 4 = k ∧ (j : ℕ) + 5 ≤ k then -1
    else if i = j then 1 else 0

/-- `U_* = U_0 V`. -/
def Ustar (k : ℕ) : Matrix (Fin k) (Fin k) ℤ := U0 k * Vmat k

/-- `A_*`: the `2k × k` matrix whose only nonzero entry is `(A_*)_{0,k-1} = -1`. -/
def Astar (k : ℕ) : Matrix (Fin (2 * k)) (Fin k) ℤ :=
  fun r l => if (r : ℕ) = 0 ∧ (l : ℕ) + 1 = k then -1 else 0

/-- Circulant graph form of Definition `def:Q`, for given frame blocks `B, C`:
`Φ_cc = A_*`, `Φ_{c,c+1} = R B U_*`, `Φ_{c,c+2} = -R C U_*` (indices mod 3). -/
def QPhiOf (k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c d : Fin 3) :
    Matrix (Fin (2 * k)) (Fin k) ℤ :=
  if d = c then Astar k
  else if d = c + 1 then Rmat k * B * Ustar k
  else -(Rmat k * C * Ustar k)

/-- Integer generator matrices (graph form) of `𝒬_{k,p}`. -/
noncomputable def QGen (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  graphGen k (QPhiOf k (frameB k) (frameC k))

/-- The integer point of `𝒬_{k,p}` with index `v` (the cell digits
`(n_{x,0..k-1}, n_{y,0..k-1}, n_{z,0..k-1})`). -/
noncomputable def Qpoint (p k : ℕ) (v : Fin (3 * k) → ZMod p) : Fin 3 → ℕ :=
  digPoint p (3 * k) (fun c => (QGen k c).map (Int.cast : ℤ → ZMod p)) v

/-- The constant `c(q)` of Theorem 1:
`c(q) = √(min{(1-1/q)², (1-2/q)² + (1-4/q)², 3(1-3/q)²})`. -/
noncomputable def cP (q : ℕ) : ℝ :=
  Real.sqrt (min ((1 - 1 / (q : ℝ)) ^ 2)
    (min ((1 - 2 / (q : ℝ)) ^ 2 + (1 - 4 / (q : ℝ)) ^ 2) (3 * (1 - 3 / (q : ℝ)) ^ 2)))

/-- The constant `c*(p) = √((1-1/p)² + ((p-1)² + (p-2)²)/p⁴)` of Theorem 2. -/
noncomputable def cQ (p : ℕ) : ℝ :=
  Real.sqrt ((1 - 1 / (p : ℝ)) ^ 2 + (((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 2) ^ 2) / (p : ℝ) ^ 4)

/-- `M̃_cd`: centred representative (in `(-p/2, p/2)` for odd `p`) of the last-level
first-offset-digit entry `(Φ_cd)_{0,k-1}` of the graph form of the digital net `C`. -/
noncomputable def Mtilde {p : ℕ} (k : ℕ) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (c d : Fin 3) : ℤ :=
  (ent (graphBlock k C c d) 0 (k - 1)).valMinAbs

/-! ## `rem:lattice3`: the lattice reading of `𝒫_{k,q}` (stage 6) -/

/-- The level-`0` layer `M` of `𝒫_{k,q}` (`prop:cell`). -/
def Mcell : Matrix (Fin 3) (Fin 3) ℤ := !![-1, -1, 1; 1, -1, -1; -1, 1, -1]

/-- `I + M/q` over `ℝ`: in cell units, a patch of `𝒫_{k,q}` without wrapping geometric digits is,
up to the jitter, a piece of a translate of the lattice `Λ_q = (I + M/q) ℤ³`. -/
noncomputable def latMat (q : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + (1 / (q : ℝ)) • Mcell.map (Int.cast : ℤ → ℝ)

/-- The orthogonal projection onto the line of `u = (1,1,1)`. -/
noncomputable def projU : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun _ _ => (1 / 3 : ℝ)

/-- The rotation by the angle `θ` about the axis `u = (1,1,1)` (Rodrigues' formula with the unit
axis `u/√3`): `P + cos θ (I - P) + (sin θ / √3) [u×]`, where `[u×] = M + I`. -/
noncomputable def rotU (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  projU + Real.cos θ • (1 - projU) +
    (Real.sin θ / Real.sqrt 3) • (Mcell.map (Int.cast : ℤ → ℝ) + 1)

/-! ## `prop:faure`: the frame is the Faure–Hammersley net (stage 6) -/

/-- The upper Pascal matrix: `P_{ji} = C(i, j)` (row `j`, column `i`). -/
def pascalP (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun j i => (((i : ℕ).choose (j : ℕ) : ℕ) : ℤ)

/-- `Λ_m`: `(Λ_m)_{ij} = (-1)^(i-j) C(m-1-j, i-j)` for `i ≥ j`, `0` above the diagonal. -/
def LamF (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => if j ≤ i then (-1) ^ ((i : ℕ) - (j : ℕ)) * (((m - 1 - (j : ℕ)).choose ((i : ℕ) - (j : ℕ)) : ℕ) : ℤ)
    else 0

/-- `D_± = diag((-1)^i)`. -/
def Dpm (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := Matrix.diagonal fun i => (-1) ^ (i : ℕ)

/-- The reversal `J`: `J_{ij} = 1` iff `i + j = m - 1`. -/
def Jrev (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j => if (i : ℕ) + (j : ℕ) + 1 = m then 1 else 0

/-! ## `rem:sign`: the flipped diagonal (stage 6) -/

/-- `E` with the row `k` flipped (`rem:sign`): `(Ed)_k = -d_{k-1} + d_k` instead of
`d_{k-1} + d_k`; all other rows as in `E`. -/
def Eflip (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j =>
    if (i : ℕ) + 2 = k then (if (j : ℕ) + 2 ≤ k then 1 else 0)
    else if (i : ℕ) + 1 = k then (if j = i then -1 else 0)
    else if (i : ℕ) = k then (if (j : ℕ) + 1 = k then -1 else if (j : ℕ) = k then 1 else 0)
    else (if j = i then 1 else 0)

/-- The flipped scramble `L' = E' K`. -/
def Lflip (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ := Eflip k * K k

/-- Generator matrices `(L' T², L', L' T)` of the flipped `𝒫_{k,q}`. -/
def PGenFlip (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  ![Lflip k * T k ^ 2, Lflip k, Lflip k * T k]

/-- The integer point of the flipped `𝒫_{k,q}` with index `v`. -/
def PpointFlip (q k : ℕ) (v : Fin (3 * k) → ZMod q) : Fin 3 → ℕ :=
  digPoint q (3 * k) (fun c => (PGenFlip k c).map (Int.cast : ℤ → ZMod q)) v

/-! ## `rem:base2`: `(t, M, 3)`-nets (stage 6) -/

/-- `(t, M, 3)`-net property in base `b` of the integer points `X i ∈ [0, b^M)³` indexed by a
finite type: every elementary box with `d_c` base-`b` digits in coordinate `c`,
`d_0 + d_1 + d_2 + t = M`, contains exactly `b^t` points (counted over the index set). -/
def IsNetT {ι : Type} [Fintype ι] (b t M : ℕ) (X : ι → Fin 3 → ℕ) : Prop :=
  ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 + t = M → ∀ a : Fin 3 → ℕ, (∀ c, a c < b ^ d c) →
    (Finset.univ.filter fun i => ∀ c, X i c / b ^ (M - d c) = a c).card = b ^ t

/-! ## `def:R`: the nets `ℛ_{k,p}`, `p = 5, 7` (stage 6) -/

/-- The parameters `(a, b, s_3, v_4, w)` of `def:R`: `(-1, 2, -1, -2, 2)` for `p = 5` and
`(3, 3, 2, -1, 0)` otherwise (used for `p = 7`). -/
def Rpar (p : ℕ) : Fin 5 → ℤ := if p = 5 then ![-1, 2, -1, -2, 2] else ![3, 3, 2, -1, 0]

/-- `R_p`: the identity except row `1`: row `1` of `R_p X` is
`a · (row 1) + (a(k-1) + b) · (row 0)` of `X`. -/
def Rpm (k : ℕ) (a b : ℤ) : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ :=
  fun i j => if i = j then (if (i : ℕ) = 1 then a else 1)
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then a * ((k : ℤ) - 1) + b else 0

/-- `Γ_p`: the identity except `(k-1,k-1) ↦ -1`, `(k-1,k-2) ↦ 1`, `(k-3,k-3) ↦ s_3`,
`(k-4,k-4) ↦ v_4`, `(k-3,k-4) ↦ w`, and `(k-4,j) ↦ -1` for `j ≤ k-5` (entries with a negative
index omitted). -/
def Gamp (k : ℕ) (s3 v4 w : ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    if (i : ℕ) + 1 = k ∧ (j : ℕ) + 1 = k then -1
    else if (i : ℕ) + 1 = k ∧ (j : ℕ) + 2 = k then 1
    else if (i : ℕ) + 3 = k ∧ (j : ℕ) + 3 = k then s3
    else if (i : ℕ) + 4 = k ∧ (j : ℕ) + 4 = k then v4
    else if (i : ℕ) + 3 = k ∧ (j : ℕ) + 4 = k then w
    else if (i : ℕ) + 4 = k ∧ (j : ℕ) + 5 ≤ k then -1
    else if i = j then 1 else 0

/-- The circulant graph form of `ℛ_{k,p}`: `Φ_cc = A_*`, `Φ_{c,c+1} = R_p B U_p`,
`Φ_{c,c+2} = R_p C U_p`, `U_p = U_0 Γ_p` (no sign change on the `C`-blocks). -/
def RPhiOf (p k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c d : Fin 3) :
    Matrix (Fin (2 * k)) (Fin k) ℤ :=
  if d = c then Astar k
  else if d = c + 1 then Rpm k (Rpar p 0) (Rpar p 1) * B * (U0 k * Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4))
  else Rpm k (Rpar p 0) (Rpar p 1) * C * (U0 k * Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4))

/-- Integer generator matrices (graph form) of `ℛ_{k,p}`. -/
noncomputable def RGen (p k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  graphGen k (RPhiOf p k (frameB k) (frameC k))

/-- The integer point of `ℛ_{k,p}` with index `v` (over `𝔽_p`). -/
noncomputable def Rpoint (p k : ℕ) (v : Fin (3 * k) → ZMod p) : Fin 3 → ℕ :=
  digPoint p (3 * k) (fun c => (RGen p k c).map (Int.cast : ℤ → ZMod p)) v

/-- The table of `cor:Rrows`, row `0`, by relative position `rel = d - c` and the distance
`c = k-1-l` of the level from the last one. -/
def tabR0 (rel : Fin 3) (c : ℕ) : ℤ :=
  if rel = 2 then (if c = 0 then 1 else if c = 1 then -1 else 0) else (if c = 0 then -1 else 0)

/-- The table of `cor:Rrows`, row `1` (`p = 5` and `p = 7`). -/
def tabR1 (p : ℕ) (rel : Fin 3) (c : ℕ) : ℤ :=
  if rel = 0 then 0
  else if p = 5 then
    (if rel = 1 then (if c = 0 then -2 else if c = 1 then 1 else if c = 2 then 1 else if c = 3 then -2 else 0)
     else (if c = 0 then -2 else if c = 1 then 1 else if c = 2 then 1 else 0))
  else
    (if rel = 1 then (if c = 0 then -3 else if c = 1 then -3 else if c = 2 then -1 else 0)
     else (if c = 1 then 3 else if c = 2 then -1 else if c = 3 then -3 else 0))

end Z3Net
