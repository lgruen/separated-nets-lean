/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DShiftDefs

@[expose] public section

/-!
# Definitions: bases two and three, the deep-shift lift (`sec:base23`), V14 stage S14′

* Digit vectors: `dval` (the integer of a digit vector, digit `0` most significant; coordinate `c` of
  `Z3NetF.digPointShift b m C τ v` is `dval b (C c *ᵥ v + τ c)`), `topD` (the first `H` digits).
* `def:lift`: the pair projections `pairSub C c c'` (`P_cc'`), `Zsub b M e` (`Z_e`), `Admissible` (the
  conditions `λ^{cc'}_e(s) ≠ 0`, written as `s ∉ P_cc' ⊔ Z_e = H_e = ker λ^{cc'}_e`), `VanishTop` (vanishing on the
  first `D` digits of each coordinate), the lift `liftGen` / `liftShift` (`L_D(P)`, index `(n, α, δ₁, δ₂)`), and
  `LiftChain` (a chain of lifts with depth parameters `D ℓ`).
* `lem:liftsep`: `vstar` (`v*_L`), `gL` (`g_L`).
* `lem:shiftcert` (the every-shift lemma of the research notes with the fixes F1–F4 of
  the research notes): `muD` (`μ_n`), `hW` (`t ↦ max(0, t − 1)²`), `vcirc` (`v°_L`; distinct points,
  `Δ = 0` allowed with weight `0`: fix F1).
* Code-level digit vectors (for the kernel certificates and the explicit data): `vecOf` (a natural number read as
  a digit vector), `colMat` (generator matrices from column codes), `liftCols` (the lift on column codes),
  `seedCols` (the seeds `(I, A_y, A_z)` of `tab:b23seeds` from their printed row integers).
-/

namespace Z3NetB23

open Matrix

/-! ## Digit vectors -/

/-- The integer with digit vector `x ∈ (ℤ/bℤ)^n`, digit `0` most significant:
`∑_j val(x_j) b^(n-1-j)`. Coordinate `c` of `Z3NetF.digPointShift b m C τ v` is `dval b (C c *ᵥ v + τ c)`. -/
def dval (b : ℕ) {n : ℕ} (x : Fin n → ZMod b) : ℕ :=
  ∑ j : Fin n, (x j).val * b ^ (n - 1 - (j : ℕ))

/-- The first `H` digits of a digit vector (`H ≤ n`). -/
def topD {R : Type*} {n : ℕ} (H : ℕ) (hH : H ≤ n) (x : Fin n → R) : Fin H → R :=
  fun r => x (Fin.castLE hH r)

/-- `t ↦ max(0, t − 1)²` (truncated subtraction). -/
def hW (t : ℕ) : ℕ := (t - 1) ^ 2

/-- **`lem:shiftcert`**: `μ_n(δ)`, the least toroidal distance `|X' − X|_{b^n}` over the integers `X ∈ [0, b^n)`
(here: over their digit vectors `X`), where `X'` has the digits of `X` plus `δ`, digit by digit modulo `b`. -/
noncomputable def muD (b : ℕ) [NeZero b] {n : ℕ} (δ : Fin n → ZMod b) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun X : Fin n → ZMod b =>
    Z3NetF.cres (b ^ n) ((dval b (X + δ) : ℤ) - (dval b X : ℤ))

/-! ## `def:lift` -/

/-- `Z_e ⊆ (ℤ/bℤ)^M × (ℤ/bℤ)^M`: the vectors that vanish on the first `e` digits of the first component (`c`)
and on the first `M + 1 − e` digits of the second (`c'`). -/
def Zsub (b M e : ℕ) : Submodule (ZMod b) ((Fin M → ZMod b) × (Fin M → ZMod b)) where
  carrier := {u | (∀ j : Fin M, (j : ℕ) < e → u.1 j = 0) ∧ ∀ j : Fin M, (j : ℕ) < M + 1 - e → u.2 j = 0}
  add_mem' := by
    intro u v hu hv
    exact ⟨fun j hj => by simp [hu.1 j hj, hv.1 j hj], fun j hj => by simp [hu.2 j hj, hv.2 j hj]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  smul_mem' := by
    intro a u hu
    exact ⟨fun j hj => by simp [hu.1 j hj], fun j hj => by simp [hu.2 j hj]⟩

/-- `P_cc' = {(C_c n, C_c' n) : n}`, an `M`-dimensional subspace of `(ℤ/bℤ)^M × (ℤ/bℤ)^M` (the digit vectors of
the pair `(c, c')` of coordinates of the unshifted net). -/
def pairSub {b M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (c c' : Fin 3) :
    Submodule (ZMod b) ((Fin M → ZMod b) × (Fin M → ZMod b)) :=
  LinearMap.range ((C c).mulVecLin.prod (C c').mulVecLin)

/-- **`def:lift`, admissibility**: for every `1 ≤ e ≤ M`, `λ^{yz}_e(s_A^{yz}) ≠ 0`, `λ^{xy}_e(s_B^{xy}) ≠ 0` and
`λ^{xz}_e((s_B − s_A)^{xz}) ≠ 0`, where `λ^{cc'}_e` is a nonzero functional with kernel `H_e = P_cc' ⊕ Z_e`; that
is, the restriction `s^{cc'}` is not in `P_cc' ⊔ Z_e`. Coordinates `x, y, z` are `0, 1, 2`. -/
def Admissible {b M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (sA sB : Fin 3 → Fin M → ZMod b) :
    Prop :=
  ∀ e : ℕ, 1 ≤ e → e ≤ M →
    (sA 1, sA 2) ∉ pairSub C 1 2 ⊔ Zsub b M e ∧
    (sB 0, sB 1) ∉ pairSub C 0 1 ⊔ Zsub b M e ∧
    (sB 0 - sA 0, sB 2 - sA 2) ∉ pairSub C 0 2 ⊔ Zsub b M e

/-- The shift vectors `s` vanish on the first `D` digits of each coordinate (`def:lift`). -/
def VanishTop {b M : ℕ} (D : ℕ) (s : Fin 3 → Fin M → ZMod b) : Prop :=
  ∀ (c : Fin 3) (j : Fin M), (j : ℕ) < D → s c j = 0

/-- Row `0` (the top digit) of coordinate `c` of the lift, as a coefficient of the index entry `j`
(`α = M`, `δ₁ = M + 1`, `δ₂ = M + 2`): `x: α`, `y: α + δ₁`, `z: α + δ₁ + δ₂`. -/
def liftTop {b : ℕ} (M : ℕ) (c : Fin 3) (j : ℕ) : ZMod b :=
  if (c : ℕ) = 0 then (if j = M then 1 else 0)
  else if (c : ℕ) = 1 then (if j = M ∨ j = M + 1 then 1 else 0)
  else (if j = M ∨ j = M + 1 ∨ j = M + 2 then 1 else 0)

/-- The two jitter rows (`t = 0`: row `M + 1`, `t = 1`: row `M + 2`) of coordinate `c` of the lift, as coefficients
of the index entry `j`: `x: (δ₂, δ₁)`, `y: (δ₁ + δ₂, δ₁)`, `z: (δ₁, δ₂)`. -/
def liftJit {b : ℕ} (M : ℕ) (c : Fin 3) (t j : ℕ) : ZMod b :=
  if (c : ℕ) = 0 then (if t = 0 then (if j = M + 2 then 1 else 0) else (if j = M + 1 then 1 else 0))
  else if (c : ℕ) = 1 then
    (if t = 0 then (if j = M + 1 ∨ j = M + 2 then 1 else 0) else (if j = M + 1 then 1 else 0))
  else (if t = 0 then (if j = M + 1 then 1 else 0) else (if j = M + 2 then 1 else 0))

/-- **`def:lift`, the generator matrices of `L_D(P)`**: index `(n, α, δ₁, δ₂) ∈ (ℤ/bℤ)^(M+3)` (entries `0 … M-1`,
`M`, `M + 1`, `M + 2`); coordinate `c` has the `M + 3` digits `top | (C_c n + δ₁ s_A + δ₂ s_B)_c | 2 jitter digits`
with `x: α | … | δ₂, δ₁`, `y: α + δ₁ | … | δ₁ + δ₂, δ₁`, `z: α + δ₁ + δ₂ | … | δ₁, δ₂`. The depth `D` enters only
through `VanishTop D sA`, `VanishTop D sB`. -/
def liftGen {b M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (sA sB : Fin 3 → Fin M → ZMod b) :
    Fin 3 → Matrix (Fin (M + 3)) (Fin (M + 3)) (ZMod b) := fun c r j =>
  if hr : (r : ℕ) = 0 then liftTop M c j
  else if hr' : (r : ℕ) ≤ M then
    if hj : (j : ℕ) < M then C c ⟨(r : ℕ) - 1, by omega⟩ ⟨j, hj⟩
    else if (j : ℕ) = M + 1 then sA c ⟨(r : ℕ) - 1, by omega⟩
    else if (j : ℕ) = M + 2 then sB c ⟨(r : ℕ) - 1, by omega⟩
    else 0
  else liftJit M c ((r : ℕ) - (M + 1)) j

/-- **`def:lift`, the shift of `L_D(P)`**: the shift `σ` of `P` embedded in the block digits (top and jitter `0`). -/
def liftShift {b M : ℕ} (σ : Fin 3 → Fin M → ZMod b) : Fin 3 → Fin (M + 3) → ZMod b := fun c r =>
  if h : 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ M then σ c ⟨(r : ℕ) - 1, by omega⟩ else 0

/-- A deep-shift chain from the digitally shifted digital net `(C₀, σ₀)` at level `L`: the lift from level `ℓ`
uses shifts vanishing on the first `D ℓ` digits (`sec:base23`, "deep-shift chain"; admissibility is not part of
this predicate, see `AdmChain`). -/
inductive LiftChain (b L : ℕ) (C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (σ₀ : Fin 3 → Fin L → ZMod b)
    (D : ℕ → ℕ) : (m : ℕ) → (Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)) → (Fin 3 → Fin m → ZMod b) → Prop
  | refl : LiftChain b L C₀ σ₀ D L C₀ σ₀
  | step {ℓ : ℕ} {C : Fin 3 → Matrix (Fin ℓ) (Fin ℓ) (ZMod b)} {σ : Fin 3 → Fin ℓ → ZMod b}
      (sA sB : Fin 3 → Fin ℓ → ZMod b) :
      LiftChain b L C₀ σ₀ D ℓ C σ → VanishTop (D ℓ) sA → VanishTop (D ℓ) sB →
      LiftChain b L C₀ σ₀ D (ℓ + 3) (liftGen C sA sB) (liftShift σ)

/-! ## `lem:liftsep` and `lem:shiftcert` -/

/-- **`v*_L`** (before `lem:liftsep`): for the digitally shifted digital net `P_L` with generator matrices `C` and
shift `σ` (points `X = digPointShift b L C σ`), `K = b^⌊L/2⌋`, `W = b^(L - ⌊L/2⌋)`, `k_c = ⌊X_c / W⌋` (the integer of
the top `⌊L/2⌋` digits): `min_{p ≠ p'} ∑_c max(0, |k_c(p) − k_c(p')|_K − 1)²` (minimum over pairs of distinct
indices). -/
noncomputable def vstar (b L : ℕ) (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (σ : Fin 3 → Fin L → ZMod b) :
    ℕ :=
  ⨅ p : {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2},
    ∑ c : Fin 3, hW (Z3NetF.cres (b ^ (L / 2))
      (((Z3NetF.digPointShift b L C σ p.1.1 c / b ^ (L - L / 2) : ℕ) : ℤ) -
        ((Z3NetF.digPointShift b L C σ p.1.2 c / b ^ (L - L / 2) : ℕ) : ℤ)))

/-- **`g_L = W √(v*_L) b^(-2L/3)`** (before `lem:liftsep`), for a value `v` of `v*_L`. -/
noncomputable def gL (b L v : ℕ) : ℝ :=
  (b : ℝ) ^ (L - L / 2) * Real.sqrt v * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))

/-- **`v°_L`** (`lem:shiftcert`(a), with fix F1): `min_Δ ∑_c max(0, μ_⌊L/2⌋(Δ_c) − 1)²` over the differences
`Δ = (top ⌊L/2⌋ digits of C_c (n' − n))_c` of two distinct points of `P_L` (`Δ = 0` allowed; then the weight
is `0`). -/
noncomputable def vcirc (b L : ℕ) [NeZero b] (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) : ℕ :=
  ⨅ p : {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2},
    ∑ c : Fin 3, hW (muD b (topD (L / 2) (Nat.div_le_self L 2) (C c *ᵥ (p.1.2 - p.1.1))))

/-! ## Code-level digit vectors and generator matrices -/

/-- A natural number `x` read as a digit vector of length `n` in base `b` (digit `0` most significant): digit `j`
is `⌊x / b^(n-1-j)⌋ mod b`. For `x < b^n`, `dval b (vecOf b n x) = x`. -/
def vecOf (b n x : ℕ) : Fin n → ZMod b := fun j => (((x / b ^ (n - 1 - (j : ℕ))) % b : ℕ) : ZMod b)

/-- Generator matrices from column codes: entry `(r, i)` of coordinate `c` is digit `r` of the code
`(cols.getD c []).getD i 0` (a digit vector of length `n`). -/
def colMat (b n : ℕ) (cols : List (List ℕ)) : Fin 3 → Matrix (Fin n) (Fin n) (ZMod b) :=
  fun c r i => vecOf b n ((cols.getD c []).getD i 0) r

/-- A shift from codes: coordinate `c` is the digit vector of `sh.getD c 0`. -/
def shOf (b n : ℕ) (sh : List ℕ) : Fin 3 → Fin n → ZMod b := fun c => vecOf b n (sh.getD c 0)

/-- **`def:lift` on column codes**: the column codes of `L_D(P)` from those of `P` (level `M`) and the codes of
`s_A`, `s_B` (one per coordinate): an old column `u` becomes `u b²` (top digit `0`, jitter `0`); the column of `α`
is `b^(M+2)` in every coordinate; those of `δ₁`, `δ₂` carry the top, block (`s_A`, `s_B`) and jitter digits of
`def:lift`. -/
def liftCols (b M : ℕ) (cols : List (List ℕ)) (sA sB : List ℕ) : List (List ℕ) :=
  let T := b ^ (M + 2)
  let q := b ^ 2
  [((cols.getD 0 []).map (· * q)) ++ [T, sA.getD 0 0 * q + 1, sB.getD 0 0 * q + b],
   ((cols.getD 1 []).map (· * q)) ++ [T, T + sA.getD 1 0 * q + b + 1, sB.getD 1 0 * q + b],
   ((cols.getD 2 []).map (· * q)) ++ [T, T + sA.getD 2 0 * q + b, T + sB.getD 2 0 * q + 1]]

/-- The shift of the lift on codes: `σ_c b²`. -/
def liftShCode (b : ℕ) (sh : List ℕ) : List ℕ := sh.map (· * b ^ 2)

/-- Digit `i` (of `M`, digit `0` most significant) of the code `x`. -/
def digAt (b M x i : ℕ) : ℕ := (x / b ^ (M - 1 - i)) % b

/-- **`tab:b23seeds`, the seed on column codes**: the generator matrices `(I, A_y, A_z)` at level `M`, where row
`d` of `A_y` is printed as the integer `rowsY[d] = ∑_j (A_y)_{dj} b^(M-1-j)`; column `i` of `A_y` is the code
`∑_d (A_y)_{di} b^(M-1-d)`. -/
def seedCols (b M : ℕ) (rowsY rowsZ : List ℕ) : List (List ℕ) :=
  [(List.range M).map (fun i => b ^ (M - 1 - i)),
   (List.range M).map (fun i => ((List.range M).map (fun d => digAt b M (rowsY.getD d 0) i * b ^ (M - 1 - d))).sum),
   (List.range M).map (fun i => ((List.range M).map (fun d => digAt b M (rowsZ.getD d 0) i * b ^ (M - 1 - d))).sum)]

/-- The matrix with printed row integers `rows` (row `d` is the digit vector of `rows[d]`, `M` digits). -/
def rowMat (b M : ℕ) (rows : List ℕ) : Matrix (Fin M) (Fin M) (ZMod b) :=
  fun d i => vecOf b M (rows.getD d 0) i

end Z3NetB23
