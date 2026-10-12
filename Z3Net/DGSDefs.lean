/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmADefs
public import Z3Net.DShiftDefs
public import Z3Net.Defs

@[expose] public section

/-!
# Definitions for `sec:dgs`: digitally shifted nets of Theorem A, and the notions of Dick, Goda and Suzuki

V14 stage S10′.

* `Z3NetA.AGen`: the generator matrices of the net `𝒫^{U*_s}_{k,q}` of `thm:A` (`Apoint` is the digital
  point set of `AGen`, `Z3NetA.Proofs.Apoint_eq_AGen`), so that its digital shifts are
  `digPointShift q (s k) (AGen s q k) τ` (`def:dshift`).
* Namespace `Z3NetDGS`: the definitions of [DGS2] = J. Dick, T. Goda, K. Suzuki, *Quasi-uniform
  digital nets and sequences II* (arXiv:2501.18226v2), transcribed for a base `b ≥ 2` (an integer),
  dimension `d`, point sets `P ⊂ [0,1)^d` given as `Finset (Fin d → ℝ)`.
-/

namespace Z3NetA

open Matrix Finset Z3NetF

open Classical in
/-- The generator matrices over `ℤ/qℤ` of the net `𝒫^{U*_s}_{k,q}` of `thm:A` (`Apoint`): those of the
net of `def:Ns` over `R_S` reduced modulo `q` by a ring homomorphism `R_S → ℤ/qℤ` (the zero matrices
if there is none; `Apoint` uses the same junk value). -/
noncomputable def AGen (s q k : ℕ) [NeZero s] : Fin s → Matrix (Fin (s * k)) (Fin (s * k)) (ZMod q) :=
  if h : Nonempty (RS s →+* ZMod q) then
    let ψ : RS s →+* ZMod q := Classical.choice h
    fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c).map ψ
  else 0

end Z3NetA

namespace Z3NetDGS

open Finset Matrix

/-! ## The definitions of Dick, Goda and Suzuki [DGS2] -/

section defs

variable {d : ℕ}

/-- [DGS2, §2.3] the toroidal distance of two coordinates `a, b ∈ [0,1)`: `min(|a - b|, 1 - |a - b|)`. -/
noncomputable def torCoord (a b : ℝ) : ℝ := min |a - b| (1 - |a - b|)

/-- [DGS2, §2.3] the toroidal Euclidean distance `‖x - y‖_{2,T} = (∑_j min(|x_j - y_j|, 1 - |x_j - y_j|)²)^{1/2}`. -/
noncomputable def torDist2 (x y : Fin d → ℝ) : ℝ := Real.sqrt (∑ j, torCoord (x j) (y j) ^ 2)

/-- [DGS2, §2.3] the toroidal maximum-norm distance `‖x - y‖_{∞,T} = max_j min(|x_j - y_j|, 1 - |x_j - y_j|)`
(`0` for `d = 0`). -/
noncomputable def torDistInf (x y : Fin d → ℝ) : ℝ := ⨆ j, torCoord (x j) (y j)

/-- [DGS2, §2.2] the maximum-norm distance `‖x - y‖_∞ = max_j |x_j - y_j|` (`0` for `d = 0`). -/
noncomputable def distInf (x y : Fin d → ℝ) : ℝ := ⨆ j, |x j - y j|

/-- [DGS2, §2.2] the covering radius `h(P) = sup_{x ∈ [0,1]^d} min_{y ∈ P} dist(x, y)` for a distance `dist`
(`dist = distInf`: `h_∞`; `dist = torDistInf`: `h_{∞,T}`). -/
noncomputable def covRad (dist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (P : Finset (Fin d → ℝ)) : ℝ :=
  ⨆ x : {x : Fin d → ℝ // ∀ j, 0 ≤ x j ∧ x j ≤ 1}, ⨅ y : P, dist x.1 y.1

/-- [DGS2, §2.2] the separation radius `q(P) = min_{x, y ∈ P, x ≠ y} dist(x, y) / 2`. -/
noncomputable def sepRad (dist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (P : Finset (Fin d → ℝ)) : ℝ :=
  ⨅ xy : {xy : (Fin d → ℝ) × (Fin d → ℝ) // xy.1 ∈ P ∧ xy.2 ∈ P ∧ xy.1 ≠ xy.2}, dist xy.1.1 xy.1.2 / 2

/-- [DGS2, §2.2] the mesh ratio `ρ(P) = h(P) / q(P)`. -/
noncomputable def meshRatio (dist : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (P : Finset (Fin d → ℝ)) : ℝ :=
  covRad dist P / sepRad dist P

/-- [DGS2, Def. 3.1] the `b`-adic elementary interval `J_{c,a} = ∏_j [a_j b^{-c_j}, (a_j + 1) b^{-c_j})`. -/
def elemInt (b : ℕ) (c a : Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ j, (a j : ℝ) / (b : ℝ) ^ c j ≤ x j ∧ x j < ((a j : ℝ) + 1) / (b : ℝ) ^ c j}

/-- [DGS2, Def. 3.1] `Q ⊂ [0,1)^d` with `N = b^m` points is a `(t,m,d)`-net in base `b` if exactly `b^t`
points of `Q` lie in each of the `b^{m-t}` elementary intervals `J_{c,a}` (`0 ≤ a_j < b^{c_j}`), for every
`c` with `c_1 + ⋯ + c_d = m - t`. -/
def IsTMSNet (b t m : ℕ) (Q : Finset (Fin d → ℝ)) : Prop :=
  (∀ x ∈ Q, ∀ j, 0 ≤ x j ∧ x j < 1) ∧ Q.card = b ^ m ∧
    ∀ c : Fin d → ℕ, ∑ j, c j = m - t → ∀ a : Fin d → ℕ, (∀ j, a j < b ^ c j) →
      ((Q : Set (Fin d → ℝ)) ∩ elemInt b c a).ncard = b ^ t

/-- [DGS2, Def. 3.2] the shifted `b`-adic elementary interval
`J_{c,a,e} = ∏_j [(a_j - e_j/b) b^{-c_j}, (a_j + (b - e_j)/b) b^{-c_j})`. -/
def shiftedInt (b : ℕ) (c a e : Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ j, ((a j : ℝ) - (e j : ℝ) / b) / (b : ℝ) ^ c j ≤ x j ∧
    x j < ((a j : ℝ) + ((b : ℝ) - e j) / b) / (b : ℝ) ^ c j}

/-- [DGS2, Def. 3.2] `A mod 1 = {x ∈ [0,1) : ∃ z ∈ ℤ, x + z ∈ A}` for `A ⊂ ℝ`. -/
def modOne (A : Set ℝ) : Set ℝ := {x | 0 ≤ x ∧ x < 1 ∧ ∃ z : ℤ, x + z ∈ A}

/-- [DGS2, Def. 3.2] the shifted toroidal elementary interval
`J̃_{c,a,e} = ∏_j [(a_j - e_j/b) b^{-c_j}, (a_j + (b - e_j)/b) b^{-c_j}) mod 1` (`mod 1` taken factor by factor). -/
def shiftedIntTor (b : ℕ) (c a e : Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ j, x j ∈ modOne (Set.Ico (((a j : ℝ) - (e j : ℝ) / b) / (b : ℝ) ^ c j)
    (((a j : ℝ) + ((b : ℝ) - e j) / b) / (b : ℝ) ^ c j))}

/-- [DGS2, Def. 3.3] `P` is `c`-separated in base `b`: every shifted elementary interval `J_{c,a,e}`
(`0 ≤ a_j ≤ b^{c_j}`, `e_j ∈ {0, …, b-1}`) contains at most one point of `P`. -/
def IsSep (b : ℕ) (c : Fin d → ℕ) (P : Finset (Fin d → ℝ)) : Prop :=
  ∀ a e : Fin d → ℕ, (∀ j, a j ≤ b ^ c j) → (∀ j, e j < b) →
    ((P : Set (Fin d → ℝ)) ∩ shiftedInt b c a e).Subsingleton

/-- [DGS2, Def. 3.3] `P` is toroidally `c`-separated in base `b`: every shifted toroidal elementary
interval `J̃_{c,a,e}` (`0 ≤ a_j < b^{c_j}`, `e_j ∈ {0, …, b-1}`) contains at most one point of `P`. -/
def IsSepTor (b : ℕ) (c : Fin d → ℕ) (P : Finset (Fin d → ℝ)) : Prop :=
  ∀ a e : Fin d → ℕ, (∀ j, a j < b ^ c j) → (∀ j, e j < b) →
    ((P : Set (Fin d → ℝ)) ∩ shiftedIntTor b c a e).Subsingleton

/-- [DGS2, Def. 3.3] `κ`-separated: `(κ, …, κ)`-separated. -/
def IsKSep (b κ : ℕ) (P : Finset (Fin d → ℝ)) : Prop := IsSep b (fun _ => κ) P

/-- [DGS2, Def. 3.3] toroidally `κ`-separated: toroidally `(κ, …, κ)`-separated. -/
def IsKSepTor (b κ : ℕ) (P : Finset (Fin d → ℝ)) : Prop := IsSepTor b (fun _ => κ) P

/-- [DGS2, Def. 3.8] `(Q_m)_{m ∈ I}`, `I ⊆ ℕ` infinite, `Q_m` a `(t,m,d)`-net in base `b`, is a
well-separated family on `I`: `Q_m` is `κ_m`-separated with `κ_m ≤ m/d + O(1)`. -/
def WellSepFamily (b t d : ℕ) (I : Set ℕ) (Q : ℕ → Finset (Fin d → ℝ)) : Prop :=
  I.Infinite ∧ (∀ m ∈ I, IsTMSNet b t m (Q m)) ∧
    ∃ κ : ℕ → ℕ, ∃ C : ℝ, ∀ m ∈ I, IsKSep b (κ m) (Q m) ∧ (κ m : ℝ) ≤ (m : ℝ) / d + C

/-- [DGS2, Def. 3.8] toroidally well-separated family: the same with toroidal `κ_m`-separation. -/
def WellSepFamilyTor (b t d : ℕ) (I : Set ℕ) (Q : ℕ → Finset (Fin d → ℝ)) : Prop :=
  I.Infinite ∧ (∀ m ∈ I, IsTMSNet b t m (Q m)) ∧
    ∃ κ : ℕ → ℕ, ∃ C : ℝ, ∀ m ∈ I, IsKSepTor b (κ m) (Q m) ∧ (κ m : ℝ) ≤ (m : ℝ) / d + C

/-- [DGS2, Def. 2.1] the digit vector `n⃗ = (n_0, …, n_{m-1})` of `n = n_0 + n_1 b + ⋯ + n_{m-1} b^{m-1}`. -/
def dgsVec (b m n : ℕ) : Fin m → ZMod b := fun i => ((n / b ^ (i : ℕ) % b : ℕ) : ZMod b)

/-- [DGS2, Defs. 2.1, 2.2] the point `x_n ⊕ δ` of the digitally shifted digital net `Q(F_1, …, F_d) ⊕ δ`
over `𝔽_b`: coordinate `j` has the digits `y_{n,j,i} = (F_j n⃗)_i + δ_{j,i}` (modulo `b`), `x = ∑_i y_i b^{-i}`
(`i = 1, …, m`; Lean index `i - 1`); `δ_j = ∑_i δ_{j,i} b^{-i}` is given by its digits. `δ = 0`: Def. 2.1. -/
noncomputable def dgsPoint (b m : ℕ) (F : Fin d → Matrix (Fin m) (Fin m) (ZMod b))
    (δ : Fin d → Fin m → ZMod b) (n : ℕ) : Fin d → ℝ :=
  fun j => ∑ i : Fin m, (((F j *ᵥ dgsVec b m n) i + δ j i).val : ℝ) / (b : ℝ) ^ ((i : ℕ) + 1)

/-- [DGS2, Defs. 2.1, 2.2] `Q(F_1, …, F_d) ⊕ δ = {x_0 ⊕ δ, …, x_{b^m - 1} ⊕ δ}`. -/
noncomputable def dgsNet (b m : ℕ) (F : Fin d → Matrix (Fin m) (Fin m) (ZMod b))
    (δ : Fin d → Fin m → ZMod b) : Finset (Fin d → ℝ) :=
  (Finset.range (b ^ m)).image (dgsPoint b m F δ)

/-- The real point `X_v / q^m ∈ [0,1)^d` of integer points `X_v ∈ [0, q^m)^d`. -/
noncomputable def ptReal {m : ℕ} (q : ℕ) (X : (Fin m → ZMod q) → Fin d → ℕ) (v : Fin m → ZMod q) :
    Fin d → ℝ :=
  fun c => (X v c : ℝ) / (q : ℝ) ^ m

/-- The point set `{X_v / q^m}` of integer points `X_v` at scale `q^m`. -/
noncomputable def ptSet {m : ℕ} (q : ℕ) [NeZero q] (X : (Fin m → ZMod q) → Fin d → ℕ) : Finset (Fin d → ℝ) :=
  Finset.univ.image (ptReal q X)

/-- `κ_m = ⌈m/s + log_q(√s/c)⌉` of `cor:dgs` (as a natural number; it is `≥ 1` whenever the net has two
points; `dgs_main`). -/
noncomputable def kappaM (s q : ℕ) (c : ℝ) (m : ℕ) : ℕ :=
  (⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉).toNat

/-- The generator matrices over `ℤ/qℤ` of the net `𝒫_{k,q}` of `thm:main` (`Z3Net.Ppoint q k` is its digital
point set). -/
abbrev PGenZ (q k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod q) :=
  fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod q)

end defs

end Z3NetDGS
