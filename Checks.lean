module
public import Z3Net.Defs

@[expose] public section

/-!
# Fidelity checks for the Challenge definitions (NOT part of the default build; no `#eval`)

Build with `lake build Checks`, or run `lake env lean Checks.lean`.

* `frameBoxInv*`: exact integer inverses of the `(k,k,k)` box matrix of the frame
  `(T², I, T)` (printed by `scripts/frame_box_inverse.py`); the Lean kernel re-checks
  `box * inverse = 1`, so `(boxMatrix (frameGen k) (k,k,k))⁻¹ = frameBoxInv k` is a theorem.
  This makes the (noncomputable) `QGen k` equal to a computable twin `QGen' k`.
* Kernel-checked (`decide +kernel`) points of `𝒫_{1,5}`, `𝒫_{2,5}`, `𝒬_{2,11}` against the
  explicit tables of Appendix `app:mats` of the paper.
* `ChecksCpp.lean` (generated): kernel-checked equality of the generator matrices mod `q`
  with the C++ reference `cpp/genz3net.h` (research repository) for many `(q, k)`.
-/

namespace Z3Net.Checks

open Z3Net Matrix

/-- Base-`q` digits of the index `i`, least significant first (the paper's index convention). -/
def idx (q m i : ℕ) : Fin m → ZMod q := fun l => (((i / q ^ (l : ℕ)) % q : ℕ) : ZMod q)

/-! ## `𝒫_{k,q}`: kernel-checked points of Appendix `app:mats` -/

-- 𝒫_{1,5}: i = 0, 1, 7, 31, 62, 124
example : Ppoint 5 1 (idx 5 3 1) = ![1, 111, 100] := by decide +kernel
example : Ppoint 5 1 (idx 5 3 7) = ![22, 78, 55] := by decide +kernel
example : Ppoint 5 1 (idx 5 3 31) = ![121, 118, 66] := by decide +kernel
example : Ppoint 5 1 (idx 5 3 62) = ![92, 81, 107] := by decide +kernel
example : Ppoint 5 1 (idx 5 3 124) = ![34, 37, 89] := by decide +kernel
-- 𝒫_{2,5}: i = 1, 9, 100, 1000, 12345, 15624
example : Ppoint 5 2 (idx 5 6 1) = ![4, 5101, 13775] := by decide +kernel
example : Ppoint 5 2 (idx 5 6 9) = ![7, 13624, 850] := by decide +kernel
example : Ppoint 5 2 (idx 5 6 100) = ![25, 586, 4250] := by decide +kernel
example : Ppoint 5 2 (idx 5 6 1000) = ![1150, 86, 4249] := by decide +kernel
example : Ppoint 5 2 (idx 5 6 12345) = ![11574, 652, 12483] := by decide +kernel
example : Ppoint 5 2 (idx 5 6 15624) = ![13620, 14504, 5107] := by decide +kernel

-- the integer matrices L = E K and T of Appendix `app:mats` for k = 2
example : L 2 = !![1, 0, 0, 0, 0, 0; -2, -1, 0, 0, 0, 0; 5, 3, 1, 0, 0, 0;
    4, 3, 2, 1, 0, 0; 5, 4, 3, 2, 1, 0; 6, 5, 4, 3, 2, 1] := by decide +kernel
example : T 2 = !![-1, -1, -1, -1, -1, -1; 5, 4, 3, 2, 1, 0; -10, -6, -3, -1, 0, 0;
    10, 4, 1, 0, 0, 0; -5, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0] := by decide +kernel
example : T 2 ^ 2 = !![0, 0, 0, 0, 0, 1; 0, 0, 0, 0, -1, -5; 0, 0, 0, 1, 4, 10;
    0, 0, -1, -3, -6, -10; 0, 1, 2, 3, 4, 5; -1, -1, -1, -1, -1, -1] := by decide +kernel
example : L 1 = !![-1, 0, 0; 2, 1, 0; 1, 1, 1] := by decide +kernel
-- T³ = 1 (paper Sec. 3) for small k
example : T 1 ^ 3 = 1 := by decide +kernel
example : T 2 ^ 3 = 1 := by decide +kernel
example : T 3 ^ 3 = 1 := by decide +kernel

/-! ## `𝒬_{k,p}`: computable twin via the exact frame box inverse -/

-- k = 2, 3, 4 (from scripts/frame_box_inverse.py)
def frameBoxInv2 : Matrix (Fin (3 * 2)) (Fin (3 * 2)) ℤ := !![0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; -3, -1, -3, -2, 2, 1; 7, 2, 2, 1, -3, -1; -5, -1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]
def frameBoxInv3 : Matrix (Fin (3 * 3)) (Fin (3 * 3)) ℤ := !![0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0; -10, -4, -1, -10, -6, -3, 6, 3, 1; 35, 13, 3, 15, 8, 3, -15, -7, -2; -46, -15, -3, -6, -3, -1, 10, 4, 1; 28, 7, 1, 0, 0, 0, 0, 0, 0; -8, -1, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0]
def frameBoxInv4 : Matrix (Fin (3 * 4)) (Fin (3 * 4)) ℤ := !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; -35, -15, -5, -1, -35, -20, -10, -4, 20, 10, 4, 1; 161, 66, 21, 4, 84, 45, 20, 6, -70, -34, -13, -3; -301, -115, -34, -6, -70, -36, -15, -4, 84, 39, 14, 3; 295, 100, 26, 4, 20, 10, 4, 1, -35, -15, -5, -1; -165, -45, -9, -1, 0, 0, 0, 0, 0, 0, 0, 0; 55, 10, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; -11, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem frameBox_inv2 : (boxMatrix (frameGen 2) (fun _ => 2))⁻¹ = frameBoxInv2 :=
  Matrix.inv_eq_right_inv (by decide +kernel)
theorem frameBox_inv3 : (boxMatrix (frameGen 3) (fun _ => 3))⁻¹ = frameBoxInv3 :=
  Matrix.inv_eq_right_inv (by decide +kernel)
theorem frameBox_inv4 : (boxMatrix (frameGen 4) (fun _ => 4))⁻¹ = frameBoxInv4 :=
  Matrix.inv_eq_right_inv (by decide +kernel)

/-- Computable twin of `graphBlock` given the inverse box matrix. -/
def graphBlockWith (k : ℕ) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ)
    (Binv : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) (c d : Fin 3) : Matrix (Fin (2 * k)) (Fin k) ℤ :=
  fun r l => ent (C c * Binv) (k + (r : ℕ)) ((d : ℕ) * k + (l : ℕ))

/-- Computable twin of `QGen` given the inverse frame box matrix. -/
def QGen' (k : ℕ) (Binv : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) :
    Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  graphGen k (QPhiOf k (graphBlockWith k (frameGen k) Binv 0 1)
    (graphBlockWith k (frameGen k) Binv 0 2))

theorem frameB_eq2 : frameB 2 = graphBlockWith 2 (frameGen 2) frameBoxInv2 0 1 := by
  unfold frameB graphBlock graphBlockWith; rw [frameBox_inv2]
theorem frameC_eq2 : frameC 2 = graphBlockWith 2 (frameGen 2) frameBoxInv2 0 2 := by
  unfold frameC graphBlock graphBlockWith; rw [frameBox_inv2]
theorem QGen_eq2 : QGen 2 = QGen' 2 frameBoxInv2 := by
  unfold QGen QGen'; rw [frameB_eq2, frameC_eq2]
theorem frameB_eq3 : frameB 3 = graphBlockWith 3 (frameGen 3) frameBoxInv3 0 1 := by
  unfold frameB graphBlock graphBlockWith; rw [frameBox_inv3]
theorem frameC_eq3 : frameC 3 = graphBlockWith 3 (frameGen 3) frameBoxInv3 0 2 := by
  unfold frameC graphBlock graphBlockWith; rw [frameBox_inv3]
theorem QGen_eq3 : QGen 3 = QGen' 3 frameBoxInv3 := by
  unfold QGen QGen'; rw [frameB_eq3, frameC_eq3]
theorem frameB_eq4 : frameB 4 = graphBlockWith 4 (frameGen 4) frameBoxInv4 0 1 := by
  unfold frameB graphBlock graphBlockWith; rw [frameBox_inv4]
theorem frameC_eq4 : frameC 4 = graphBlockWith 4 (frameGen 4) frameBoxInv4 0 2 := by
  unfold frameC graphBlock graphBlockWith; rw [frameBox_inv4]
theorem QGen_eq4 : QGen 4 = QGen' 4 frameBoxInv4 := by
  unfold QGen QGen'; rw [frameB_eq4, frameC_eq4]

def Qpoint' (p k : ℕ) (Binv : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) (v : Fin (3 * k) → ZMod p) :
    Fin 3 → ℕ :=
  digPoint p (3 * k) (fun c => (QGen' k Binv c).map (Int.cast : ℤ → ZMod p)) v

theorem Qpoint_eq2 (p : ℕ) : Qpoint p 2 = Qpoint' p 2 frameBoxInv2 := by
  funext v; simp only [Qpoint, Qpoint', QGen_eq2]

-- Prop. `prop:rows` for k = 2 (rows 0, 1 of B, C): β₀ = (1-x)^(-2), γ₀ = -(1-x)^(-3) in reverse
-- level order, i.e. B row 0 = (2, 1), C row 0 = (-3, -1) (levels 0, 1).
example : graphBlockWith 2 (frameGen 2) frameBoxInv2 0 1 0 = ![2, 1] := by decide +kernel
example : graphBlockWith 2 (frameGen 2) frameBoxInv2 0 2 0 = ![-3, -1] := by decide +kernel

-- 𝒬_{2,11} graph-form blocks of Appendix `app:mats` (mod 11), via the twin
example : (QPhiOf 2 (graphBlockWith 2 (frameGen 2) frameBoxInv2 0 1)
    (graphBlockWith 2 (frameGen 2) frameBoxInv2 0 2) 0 1).map (Int.cast : ℤ → ZMod 11)
    = !![10, 10; 10, 0; 0, 0; 0, 0] := by decide +kernel
example : (QPhiOf 2 (graphBlockWith 2 (frameGen 2) frameBoxInv2 0 1)
    (graphBlockWith 2 (frameGen 2) frameBoxInv2 0 2) 0 2).map (Int.cast : ℤ → ZMod 11)
    = !![0, 10; 10, 1; 2, 10; 10, 0] := by decide +kernel

-- 𝒬_{2,11} points of Appendix `app:mats` (kernel-checked through `Qpoint_eq2`)
example : Qpoint 11 2 (idx 11 6 1) = ![161051, 1242, 14520] := by
  rw [Qpoint_eq2]; decide +kernel
example : Qpoint 11 2 (idx 11 6 7) = ![1127357, 521, 5808] := by
  rw [Qpoint_eq2]; decide +kernel
example : Qpoint 11 2 (idx 11 6 1000) = ![1641486, 1300828, 13852] := by
  rw [Qpoint_eq2]; decide +kernel
example : Qpoint 11 2 (idx 11 6 12345) = ![497431, 618626, 13769] := by
  rw [Qpoint_eq2]; decide +kernel
example : Qpoint 11 2 (idx 11 6 1771560) = ![1762476, 1762476, 1762476] := by
  rw [Qpoint_eq2]; decide +kernel


/-! ## Orientation of `graphBlock` / `Mtilde` (Proposition `prop:cell`, Corollary `cor:rows`)

For `𝒫_{k,p}` the first-offset-digit layer is `M̃ = M = [[-1,-1,1],[1,-1,-1],[-1,1,-1]]`
(row = coordinate whose offset digit, column = coordinate whose last cell digit); for `𝒬_{k,p}`
it is `M̃ = -𝟙𝟙ᵀ` (paper, after Proposition `prop:ceil`). Checked here for `p = 11`, `k = 2, 3`. -/

def pBoxInv2 : Matrix (Fin (3 * 2)) (Fin (3 * 2)) ℤ := !![0, 0, 1, 0, 0, 0; 0, 0, -2, -1, 0, 0; -1, 1, 1, 2, 0, -1; 3, -2, 0, -1, -1, 1; -3, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0]
def pBoxInv3 : Matrix (Fin (3 * 3)) (Fin (3 * 3)) ℤ := !![0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, -4, 1, 0, 0, 0, 0; 0, 0, 0, 6, -3, -1, 0, 0, 0; 0, -1, 1, -4, 3, 3, 0, 0, -1; 1, 4, -3, 1, -1, -3, 1, -1, 2; -4, -6, 3, 0, 0, 1, 0, 1, -1; 6, 4, -1, 0, 0, 0, 0, 0, 0; -4, -1, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- `P_{k,11}` generator matrices over `ZMod 11`. -/
def P11 (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod 11) :=
  fun c => (PGen k c).map (Int.cast : ℤ → ZMod 11)

theorem pBox_inv2 : (boxMatrix (P11 2) (fun _ => 2))⁻¹ = pBoxInv2.map (Int.cast : ℤ → ZMod 11) :=
  Matrix.inv_eq_right_inv (by decide +kernel)
theorem pBox_inv3 : (boxMatrix (P11 3) (fun _ => 3))⁻¹ = pBoxInv3.map (Int.cast : ℤ → ZMod 11) :=
  Matrix.inv_eq_right_inv (by decide +kernel)

/-- The paper's geometric layer `M`. -/
def Mpaper : Fin 3 → Fin 3 → ℤ := ![![-1, -1, 1], ![1, -1, -1], ![-1, 1, -1]]

theorem Mtilde_P11_2 : (fun c d => Mtilde 2 (P11 2) c d) = Mpaper := by
  unfold Mtilde graphBlock; rw [pBox_inv2]; decide +kernel
theorem Mtilde_P11_3 : (fun c d => Mtilde 3 (P11 3) c d) = Mpaper := by
  unfold Mtilde graphBlock; rw [pBox_inv3]; decide +kernel

/-- `𝒬_{k,11}` generator matrices over `ZMod 11` (graph form, so the box matrix is `1`). -/
noncomputable def Q11 (k : ℕ) : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod 11) :=
  fun c => (QGen k c).map (Int.cast : ℤ → ZMod 11)

theorem qBox_inv2 : (boxMatrix (Q11 2) (fun _ => 2))⁻¹ = 1 := by
  apply Matrix.inv_eq_right_inv; rw [mul_one]; unfold Q11; rw [QGen_eq2]; decide +kernel

theorem Mtilde_Q11_2 : (fun c d => Mtilde 2 (Q11 2) c d) = fun _ _ => -1 := by
  unfold Mtilde graphBlock; rw [qBox_inv2]; simp only [Matrix.mul_one]; unfold Q11; rw [QGen_eq2]; decide +kernel

end Z3Net.Checks
