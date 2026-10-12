/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `rem:q11`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.NetPoly

@[expose] public section

/-!
# `rem:q11`: a close pair of `𝒬_{3,9}` (main entry, stage 6)

The frame's box matrix for `k = 3` has the explicit integer inverse `Binv3` (checked in the
kernel), so `frameB 3`, `frameC 3`, `QGen 3` are explicit integer matrices; the two points with
indices `v = (6,0,0,1,5,0,3,6,0)` and `w = (5,8,8,1,4,8,3,5,8)` (cells `n` and `n - (1,1,1)`) are
computed in the kernel, at squared toroidal distance `216858928882` (scale `N = 9^9`), i.e. at
normalized distance `0.87626… < c*(9) = 0.89852…`.
-/

namespace Z3Net.Proofs.Q11

open Matrix

def Binv3 : Matrix (Fin (3 * 3)) (Fin (3 * 3)) ℤ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0;
     -10, -4, -1, -10, -6, -3, 6, 3, 1;
     35, 13, 3, 15, 8, 3, -15, -7, -2;
     -46, -15, -3, -6, -3, -1, 10, 4, 1;
     28, 7, 1, 0, 0, 0, 0, 0, 0;
     -8, -1, 0, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
lemma box3_mul : boxMatrix (frameGen 3) (fun _ => 3) * Binv3 = 1 := by
  decide +kernel


lemma box3_inv : (boxMatrix (frameGen 3) (fun _ => 3))⁻¹ = Binv3 :=
  Matrix.inv_eq_right_inv box3_mul

def B3 : Matrix (Fin (2 * 3)) (Fin 3) ℤ :=
  !![6, 3, 1;
     -15, -7, -2;
     10, 4, 1;
     0, 0, 0;
     0, 0, 0;
     0, 0, 0]

def C3 : Matrix (Fin (2 * 3)) (Fin 3) ℤ :=
  !![-10, -4, -1;
     35, 13, 3;
     -46, -15, -3;
     28, 7, 1;
     -8, -1, 0;
     1, 0, 0]

set_option maxRecDepth 100000 in
lemma frameB3 : frameB 3 = B3 := by
  unfold frameB graphBlock; rw [box3_inv]; ext r l; fin_cases r <;> fin_cases l <;> decide +kernel

set_option maxRecDepth 100000 in
lemma frameC3 : frameC 3 = C3 := by
  unfold frameC graphBlock; rw [box3_inv]; ext r l; fin_cases r <;> fin_cases l <;> decide +kernel

def G3 : Fin 3 → Matrix (Fin (3 * 3)) (Fin (3 * 3)) ℤ :=
  ![!![1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, -1, 0, -1, -1, 0, 0, -1;
     0, 0, 0, -2, -1, 0, 2, -1, 1;
     0, 0, 0, 0, 0, -1, -8, 3, -3;
     0, 0, 0, 0, 0, 0, 12, -3, 1;
     0, 0, 0, 0, 0, 0, -8, 1, 0;
     0, 0, 0, 0, 0, 0, 2, 0, 0],
    !![0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, -1, 0, 0, -1, 0, -1, -1;
     2, -1, 1, 0, 0, 0, -2, -1, 0;
     -8, 3, -3, 0, 0, 0, 0, 0, -1;
     12, -3, 1, 0, 0, 0, 0, 0, 0;
     -8, 1, 0, 0, 0, 0, 0, 0, 0;
     2, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1;
     0, -1, -1, 0, 0, -1, 0, 0, -1;
     -2, -1, 0, 2, -1, 1, 0, 0, 0;
     0, 0, -1, -8, 3, -3, 0, 0, 0;
     0, 0, 0, 12, -3, 1, 0, 0, 0;
     0, 0, 0, -8, 1, 0, 0, 0, 0;
     0, 0, 0, 2, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
lemma QGen3 : QGen 3 = G3 := by
  unfold QGen; rw [frameB3, frameC3]; decide +kernel

def vQ : Fin (3 * 3) → ZMod 9 := ![6, 0, 0, 1, 5, 0, 3, 6, 0]
def wQ : Fin (3 * 3) → ZMod 9 := ![5, 8, 8, 1, 4, 8, 3, 5, 8]

set_option maxRecDepth 100000 in
lemma pt_v : Qpoint 9 3 vQ = ![258531837, 67143144, 157863305] := by
  unfold Qpoint; rw [QGen3]; decide +kernel

set_option maxRecDepth 100000 in
lemma pt_w : Qpoint 9 3 wQ = ![258244116, 66901015, 157588625] := by
  unfold Qpoint; rw [QGen3]; decide +kernel

lemma dist_vw : torusDist2 (9 ^ 9) (Qpoint 9 3 vQ) (Qpoint 9 3 wQ) = 216858928882 := by
  rw [pt_v, pt_w]; decide +kernel

theorem Q9_witness : ∃ v w : Fin (3 * 3) → ZMod 9,
    (∀ c, (Qpoint 9 3 w c / 9 ^ 6 + 1) % 9 ^ 3 = Qpoint 9 3 v c / 9 ^ 6) ∧
      Real.sqrt (torusDist2 (9 ^ 9) (Qpoint 9 3 v) (Qpoint 9 3 w)) / 9 ^ 6 < 0.8763 ∧
      (0.8763 : ℝ) < cQ 9 := by
  refine ⟨vQ, wQ, ?_, ?_, ?_⟩
  · intro c; rw [pt_v, pt_w]; fin_cases c <;> decide +kernel
  · rw [dist_vw, div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]
    norm_num
  · unfold cQ
    rw [Real.lt_sqrt (by norm_num)]
    norm_num

end Z3Net.Proofs.Q11
