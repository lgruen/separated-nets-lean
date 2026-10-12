/-
Proof module (stage 12, entry main): the printed value of `rem:q11` as a compared statement.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Defs
public import Z3Net.S6Q11

@[expose] public section

/-!
# Stage 12 addition to entry main

Restatement (identical to the stage-12 block of `Challenge.lean`) of `Q9_witness_value`: the pair
`vQ`, `wQ` of `Z3Net/S6Q11.lean` (squared toroidal distance `216858928882` at scale `N = 9^9`,
`Proofs.Q11.dist_vw`) has normalized distance in `[0.8762, 0.8763)`, and `c*(9) ∈ [0.8985, 0.8986)`,
so the four-digit truncations `.8762` and `.8985` printed in `rem:q11` are certified.
-/

namespace Z3Net

/-- **`rem:q11`, the printed values**: `𝒬_{3,9}` has two points in the toroidally adjacent cells
`n` (of the point `v`) and `n - (1,1,1)` (of the point `w`) whose normalized toroidal distance
`δ N^(1/3)` (`N = 9^9`, distances at integer scale `N`) lies in `[0.8762, 0.8763)` (printed as
`.8762`, truncated), and `c*(9)` lies in `[0.8985, 0.8986)` (printed as `.8985`). -/
theorem Q9_witness_value : ∃ v w : Fin (3 * 3) → ZMod 9,
    (∀ c, (Qpoint 9 3 w c / 9 ^ 6 + 1) % 9 ^ 3 = Qpoint 9 3 v c / 9 ^ 6) ∧
      (0.8762 : ℝ) ≤ Real.sqrt (torusDist2 (9 ^ 9) (Qpoint 9 3 v) (Qpoint 9 3 w)) / 9 ^ 6 ∧
      Real.sqrt (torusDist2 (9 ^ 9) (Qpoint 9 3 v) (Qpoint 9 3 w)) / 9 ^ 6 < 0.8763 ∧
      (0.8985 : ℝ) ≤ cQ 9 ∧ cQ 9 < 0.8986 := by
  refine ⟨Proofs.Q11.vQ, Proofs.Q11.wQ, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [Proofs.Q11.pt_v, Proofs.Q11.pt_w]; fin_cases c <;> decide +kernel
  · rw [Proofs.Q11.dist_vw, le_div_iff₀ (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Proofs.Q11.dist_vw, div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]
    norm_num
  · unfold cQ
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  · unfold cQ
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num

end Z3Net
