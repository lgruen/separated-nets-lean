module
public import Z3Net.KNRange

@[expose] public section

/-!
# Kernel-checked relaxation certificates, `m ≡ 1 (mod 3)`, `p ∈ {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}`

Each theorem is the exhaustive enumeration of `checkAll` (all coarse steps in the range box, all
carry chains, all wrap options) plus the side conditions `sideOK`, by `decide +kernel`
(no `native_decide`).
-/

namespace Z3NetKN.Relax

/-- `p = 5`: `T = 85` (`c ≈ 0.63061`). -/
theorem cert1_5 : checkAll (cfg1 5 rows1_5) 85 = true ∧ sideOK (cfg1 5 rows1_5) 85 = true := by
  decide +kernel

/-- `p = 7`: `T = 360` (`c ≈ 0.74072`). -/
theorem cert1_7 : checkAll (cfg1 7 rows1_7) 360 = true ∧ sideOK (cfg1 7 rows1_7) 360 = true := by
  decide +kernel

/-- `p = 11`: `T = 2161` (`c ≈ 0.85442`). -/
theorem cert1_11 : checkAll (cfg1 11 rows1_11) 2161 = true ∧ sideOK (cfg1 11 rows1_11) 2161 = true := by
  decide +kernel

/-- `p = 13`: `T = 3794` (`c ≈ 0.85699`). -/
theorem cert1_13 : checkAll (cfg1 13 rows1_13) 3794 = true ∧ sideOK (cfg1 13 rows1_13) 3794 = true := by
  decide +kernel

/-- `p = 17`: `T = 9986` (`c ≈ 0.88909`). -/
theorem cert1_17 : checkAll (cfg1 17 rows1_17) 9986 = true ∧ sideOK (cfg1 17 rows1_17) 9986 = true := by
  decide +kernel

/-- `p = 19`: `T = 14904` (`c ≈ 0.90239`). -/
theorem cert1_19 : checkAll (cfg1 19 rows1_19) 14904 = true ∧ sideOK (cfg1 19 rows1_19) 14904 = true := by
  decide +kernel

/-- `p = 23`: `T = 30277` (`c ≈ 0.93543`). -/
theorem cert1_23 : checkAll (cfg1 23 rows1_23) 30277 = true ∧ sideOK (cfg1 23 rows1_23) 30277 = true := by
  decide +kernel

/-- `p = 29`: `T = 71485` (`c ≈ 0.97674`). -/
theorem cert1_29 : checkAll (cfg1 29 rows1_29) 71485 = true ∧ sideOK (cfg1 29 rows1_29) 71485 = true := by
  decide +kernel

/-- `p = 31`: `T = 86406` (`c ≈ 0.96088`). -/
theorem cert1_31 : checkAll (cfg1 31 rows1_31) 86406 = true ∧ sideOK (cfg1 31 rows1_31) 86406 = true := by
  decide +kernel

/-- `p = 37`: `T = 160082` (`c ≈ 0.97387`). -/
theorem cert1_37 : checkAll (cfg1 37 rows1_37) 160082 = true ∧ sideOK (cfg1 37 rows1_37) 160082 = true := by
  decide +kernel

/-- `p = 41`: `T = 215869` (`c ≈ 0.95306`). -/
theorem cert1_41 : checkAll (cfg1 41 rows1_41) 215869 = true ∧ sideOK (cfg1 41 rows1_41) 215869 = true := by
  decide +kernel

/-- `p = 43`: `T = 273203` (`c ≈ 0.99037`). -/
theorem cert1_43 : checkAll (cfg1 43 rows1_43) 273203 = true ∧ sideOK (cfg1 43 rows1_43) 273203 = true := by
  decide +kernel

end Z3NetKN.Relax
