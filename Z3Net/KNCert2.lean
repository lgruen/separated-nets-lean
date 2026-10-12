module
public import Z3Net.KNRange

@[expose] public section

/-!
# Kernel-checked relaxation certificates, `m ≡ 2 (mod 3)`, `p ∈ {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 79}`

Each theorem is the exhaustive enumeration of `checkAll` (all coarse steps in the range box, all
carry chains, all wrap options) plus the side conditions `sideOK`, by `decide +kernel`
(no `native_decide`).
-/

namespace Z3NetKN.Relax

/-- `p = 5`: `T = 19` (`c ≈ 0.50982`). -/
theorem cert2_5 : checkAll (cfg2 5 rows2_5) 19 = true ∧ sideOK (cfg2 5 rows2_5) 19 = true := by
  decide +kernel

/-- `p = 7`: `T = 73` (`c ≈ 0.63806`). -/
theorem cert2_7 : checkAll (cfg2 7 rows2_7) 73 = true ∧ sideOK (cfg2 7 rows2_7) 73 = true := by
  decide +kernel

/-- `p = 11`: `T = 425` (`c ≈ 0.84270`). -/
theorem cert2_11 : checkAll (cfg2 11 rows2_11) 425 = true ∧ sideOK (cfg2 11 rows2_11) 425 = true := by
  decide +kernel

/-- `p = 13`: `T = 691` (`c ≈ 0.85997`). -/
theorem cert2_13 : checkAll (cfg2 13 rows2_13) 691 = true ∧ sideOK (cfg2 13 rows2_13) 691 = true := by
  decide +kernel

/-- `p = 17`: `T = 1312` (`c ≈ 0.82864`). -/
theorem cert2_17 : checkAll (cfg2 17 rows2_17) 1312 = true ∧ sideOK (cfg2 17 rows2_17) 1312 = true := by
  decide +kernel

/-- `p = 19`: `T = 1798` (`c ≈ 0.83635`). -/
theorem cert2_19 : checkAll (cfg2 19 rows2_19) 1798 = true ∧ sideOK (cfg2 19 rows2_19) 1798 = true := by
  decide +kernel

/-- `p = 23`: `T = 4022` (`c ≈ 0.96958`). -/
theorem cert2_23 : checkAll (cfg2 23 rows2_23) 4022 = true ∧ sideOK (cfg2 23 rows2_23) 4022 = true := by
  decide +kernel

/-- `p = 29`: `T = 7685` (`c ≈ 0.98392`). -/
theorem cert2_29 : checkAll (cfg2 29 rows2_29) 7685 = true ∧ sideOK (cfg2 29 rows2_29) 7685 = true := by
  decide +kernel

/-- `p = 31`: `T = 9019` (`c ≈ 0.97521`). -/
theorem cert2_31 : checkAll (cfg2 31 rows2_31) 9019 = true ∧ sideOK (cfg2 31 rows2_31) 9019 = true := by
  decide +kernel

/-- `p = 37`: `T = 13777` (`c ≈ 0.95201`). -/
theorem cert2_37 : checkAll (cfg2 37 rows2_37) 13777 = true ∧ sideOK (cfg2 37 rows2_37) 13777 = true := by
  decide +kernel

/-- `p = 41`: `T = 20116` (`c ≈ 1.00321`). -/
theorem cert2_41 : checkAll (cfg2 41 rows2_41) 20116 = true ∧ sideOK (cfg2 41 rows2_41) 20116 = true := by
  decide +kernel

/-- `p = 43`: `T = 22853` (`c ≈ 1.00349`). -/
theorem cert2_43 : checkAll (cfg2 43 rows2_43) 22853 = true ∧ sideOK (cfg2 43 rows2_43) 22853 = true := by
  decide +kernel

/-- `p = 47`: `T = 28556` (`c ≈ 0.99629`). -/
theorem cert2_47 : checkAll (cfg2 47 rows2_47) 28556 = true ∧ sideOK (cfg2 47 rows2_47) 28556 = true := by
  decide +kernel

/-- `p = 53`: `T = 37546` (`c ≈ 0.97330`). -/
theorem cert2_53 : checkAll (cfg2 53 rows2_53) 37546 = true ∧ sideOK (cfg2 53 rows2_53) 37546 = true := by
  decide +kernel

/-- `p = 59`: `T = 54357` (`c ≈ 1.01506`). -/
theorem cert2_59 : checkAll (cfg2 59 rows2_59) 54357 = true ∧ sideOK (cfg2 59 rows2_59) 54357 = true := by
  decide +kernel

/-- `p = 61`: `T = 58586` (`c ≈ 1.00799`). -/
theorem cert2_61 : checkAll (cfg2 61 rows2_61) 58586 = true ∧ sideOK (cfg2 61 rows2_61) 58586 = true := by
  decide +kernel

/-- `p = 79`: `T = 119786` (`c ≈ 1.02102`). -/
theorem cert2_79 : checkAll (cfg2 79 rows2_79) 119786 = true ∧ sideOK (cfg2 79 rows2_79) 119786 = true := by
  decide +kernel

end Z3NetKN.Relax
