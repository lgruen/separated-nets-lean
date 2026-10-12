module
public import Z3Net.KNRange

@[expose] public section

/-!
# Kernel-checked relaxation certificates, `m ≡ 1 (mod 3)`, `p ∈ {47, 53, 59, 61, 67, 71, 73, 79}`

Each theorem is the exhaustive enumeration of `checkAll` (all coarse steps in the range box, all
carry chains, all wrap options) plus the side conditions `sideOK`, by `decide +kernel`
(no `native_decide`).
-/

namespace Z3NetKN.Relax

/-- `p = 47`: `T = 381649` (`c ≈ 1.00926`). -/
theorem cert1_47 : checkAll (cfg1 47 rows1_47) 381649 = true ∧ sideOK (cfg1 47 rows1_47) 381649 = true := by
  decide +kernel

/-- `p = 53`: `T = 576177` (`c ≈ 1.01504`). -/
theorem cert1_53 : checkAll (cfg1 53 rows1_53) 576177 = true ∧ sideOK (cfg1 53 rows1_53) 576177 = true := by
  decide +kernel

/-- `p = 59`: `T = 838749` (`c ≈ 1.02423`). -/
theorem cert1_59 : checkAll (cfg1 59 rows1_59) 838749 = true ∧ sideOK (cfg1 59 rows1_59) 838749 = true := by
  decide +kernel

/-- `p = 61`: `T = 918186` (`c ≈ 1.01371`). -/
theorem cert1_61 : checkAll (cfg1 61 rows1_61) 918186 = true ∧ sideOK (cfg1 61 rows1_61) 918186 = true := by
  decide +kernel

/-- `p = 67`: `T = 1214947` (`c ≈ 0.99729`). -/
theorem cert1_67 : checkAll (cfg1 67 rows1_67) 1214947 = true ∧ sideOK (cfg1 67 rows1_67) 1214947 = true := by
  decide +kernel

/-- `p = 71`: `T = 1544201` (`c ≈ 1.02075`). -/
theorem cert1_71 : checkAll (cfg1 71 rows1_71) 1544201 = true ∧ sideOK (cfg1 71 rows1_71) 1544201 = true := by
  decide +kernel

/-- `p = 73`: `T = 1710627` (`c ≈ 1.02575`). -/
theorem cert1_73 : checkAll (cfg1 73 rows1_73) 1710627 = true ∧ sideOK (cfg1 73 rows1_73) 1710627 = true := by
  decide +kernel

/-- `p = 79`: `T = 2267461` (`c ≈ 1.03528`). -/
theorem cert1_79 : checkAll (cfg1 79 rows1_79) 2267461 = true ∧ sideOK (cfg1 79 rows1_79) 2267461 = true := by
  decide +kernel

end Z3NetKN.Relax
