/-
Proof module (stage 6, entry PP): the 37 tabulated designs satisfy the hypotheses of `prop:pp1`,
`prop:pp2` (kernel evaluation, `decide +kernel`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.KNDefs

@[expose] public section

namespace Z3NetKN.PPTab

instance (R : Rows) : Decidable (CondS2 R) := by unfold CondS2; infer_instance
instance (p : ℕ) (R : Rows) : Decidable (CondN2 p R) := by unfold CondN2; infer_instance
instance (R : Rows) : Decidable (CondS1 R) := by unfold CondS1; infer_instance
instance (p : ℕ) (R : Rows) : Decidable (CondN1 p R) := by unfold CondN1; infer_instance

set_option maxRecDepth 100000 in
theorem pp2_table : ∀ x ∈ table2, CondS2 x.2.2 ∧ CondN2 x.1 x.2.2 ∧ kap1 x.1 x.2.2 = -1 ∧
    kap2 x.1 x.2.2 = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pp1_table : ∀ x ∈ table1, CondS1 x.2.2 ∧ CondN1 x.1 x.2.2 ∧ J1 x.1 x.2.2 = 1 ∧
    J2 x.1 x.2.2 = -1 ∧ J3 x.1 x.2.2 = 2 ∧ J4 x.1 x.2.2 = 2 ∧ J5 x.1 x.2.2 = 1 := by
  decide +kernel

end Z3NetKN.PPTab
