module
public import Z3Net.KNSep
public import Z3Net.KNCert1a
public import Z3Net.KNCert1b
public import Z3Net.KNCert2

@[expose] public section

/-!
# KN separation, part 8: the per-prime separation theorems `KN1_sep`, `KN2_sep`

Every design of `table1` / `table2` carries a kernel-checked certificate (`KNCert1a/1b/2`);
`Geom.sep_of_cert` turns it into the separation bound for every `k ≥ 2`.
-/

namespace Z3NetKN.Relax

theorem table1_cert : ∀ x ∈ table1,
    (checkAll (cfg1 x.1 x.2.2) x.2.1 = true ∧ sideOK (cfg1 x.1 x.2.2) x.2.1 = true) ∧ 2 ≤ x.1 := by
  intro x hx
  simp only [table1, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨cert1_5, by norm_num⟩, ⟨cert1_7, by norm_num⟩, ⟨cert1_11, by norm_num⟩, ⟨cert1_13, by norm_num⟩, ⟨cert1_17, by norm_num⟩, ⟨cert1_19, by norm_num⟩, ⟨cert1_23, by norm_num⟩, ⟨cert1_29, by norm_num⟩, ⟨cert1_31, by norm_num⟩, ⟨cert1_37, by norm_num⟩, ⟨cert1_41, by norm_num⟩, ⟨cert1_43, by norm_num⟩, ⟨cert1_47, by norm_num⟩, ⟨cert1_53, by norm_num⟩, ⟨cert1_59, by norm_num⟩, ⟨cert1_61, by norm_num⟩, ⟨cert1_67, by norm_num⟩, ⟨cert1_71, by norm_num⟩, ⟨cert1_73, by norm_num⟩, ⟨cert1_79, by norm_num⟩]

theorem table2_cert : ∀ x ∈ table2,
    (checkAll (cfg2 x.1 x.2.2) x.2.1 = true ∧ sideOK (cfg2 x.1 x.2.2) x.2.1 = true) ∧ 2 ≤ x.1 := by
  intro x hx
  simp only [table2, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨cert2_5, by norm_num⟩, ⟨cert2_7, by norm_num⟩, ⟨cert2_11, by norm_num⟩, ⟨cert2_13, by norm_num⟩, ⟨cert2_17, by norm_num⟩, ⟨cert2_19, by norm_num⟩, ⟨cert2_23, by norm_num⟩, ⟨cert2_29, by norm_num⟩, ⟨cert2_31, by norm_num⟩, ⟨cert2_37, by norm_num⟩, ⟨cert2_41, by norm_num⟩, ⟨cert2_43, by norm_num⟩, ⟨cert2_47, by norm_num⟩, ⟨cert2_53, by norm_num⟩, ⟨cert2_59, by norm_num⟩, ⟨cert2_61, by norm_num⟩, ⟨cert2_79, by norm_num⟩]

end Z3NetKN.Relax

namespace Z3NetKN.Proofs

open Z3NetKN.Relax Z3NetKN.Geom

theorem KN1_sep (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (hC : IsKN 1 p k R C)
    (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k - 2) ≤
      torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) := by
  obtain ⟨⟨h1, h2⟩, hp⟩ := table1_cert _ hmem
  have := sep_of_cert (Or.inl rfl) (by omega) hp R (rg1 p) T h1 h2 C hC v w hvw
  rwa [← pow_mul, show (3 * k + 1 - (k + 2)) * 2 = 4 * k - 2 by omega] at this

theorem KN2_sep (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p)) (hC : IsKN 2 p k R C)
    (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 2)) (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) := by
  obtain ⟨⟨h1, h2⟩, hp⟩ := table2_cert _ hmem
  have := sep_of_cert (Or.inr rfl) hk hp R (rg2 p) T h1 h2 C hC v w hvw
  rwa [← pow_mul, show (3 * k + 2 - (k + 2)) * 2 = 4 * k by omega] at this

end Z3NetKN.Proofs
