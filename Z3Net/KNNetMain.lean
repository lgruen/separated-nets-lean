module
public import Z3Net.KNNetProof
public import Z3Net.KNNetCert1
public import Z3Net.KNNetCert2

@[expose] public section

/-!
# `KN1_net`, `KN2_net`: the per-prime designs are realized by nets for every `k`

Every design of `table1` / `table2` has a kernel-checked gauge certificate (`KNNetCert1/2`), and
`net_of_cert1` / `net_of_cert2` turn it into a `(0, 3k+r, 3)`-net over `𝔽_p` with exactly the
designed rows, for every `k ≥ 3` resp. `k ≥ 2` (`prop:pp1`, `prop:pp2` of the paper; Lean proof via
the explicit frame gauge `h r` to a `k`-independent window instead of the invariants of
`lem:ppinv`).
-/

namespace Z3NetKN.Proofs

open Z3NetKN.NetKN

/-- **`m ≡ 1`, net part** (`KN1_net` of `ChallengeKN.lean`). -/
theorem KN1_net (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  simp only [table1, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact net_of_cert1 5 k (by norm_num) hk rows1_5 gcert1_5 gcert1_5_ok
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact net_of_cert1 7 k (by norm_num) hk rows1_7 gcert1_7 gcert1_7_ok
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact net_of_cert1 11 k (by norm_num) hk rows1_11 gcert1_11 gcert1_11_ok
  · have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact net_of_cert1 13 k (by norm_num) hk rows1_13 gcert1_13 gcert1_13_ok
  · have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    exact net_of_cert1 17 k (by norm_num) hk rows1_17 gcert1_17 gcert1_17_ok
  · have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact net_of_cert1 19 k (by norm_num) hk rows1_19 gcert1_19 gcert1_19_ok
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact net_of_cert1 23 k (by norm_num) hk rows1_23 gcert1_23 gcert1_23_ok
  · have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    exact net_of_cert1 29 k (by norm_num) hk rows1_29 gcert1_29 gcert1_29_ok
  · have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact net_of_cert1 31 k (by norm_num) hk rows1_31 gcert1_31 gcert1_31_ok
  · have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    exact net_of_cert1 37 k (by norm_num) hk rows1_37 gcert1_37 gcert1_37_ok
  · have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    exact net_of_cert1 41 k (by norm_num) hk rows1_41 gcert1_41 gcert1_41_ok
  · have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact net_of_cert1 43 k (by norm_num) hk rows1_43 gcert1_43 gcert1_43_ok
  · have : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    exact net_of_cert1 47 k (by norm_num) hk rows1_47 gcert1_47 gcert1_47_ok
  · have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    exact net_of_cert1 53 k (by norm_num) hk rows1_53 gcert1_53 gcert1_53_ok
  · have : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    exact net_of_cert1 59 k (by norm_num) hk rows1_59 gcert1_59 gcert1_59_ok
  · have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    exact net_of_cert1 61 k (by norm_num) hk rows1_61 gcert1_61 gcert1_61_ok
  · have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact net_of_cert1 67 k (by norm_num) hk rows1_67 gcert1_67 gcert1_67_ok
  · have : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    exact net_of_cert1 71 k (by norm_num) hk rows1_71 gcert1_71 gcert1_71_ok
  · have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    exact net_of_cert1 73 k (by norm_num) hk rows1_73 gcert1_73 gcert1_73_ok
  · have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    exact net_of_cert1 79 k (by norm_num) hk rows1_79 gcert1_79 gcert1_79_ok

/-- **`m ≡ 2`, net part** (`KN2_net` of `ChallengeKN.lean`). -/
theorem KN2_net (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKN 2 p k R C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) := by
  simp only [table2, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact net_of_cert2 5 k hk rows2_5 gcert2_5 gcert2_5_ok
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact net_of_cert2 7 k hk rows2_7 gcert2_7 gcert2_7_ok
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact net_of_cert2 11 k hk rows2_11 gcert2_11 gcert2_11_ok
  · have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact net_of_cert2 13 k hk rows2_13 gcert2_13 gcert2_13_ok
  · have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    exact net_of_cert2 17 k hk rows2_17 gcert2_17 gcert2_17_ok
  · have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact net_of_cert2 19 k hk rows2_19 gcert2_19 gcert2_19_ok
  · have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact net_of_cert2 23 k hk rows2_23 gcert2_23 gcert2_23_ok
  · have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    exact net_of_cert2 29 k hk rows2_29 gcert2_29 gcert2_29_ok
  · have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact net_of_cert2 31 k hk rows2_31 gcert2_31 gcert2_31_ok
  · have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    exact net_of_cert2 37 k hk rows2_37 gcert2_37 gcert2_37_ok
  · have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    exact net_of_cert2 41 k hk rows2_41 gcert2_41 gcert2_41_ok
  · have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact net_of_cert2 43 k hk rows2_43 gcert2_43 gcert2_43_ok
  · have : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    exact net_of_cert2 47 k hk rows2_47 gcert2_47 gcert2_47_ok
  · have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    exact net_of_cert2 53 k hk rows2_53 gcert2_53 gcert2_53_ok
  · have : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    exact net_of_cert2 59 k hk rows2_59 gcert2_59 gcert2_59_ok
  · have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    exact net_of_cert2 61 k hk rows2_61 gcert2_61 gcert2_61_ok
  · have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    exact net_of_cert2 79 k hk rows2_79 gcert2_79 gcert2_79_ok

end Z3NetKN.Proofs
