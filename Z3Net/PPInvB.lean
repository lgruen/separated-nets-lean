module
public import Z3Net.PPInvT
public import Z3Net.D3Gauge
public import Z3Net.S6Faure

@[expose] public section

/-!
# `lem:ppinv` (b): the invariants of the frame `Φ^F` (entry PPInv)

The frame readings `(τ², I, τ)` are `(T_x φ_∞, φ_0, T_z φ_1)` with `T_x = τ² J = D_± J P J` and
`T_z = Λ_m` lower triangular with unit diagonal (`prop:faure`: `τ = Λ_m P`, `τ² = D_± J P`;
`φ_∞ = J`, `φ_1 = P`).  By `PPInvT.gauge_of` the windows of `Φ^F` are a gauge transform of those
of the frame `(φ_∞, φ_0, φ_1)`, whose entries are the closed forms of entry KN (`KNNetWin1`,
`KNNetWin2`, and `win1_xi2'` in every characteristic); `val2`, `val1` evaluate the invariants.
-/

namespace Z3NetPI.InvB

open Matrix Finset Z3NetKN.Frame Z3NetKN.Realize Z3NetPI.InvA Z3NetPI.InvT Z3NetPI.Val

/-! ## The reversal `J` -/

lemma J_mul_right {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    (A * Z3Net.Jrev m) i j = A i ⟨m - 1 - j, by omega⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨m - 1 - j, by omega⟩]
  · simp [Z3Net.Jrev]; omega
  · intro b _ hb
    simp only [Z3Net.Jrev]
    rw [if_neg (fun h => hb (Fin.ext (by simp; omega))), mul_zero]
  · simp

lemma J_mul_left {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    (Z3Net.Jrev m * A) i j = A ⟨m - 1 - i, by omega⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · simp [Z3Net.Jrev]; omega
  · intro b _ hb
    simp only [Z3Net.Jrev]
    rw [if_neg (fun h => hb (Fin.ext (by simp; omega))), zero_mul]
  · simp

lemma J_sq (m : ℕ) : Z3Net.Jrev m * Z3Net.Jrev m = 1 := by
  ext i j
  rw [J_mul_right]
  simp only [Z3Net.Jrev, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp; omega
  · rw [if_neg (by have : (i : ℕ) ≠ j := fun e => h (Fin.ext e); simp; omega), if_neg h]

lemma tx_entry (m : ℕ) (hm : 1 ≤ m) (i j : Fin m) :
    (Z3Net.tau m * Z3Net.tau m * Z3Net.Jrev m) i j =
      (-1) ^ (i : ℕ) * (((m - 1 - (j : ℕ)).choose (m - 1 - (i : ℕ)) : ℕ) : ℤ) := by
  rw [J_mul_right, ← sq, Z3Net.Proofs.Faure.faure_tau2 m hm, Matrix.mul_assoc, Z3Net.Dpm,
    Matrix.diagonal_mul, J_mul_left]
  simp [Z3Net.pascalP]

/-! ## The frame as a lower-triangular change of the readings `(φ_∞, φ_0, φ_1)` -/

variable {F : Type*} [Field F]

/-- `T = (τ² J, I, Λ_m)`. -/
def Tfr (F : Type*) [Field F] (m : ℕ) : Fin 3 → Matrix (Fin m) (Fin m) F :=
  ![((Z3Net.tau m * Z3Net.tau m) * Z3Net.Jrev m).map (Int.cast : ℤ → F), 1,
    (Z3Net.LamF m).map (Int.cast : ℤ → F)]

lemma Tfr_low (m : ℕ) (hm : 1 ≤ m) : ∀ c (i j : Fin m), i < j → Tfr F m c i j = 0 := by
  intro c i j hij
  have hij' : (i : ℕ) < j := hij
  fin_cases c
  · simp only [Tfr, Fin.zero_eta, Matrix.cons_val_zero, Matrix.map_apply]
    rw [tx_entry m hm, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · simp only [Tfr, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact Matrix.one_apply_ne (ne_of_lt hij)
  · simp only [Tfr, Fin.reduceFinMk, Matrix.cons_val, Matrix.map_apply]
    rw [(Z3Net.Proofs.Faure.faure_Lam m).2 i j hij]; simp

lemma Tfr_diag (m : ℕ) (hm : 1 ≤ m) : ∀ c (i : Fin m), Tfr F m c i i ≠ 0 := by
  intro c i
  fin_cases c
  · simp only [Tfr, Fin.zero_eta, Matrix.cons_val_zero, Matrix.map_apply]
    rw [tx_entry m hm, Nat.choose_self]
    simp
  · simp [Tfr]
  · simp only [Tfr, Fin.reduceFinMk, Matrix.cons_val, Matrix.map_apply]
    rw [(Z3Net.Proofs.Faure.faure_Lam m).1 i]; simp

lemma phiX_eq (m : ℕ) : Z3NetKN.Phi.phiX (F := F) m = (Z3Net.Jrev m).map (Int.cast : ℤ → F) := by
  ext i j
  by_cases h : (i : ℕ) + j + 1 = m <;> simp [Z3NetKN.Phi.phiX, Z3Net.Jrev, h]

lemma phiZ_eq (m : ℕ) : Z3NetKN.Phi.phiZ (F := F) m = (Z3Net.pascalP m).map (Int.cast : ℤ → F) := by
  ext i j; simp [Z3NetKN.Phi.phiZ, Z3Net.pascalP]

lemma Tfr_mul (m : ℕ) (hm : 1 ≤ m) :
    ∀ c, frameF F m c = Tfr F m c * Z3NetKN.Phi.phi m c := by
  have hmap := fun (A B : Matrix (Fin m) (Fin m) ℤ) =>
    (Matrix.map_mul (f := Int.castRingHom F) (L := A) (M := B))
  intro c
  fin_cases c
  · simp only [Tfr, Z3NetKN.Phi.phi, Fin.zero_eta, Matrix.cons_val_zero, phiX_eq]
    have := hmap (Z3Net.tau m * Z3Net.tau m * Z3Net.Jrev m) (Z3Net.Jrev m)
    simp only [Int.coe_castRingHom] at this
    rw [← this, Matrix.mul_assoc, J_sq, Matrix.mul_one]
    rfl
  · simp only [Tfr, Z3NetKN.Phi.phi, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.mul_one]
    ext a b; simp [frameF, frameZ, Matrix.one_apply]
  · simp only [Tfr, Z3NetKN.Phi.phi, Fin.reduceFinMk, Matrix.cons_val, phiZ_eq]
    have := hmap (Z3Net.LamF m) (Z3Net.pascalP m)
    simp only [Int.coe_castRingHom] at this
    rw [← this, ← Z3Net.Proofs.Faure.faure_tau m hm]
    rfl

/-! ## The windows of `Φ^F` -/

lemma winF_eq (r p k : ℕ) [Fact p.Prime] (hr : r ≤ 3) :
    winF r p k = WP (Z3NetKN.depth r k) (gr (frameF (ZMod p) (3 * k + r)) (Z3NetKN.depth r k)) := by
  funext c d
  ext ρ i
  simp only [winF, WP, Matrix.of_apply]
  rw [show Z3NetPI.frameGrN r p k c = Z3NetKN.frameGrN r p k c from rfl,
    Z3NetKN.Proofs.D3.frameGrN_eq r p k hr c, Z3NetKN.Proofs.D3.offK_eq_offN]
  rfl

lemma WP_ent {m : ℕ} (K : Fin 3 → ℕ) (G : Fin 3 → Matrix (Fin m) (Fin m) F) (c d : Fin 3)
    (ρ : Fin 2) (i : Fin 3) (hi : (i : ℕ) < K d) (r0 n0 : ℕ) (h1 : K c + ρ = r0)
    (h2 : offK K d + (K d - 1 - i) = n0) : WP K G c d ρ i = Z3NetKN.ent (G c) r0 n0 := by
  subst h1 h2; simp [WP, hi]; rfl

/-- The invariants of the windows of the frame `(φ_∞, φ_0, φ_1)`, `m ≡ 2`, `k ≥ 1`. -/
theorem phi_vals2 (j : ℕ) :
    DefK (WP (Z3NetKN.depth 2 (j + 1))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 1) + 2)) (Z3NetKN.depth 2 (j + 1)))) ∧
      kapW1 (WP (Z3NetKN.depth 2 (j + 1))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 1) + 2)) (Z3NetKN.depth 2 (j + 1)))) = -1 ∧
      kapW2 (WP (Z3NetKN.depth 2 (j + 1))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 1) + 2)) (Z3NetKN.depth 2 (j + 1)))) = -1 := by
  set K := Z3NetKN.depth 2 (j + 1) with hKd
  set W := WP K (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 1) + 2)) K) with hW
  have hS : ((-1 : F) ^ (j + 1)) = 1 ∨ ((-1 : F) ^ (j + 1)) = -1 := neg_one_pow_eq_or _ _
  have xk := Z3NetKN.Win.win2_xk (F := F) (j + 1)
  have xk1 := Z3NetKN.Win.win2_xk1 (F := F) j
  have yk := Z3NetKN.Win.win2_yk (F := F) (j + 1)
  have yk1 := Z3NetKN.Win.win2_yk1 (F := F) j
  exact val2 W ((j + 1 : ℕ) : F) ((-1) ^ (j + 1)) hS
    ((WP_ent K _ 1 0 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk.1.trans (by ring)))
    ((WP_ent K _ 1 0 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk1.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk.2.1.trans (by ring)))
    ((WP_ent K _ 2 0 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk1.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth])).trans (xk1.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 0 1 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk.1.trans (by ring)))
    ((WP_ent K _ 0 1 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk1.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk.2.1.trans (by ring)))
    ((WP_ent K _ 2 1 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk1.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; omega)).trans (yk1.2.2.trans (by push_cast; ring)))

/-- `lem:ppinv` (b), `m ≡ 2`. -/
theorem ppinv_b2 (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) :
    DefK (winF 2 p k) ∧ kapW1 (winF 2 p k) = -1 ∧ kapW2 (winF 2 p k) = -1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set K := Z3NetKN.depth 2 (j + 1) with hKd
  have hK : K 0 + K 1 + K 2 = 3 * (j + 1) + 2 := depth_sum 2 _ (by norm_num)
  have hg := gauge_of (Z3NetKN.Phi.phi (F := ZMod p) (3 * (j + 1) + 2))
    (frameF (ZMod p) (3 * (j + 1) + 2)) (Tfr (ZMod p) (3 * (j + 1) + 2))
    (Z3NetKN.Phi.phi_T0 _) (frame_T0 _ _ (by omega)) K hK (Tfr_low _ (by omega))
    (Tfr_diag _ (by omega)) (Tfr_mul _ (by omega))
    (fun c => by fin_cases c <;> simp [K, Z3NetKN.depth] <;> omega)
  have hv := phi_vals2 (F := ZMod p) j
  obtain ⟨hD, h1, h2⟩ := kap_inv hg hv.1
  rw [winF_eq 2 p (j + 1) (by norm_num)]
  exact ⟨hD, h1.trans hv.2.1, h2.trans hv.2.2⟩

/-- The invariants of the windows of the frame `(φ_∞, φ_0, φ_1)`, `m ≡ 1`, `k ≥ 2`. -/
theorem phi_vals1 (j : ℕ) :
    DefJ (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) ∧
      JW1 (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) = 1 ∧
      JW2 (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) = -1 ∧
      JW3 (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) = 2 ∧
      JW4 (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) = 2 ∧
      JW5 (WP (Z3NetKN.depth 1 (j + 2))
        (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) (Z3NetKN.depth 1 (j + 2)))) = 1 := by
  set K := Z3NetKN.depth 1 (j + 2) with hKd
  set W := WP K (gr (Z3NetKN.Phi.phi (F := F) (3 * (j + 2) + 1)) K) with hW
  have hS : ((-1 : F) ^ (j + 2)) = 1 ∨ ((-1 : F) ^ (j + 2)) = -1 := neg_one_pow_eq_or _ _
  have hc := two_choose_cast (F := F) (j + 2)
  push_cast at hc
  have xi0 := Z3NetKN.Win.win1_xi0 (F := F) (j + 2) (by omega)
  have xi1 := Z3NetKN.Win.win1_xi1 (F := F) (j + 1)
  have xi2 := win1_xi2' (F := F) j
  have eta0 := Z3NetKN.Win.win1_eta0 (F := F) (j + 1)
  have eta1 := Z3NetKN.Win.win1_eta1 (F := F) j
  have zeta0 := Z3NetKN.Win.win1_zeta0 (F := F) (j + 1)
  have zeta1 := Z3NetKN.Win.win1_zeta1 (F := F) j
  exact val1 W ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) (((j + 2).choose 2 : ℕ) : F) hS
    (two_choose_cast (j + 2))
    ((WP_ent K _ 1 0 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi0.1.trans (by ring)))
    ((WP_ent K _ 1 0 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi1.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 0 0 2 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 0 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi0.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 0 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi1.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 0 1 2 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi2.2.1.trans (by push_cast; linear_combination (-1) ^ (j + 2) * hc)))
    ((WP_ent K _ 2 0 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi0.2.2.1.trans (by ring)))
    ((WP_ent K _ 2 0 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi1.2.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 0 2 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi2.2.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi0.2.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi1.2.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 2 0 1 2 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (xi2.2.2.2.trans (by push_cast; linear_combination (-1 : F) * hc)))
    ((WP_ent K _ 0 1 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta0.1.trans (by ring)))
    ((WP_ent K _ 0 1 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta1.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta0.2.1.trans (by ring)))
    ((WP_ent K _ 2 1 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta1.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta0.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 2 1 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (eta1.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 0 2 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta0.1.trans (by ring)))
    ((WP_ent K _ 0 2 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta1.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 2 0 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta0.2.1.trans (by ring)))
    ((WP_ent K _ 1 2 0 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta1.2.1.trans (by push_cast; ring)))
    ((WP_ent K _ 1 2 1 0 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta0.2.2.trans (by push_cast; ring)))
    ((WP_ent K _ 1 2 1 1 (by simp [K, Z3NetKN.depth]) _ _ (by simp [K, Z3NetKN.depth])
      (by simp [K, offK, Z3NetKN.depth]; try omega)).trans (zeta1.2.2.trans (by push_cast; ring)))

/-- `lem:ppinv` (b), `m ≡ 1`. -/
theorem ppinv_b1 (p k : ℕ) [Fact p.Prime] (hk : 2 ≤ k) :
    DefJ (winF 1 p k) ∧ JW1 (winF 1 p k) = 1 ∧ JW2 (winF 1 p k) = -1 ∧ JW3 (winF 1 p k) = 2 ∧
      JW4 (winF 1 p k) = 2 ∧ JW5 (winF 1 p k) = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  set K := Z3NetKN.depth 1 (j + 2) with hKd
  have hK : K 0 + K 1 + K 2 = 3 * (j + 2) + 1 := depth_sum 1 _ (by norm_num)
  have hg := gauge_of (Z3NetKN.Phi.phi (F := ZMod p) (3 * (j + 2) + 1))
    (frameF (ZMod p) (3 * (j + 2) + 1)) (Tfr (ZMod p) (3 * (j + 2) + 1))
    (Z3NetKN.Phi.phi_T0 _) (frame_T0 _ _ (by omega)) K hK (Tfr_low _ (by omega))
    (Tfr_diag _ (by omega)) (Tfr_mul _ (by omega))
    (fun c => by fin_cases c <;> simp [K, Z3NetKN.depth] <;> omega)
  have hv := phi_vals1 (F := ZMod p) j
  obtain ⟨hD, h1, h2, h3, h4, h5⟩ := J_inv hg hv.1
  rw [winF_eq 1 p (j + 2) (by norm_num)]
  exact ⟨hD, h1.trans hv.2.1, h2.trans hv.2.2.1, h3.trans hv.2.2.2.1, h4.trans hv.2.2.2.2.1,
    h5.trans hv.2.2.2.2.2⟩

end Z3NetPI.InvB
