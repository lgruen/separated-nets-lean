/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Bridge

@[expose] public section

/-!
# V14 stage S14′: soundness of the certificate checks of `thm:base23`

* `chain_net`: if `netChk b r` holds, every chain level `k ≤ b23NL b r` is a `(0, M₀ + 3k, 3)`-net (any shift):
  the seed by `chkNet`, each lift by `lem:lift`(A) with the admissibility of `liftChk` (`admPair`); and
  `b23Gen_succ`: the chain level `k + 1` is the lift `liftGen` of level `k` (`def:lift`).
* `c1_vcirc`: if `c1Chk b r` holds, `v°_L ≥ b23V b r` at the certificate level.
* `c2_dist`: if `c2Chk b r k` holds, every digital shift of the chain level `k` has squared toroidal distance `≥ U`.
* `wit_net`, `wit_dist`: the same for the explicit witnesses.
-/

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

lemma vecOf_dsub {b : ℕ} [NeZero b] (M x y : ℕ) : vecOf b M (dsub b M x y) = vecOf b M x - vecOf b M y := by
  rw [dsub, vecOf_dadd, vecOf_smul]
  have h1 : ((b - 1 : ℕ) : ZMod b) + 1 = 0 := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel NeZero.one_le, ZMod.natCast_self]
  rw [eq_neg_of_add_eq_zero_left h1, neg_one_smul, ← sub_eq_add_neg]

lemma colMat_mulVec_sum {b n : ℕ} (cols : List (List ℕ)) (c : Fin 3) (d : Fin n → ZMod b) :
    colMat b n cols c *ᵥ d = ∑ i : Fin n, d i • vecOf b n ((cols.getD c []).getD i 0) := by
  funext r
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colMat]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma topD_sum {b n H : ℕ} (hH : H ≤ n) (f : Fin n → Fin n → ZMod b) :
    topD H hH (∑ i, f i) = ∑ i, topD H hH (f i) := by
  funext r; simp [topD, Finset.sum_apply]

lemma topD_colMat {b : ℕ} [NeZero b] {n H : ℕ} (hH : H ≤ n) (cols : List (List ℕ)) (c : Fin 3) (d : Fin n → ZMod b) :
    topD H hH (colMat b n cols c *ᵥ d) = ∑ i : Fin n, d i • vecOf b H ((cols.getD c []).getD i 0 / b ^ (n - H)) := by
  rw [colMat_mulVec_sum, topD_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← topD_vecOf n H _ hH]
  funext r; simp [topD]

lemma colsOK_mem {b n k : ℕ} {cols : List (List ℕ)} (h : colsOK b n k cols = true) :
    ∀ cs ∈ cols, cs.length = k ∧ ∀ x ∈ cs, x < b ^ n := by
  simp only [colsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2

variable {b : ℕ} [Fact b.Prime]

lemma two_le : 2 ≤ b := (Fact.out : b.Prime).two_le

omit [Fact b.Prime] in
lemma colsOK_spec {n k : ℕ} {cols : List (List ℕ)} (h : colsOK b n k cols = true) :
    cols.length = 3 ∧ ∀ c : Fin 3, (cols.getD c []).length = k ∧ ∀ x ∈ cols.getD c [], x < b ^ n := by
  simp only [colsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun c => ?_⟩
  have hm : cols.getD c [] ∈ cols := by
    rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact c.isLt)]; exact List.getElem_mem _
  exact ⟨(h.2 _ hm).1, (h.2 _ hm).2⟩

/-- **Admissibility from the certificate** `liftChk`. -/
lemma liftChk_sound {M : ℕ} {cols : List (List ℕ)} {sA sB : List ℕ} {lam : List (List ℕ)}
    (hc : colsOK b M M cols = true) (h : liftChk b M cols sA sB lam = true) :
    Admissible (colMat b M cols) (shOf b M sA) (shOf b M sB) := by
  obtain ⟨-, hcols⟩ := colsOK_spec hc
  have hl : ∀ c : Fin 3, (cols.getD c []).length = M := fun c => (hcols c).1
  simp only [liftChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, hall⟩ := h
  intro e he1 he2
  have h1 := hall (e - 1) (by omega)
  obtain ⟨⟨a1, a2⟩, a3⟩ := h1
  rw [show e - 1 + 1 = e by omega] at a1 a2 a3
  refine ⟨?_, ?_, ?_⟩
  · exact admPair_sound M e he1 he2 cols 1 2 _ _ _ _ hl a1
  · exact admPair_sound M e he1 he2 cols 0 1 _ _ _ _ hl a2
  · have hz : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
    have := admPair_sound M e he1 he2 cols 0 2 _ _ _ _ hl a3
    have hz' : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
    rwa [vecOf_dsub, vecOf_dsub] at this

omit [Fact b.Prime] in
lemma liftChk_bounds {M : ℕ} {cols : List (List ℕ)} {sA sB : List ℕ} {lam : List (List ℕ)}
    (h : liftChk b M cols sA sB lam = true) :
    sA.length = 3 ∧ sB.length = 3 ∧ (∀ c : Fin 3, sA.getD c 0 < b ^ M) ∧ ∀ c : Fin 3, sB.getD c 0 < b ^ M := by
  simp only [liftChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hA⟩, hB⟩, hb⟩, -⟩ := h
  refine ⟨hA, hB, fun c => ?_, fun c => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by rw [hA]; exact c.isLt)]; exact hb _ (List.mem_append_left _ (List.getElem_mem _))
  · rw [List.getD_eq_getElem _ _ (by rw [hB]; exact c.isLt)]; exact hb _ (List.mem_append_right _ (List.getElem_mem _))

/-- The lifted column codes are of the right size. -/
lemma liftCols_ok {M : ℕ} {cols : List (List ℕ)} {sA sB : List ℕ} (hc : colsOK b M M cols = true)
    (hA : ∀ c : Fin 3, sA.getD c 0 < b ^ M) (hB : ∀ c : Fin 3, sB.getD c 0 < b ^ M) :
    colsOK b (M + 3) (M + 3) (liftCols b M cols sA sB) = true := by
  obtain ⟨-, hcols⟩ := colsOK_spec hc
  have hb0 : 0 < b := by have := two_le (b := b); omega
  have hl : ∀ c : Fin 3, (cols.getD c []).length = M := fun c => (hcols c).1
  simp only [colsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨rfl, fun cs hcs => ?_⟩
  -- the three coordinate lists
  have key : ∀ c : Fin 3, ((liftCols b M cols sA sB).getD c []).length = M + 3 ∧
      ∀ x ∈ (liftCols b M cols sA sB).getD c [], x < b ^ (M + 3) := by
    intro c
    have hlen : ((liftCols b M cols sA sB).getD c []).length = M + 3 := by
      fin_cases c <;> simp [liftCols, hl 0, hl 1, hl 2] <;> [exact hl 0; exact hl 1; exact hl 2]
    refine ⟨hlen, fun x hx => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [← List.getD_eq_getElem _ 0 hj, liftCols_getD b M cols sA sB hl c j (by rw [hlen] at hj; exact hj)]
    have hbl : blC M cols sA sB c j < b ^ M := by
      unfold blC
      split_ifs with h1 h2 h3
      · rw [List.getD_eq_getElem _ _ (by rw [hl c]; exact h1)]; exact (hcols c).2 _ (List.getElem_mem _)
      · exact pow_pos hb0 _
      · exact hA c
      · exact hB c
    have b2 := two_le (b := b)
    exact lc_lt hb0 (by unfold tpC; split_ifs <;> omega) hbl (by unfold j1C; split_ifs <;> omega)
      (by unfold j0C; split_ifs <;> omega)
  simp only [liftCols, List.mem_cons, List.not_mem_nil, or_false] at hcs
  rcases hcs with rfl | rfl | rfl
  · exact ⟨(key 0).1, fun x hx => (key 0).2 x hx⟩
  · exact ⟨(key 1).1, fun x hx => (key 1).2 x hx⟩
  · exact ⟨(key 2).1, fun x hx => (key 2).2 x hx⟩

/-- The certificate data of lift `k` of the chain. -/
lemma netChk_lift {r : ℕ} (h : netChk b r = true) (k : ℕ) (hk : k < b23NL b r) :
    liftChk b (b23Lev b r k) (b23Cols b r k) ((b23Lifts b r).getD k ([], [])).1 ((b23Lifts b r).getD k ([], [])).2
      ((b23Lam b r).getD k []) = true := by
  simp only [netChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 k hk

/-- **The chain levels are nets**, their codes are of the right size, and each is the lift of the previous one. -/
theorem chain_ok {r : ℕ} (h : netChk b r = true) : ∀ k, k ≤ b23NL b r →
    colsOK b (b23Lev b r k) (b23Lev b r k) (b23Cols b r k) = true ∧
      ∀ σ, Z3NetF.IsNet0 3 b (b23Lev b r k) (Z3NetF.digPointShift b (b23Lev b r k) (b23Gen b r k) σ) := by
  have h0 := h
  simp only [netChk, Bool.and_eq_true] at h0
  obtain ⟨⟨hc0, hn0⟩, -⟩ := h0
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨-, hcols⟩ := colsOK_spec hc0
    exact ⟨hc0, fun σ => chkNet_sound _ _ (fun c => (hcols c).1) (fun c => (hcols c).2) hn0 σ⟩
  | succ k ih =>
    intro hk
    obtain ⟨hck, hnk⟩ := ih (by omega)
    have hl := netChk_lift h k (by omega)
    obtain ⟨-, -, hA, hB⟩ := liftChk_bounds hl
    have hadm := liftChk_sound hck hl
    obtain ⟨-, hcols⟩ := colsOK_spec hck
    have e := colMat_liftCols two_le (b23Lev b r k) (b23Cols b r k) _ _ (fun c => (hcols c).1)
      (fun c => (hcols c).2) hA hB
    refine ⟨liftCols_ok hck hA hB, fun σ => ?_⟩
    have := Proofs.lift_net (b23Gen b r k) (shOf b (b23Lev b r k) [0, 0, 0]) _ _ (hnk _) hadm
    rw [net_shift_iff] at this ⊢
    show Z3NetF.IsNet0 3 b (b23Lev b r k + 3) (Z3NetF.digPoint b (b23Lev b r k + 3)
      (colMat b (b23Lev b r k + 3) (liftCols b (b23Lev b r k) (b23Cols b r k) _ _)))
    rw [e]
    exact this

/-- **`def:lift` along the chain**: level `k + 1` is the lift of level `k` with the parameters `b23Lifts`. -/
theorem b23Gen_succ {r : ℕ} (h : netChk b r = true) (k : ℕ) (hk : k < b23NL b r) :
    b23Gen b r (k + 1) = liftGen (b23Gen b r k) (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).1)
      (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).2) := by
  obtain ⟨hck, -⟩ := chain_ok h k (by omega)
  obtain ⟨-, hcols⟩ := colsOK_spec hck
  obtain ⟨-, -, hA, hB⟩ := liftChk_bounds (netChk_lift h k hk)
  exact colMat_liftCols two_le _ _ _ _ (fun c => (hcols c).1) (fun c => (hcols c).2) hA hB

/-! ## Linear identities from generator columns -/

/-- The box `(d₀, d₁, d₂)` from the net property. -/
lemma box_of_net {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b))
    (hnet : Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m C 0)) (d0 d1 d2 : ℕ) (hd : d0 + d1 + d2 = m)
    (n : Fin m → ZMod b) (h0 : ∀ j : Fin m, (j : ℕ) < d0 → (C 0 *ᵥ n) j = 0)
    (h1 : ∀ j : Fin m, (j : ℕ) < d1 → (C 1 *ᵥ n) j = 0) (h2 : ∀ j : Fin m, (j : ℕ) < d2 → (C 2 *ᵥ n) j = 0) :
    n = 0 := by
  rw [net_iff_boxInj] at hnet
  apply hnet ![d0, d1, d2] (by simp [Fin.sum_univ_three, hd]) n
  intro c j hj
  fin_cases c
  · exact h0 j hj
  · exact h1 j hj
  · exact h2 j hj

/-! ## `v°_L` at the certificate level -/

/-- **The certificate `v°_L ≥ v`** from `c1Chk` (and the net property of the chain). -/
theorem c1_vcirc {r : ℕ} (hn : netChk b r = true) (h : c1Chk b r = true)
    (hev : 2 * (b23Lev b r (b23NL b r) / 2) = b23Lev b r (b23NL b r)) (hL1 : 1 ≤ b23Lev b r (b23NL b r)) :
    b23V b r ≤ vcirc b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  set L := b23Lev b r (b23NL b r) with hLdef
  set H := L / 2
  set cols := b23Cols b r (b23NL b r)
  have hnet := (chain_ok hn (b23NL b r) le_rfl).2 0
  simp only [c1Chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.mem_append] at h
  obtain ⟨⟨⟨⟨⟨hc, hgx⟩, hgy⟩, hbd⟩, hid⟩, hchk⟩ := h
  have hbx : ∀ x ∈ b23Gx b r, x < b ^ H := fun x hx => hbd x (Or.inl hx)
  have hby : ∀ x ∈ b23Gy b r, x < b ^ H := fun x hx => hbd x (Or.inr hx)
  haveI hne : Nonempty {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} :=
    ⟨⟨(0, Pi.single ⟨0, hL1⟩ 1), fun e => by have := congrFun e ⟨0, hL1⟩; simp at this⟩⟩
  apply le_ciInf
  rintro ⟨⟨n, n'⟩, hnn⟩
  simp only
  set d := n' - n
  have hd : d ≠ 0 := fun h0 => hnn (sub_eq_zero.1 h0).symm
  set Δ : Fin 3 → Fin H → ZMod b := fun c => topD H (Nat.div_le_self L 2) (b23Gen b r (b23NL b r) c *ᵥ d)
  -- `Δ_z = G_x Δ_x + G_y Δ_y`
  have hz : Δ 2 = colMatR b H H (b23Gx b r) *ᵥ Δ 0 + colMatR b H H (b23Gy b r) *ᵥ Δ 1 := by
    simp only [Δ, b23Gen]
    rw [topD_colMat, topD_colMat, topD_colMat, Matrix.mulVec_sum, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← vecOf_matvec _ _ _ hgx,
      ← vecOf_matvec _ _ _ hgy, ← vecOf_dadd]
    congr 2
    have := hid i i.isLt
    simpa [L, H, cols] using this
  have hxy : ¬(Δ 0 = 0 ∧ Δ 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hd
    apply box_of_net _ hnet H H 0 (by omega) d
    · intro j hj; exact congrFun h0 ⟨j, hj⟩
    · intro j hj; exact congrFun h1 ⟨j, hj⟩
    · intro j hj; omega
  -- the minimizing digits
  have hX : ∀ c : Fin 3, ∃ X : Fin H → ZMod b, muD b (Δ c) = wt X (Δ c) := by
    intro c
    obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin H → ZMod b))
      (fun X : Fin H → ZMod b => Z3NetF.cres (b ^ H) ((dval b (X + Δ c) : ℤ) - dval b X))
    exact ⟨X, hX⟩
  choose X hXc using hX
  have := chk1_sound two_le hgx hgy hbx hby hchk (Δ 0) (Δ 1) hxy X
  rw [← hz, ← hXc, ← hXc, ← hXc] at this
  rw [Fin.sum_univ_three]
  exact this

/-! ## The exact every-shift distances at the chain levels -/

/-- **The every-shift distance at a chain level** from `c2Chk`. -/
theorem c2_dist {r k : ℕ} (hn : netChk b r = true) (hk : k < b23NL b r) (h : c2Chk b r k = true)
    (τ : Fin 3 → Fin (b23Lev b r k) → ZMod b) (v w : Fin (b23Lev b r k) → ZMod b) (hvw : v ≠ w) :
    ((b23Mid b r).getD k (0, 0, [], [], [])).2.1 ≤
      Z3NetF.torusDist2 (b ^ b23Lev b r k) (Z3NetF.digPointShift b (b23Lev b r k) (b23Gen b r k) τ v)
        (Z3NetF.digPointShift b (b23Lev b r k) (b23Gen b r k) τ w) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  set D := (b23Mid b r).getD k (0, 0, [], [], [])
  have hnet := (chain_ok hn k (by omega)).2 0
  simp only [c2Chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hc, hx⟩, hy⟩, hz⟩, h2⟩, hid⟩, hchk⟩ := h
  obtain ⟨hxl, hxs⟩ := colsOK_spec hx
  obtain ⟨hyl, hys⟩ := colsOK_spec hy
  obtain ⟨hzl, hzs⟩ := colsOK_spec hz
  set Hp := D.1
  set d := w - v
  have hd : d ≠ 0 := fun h0 => hvw (sub_eq_zero.1 h0).symm
  set Δ : Fin 3 → Fin (b23Lev b r k) → ZMod b := fun c => b23Gen b r k c *ᵥ d
  set tx := topD Hp (by omega) (Δ 0)
  set ty := topD Hp (by omega) (Δ 1)
  set tz := topD ((b23Lev b r k) - 2 * Hp) (by omega) (Δ 2)
  have memL : ∀ (L : List (List ℕ)), L.length = 3 → ∀ c : Fin 3, L.getD c [] ∈ L := fun L hL c => by
    rw [List.getD_eq_getElem _ _ (by rw [hL]; exact c.isLt)]; exact List.getElem_mem _
  have hΔ : ∀ c : Fin 3, Δ c = colMatR b (b23Lev b r k) Hp (D.2.2.1.getD c []) *ᵥ tx + colMatR b (b23Lev b r k) Hp (D.2.2.2.1.getD c []) *ᵥ ty +
      colMatR b (b23Lev b r k) ((b23Lev b r k) - 2 * Hp) (D.2.2.2.2.getD c []) *ᵥ tz := by
    intro c
    simp only [Δ, tx, ty, tz, b23Gen]
    rw [topD_colMat, topD_colMat, topD_colMat, Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum,
      colMat_mulVec_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← smul_add,
      ← vecOf_matvec _ _ _ (hxs c).1, ← vecOf_matvec _ _ _ (hys c).1, ← vecOf_matvec _ _ _ (hzs c).1,
      ← vecOf_dadd, ← vecOf_dadd, show (b23Lev b r k) - ((b23Lev b r k) - 2 * Hp) = 2 * Hp by omega]
    congr 2
    have := hid i i.isLt c c.isLt
    simpa [D, Hp] using this
  have hne : ¬(tx = 0 ∧ ty = 0 ∧ tz = 0) := by
    rintro ⟨h0, h1, h3⟩
    apply hd
    apply box_of_net _ hnet Hp Hp ((b23Lev b r k) - 2 * Hp) (by omega) d
    · intro j hj; exact congrFun h0 ⟨j, hj⟩
    · intro j hj; exact congrFun h1 ⟨j, hj⟩
    · intro j hj; exact congrFun h3 ⟨j, hj⟩
  have hX := chk2_sound two_le h2 hxl hyl hzl (fun c hc => (colsOK_mem hx c hc).1) (fun c hc => (colsOK_mem hy c hc).1)
    (fun c hc => (colsOK_mem hz c hc).1) (fun c hc => (colsOK_mem hx c hc).2) (fun c hc => (colsOK_mem hy c hc).2)
    (fun c hc => (colsOK_mem hz c hc).2) hchk tx ty tz Δ hΔ rfl rfl rfl hne
  have hmu := sum_muD_ge _ Δ hX
  exact hmu.trans ((shiftcert_b (b23Gen b r k)).1 τ v w :)

/-! ## The witnesses -/

theorem wit_ok {m U : ℕ} {cols : List (List ℕ)} (h : witChk b m cols U = true) :
    (∀ σ, Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m (colMat b m cols) σ)) ∧
    ∀ (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b), v ≠ w →
      U ≤ Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m (colMat b m cols) τ v)
        (Z3NetF.digPointShift b m (colMat b m cols) τ w) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  simp only [witChk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hnet⟩, hdist⟩ := h
  obtain ⟨-, hcols⟩ := colsOK_spec hc
  refine ⟨fun σ => chkNet_sound m cols (fun c => (hcols c).1) (fun c => (hcols c).2) hnet σ, fun τ v w hvw => ?_⟩
  have hd : w - v ≠ 0 := fun h0 => hvw (sub_eq_zero.1 h0).symm
  have hX := chkDist_sound two_le m U cols (fun c => (hcols c).1) (fun c => (hcols c).2) hdist (w - v) hd
  exact (sum_muD_ge U (fun c => colMat b m cols c *ᵥ (w - v)) hX).trans ((shiftcert_b (colMat b m cols)).1 τ v w)

end Z3NetB23.Proofs
