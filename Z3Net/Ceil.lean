/-
Proofs of Proposition `prop:ceil` (first-order ceiling) and Proposition A.
-/
module
public import Z3Net.CeilArith

@[expose] public section

namespace Z3Net.Proofs

open Matrix Finset Z3Net

/-! ## Digits of a digital point -/

/-- Digit `j` (most significant first) of `C v`, and `0` out of range. -/
def digN {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) (j : ℕ) : ZMod q :=
  if h : j < m then (C *ᵥ v) ⟨j, h⟩ else 0

theorem digN_add {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v w : Fin m → ZMod q) (j : ℕ) :
    digN C (v + w) j = digN C v j + digN C w j := by
  unfold digN; split_ifs <;> simp [mulVec_add]

theorem digN_sub {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v w : Fin m → ZMod q) (j : ℕ) :
    digN C (v - w) j = digN C v j - digN C w j := by
  unfold digN; split_ifs <;> simp [mulVec_sub]

theorem digN_smul {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (t : ZMod q)
    (v : Fin m → ZMod q) (j : ℕ) : digN C (t • v) j = t * digN C v j := by
  unfold digN; split_ifs <;> simp [mulVec_smul]

theorem coord_eq_bval {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) :
    coord q m C v = bval q (fun j => (digN C v j).val) m := by
  unfold coord bval
  rw [← Fin.sum_univ_eq_sum_range (fun j => (digN C v j).val * q ^ (m - 1 - j)) m]
  apply Fintype.sum_congr
  intro j
  simp [digN, j.isLt]

theorem coord_div {q m d : ℕ} [NeZero q] (C : Matrix (Fin m) (Fin m) (ZMod q))
    (v : Fin m → ZMod q) (hd : d ≤ m) :
    coord q m C v / q ^ (m - d) = bval q (fun j => (digN C v j).val) d := by
  rw [coord_eq_bval]
  have key : ∀ x : ℕ → ℕ, (∀ j, x j < q) → bval q x m / q ^ (m - d) = bval q x d := by
    intro x hx
    obtain ⟨e, he⟩ : ∃ e, m = d + e := ⟨m - d, by omega⟩
    rw [he, show d + e - d = e by omega]
    exact bval_div (fun j _ => hx j)
  exact key _ (fun j => ZMod.val_lt _)

/-- From the net property: every prescribed set of leading digits (box `d`) is realised. -/
theorem exists_prefix {p m : ℕ} [NeZero p] {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p)}
    (hC : IsNet0 p m (digPoint p m C)) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m)
    (t : Fin 3 → ℕ → ZMod p) : ∃ v, ∀ c, ∀ j < d c, digN (C c) v j = t c j := by
  obtain ⟨v, hv, -⟩ := hC d hd (fun c => bval p (fun j => (t c j).val) (d c))
    (fun c => bval_lt (fun j _ => ZMod.val_lt _))
  refine ⟨v, fun c j hj => ?_⟩
  have hdc : d c ≤ m := by fin_cases c <;> simp <;> omega
  have h1 := hv c
  simp only [digPoint] at h1
  rw [coord_div _ _ hdc] at h1
  have := bval_inj (fun j _ => ZMod.val_lt _) (fun j _ => ZMod.val_lt _) h1 j hj
  exact ZMod.val_injective p this

/-! ## The graph form and the axis step `n ↦ n + e_{a,k-1}` -/

theorem idx_lt (c : Fin 3) {j k : ℕ} (hj : j < k) : c.val * k + j < 3 * k := by
  have := c.isLt
  have : c.val * k ≤ 2 * k := Nat.mul_le_mul_right _ (by omega)
  omega

theorem idx_eq_iff (c a : Fin 3) {j k : ℕ} (hj : j < k) :
    c.val * k + j = a.val * k + (k - 1) ↔ c = a ∧ j = k - 1 := by
  fin_cases c <;> fin_cases a <;> simp <;> omega

section graph

variable {p k : ℕ} {C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p)}

theorem C_row (c : Fin 3) {j : ℕ} (hj : j < k) :
    C c ⟨j, by omega⟩ = boxMatrix C (fun _ => k) ⟨c.val * k + j, idx_lt c hj⟩ := by
  unfold boxMatrix
  fin_cases c
  · simp [hj]
  · simp only [Fin.isValue, Fin.mk_one, Fin.val_one]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; ext; simp
  · simp only [Fin.isValue, Fin.reduceFinMk, Fin.val_two]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1; ext; simp; omega

theorem isUnit_of_Mtilde {c d : Fin 3} (h : Mtilde k C c d ≠ 0) :
    IsUnit (boxMatrix C (fun _ => k)).det := by
  by_contra hn
  apply h
  unfold Mtilde graphBlock ent
  rw [nonsing_inv_apply_not_isUnit _ hn]
  simp

/-- Index of the last level of the cell `n_a`. -/
def lastIdx (k : ℕ) (hk : 0 < k) (a : Fin 3) : Fin (3 * k) :=
  ⟨a.val * k + (k - 1), idx_lt a (by omega)⟩

/-- The index step realising `n ↦ n + e_{a,k-1}` (the last level of the cell `n_a` increases
by one): `δ = B_kkk⁻¹ e_{a k + k - 1}`. -/
noncomputable def delta (k : ℕ) (hk : 0 < k) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (a : Fin 3) : Fin (3 * k) → ZMod p :=
  (boxMatrix C (fun _ => k))⁻¹ *ᵥ Pi.single (lastIdx k hk a) 1

theorem mulVec_delta (hk : 0 < k) (c a : Fin 3) (i : Fin (3 * k)) :
    (C c *ᵥ delta k hk C a) i = (C c * (boxMatrix C (fun _ => k))⁻¹) i (lastIdx k hk a) := by
  unfold delta
  rw [mulVec_mulVec, mulVec_single_one]
  rfl

theorem digN_delta_cell (hk : 0 < k) (hu : IsUnit (boxMatrix C (fun _ => k)).det) (c a : Fin 3)
    {j : ℕ} (hj : j < k) :
    digN (C c) (delta k hk C a) j = if c = a ∧ j = k - 1 then 1 else 0 := by
  unfold digN
  rw [dif_pos (by omega), mulVec_delta]
  have : (C c * (boxMatrix C (fun _ => k))⁻¹) ⟨j, by omega⟩ (lastIdx k hk a)
      = (boxMatrix C (fun _ => k) * (boxMatrix C (fun _ => k))⁻¹) ⟨c.val * k + j, idx_lt c hj⟩
          (lastIdx k hk a) := by
    simp only [mul_apply]
    exact Finset.sum_congr rfl (fun l _ => by rw [C_row (C := C) c hj])
  rw [this, mul_nonsing_inv _ hu, one_apply]
  unfold lastIdx
  simp only [Fin.mk.injEq, idx_eq_iff c a hj]

theorem digN_delta_k (hk : 0 < k) (c a : Fin 3) :
    digN (C c) (delta k hk C a) k = ent (graphBlock k C c a) 0 (k - 1) := by
  unfold digN
  rw [dif_pos (by omega), mulVec_delta]
  have h1 : 0 < 2 * k ∧ k - 1 < k := ⟨by omega, by omega⟩
  have h2 : k + 0 < 3 * k ∧ a.val * k + (k - 1) < 3 * k := ⟨by omega, idx_lt a (by omega)⟩
  simp only [graphBlock, ent, h1, h2, dif_pos]
  rfl

end graph

/-! ## The coordinate change along one step: head and tail -/

section step

variable {p k : ℕ} [NeZero p]

theorem coord_sub_eq {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p) :
    (coord p m A w : ℤ) - coord p m A v
      = zval p (fun j => ((digN A w j).val : ℤ) - (digN A v j).val) m := by
  rw [coord_eq_bval, coord_eq_bval, bval_cast, bval_cast, zval_sub]

theorem val_diff_bounds (x y : ZMod p) :
    -((p : ℤ) - 1) ≤ (x.val : ℤ) - y.val ∧ (x.val : ℤ) - y.val ≤ (p : ℤ) - 1 := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  constructor <;> omega

theorem val_neg_one' (hp1 : 1 < p) : ((-1 : ZMod p).val : ℤ) = (p : ℤ) - 1 := by
  have : Fact (1 < p) := ⟨hp1⟩
  rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  omega

theorem zval_head (hk : 2 ≤ k) (e : ℕ → ℤ) (h0 : ∀ j < k - 1, e j = 0) :
    zval (p : ℤ) e (3 * k)
      = (p : ℤ) ^ (2 * k - 1) * ((p : ℤ) * e (k - 1) + e k)
        + zval (p : ℤ) (fun i => e (k + 1 + i)) (2 * k - 1) := by
  have H : zval (p : ℤ) e (k + 1) = (p : ℤ) * e (k - 1) + e k := by
    rw [show k + 1 = (k - 1) + 1 + 1 by omega, zval_succ, zval_succ, zval_eq_zero _ h0,
      show k - 1 + 1 = k by omega]
    ring
  rw [show 3 * k = (k + 1) + (2 * k - 1) by omega, zval_add, H]

/-- A transverse coordinate (cell unchanged): `|Δ| < (|M̃| + 1) p^(2k-1)` if the first offset
digit does not wrap. -/
theorem transverse_bound (hp1' : 1 < p) (hk : 2 ≤ k) (A : Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (v δ : Fin (3 * k) → ZMod p) (h0 : ∀ j < k, digN A δ j = 0) (M : ZMod p)
    (hM : digN A δ k = M) (hg : good M (digN A v k)) :
    |(coord p (3 * k) A (v + δ) : ℤ) - coord p (3 * k) A v|
      < (|M.valMinAbs| + 1) * (p : ℤ) ^ (2 * k - 1) := by
  have : Fact (1 < p) := ⟨hp1'⟩
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp1'.le
  rw [coord_sub_eq, zval_head hk]
  swap
  · intro j hj
    rw [digN_add, h0 j (by omega), add_zero, sub_self]
  rw [digN_add, h0 (k - 1) (by omega), add_zero, sub_self, mul_zero, zero_add, digN_add, hM]
  unfold good at hg
  rw [hg, add_sub_cancel_left]
  set T := zval (p : ℤ) (fun i => ((digN A (v + δ) (k + 1 + i)).val : ℤ)
    - (digN A v (k + 1 + i)).val) (2 * k - 1)
  have hT1 : T ≤ (p : ℤ) ^ (2 * k - 1) - 1 :=
    zval_le hp1 (fun j _ => (val_diff_bounds _ _).2)
  have hT2 : -((p : ℤ) ^ (2 * k - 1) - 1) ≤ T :=
    zval_ge hp1 (fun j _ => (val_diff_bounds _ _).1)
  have hP : (0 : ℤ) < (p : ℤ) ^ (2 * k - 1) := by positivity
  have h1 := neg_abs_le M.valMinAbs
  have h2 := le_abs_self M.valMinAbs
  rw [abs_lt]
  constructor <;> nlinarith

/-- The axis coordinate `a`: with the cell digit `k-1` stepping `0 → 1` and the offset digits
`k, …, 2k-2` all `= -1`, `Δ = p^(2k-1) val(M) + T` with `-(p^(2k-1)-1) ≤ T ≤ p^(k+1) - 1`. -/
theorem axis_decomp (hp1' : 1 < p) (hk : 2 ≤ k) (A : Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (v δ : Fin (3 * k) → ZMod p) (h0 : ∀ j < k - 1, digN A δ j = 0)
    (h1 : digN A δ (k - 1) = 1) (hv1 : digN A v (k - 1) = 0) (M : ZMod p)
    (hM : digN A δ k = M) (hM0 : M ≠ 0) (hneg : ∀ j, k ≤ j → j < 2 * k - 1 → digN A v j = -1) :
    ∃ T : ℤ, (coord p (3 * k) A (v + δ) : ℤ) - coord p (3 * k) A v
        = (p : ℤ) ^ (2 * k - 1) * (M.val : ℤ) + T
      ∧ -((p : ℤ) ^ (2 * k - 1) - 1) ≤ T ∧ T ≤ (p : ℤ) ^ (k + 1) - 1 := by
  have : Fact (1 < p) := ⟨hp1'⟩
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp1'.le
  rw [coord_sub_eq, zval_head hk]
  swap
  · intro j hj
    rw [digN_add, h0 j hj, add_zero, sub_self]
  set T := zval (p : ℤ) (fun i => ((digN A (v + δ) (k + 1 + i)).val : ℤ)
    - (digN A v (k + 1 + i)).val) (2 * k - 1) with hTdef
  refine ⟨T, ?_, ?_, ?_⟩
  · rw [digN_add, h1, hv1, zero_add, ZMod.val_one, ZMod.val_zero, digN_add, hM,
      hneg k le_rfl (by omega), val_neg_one' hp1']
    have hMv : 1 ≤ M.val := by
      rcases Nat.eq_zero_or_pos M.val with h | h
      · exact absurd ((ZMod.val_eq_zero M).mp h) hM0
      · exact h
    rw [neg_add_eq_sub, ZMod.val_sub (by rw [ZMod.val_one]; exact hMv), ZMod.val_one]
    push_cast [hMv]
    ring
  · exact zval_ge hp1 (fun j _ => (val_diff_bounds _ _).1)
  · rw [hTdef, show 2 * k - 1 = (k - 2) + (k + 1) by omega, zval_add]
    have hA : zval (p : ℤ) (fun i => ((digN A (v + δ) (k + 1 + i)).val : ℤ)
        - (digN A v (k + 1 + i)).val) (k - 2) ≤ 0 := by
      apply zval_nonpos (by positivity)
      intro j hj
      rw [hneg (k + 1 + j) (by omega) (by omega), val_neg_one' hp1']
      have := ZMod.val_lt (digN A (v + δ) (k + 1 + j))
      omega
    have hB := zval_le hp1 (n := k + 1) (e := fun j => ((digN A (v + δ) (k + 1 + (k - 2 + j))).val : ℤ)
        - (digN A v (k + 1 + (k - 2 + j))).val) (fun j _ => (val_diff_bounds _ _).2)
    have hP : (0 : ℤ) ≤ (p : ℤ) ^ (k + 1) := by positivity
    nlinarith

end step

/-! ## The witness pair -/

theorem fin3_ne1 (a : Fin 3) : a + 1 ≠ a := by fin_cases a <;> decide
theorem fin3_ne2 (a : Fin 3) : a + 2 ≠ a := by fin_cases a <;> decide
theorem fin3_ne21 (a : Fin 3) : a + 2 ≠ a + 1 := by fin_cases a <;> decide

/-- **Core of `prop:ceil`.** For a digital `(0,3k,3)`-net over `𝔽_p` (`p` odd prime, `k ≥ 2`)
with `M̃_aa ≠ 0` there are two distinct indices `v`, `w = v + δ` (neighbouring cells along the
last level of axis `a`) such that, in integer coordinates,
`Δ_a = p^(2k-1) val(M_aa) + T` with `-(p^(2k-1)-1) ≤ T ≤ p^(k+1)-1`, and
`|Δ_c| < (|M̃_ca| + 1) p^(2k-1)` for the two other coordinates. -/
theorem ceil_core {p k : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (hM : Mtilde k C a a ≠ 0) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      (∃ T : ℤ, (coord p (3 * k) (C a) w : ℤ) - coord p (3 * k) (C a) v
          = (p : ℤ) ^ (2 * k - 1) * ((ent (graphBlock k C a a) 0 (k - 1)).val : ℤ) + T
        ∧ -((p : ℤ) ^ (2 * k - 1) - 1) ≤ T ∧ T ≤ (p : ℤ) ^ (k + 1) - 1) ∧
      |(coord p (3 * k) (C (a + 1)) w : ℤ) - coord p (3 * k) (C (a + 1)) v|
        < (|Mtilde k C (a + 1) a| + 1) * (p : ℤ) ^ (2 * k - 1) ∧
      |(coord p (3 * k) (C (a + 2)) w : ℤ) - coord p (3 * k) (C (a + 2)) v|
        < (|Mtilde k C (a + 2) a| + 1) * (p : ℤ) ^ (2 * k - 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hk0 : 0 < k := by omega
  have hu := isUnit_of_Mtilde hM
  have n1 := fin3_ne1 a
  have n2 := fin3_ne2 a
  have n21 := fin3_ne21 a
  set δ := delta k hk0 C a with hδ
  set M : Fin 3 → ZMod p := fun c => ent (graphBlock k C c a) 0 (k - 1) with hMdef
  have hMt : ∀ c, Mtilde k C c a = (M c).valMinAbs := fun c => rfl
  -- target digits of the axis coordinate: cell `0`, first `k-1` offset digits `-1`
  set τ : ℕ → ZMod p := fun j => if j < k then 0 else -1 with hτ
  -- the boxes `(2k-1, k+1, 0)` and `(2k-1, 0, k+1)` (in the order `a, a+1, a+2`)
  set d1 : Fin 3 → ℕ := fun c => if c = a then 2 * k - 1 else if c = a + 1 then k + 1 else 0
  set d2 : Fin 3 → ℕ := fun c => if c = a then 2 * k - 1 else if c = a + 2 then k + 1 else 0
  have hd1 : d1 0 + d1 1 + d1 2 = 3 * k := by fin_cases a <;> simp [d1] <;> omega
  have hd2 : d2 0 + d2 1 + d2 2 = 3 * k := by fin_cases a <;> simp [d2] <;> omega
  have d1a : d1 a = 2 * k - 1 := by simp [d1]
  have d1b : d1 (a + 1) = k + 1 := by simp [d1, n1]
  have d2a : d2 a = 2 * k - 1 := by simp [d2]
  have d2c : d2 (a + 2) = k + 1 := by simp [d2, n2]
  obtain ⟨v1, hv1⟩ := exists_prefix hC d1 hd1 (fun c j => if c = a then τ j else 0)
  obtain ⟨v2, hv2⟩ := exists_prefix hC d1 hd1
    (fun c j => if c = a then τ j else if j = k then 1 else 0)
  obtain ⟨v3, hv3⟩ := exists_prefix hC d2 hd2
    (fun c j => if c = a then τ j else if j = k then digN (C (a + 2)) v1 k + 1 else 0)
  have ha1 : ∀ j < 2 * k - 1, digN (C a) v1 j = τ j := fun j hj => by
    simpa using hv1 a j (by rw [d1a]; exact hj)
  have ha2 : ∀ j < 2 * k - 1, digN (C a) v2 j = τ j := fun j hj => by
    simpa using hv2 a j (by rw [d1a]; exact hj)
  have ha3 : ∀ j < 2 * k - 1, digN (C a) v3 j = τ j := fun j hj => by
    simpa using hv3 a j (by rw [d2a]; exact hj)
  have hb1 : digN (C (a + 1)) v1 k = 0 := by
    simpa [n1] using hv1 (a + 1) k (by rw [d1b]; omega)
  have hb2 : digN (C (a + 1)) v2 k = 1 := by
    simpa [n1] using hv2 (a + 1) k (by rw [d1b]; omega)
  have hc3 : digN (C (a + 2)) v3 k = digN (C (a + 2)) v1 k + 1 := by
    simpa [n2] using hv3 (a + 2) k (by rw [d2c]; omega)
  -- two directions inside the affine set of the axis conditions
  set u1 := v2 - v1
  set u2 := v3 - v1
  have hu1a : ∀ j < 2 * k - 1, digN (C a) u1 j = 0 := fun j hj => by
    rw [digN_sub, ha2 j hj, ha1 j hj, sub_self]
  have hu2a : ∀ j < 2 * k - 1, digN (C a) u2 j = 0 := fun j hj => by
    rw [digN_sub, ha3 j hj, ha1 j hj, sub_self]
  have hu1b : digN (C (a + 1)) u1 k = 1 := by rw [digN_sub, hb2, hb1, sub_zero]
  have hu2c : digN (C (a + 2)) u2 k = 1 := by rw [digN_sub, hc3, add_sub_cancel_left]
  obtain ⟨u, hua, hub, huc⟩ : ∃ u : Fin (3 * k) → ZMod p,
      (∀ j < 2 * k - 1, digN (C a) u j = 0) ∧ digN (C (a + 1)) u k ≠ 0
        ∧ digN (C (a + 2)) u k ≠ 0 := by
    have : Fact p.Prime := ⟨hp⟩
    by_cases h1 : digN (C (a + 2)) u1 k = 0
    · by_cases h2 : digN (C (a + 1)) u2 k = 0
      · refine ⟨u1 + u2, fun j hj => ?_, ?_, ?_⟩
        · rw [digN_add, hu1a j hj, hu2a j hj, add_zero]
        · rw [digN_add, hu1b, h2, add_zero]; exact one_ne_zero
        · rw [digN_add, hu2c, h1, zero_add]; exact one_ne_zero
      · exact ⟨u2, hu2a, h2, by rw [hu2c]; exact one_ne_zero⟩
    · exact ⟨u1, hu1a, by rw [hu1b]; exact one_ne_zero, h1⟩
  -- a point on the line avoiding both wrap sets
  obtain ⟨t, htb, htc⟩ := exists_good_line hp hp2 (M (a + 1)) (M (a + 2))
    (digN (C (a + 1)) v1 k) (digN (C (a + 1)) u k) (digN (C (a + 2)) v1 k)
    (digN (C (a + 2)) u k) hub huc
  set v := v1 + t • u with hv
  have hva : ∀ j < 2 * k - 1, digN (C a) v j = τ j := fun j hj => by
    rw [hv, digN_add, digN_smul, hua j hj, mul_zero, add_zero, ha1 j hj]
  have hvb : digN (C (a + 1)) v k = digN (C (a + 1)) v1 k + t * digN (C (a + 1)) u k := by
    rw [hv, digN_add, digN_smul]
  have hvc : digN (C (a + 2)) v k = digN (C (a + 2)) v1 k + t * digN (C (a + 2)) u k := by
    rw [hv, digN_add, digN_smul]
  -- the step
  have hcell : ∀ c, c ≠ a → ∀ j < k, digN (C c) δ j = 0 := fun c hc j hj => by
    rw [hδ, digN_delta_cell hk0 hu c a hj, if_neg (fun h => hc h.1)]
  have hoff : ∀ c, digN (C c) δ k = M c := fun c => digN_delta_k hk0 c a
  refine ⟨v, v + δ, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : δ = 0 := by
      have := congrArg (fun x => x - v) h
      simpa using this.symm
    have h1 := digN_delta_cell (C := C) hk0 hu a a (j := k - 1) (by omega)
    rw [← hδ, h0, if_pos ⟨rfl, rfl⟩] at h1
    simp [digN] at h1
    have : Fact (1 < p) := ⟨hp1⟩
    exact zero_ne_one h1
  · have hMa0 : M a ≠ 0 := by
      intro h; apply hM; rw [hMt, h, ZMod.valMinAbs_zero]
    exact axis_decomp hp1 hk (C a) v δ
      (fun j hj => by
        rw [hδ, digN_delta_cell hk0 hu a a (by omega), if_neg (fun h => by omega)])
      (by rw [hδ, digN_delta_cell hk0 hu a a (by omega), if_pos ⟨rfl, rfl⟩])
      (by rw [hva (k - 1) (by omega), hτ]; simp; omega)
      (M a) (hoff a) hMa0
      (fun j hj1 hj2 => by rw [hva j hj2, hτ]; simp; omega)
  · rw [hMt]
    exact transverse_bound hp1 hk (C (a + 1)) v δ (hcell _ n1) (M (a + 1)) (hoff _)
      (by rw [hvb]; exact htb)
  · rw [hMt]
    exact transverse_bound hp1 hk (C (a + 2)) v δ (hcell _ n2) (M (a + 2)) (hoff _)
      (by rw [hvc]; exact htc)

/-! ## Real-number bounds -/

theorem sum_fin3_rot (f : Fin 3 → ℝ) (a : Fin 3) : ∑ c, f c = f a + f (a + 1) + f (a + 2) := by
  fin_cases a <;> simp [Fin.sum_univ_three] <;> ring

/-- `|D| < B p^(2k-1)` gives `(D / p^(2k))² < B² / p²`. -/
theorem sq_div_lt_of_abs {p k : ℕ} (hp : 1 < p) (hk : 1 ≤ k) (D B : ℤ)
    (h : |D| < B * (p : ℤ) ^ (2 * k - 1)) :
    ((D : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < (B : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hQ : (0 : ℝ) < (p : ℝ) ^ (2 * k - 1) := by positivity
  have hpow : (p : ℝ) ^ (2 * k) = (p : ℝ) ^ (2 * k - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  have hD : |(D : ℝ)| < (B : ℝ) * (p : ℝ) ^ (2 * k - 1) := by exact_mod_cast h
  have hB : (D : ℝ) / (p : ℝ) ^ (2 * k - 1) ∈ Set.Ioo (-(B : ℝ)) B := by
    rw [abs_lt] at hD
    constructor
    · rw [lt_div_iff₀ hQ]; linarith
    · rw [div_lt_iff₀ hQ]; linarith
  have e : ((D : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 = ((D : ℝ) / (p : ℝ) ^ (2 * k - 1)) ^ 2 / (p : ℝ) ^ 2 := by
    rw [hpow]; field_simp
  rw [e]
  apply div_lt_div_of_pos_right _ (by positivity)
  exact sq_lt_sq' hB.1 hB.2

/-- Integer coordinate difference `X_c(w) - X_c(v)`. -/
def dz {p k : ℕ} (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p)) (c : Fin 3)
    (v w : Fin (3 * k) → ZMod p) : ℤ :=
  (coord p (3 * k) (C c) w : ℤ) - coord p (3 * k) (C c) v

theorem cellDist2_eq {p k : ℕ} (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (a : Fin 3) (v w : Fin (3 * k) → ZMod p) :
    cellDist2 p k (digPoint p (3 * k) C w) (digPoint p (3 * k) C v)
      = ((dz C a v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 + ((dz C (a + 1) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2
        + ((dz C (a + 2) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 := by
  unfold cellDist2
  rw [sum_fin3_rot _ a]
  simp only [digPoint, dz]
  push_cast
  ring

/-- **Proposition `prop:ceil` (i)** (statement identical to `Z3Net.ceil_neg`). -/
theorem ceil_neg (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : Mtilde k C a a ≤ -1) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w)
        < (1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ (k - 1)) ^ 2
          + (((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ) ^ 2 + ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ) ^ 2)
            / (p : ℝ) ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨v, w, hvw, ⟨T, hDa, hT1, hT2⟩, hb, hc⟩ :=
    ceil_core hp hp2 hk C hC a (by omega)
  refine ⟨w, v, hvw.symm, ?_⟩
  rw [cellDist2_eq C a v w, add_div]
  have h2 := sq_div_lt_of_abs hp1 (by omega) _ _ hb
  have h3 := sq_div_lt_of_abs hp1 (by omega) _ _ hc
  change ((dz C (a + 1) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < _ at h2
  change ((dz C (a + 2) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < _ at h3
  suffices h1 : ((dz C a v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < (1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ (k - 1)) ^ 2 by
    linarith
  -- the axis coordinate
  set M := ent (graphBlock k C a a) 0 (k - 1)
  have hMt : Mtilde k C a a = M.valMinAbs := rfl
  have hval : (M.val : ℤ) = M.valMinAbs + p := by
    have := ZMod.valMinAbs_def_pos M
    rw [← hMt] at this ⊢
    split_ifs at this <;> omega
  have hlow : -((p : ℤ) / 2) ≤ Mtilde k C a a := by
    have := ZMod.natAbs_valMinAbs_le M
    rw [hMt]; omega
  change dz C a v w = _ at hDa
  set D := dz C a v w
  have hval' : (M.val : ℤ) = Mtilde k C a a + p := by rw [hMt]; exact hval
  rw [hval'] at hDa
  generalize Mtilde k C a a = μ at ha hlow hDa
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have e1 : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
  have e2 : n + 2 - 1 = n + 1 := by omega
  rw [e1] at hDa hT1
  rw [e2]
  have hP : (0 : ℤ) < (p : ℤ) := by omega
  have hD0 : 0 < D := by
    rw [hDa]
    have h3 : (0 : ℤ) < (p : ℤ) ^ (2 * n + 3) := by positivity
    have h4 : 1 ≤ μ + p := by omega
    nlinarith
  have hDR : D < (p : ℤ) ^ (2 * n + 4) - (p : ℤ) ^ (2 * n + 3) + (p : ℤ) ^ (n + 3) := by
    rw [hDa, show (p : ℤ) ^ (2 * n + 4) = (p : ℤ) ^ (2 * n + 3) * p by ring]
    have h3 : (0 : ℤ) < (p : ℤ) ^ (2 * n + 3) := by positivity
    nlinarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hP
  have hreal : (D : ℝ) / (p : ℝ) ^ (2 * (n + 2)) < 1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ (n + 1) := by
    have : (D : ℝ) < (p : ℝ) ^ (2 * n + 4) - (p : ℝ) ^ (2 * n + 3) + (p : ℝ) ^ (n + 3) := by
      exact_mod_cast hDR
    rw [div_lt_iff₀ (by positivity)]
    have e : (1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ (n + 1)) * (p : ℝ) ^ (2 * (n + 2))
        = (p : ℝ) ^ (2 * n + 4) - (p : ℝ) ^ (2 * n + 3) + (p : ℝ) ^ (n + 3) := by
      field_simp; ring
    rw [e]; exact this
  have hpos : (0 : ℝ) ≤ (D : ℝ) / (p : ℝ) ^ (2 * (n + 2)) := by
    apply div_nonneg _ (by positivity); exact_mod_cast hD0.le
  exact pow_lt_pow_left₀ hreal hpos (by norm_num)

/-- **Proposition `prop:ceil` (ii)** (statement identical to `Z3Net.ceil_pos`). -/
theorem ceil_pos (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w)
        < (((Mtilde k C a a + 1 : ℤ) : ℝ) ^ 2 + ((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ) ^ 2
            + ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ) ^ 2) / (p : ℝ) ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨v, w, hvw, ⟨T, hDa, hT1, hT2⟩, hb, hc⟩ :=
    ceil_core hp hp2 hk C hC a (by omega)
  refine ⟨w, v, hvw.symm, ?_⟩
  rw [cellDist2_eq C a v w, add_div, add_div]
  have h2 := sq_div_lt_of_abs hp1 (by omega) _ _ hb
  have h3 := sq_div_lt_of_abs hp1 (by omega) _ _ hc
  change ((dz C (a + 1) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < _ at h2
  change ((dz C (a + 2) v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2 < _ at h3
  suffices h1 : ((dz C a v w : ℝ) / (p : ℝ) ^ (2 * k)) ^ 2
      < ((Mtilde k C a a + 1 : ℤ) : ℝ) ^ 2 / (p : ℝ) ^ 2 by
    linarith
  -- the axis coordinate: `val M = M̃_aa`
  set M := ent (graphBlock k C a a) 0 (k - 1)
  have hMt : Mtilde k C a a = M.valMinAbs := rfl
  have hval : (M.val : ℤ) = Mtilde k C a a := by
    have := ZMod.valMinAbs_def_pos M
    have hlt := ZMod.val_lt M
    rw [← hMt] at this
    split_ifs at this <;> omega
  change dz C a v w = _ at hDa
  rw [hval] at hDa
  apply sq_div_lt_of_abs hp1 (by omega)
  have hP : (0 : ℤ) < (p : ℤ) := by omega
  have hpow : (p : ℤ) ^ (k + 1) ≤ (p : ℤ) ^ (2 * k - 1) :=
    pow_le_pow_right₀ (by omega) (by omega)
  have h3 : (0 : ℤ) < (p : ℤ) ^ (2 * k - 1) := by positivity
  rw [hDa, abs_lt]
  constructor <;> nlinarith

/-- **Proposition A, first part** (statement identical to `Z3Net.propA_neg`). -/
theorem propA_neg (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : Mtilde k C a a ≤ -1)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 1 - 1 / (p : ℝ) + 7 * (C₀ : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
  obtain ⟨v, w, hvw, hd⟩ := ceil_neg p k hp hp2 (by omega) C hC a ha
  refine ⟨v, w, hvw, ?_⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  set x : ℝ := 1 / (p : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx3 : x ≤ 1 / 3 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hp3r
  have hy : 1 / (p : ℝ) ^ (k - 1) ≤ x ^ 2 := by
    rw [hx, div_pow, one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hy0 : 0 < 1 / (p : ℝ) ^ (k - 1) := by positivity
  set B1 : ℝ := ((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ)
  set B2 : ℝ := ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ)
  have hc1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  set c : ℝ := (C₀ : ℝ)
  have hB1 : 0 ≤ B1 ∧ B1 ≤ c + 1 := by
    constructor
    · simp only [B1]; push_cast; positivity
    · simp only [B1, c]; push_cast
      have : |((Mtilde k C (a + 1) a : ℤ) : ℝ)| ≤ (C₀ : ℝ) := by exact_mod_cast hb
      linarith
  have hB2 : 0 ≤ B2 ∧ B2 ≤ c + 1 := by
    constructor
    · simp only [B2]; push_cast; positivity
    · simp only [B2, c]; push_cast
      have : |((Mtilde k C (a + 2) a : ℤ) : ℝ)| ≤ (C₀ : ℝ) := by exact_mod_cast hc
      linarith
  have hB1s : B1 ^ 2 ≤ (c + 1) ^ 2 := pow_le_pow_left₀ hB1.1 hB1.2 2
  have hB2s : B2 ^ 2 ≤ (c + 1) ^ 2 := pow_le_pow_left₀ hB2.1 hB2.2 2
  have hRpos : 0 < 1 - x + 7 * c ^ 2 * x ^ 2 := by nlinarith
  have hgoal : 1 - 1 / (p : ℝ) + 7 * c ^ 2 / (p : ℝ) ^ 2 = 1 - x + 7 * c ^ 2 * x ^ 2 := by
    rw [hx]; field_simp
  rw [hgoal, Real.sqrt_lt' hRpos]
  have hd' : cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w)
      < (1 - x + 1 / (p : ℝ) ^ (k - 1)) ^ 2 + (B1 ^ 2 + B2 ^ 2) * x ^ 2 := by
    have e : (B1 ^ 2 + B2 ^ 2) / (p : ℝ) ^ 2 = (B1 ^ 2 + B2 ^ 2) * x ^ 2 := by
      rw [hx]; field_simp
    rw [← e]; exact hd
  have h1 : (1 - x + 1 / (p : ℝ) ^ (k - 1)) ^ 2 ≤ (1 - x + x ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (B1 ^ 2 + B2 ^ 2) * x ^ 2 ≤ 2 * (c + 1) ^ 2 * x ^ 2 := by
    have : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have h3 : (1 - x + x ^ 2) ^ 2 + 2 * (c + 1) ^ 2 * x ^ 2 ≤ (1 - x + 7 * c ^ 2 * x ^ 2) ^ 2 := by
    have hx2 : 0 < x ^ 2 := by positivity
    have h7 : 0 ≤ 7 * c ^ 2 - 1 := by nlinarith
    have hk1 : 0 ≤ (7 * c ^ 2 - 1) * (2 - 2 * x) - 2 * (c + 1) ^ 2 := by
      nlinarith [mul_nonneg h7 (by linarith : (0 : ℝ) ≤ 1 / 3 - x),
        mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) (by linarith : (0 : ℝ) ≤ 11 * c + 5)]
    have hk2 : 0 ≤ (7 * c ^ 2 - 1) * (7 * c ^ 2 + 1) * x ^ 2 := by
      have : 0 ≤ 7 * c ^ 2 - 1 := by nlinarith
      positivity
    have e : (1 - x + 7 * c ^ 2 * x ^ 2) ^ 2 - ((1 - x + x ^ 2) ^ 2 + 2 * (c + 1) ^ 2 * x ^ 2)
        = x ^ 2 * (((7 * c ^ 2 - 1) * (2 - 2 * x) - 2 * (c + 1) ^ 2)
          + (7 * c ^ 2 - 1) * (7 * c ^ 2 + 1) * x ^ 2) := by ring
    nlinarith
  linarith

/-- **Proposition A, second part, every `k ≥ 2`** (statement identical to
`Z3Net.propA_pos_k2`). -/
theorem propA_pos_k2 (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a)
    (ha' : Mtilde k C a a ≤ C₀)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 4 * (C₀ : ℝ) / (p : ℝ) := by
  obtain ⟨v, w, hvw, hd⟩ := ceil_pos p k hp hp2 hk C hC a ha
  refine ⟨v, w, hvw, ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hc1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  set c : ℝ := (C₀ : ℝ)
  set B0 : ℝ := ((Mtilde k C a a + 1 : ℤ) : ℝ)
  set B1 : ℝ := ((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ)
  set B2 : ℝ := ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ)
  have hB0 : 0 ≤ B0 ∧ B0 ≤ c + 1 := by
    have h1 : ((Mtilde k C a a : ℤ) : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast ha'
    have h2 : (1 : ℝ) ≤ ((Mtilde k C a a : ℤ) : ℝ) := by exact_mod_cast ha
    simp only [B0, c]; push_cast; constructor <;> linarith
  have hB1 : 0 ≤ B1 ∧ B1 ≤ c + 1 := by
    have h1 : |((Mtilde k C (a + 1) a : ℤ) : ℝ)| ≤ (C₀ : ℝ) := by exact_mod_cast hb
    have h2 : (0 : ℝ) ≤ |((Mtilde k C (a + 1) a : ℤ) : ℝ)| := abs_nonneg _
    simp only [B1, c]; push_cast; constructor <;> linarith
  have hB2 : 0 ≤ B2 ∧ B2 ≤ c + 1 := by
    have h1 : |((Mtilde k C (a + 2) a : ℤ) : ℝ)| ≤ (C₀ : ℝ) := by exact_mod_cast hc
    have h2 : (0 : ℝ) ≤ |((Mtilde k C (a + 2) a : ℤ) : ℝ)| := abs_nonneg _
    simp only [B2, c]; push_cast; constructor <;> linarith
  have hs : B0 ^ 2 + B1 ^ 2 + B2 ^ 2 < (4 * c) ^ 2 := by
    have := pow_le_pow_left₀ hB0.1 hB0.2 2
    have := pow_le_pow_left₀ hB1.1 hB1.2 2
    have := pow_le_pow_left₀ hB2.1 hB2.2 2
    nlinarith
  rw [Real.sqrt_lt' (by positivity), div_pow]
  calc _ < (B0 ^ 2 + B1 ^ 2 + B2 ^ 2) / (p : ℝ) ^ 2 := hd
    _ < (4 * c) ^ 2 / (p : ℝ) ^ 2 := div_lt_div_of_pos_right hs (by positivity)

/-- **Proposition A, second part** (statement identical to `Z3Net.propA_pos`; the case `k ≥ 3`
of `propA_pos_k2`). -/
theorem propA_pos (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a)
    (ha' : Mtilde k C a a ≤ C₀)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 4 * (C₀ : ℝ) / (p : ℝ) :=
  propA_pos_k2 p k C₀ hp hp2 (by omega) hC₀ C hC a ha ha' hb hc

end Z3Net.Proofs
