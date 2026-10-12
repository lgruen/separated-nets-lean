module
public import Z3Net.PPInvVal

@[expose] public section

/-!
# `lem:ppinv` (b): changing the readings by lower-triangular matrices is a gauge move on the
windows (entry PPInv)

If `Y_c = T_c X_c` with `T_c` lower triangular (nonzero diagonal), then the graph forms satisfy
`gr Y c · D = T_c · gr X c` with `D` the block-diagonal matrix of the leading `K_c × K_c` blocks of
the `T_c` (`gr_mul`), and on the windows (`win_rel`, `gauge_of`):
`W^Y_cd = L_c W^X_cd U_d` with `L_c` (rows `K_c, K_c + 1` of `T_c`) lower triangular and `U_d` (the
inverse of the trailing levels of `T_d`, in the window index) upper triangular, i.e. the moves of
`lem:ppinv` (a). Windows are padded with `0` beyond the cell (`WP`).
-/

namespace Z3NetPI.InvT

open Matrix Finset Z3NetKN.Frame Z3NetKN.Realize Z3NetPI.InvA

variable {F : Type*} [Field F] {m : ℕ}

lemma entKN {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) :
    Z3NetKN.ent A i j = ent A i j := rfl

lemma ent_fin {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i : Fin a) (j : Fin b) :
    ent A i j = A i j := by
  simp [ent, i.isLt, j.isLt]

lemma offK_add_le (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (d : Fin 3) : offK K d + K d ≤ m := by
  fin_cases d <;> simp [offK] <;> omega

lemma blk_iff (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (x : ℕ) (hx : x < m) (d : Fin 3) :
    blk K x = d ↔ offK K d ≤ x ∧ x < offK K d + K d := by
  by_cases h1 : x < K 0
  · have : blk K x = 0 := by simp [blk, h1]
    rw [this]; fin_cases d <;> simp [offK] <;> omega
  · by_cases h2 : x < K 0 + K 1
    · have : blk K x = 1 := by simp [blk, h1, h2]
      rw [this]; fin_cases d <;> simp [offK] <;> omega
    · have : blk K x = 2 := by simp [blk, h1, h2]
      rw [this]; fin_cases d <;> simp [offK] <;> omega

lemma sum_block (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (d : Fin 3) (f : Fin m → F)
    (hf : ∀ n : Fin m, blk K n ≠ d → f n = 0) :
    ∑ n, f n = ∑ j ∈ range (K d), (if h : offK K d + j < m then f ⟨offK K d + j, h⟩ else 0) := by
  have e1 : ∑ n, f n = ∑ x ∈ range m, (if h : x < m then f ⟨x, h⟩ else 0) := by
    rw [Finset.sum_range]; simp
  rw [e1]
  have hle := offK_add_le K hK d
  have hsub : Ico (offK K d) (offK K d + K d) ⊆ range m := by
    intro x hx; simp only [mem_Ico, mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub (fun x hx hx' => ?_)]
  · rw [Finset.sum_Ico_eq_sum_range]; simp
  · simp only [mem_Ico, mem_range, not_and, not_lt] at hx hx'
    rw [dif_pos hx]; apply hf; intro hb
    have := (blk_iff K hK x hx d).1 hb; have := hx' this.1; omega

lemma box_ent (X : Fin 3 → Matrix (Fin m) (Fin m) F) (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m)
    (n col : Fin m) : Z3Net.boxMatrix X K n col = ent (X (blk K n)) (lev K n) col := by
  obtain ⟨hlt, heq⟩ := Z3NetKN.Realize.blk_lev K hK n
  have hr := boxMatrix_row X K hK (blk K n) ⟨lev K n, by have := n.isLt; omega⟩ hlt
  have hn : n = ⟨offK K (blk K n) + lev K n, offK_lt K hK _ _ hlt⟩ := Fin.ext heq.symm
  calc Z3Net.boxMatrix X K n col
      = Z3Net.boxMatrix X K ⟨offK K (blk K n) + lev K n, offK_lt K hK _ _ hlt⟩ col := by
        rw [← hn]
    _ = X (blk K n) ⟨lev K n, by have := n.isLt; omega⟩ col := by rw [hr]
    _ = _ := by
        simp only [ent]; rw [dif_pos ⟨by have := n.isLt; omega, col.isLt⟩]

/-- The block-diagonal matrix of the leading blocks of the `T_c`. -/
def Dg (K : Fin 3 → ℕ) (T : Fin 3 → Matrix (Fin m) (Fin m) F) : Matrix (Fin m) (Fin m) F :=
  fun n n' => if blk K n = blk K n' then ent (T (blk K n)) (lev K n) (lev K n') else 0

lemma ent_low (T : Matrix (Fin m) (Fin m) F) (hT : ∀ i j : Fin m, i < j → T i j = 0) (i j : ℕ)
    (h : i < j) : ent T i j = 0 := by
  simp only [ent]; split_ifs with hh
  · exact hT _ _ (by change i < j; exact h)
  · rfl

lemma box_mul (X T : Fin 3 → Matrix (Fin m) (Fin m) F) (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m)
    (hT : ∀ c (i j : Fin m), i < j → T c i j = 0) :
    Z3Net.boxMatrix (fun c => T c * X c) K = Dg K T * Z3Net.boxMatrix X K := by
  ext n col
  rw [box_ent _ K hK n col, Matrix.mul_apply]
  obtain ⟨hlt, heq⟩ := Z3NetKN.Realize.blk_lev K hK n
  rw [ent_mul]
  rw [sum_block K hK (blk K n) _ (fun n' hn' => by
    simp only [Dg, if_neg (Ne.symm hn'), zero_mul])]
  rw [sum_range_eq_of_zero _ m (K (blk K n))
    (fun x hx => by rw [show ent (X (blk K n)) x col = 0 by simp [ent, show ¬ x < m by omega],
      mul_zero])
    (fun x hx => by rw [ent_low _ (hT _) _ _ (by omega), zero_mul])]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < K (blk K n) := by simpa using hj
  have hjm : offK K (blk K n) + j < m := offK_lt K hK _ _ hj'
  obtain ⟨hb, hl⟩ := Z3NetKN.Realize.blk_of K (blk K n) j hj'
  rw [dif_pos hjm, box_ent X K hK ⟨_, hjm⟩ col]
  simp only [Dg]
  rw [if_pos (by rw [hb]), hb, hl]

theorem gr_mul (X Y T : Fin 3 → Matrix (Fin m) (Fin m) F) (hX : T0 X) (hY : T0 Y)
    (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (hT : ∀ c (i j : Fin m), i < j → T c i j = 0)
    (hYT : ∀ c, Y c = T c * X c) (c : Fin 3) :
    gr Y K c * Dg K T = T c * gr X K c := by
  have hbox : Z3Net.boxMatrix Y K = Dg K T * Z3Net.boxMatrix X K := by
    rw [show Y = fun c => T c * X c from funext hYT]; exact box_mul X T K hK hT
  have hBY := (isUnit_iff_isUnit_det _).1 (isUnit_box hY K hK)
  rw [hbox, det_mul] at hBY
  have hD : IsUnit (Dg K T).det := isUnit_of_mul_isUnit_left hBY
  unfold gr
  rw [hbox, Matrix.mul_inv_rev, hYT c, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc (Z3Net.boxMatrix X K)⁻¹, nonsing_inv_mul _ hD, mul_one]

/-! ## Entries of the two sides of `gr_mul` -/

lemma lhs_entry (G T : Fin 3 → Matrix (Fin m) (Fin m) F) (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m)
    (c d : Fin 3) (i : ℕ) (j' : ℕ) (hj' : j' < K d) :
    ent (G c * Dg K T) i (offK K d + j') =
      ∑ j ∈ range (K d), ent (G c) i (offK K d + j) * ent (T d) j j' := by
  have hcol : offK K d + j' < m := offK_lt K hK d j' hj'
  obtain ⟨hbc, hlc⟩ := Z3NetKN.Realize.blk_of K d j' hj'
  by_cases hi : i < m
  · rw [show ent (G c * Dg K T) i (offK K d + j') = (G c * Dg K T) ⟨i, hi⟩ ⟨_, hcol⟩ by
      simp [ent, hi, hcol], Matrix.mul_apply]
    rw [sum_block K hK d _ (fun n hn => by
      simp only [Dg, hbc]; rw [if_neg hn, mul_zero])]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj2 : j < K d := by simpa using hj
    have hjm : offK K d + j < m := offK_lt K hK d j hj2
    obtain ⟨hb, hl⟩ := Z3NetKN.Realize.blk_of K d j hj2
    rw [dif_pos hjm]
    simp only [Dg, hb, hbc, hl, hlc, if_true]
    simp [ent, hi, hjm]
  · simp [ent, hi]

lemma rhs_entry (X T : Fin 3 → Matrix (Fin m) (Fin m) F) (hX : T0 X) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) (hT : ∀ c (i j : Fin m), i < j → T c i j = 0)
    (c d : Fin 3) (hcd : c ≠ d) (hKm : K c + 2 ≤ m) (ρ : ℕ) (hρ : ρ < 2) (j' : ℕ) (hj' : j' < K d) :
    ent (T c * gr X K c) (K c + ρ) (offK K d + j') =
      ∑ ρ' ∈ range 2, ent (T c) (K c + ρ) (K c + ρ') * ent (gr X K c) (K c + ρ') (offK K d + j') := by
  have hcol : offK K d + j' < m := offK_lt K hK d j' hj'
  obtain ⟨hbc, _⟩ := Z3NetKN.Realize.blk_of K d j' hj'
  rw [ent_mul, sum_range_eq_of_zero _ m (K c + 2)
    (fun x hx => by rw [show ent (gr X K c) x (offK K d + j') = 0 by
      simp [ent, show ¬ x < m by omega], mul_zero])
    (fun x hx => by rw [ent_low _ (hT c) _ _ (by omega), zero_mul]), Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun x hx => ?_), zero_add]
  have hx : x < K c := by simpa using hx
  have hxm : x < m := by omega
  rw [show ent (gr X K c) x (offK K d + j') = gr X K c ⟨x, hxm⟩ ⟨_, hcol⟩ by
    simp [ent, hxm, hcol], gr_coarse hX K hK c ⟨x, hxm⟩ ⟨_, hcol⟩ hx]
  rw [if_neg, mul_zero]
  intro he
  have h1 := (Z3NetKN.Realize.blk_of K c x hx).1
  simp only at he
  rw [he] at hbc
  exact hcd (h1.symm.trans hbc)

/-! ## The windows (padded with `0` beyond the cell) -/

/-- Window data of `G`: geometric row `ρ` of `c` on window column `i` of `d` (`0` if `i ≥ K_d`). -/
def WP (K : Fin 3 → ℕ) (G : Fin 3 → Matrix (Fin m) (Fin m) F) (c d : Fin 3) :
    Matrix (Fin 2) (Fin 3) F :=
  Matrix.of fun ρ i => if (i : ℕ) < K d then ent (G c) (K c + ρ) (offK K d + (K d - 1 - i)) else 0

/-- The trailing levels of `T_d` in the window index (identity beyond the cell). -/
def UP (K : Fin 3 → ℕ) (T : Fin 3 → Matrix (Fin m) (Fin m) F) (d : Fin 3) :
    Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i'' i => if (i'' : ℕ) < K d ∧ (i : ℕ) < K d then
    ent (T d) (K d - 1 - i'') (K d - 1 - i) else if i'' = i then 1 else 0

/-- Rows `K_c, K_c + 1` of `T_c` on themselves. -/
def LP (K : Fin 3 → ℕ) (T : Fin 3 → Matrix (Fin m) (Fin m) F) (c : Fin 3) :
    Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun ρ ρ' => ent (T c) (K c + ρ) (K c + ρ')

theorem win_rel (X Y T : Fin 3 → Matrix (Fin m) (Fin m) F) (hX : T0 X) (hY : T0 Y)
    (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (hT : ∀ c (i j : Fin m), i < j → T c i j = 0)
    (hYT : ∀ c, Y c = T c * X c) (c d : Fin 3) (hcd : c ≠ d) (hKm : K c + 2 ≤ m) :
    WP K (gr Y K) c d * UP K T d = LP K T c * WP K (gr X K) c d := by
  ext ρ i
  simp only [Matrix.mul_apply, WP, UP, LP, Matrix.of_apply]
  by_cases hi : (i : ℕ) < K d
  · simp only [hi, if_true, and_true]
    -- the identity `gr_mul` at the entry `(K_c + ρ, level K_d - 1 - i of d)`
    have key := congrArg (fun A => ent A (K c + ρ) (offK K d + (K d - 1 - i)))
      (gr_mul X Y T hX hY K hK hT hYT c)
    rw [lhs_entry (gr Y K) T K hK c d _ _ (by omega),
      rhs_entry X T hX K hK hT c d hcd hKm ρ ρ.isLt _ (by omega)] at key
    rw [Fin.sum_univ_eq_sum_range (fun ρ' => ent (T c) (K c + ρ) (K c + ρ') *
      ent (gr X K c) (K c + ρ') (offK K d + (K d - 1 - i))) 2, ← key]
    set f : ℕ → F := fun j => ent (gr Y K c) (K c + ρ) (offK K d + j) *
      ent (T d) j (K d - 1 - i) with hf
    set h : ℕ → F := fun t => if t < K d then f (K d - 1 - t) else 0 with hh
    have hi3 : (i : ℕ) + 1 ≤ 3 := by have := i.isLt; omega
    calc _ = ∑ x : Fin 3, h x := Finset.sum_congr rfl (fun x _ => by
            simp only [hh, hf]; split_ifs <;> simp_all)
      _ = ∑ t ∈ range 3, h t := Fin.sum_univ_eq_sum_range h 3
      _ = ∑ t ∈ range ((i : ℕ) + 1), h t := by
          refine (Finset.sum_subset (range_subset_range.2 hi3) (fun t ht ht' => ?_)).symm
          simp only [mem_range, not_lt] at ht ht'
          simp only [hh, hf]
          split_ifs
          · rw [ent_low _ (hT d) _ _ (by omega), mul_zero]
          · rfl
      _ = ∑ t ∈ range ((i : ℕ) + 1), f (K d - 1 - t) := by
          refine Finset.sum_congr rfl (fun t ht => ?_)
          have : t < (i : ℕ) + 1 := by simpa using ht
          simp only [hh]; rw [if_pos (by omega)]
      _ = ∑ t ∈ range (K d), f (K d - 1 - t) := by
          refine Finset.sum_subset (range_subset_range.2 (by omega)) (fun t ht ht' => ?_)
          simp only [mem_range, not_lt] at ht ht'
          simp only [hf]
          rw [ent_low _ (hT d) _ _ (by omega), mul_zero]
      _ = _ := Finset.sum_range_reflect f (K d)
  · simp only [hi, if_false, and_false, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hb; rw [if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Inverting the column factor -/

/-- The inverse of an upper-triangular `3 × 3` matrix. -/
def inv3 (U : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  !![(U 0 0)⁻¹, -(U 0 1) * (U 0 0 * U 1 1)⁻¹,
      (U 0 1 * U 1 2 - U 0 2 * U 1 1) * (U 0 0 * U 1 1 * U 2 2)⁻¹;
    0, (U 1 1)⁻¹, -(U 1 2) * (U 1 1 * U 2 2)⁻¹;
    0, 0, (U 2 2)⁻¹]

lemma mul_inv3 (U : Matrix (Fin 3) (Fin 3) F) (hup : ∀ i i' : Fin 3, i' < i → U i i' = 0)
    (hd : ∀ i, U i i ≠ 0) : U * inv3 U = 1 := by
  have h10 := hup 1 0 (by decide); have h20 := hup 2 0 (by decide)
  have h21 := hup 2 1 (by decide)
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, inv3, h10, h20, h21, Matrix.one_apply] <;>
    field_simp <;> ring

theorem gauge_of (X Y T : Fin 3 → Matrix (Fin m) (Fin m) F) (hX : T0 X) (hY : T0 Y)
    (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (hT : ∀ c (i j : Fin m), i < j → T c i j = 0)
    (hTd : ∀ c (i : Fin m), T c i i ≠ 0) (hYT : ∀ c, Y c = T c * X c)
    (hKm : ∀ c, K c + 2 ≤ m) :
    Gauge (LP K T) (fun d => inv3 (UP K T d)) (fun _ _ => 1) (WP K (gr X K)) (WP K (gr Y K)) := by
  have hTd' : ∀ c (i : ℕ), i < m → ent (T c) i i ≠ 0 := by
    intro c i hi; simp only [ent, hi, and_self, dite_true]; exact hTd c ⟨i, hi⟩
  have hUup : ∀ d (i i' : Fin 3), i' < i → UP K T d i i' = 0 := by
    intro d i i' hii
    simp only [UP, Matrix.of_apply]
    split_ifs with h1 h2
    · exact ent_low _ (hT d) _ _ (by
        have : (i' : ℕ) < i := hii
        omega)
    · exact absurd h2 (ne_of_gt hii)
    · rfl
  have hUd : ∀ d (i : Fin 3), UP K T d i i ≠ 0 := by
    intro d i
    simp only [UP, Matrix.of_apply]
    split_ifs with h1
    · exact hTd' d _ (by have := offK_add_le K hK d; omega)
    · exact one_ne_zero
  refine ⟨fun c => ⟨?_, ?_, ?_⟩, fun d => ⟨?_, ?_⟩, fun _ _ _ => one_ne_zero, fun c d hcd => ?_⟩
  · simp only [LP, Matrix.of_apply]; exact ent_low _ (hT c) _ _ (by simp)
  · simp only [LP, Matrix.of_apply]; exact hTd' c _ (by have := hKm c; simp; omega)
  · simp only [LP, Matrix.of_apply]; exact hTd' c _ (by have := hKm c; simp; omega)
  · intro i i' hii
    have := hUup d
    fin_cases i <;> fin_cases i' <;> simp_all [inv3] <;> exact absurd hii (by decide)
  · intro i
    fin_cases i <;> simp [inv3, hUd d 0, hUd d 1, hUd d 2]
  · rw [one_smul]
    have hrel := win_rel X Y T hX hY K hK hT hYT c d hcd (hKm c)
    calc WP K (gr Y K) c d = WP K (gr Y K) c d * (UP K T d * inv3 (UP K T d)) := by
          rw [mul_inv3 _ (hUup d) (hUd d), Matrix.mul_one]
      _ = LP K T c * WP K (gr X K) c d * inv3 (UP K T d) := by
          rw [← Matrix.mul_assoc, hrel]

end Z3NetPI.InvT
