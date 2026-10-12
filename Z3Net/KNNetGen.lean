module
public import Z3Net.KNFrame

@[expose] public section

/-!
# Realizing prescribed window rows in a `t = 0` graph form (KN entry, `KN1_net` / `KN2_net`)

Generic linear algebra over a field for the per-prime net statements.  `G` is a family of three
`m × m` matrices in *graph form* with depths `K` (`IsGF`: row `j < K c` of `G c` is the unit vector
at column `offK K c + j`) which is `t = 0` in kernel form (`T0`).  Three kinds of moves keep `T0`:

* `T0_rows`: left multiplication of each `G c` by a lower-triangular matrix with nonzero diagonal;
* `T0_cols`: on the offset rows, right multiplication by a matrix `V` that is *level-lower-
  triangular* (an entry `V n' n ≠ 0` only if `n'`, `n` lie in the same block and `n'` is at the
  same or a deeper level; nonzero diagonal) -- a change of the index basis in which a level absorbs
  deeper levels of its own cell;
* `T0_transfer`: scaling the block `(c, d)`, `c ≠ d`, of all offset rows of `c` by `μ c d ≠ 0`
  and changing the offset rows of `c` arbitrarily on the own cell of `c`.

`pivot_inj`: the matrix of the *geometric* offset rows of the coordinates `c ≠ d` on the last
levels of the cell of `d` has trivial kernel (it is a box minor).
-/

namespace Z3NetKN.Realize

open Matrix Finset Z3NetKN.Frame

variable {F : Type*} [Field F] {m : ℕ}

/-- Graph form: row `j < K c` of `G c` is the unit vector at column `offK K c + j`. -/
def IsGF (G : Fin 3 → Matrix (Fin m) (Fin m) F) (K : Fin 3 → ℕ) : Prop :=
  ∀ c (j col : Fin m), (j : ℕ) < K c → G c j col = if (col : ℕ) = offK K c + j then 1 else 0

/-! ## Blocks and levels -/

/-- The block containing column `n`. -/
def blk (K : Fin 3 → ℕ) (n : ℕ) : Fin 3 :=
  if n < K 0 then 0 else if n < K 0 + K 1 then 1 else 2

/-- The level of column `n` in its block. -/
def lev (K : Fin 3 → ℕ) (n : ℕ) : ℕ := n - offK K (blk K n)

lemma offK_blk_le (K : Fin 3 → ℕ) (n : ℕ) : offK K (blk K n) ≤ n := by
  unfold blk
  split_ifs with h1 h2 <;> simp [offK] <;> omega

lemma eq_of_blk_lev (K : Fin 3 → ℕ) (a b : Fin m) (hb : blk K a = blk K b) (hl : lev K a = lev K b) :
    a = b := by
  have ha := offK_blk_le K a
  have hb' := offK_blk_le K b
  unfold lev at hl
  rw [hb] at hl ha
  exact Fin.ext (by omega)

lemma blk_lev (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (n : Fin m) :
    lev K n < K (blk K n) ∧ offK K (blk K n) + lev K n = n := by
  have := n.isLt
  unfold lev blk
  split_ifs with h1 h2 <;> simp [offK] <;> omega

lemma blk_of (K : Fin 3 → ℕ) (c : Fin 3) (j : ℕ) (hj : j < K c) :
    blk K (offK K c + j) = c ∧ lev K (offK K c + j) = j := by
  unfold lev
  have hb : blk K (offK K c + j) = c := by
    unfold blk
    rcases c with ⟨_ | _ | _ | c, hc⟩
    · simp [offK] at hj ⊢; omega
    · simp [offK] at hj ⊢ <;> omega
    · simp [offK] at hj ⊢ <;> omega
    · omega
  refine ⟨hb, ?_⟩
  rw [hb]; omega

/-! ## Moves -/

/-- A lower-triangular left factor with nonzero diagonal does not enlarge prefix kernels. -/
lemma prefImp_lowerTri (Λ X : Matrix (Fin m) (Fin m) F)
    (hlow : ∀ i j : Fin m, i < j → Λ i j = 0) (hdiag : ∀ i, Λ i i ≠ 0) :
    PrefImp (Λ * X) X := by
  intro d v hv
  have key : ∀ n : ℕ, ∀ i : Fin m, (i : ℕ) = n → (i : ℕ) < d → (X *ᵥ v) i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hin hid
      have h0 := hv i hid
      rw [← mulVec_mulVec] at h0
      simp only [mulVec, dotProduct] at h0
      rw [Finset.sum_eq_single i] at h0
      · exact (mul_eq_zero.mp h0).resolve_left (hdiag i)
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · have : (X *ᵥ v) j = 0 := ih j (by rw [← hin]; exact hlt) j rfl (by
            have : (j : ℕ) < i := hlt; omega)
          simp only [mulVec, dotProduct] at this
          rw [this, mul_zero]
        · rw [hlow i j hgt, zero_mul]
      · simp
  exact fun i hi => key i i rfl hi

theorem T0_rows {G : Fin 3 → Matrix (Fin m) (Fin m) F} (hG : T0 G)
    (Λ : Fin 3 → Matrix (Fin m) (Fin m) F)
    (hlow : ∀ c (i j : Fin m), i < j → Λ c i j = 0) (hdiag : ∀ c i, Λ c i i ≠ 0) :
    T0 (fun c => Λ c * G c) :=
  T0_of_prefImp hG (fun c => prefImp_lowerTri (Λ c) (G c) (hlow c) (hdiag c))

/-- In graph form, a coarse digit of `G c *ᵥ v` is a coordinate of `v`. -/
lemma gf_digit {G : Fin 3 → Matrix (Fin m) (Fin m) F} {K : Fin 3 → ℕ} (hK : K 0 + K 1 + K 2 = m)
    (hGF : IsGF G K) (c : Fin 3) (v : Fin m → F) (j : Fin m) (hj : (j : ℕ) < K c) :
    (G c *ᵥ v) j = v ⟨offK K c + j, offK_lt K hK c j hj⟩ :=
  mulVec_coarse (G c) (offK K c) (K c) (hGF c) v j hj (offK_lt K hK c j hj)

/-- Level-lower-triangular matrices (within each block, a column absorbs deeper levels). -/
def LevLow (K : Fin 3 → ℕ) (V : Matrix (Fin m) (Fin m) F) : Prop :=
  (∀ n' n : Fin m, V n' n ≠ 0 → blk K n' = blk K n ∧ lev K n ≤ lev K n') ∧ ∀ n, V n n ≠ 0

lemma LevLow.inj {K : Fin 3 → ℕ} {V : Matrix (Fin m) (Fin m) F} (hV : LevLow K V)
    (v : Fin m → F) (h : V *ᵥ v = 0) : v = 0 := by
  have key : ∀ L : ℕ, ∀ n : Fin m, lev K n = L → v n = 0 := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ih =>
      intro n hn
      have h0 := congrFun h n
      simp only [mulVec, dotProduct, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single n] at h0
      · exact (mul_eq_zero.mp h0).resolve_left (hV.2 n)
      · intro j _ hjn
        by_cases hz : V n j = 0
        · rw [hz, zero_mul]
        · obtain ⟨hb, hl⟩ := hV.1 n j hz
          rcases Nat.lt_or_ge (lev K j) L with hlt | hge
          · rw [ih _ hlt j rfl, mul_zero]
          · exfalso; apply hjn
            exact eq_of_blk_lev K j n hb.symm (by rw [hn]; omega)
      · simp
  funext n; exact key _ n rfl

/-- Column move on the offset rows: `G' c i = (G c * V) i` for `i ≥ K c`. -/
def colMove (K : Fin 3 → ℕ) (G : Fin 3 → Matrix (Fin m) (Fin m) F) (V : Matrix (Fin m) (Fin m) F) :
    Fin 3 → Matrix (Fin m) (Fin m) F :=
  fun c i => if (i : ℕ) < K c then G c i else (G c * V) i

lemma colMove_GF {G : Fin 3 → Matrix (Fin m) (Fin m) F} {K : Fin 3 → ℕ} (hGF : IsGF G K)
    (V : Matrix (Fin m) (Fin m) F) : IsGF (colMove K G V) K := by
  intro c j col hj
  simp only [colMove, if_pos hj]
  exact hGF c j col hj

theorem T0_cols {G : Fin 3 → Matrix (Fin m) (Fin m) F} {K : Fin 3 → ℕ} (hK : K 0 + K 1 + K 2 = m)
    (hG : T0 G) (hGF : IsGF G K) {V : Matrix (Fin m) (Fin m) F} (hV : LevLow K V) :
    T0 (colMove K G V) := by
  intro e he v hv
  apply hV.inj v
  apply hG e he
  intro c i hi
  by_cases hiK : (i : ℕ) < K c
  · rw [gf_digit hK hGF c _ i hiK]
    change ∑ n, V ⟨offK K c + i, offK_lt K hK c i hiK⟩ n * v n = 0
    apply Finset.sum_eq_zero
    intro n _
    by_cases hz : V ⟨offK K c + i, offK_lt K hK c i hiK⟩ n = 0
    · rw [hz, zero_mul]
    · obtain ⟨hb, hl⟩ := hV.1 _ n hz
      have hbo := blk_of K c i hiK
      rw [hbo.1] at hb
      rw [hbo.2] at hl
      obtain ⟨hlt, hpos⟩ := blk_lev K hK n
      rw [← hb] at hlt hpos
      have hvn := hv c ⟨lev K n, by omega⟩ (by simp; omega)
      have hrow : colMove K G V c ⟨lev K n, by omega⟩ = G c ⟨lev K n, by omega⟩ := by
        simp only [colMove]; rw [if_pos (by simpa using hlt)]
      have : (colMove K G V c *ᵥ v) ⟨lev K n, by omega⟩ = (G c *ᵥ v) ⟨lev K n, by omega⟩ := by
        simp only [mulVec, hrow]
      rw [this, gf_digit hK hGF c v _ (by simpa using hlt)] at hvn
      have hn : (⟨offK K c + lev K n, offK_lt K hK c _ hlt⟩ : Fin m) = n := Fin.ext (by simp; omega)
      rw [hn] at hvn
      rw [hvn, mul_zero]
  · have h1 := hv c i hi
    have : (colMove K G V c *ᵥ v) i = (G c *ᵥ (V *ᵥ v)) i := by
      simp only [mulVec, colMove, if_neg hiK]
      rw [dotProduct_mulVec, row_mul_right]
    rw [this] at h1
    exact h1

lemma third (c c' : Fin 3) (h : c' ≠ c) :
    ∃ d : Fin 3, d ≠ c ∧ d ≠ c' ∧ ∀ x : Fin 3, x ≠ c → x ≠ c' → x = d := by
  revert c c'; decide

/-- **Block scaling / own cell.**  If the offset rows of `G'` agree with those of `G` up to a
nonzero factor `μ c d` on every block `d ≠ c` (and arbitrarily on the own block), `T0` transfers. -/
theorem T0_transfer {G G' : Fin 3 → Matrix (Fin m) (Fin m) F} {K : Fin 3 → ℕ}
    (hK : K 0 + K 1 + K 2 = m) (hG : T0 G) (hGF : IsGF G K) (hGF' : IsGF G' K)
    (μ : Fin 3 → Fin 3 → F) (hμ : ∀ c d, c ≠ d → μ c d ≠ 0)
    (h : ∀ c (i n : Fin m), K c ≤ (i : ℕ) → blk K n ≠ c → G' c i n = μ c (blk K n) * G c i n) :
    T0 G' := by
  intro e he v hv
  -- coordinates of `v` in a cell of a coordinate with `K c ≤ e c` vanish
  have hA : ∀ c, K c ≤ e c → ∀ n : Fin m, blk K n = c → v n = 0 := by
    intro c hce n hn
    obtain ⟨hlt, hpos⟩ := blk_lev K hK n
    rw [hn] at hlt hpos
    have hvn := hv c ⟨lev K n, by omega⟩ (by simp; omega)
    rw [gf_digit hK hGF' c v _ (by simpa using hlt)] at hvn
    have hn' : (⟨offK K c + lev K n, offK_lt K hK c _ hlt⟩ : Fin m) = n := Fin.ext (by simp; omega)
    rwa [hn'] at hvn
  classical
  let E : Fin 3 → Prop := fun c => K c < e c
  let ν : Fin 3 → F :=
    if hu : ∃ c, E c ∧ ∀ c', E c' → c' = c then
      fun d => if d = hu.choose then 1 else μ hu.choose d
    else fun _ => 1
  have hν : ∀ d, ν d ≠ 0 := by
    intro d
    by_cases hu : ∃ c, E c ∧ ∀ c', E c' → c' = c
    · simp only [ν, dif_pos hu]
      by_cases h1 : d = hu.choose
      · rw [if_pos h1]; exact one_ne_zero
      · rw [if_neg h1]; exact hμ _ _ (Ne.symm h1)
    · simp only [ν, dif_neg hu]; exact one_ne_zero
  let w : Fin m → F := fun n => ν (blk K n) * v n
  have hw : w = 0 := by
    apply hG e he
    intro c i hi
    by_cases hiK : (i : ℕ) < K c
    · rw [gf_digit hK hGF c w i hiK]
      have hvc := hv c i hi
      rw [gf_digit hK hGF' c v i hiK] at hvc
      simp only [w, hvc, mul_zero]
    · have hEc : E c := by simp only [E]; omega
      have h0 := hv c i hi
      simp only [mulVec, dotProduct] at h0 ⊢
      by_cases hu : ∃ c, E c ∧ ∀ c', E c' → c' = c
      · have hc0 : c = hu.choose := hu.choose_spec.2 c hEc
        rw [← h0]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hbn : blk K n = c
        · simp [w, hA c (by omega) n hbn]
        · simp only [w, ν, dif_pos hu]
          rw [if_neg (by rw [← hc0]; exact hbn), h c i n (by omega) hbn, ← hc0]
          ring
      · -- a second coordinate `c'` with excess: only the third block carries `v`
        have : ∃ c', E c' ∧ c' ≠ c := by
          by_contra hno
          push_neg at hno
          exact hu ⟨c, hEc, fun c' hc' => hno c' hc'⟩
        obtain ⟨c', hEc', hc'c⟩ := this
        obtain ⟨d, hdc, hdc', hd⟩ := third c c' hc'c
        have hsum : ∑ n, G' c i n * v n = μ c d * ∑ n, G c i n * v n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          by_cases hb1 : blk K n = c
          · rw [hA c (by simp only [E] at hEc; omega) n hb1]; ring
          by_cases hb2 : blk K n = c'
          · rw [hA c' (by simp only [E] at hEc'; omega) n hb2]; ring
          rw [h c i n (by omega) hb1, hd _ hb1 hb2]; ring
        rw [hsum] at h0
        have h1 := (mul_eq_zero.mp h0).resolve_left (hμ c d (Ne.symm hdc))
        simp only [w, ν, dif_neg hu, one_mul]
        exact h1
  funext n
  have := congrFun hw n
  simp only [w, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left (hν _)

/-! ## Picking terms out of sums over `Fin m` -/

/-- Total accessor for vectors. -/
def fe (f : Fin m → F) (j : ℕ) : F := if h : j < m then f ⟨j, h⟩ else 0

lemma sum_pick_right (f : Fin m → F) (q : ℕ → ℕ) (S : Finset ℕ) (hq : ∀ i ∈ S, q i < m)
    (y : ℕ → F) :
    ∑ n : Fin m, f n * (∑ i ∈ S, if (n : ℕ) = q i then y i else 0) = ∑ i ∈ S, fe f (q i) * y i := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single ⟨q i, hq i hi⟩]
  · simp [fe, hq i hi]
  · intro n _ hn
    rw [if_neg (fun h => hn (Fin.ext h)), mul_zero]
  · simp

lemma sum_pick_left (f : Fin m → F) (q : ℕ → ℕ) (S : Finset ℕ) (hq : ∀ i ∈ S, q i < m)
    (y : ℕ → F) :
    ∑ n : Fin m, (∑ i ∈ S, if (n : ℕ) = q i then y i else 0) * f n = ∑ i ∈ S, y i * fe f (q i) := by
  simp_rw [mul_comm _ (f _), sum_pick_right f q S hq y, mul_comm]

/-- **Pivot minors.**  For a box `e` with `e d = K d - P`, `e c = K c + g c` (`c ≠ d`), the
geometric rows of the coordinates `c ≠ d` (the first `g c` offset rows) restricted to the last
`P` levels of the cell of `d` have trivial kernel. -/
theorem pivot_inj {G : Fin 3 → Matrix (Fin m) (Fin m) F} {K : Fin 3 → ℕ} (hK : K 0 + K 1 + K 2 = m)
    (hG : T0 G) (hGF : IsGF G K) (g : Fin 3 → ℕ) (d : Fin 3) (P : ℕ) (hPK : P ≤ K d)
    (e : Fin 3 → ℕ) (he : e 0 + e 1 + e 2 = m) (hed : e d = K d - P)
    (hec : ∀ c, c ≠ d → e c = K c + g c) (x : ℕ → F)
    (hx : ∀ c, c ≠ d → ∀ ρ, ρ < g c →
      ∑ i ∈ range P, ent (G c) (K c + ρ) (offK K d + (K d - 1 - i)) * x i = 0) :
    ∀ i < P, x i = 0 := by
  have hq : ∀ i ∈ range P, offK K d + (K d - 1 - i) < m := by
    intro i hi
    have := offK_lt K hK d (K d - 1 - i) (by simp at hi; omega)
    exact this
  let v : Fin m → F := fun n => ∑ i ∈ range P, if (n : ℕ) = offK K d + (K d - 1 - i) then x i else 0
  have hv : v = 0 := by
    apply hG e he
    intro c j hj
    by_cases hjK : (j : ℕ) < K c
    · rw [gf_digit hK hGF c v j hjK]
      simp only [v]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      intro heq
      have hi' : i < P := by simpa using hi
      have h1 := blk_of K c j hjK
      have h2 := blk_of K d (K d - 1 - i) (by omega)
      by_cases hcd : c = d
      · subst hcd
        rw [hed] at hj
        omega
      · apply hcd
        rw [← h1.1, ← h2.1, heq]
    · have hcd : c ≠ d := by
        intro h; subst h; rw [hed] at hj; omega
      have hρ : (j : ℕ) - K c < g c := by rw [hec c hcd] at hj; omega
      have := hx c hcd ((j : ℕ) - K c) hρ
      rw [show K c + ((j : ℕ) - K c) = j by omega] at this
      rw [← this]
      simp only [mulVec, dotProduct, v]
      rw [sum_pick_right _ _ _ hq]
      apply Finset.sum_congr rfl
      intro i hi
      simp [fe, ent, hq i hi]
  intro i hi
  have := congrFun hv ⟨offK K d + (K d - 1 - i), hq i (by simpa using hi)⟩
  simp only [v, Pi.zero_apply] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j hj hji
    rw [if_neg]
    intro h
    simp at hj
    apply hji
    omega
  · intro h; exact absurd (by simpa using hi) h

end Z3NetKN.Realize
