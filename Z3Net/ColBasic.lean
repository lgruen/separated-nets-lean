/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColDefs

@[expose] public section

/-!
# V14 stage S9′: basic lemmas for column point sets

The centred residue `cres N u` is the distance from `u` to `Nℤ` (`cres_le`, `cres_exists`,
`cres_ge`); the squared toroidal distance is the least `|y - x + N k|²` over translates
(`torus_le`, `torus_exists`); heights are constant on columns (`height_const`); the digital column
nets are column point sets (`digPoint_colGenW`, `isHeight_colPhi`); a triangle inequality in `ℝ³`
(`tri_lower`).
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

/-! ## The centred residue -/

lemma cres_spec (N : ℕ) (hN : 0 < N) (u : ℤ) :
    ((cres N u : ℕ) : ℤ) = min (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) := by
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have ht : ((u % (N : ℤ)).toNat : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg h0
  have hle : (u % (N : ℤ)).toNat ≤ N := by omega
  unfold cres
  rw [Nat.cast_min, Nat.cast_sub hle, ht]

lemma cres_le (N : ℕ) (hN : 0 < N) (u k : ℤ) : (cres N u : ℤ) ≤ |u + N * k| := by
  rw [cres_spec N hN]
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have hu : u = u % (N : ℤ) + N * (u / N) := (Int.emod_add_mul_ediv u N).symm
  set r := u % (N : ℤ)
  set t := k + u / N
  have he : u + N * k = r + N * t := by simp only [t, r]; linear_combination hu
  rw [he]
  rcases le_or_gt 0 t with ht | ht
  · have : 0 ≤ r + N * t := by nlinarith
    rw [abs_of_nonneg this]; exact le_trans (min_le_left _ _) (by nlinarith)
  · have ht' : t ≤ -1 := by omega
    have : r + N * t < 0 := by nlinarith
    rw [abs_of_neg this]; exact le_trans (min_le_right _ _) (by nlinarith)

lemma cres_exists (N : ℕ) (hN : 0 < N) (u : ℤ) : ∃ k : ℤ, (cres N u : ℤ) = |u + N * k| := by
  rw [cres_spec N hN]
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have hu : u = u % (N : ℤ) + N * (u / N) := (Int.emod_add_mul_ediv u N).symm
  rcases le_total (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) with h | h
  · refine ⟨-(u / N), ?_⟩
    rw [min_eq_left h]
    have : u + N * -(u / N) = u % (N : ℤ) := by linear_combination hu
    rw [this, abs_of_nonneg h0]
  · refine ⟨-(u / N) - 1, ?_⟩
    rw [min_eq_right h]
    have : u + N * (-(u / N) - 1) = u % (N : ℤ) - N := by linear_combination hu
    rw [this, abs_of_neg (by linarith)]
    ring

lemma cres_ge (N : ℕ) (hN : 0 < N) (u m : ℤ) (h : ∀ k : ℤ, m ≤ |u + N * k|) :
    m ≤ (cres N u : ℤ) := by
  obtain ⟨k, hk⟩ := cres_exists N hN u
  rw [hk]; exact h k

lemma cres_add_mul (N : ℕ) (u k : ℤ) : cres N (u + N * k) = cres N u := by
  unfold cres; rw [Int.add_mul_emod_self_left]

lemma cres_neg (N : ℕ) (hN : 0 < N) (u : ℤ) : cres N (-u) = cres N u := by
  have h1 : (cres N (-u) : ℤ) ≤ cres N u := by
    apply cres_ge N hN
    intro k
    rw [show u + N * k = -(-u + N * (-k)) by ring, abs_neg]
    exact cres_le N hN _ _
  have h2 : (cres N u : ℤ) ≤ cres N (-u) := by
    apply cres_ge N hN
    intro k
    rw [show -u + N * k = -(u + N * (-k)) by ring, abs_neg]
    exact cres_le N hN _ _
  exact_mod_cast le_antisymm h1 h2

lemma two_cres_le (N : ℕ) (hN : 0 < N) (u : ℤ) : 2 * (cres N u : ℤ) ≤ N := by
  rw [cres_spec N hN]
  rcases le_total (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

lemma cres_eq_abs (N : ℕ) (hN : 0 < N) (u : ℤ) (h : 2 * |u| ≤ N) : (cres N u : ℤ) = |u| := by
  apply le_antisymm
  · simpa using cres_le N hN u 0
  · apply cres_ge N hN
    intro k
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have : (N : ℤ) ≤ |N * k| := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast hN)]
        have : 1 ≤ |k| := by rw [abs_of_neg hk]; omega
        nlinarith
      have := abs_sub_abs_le_abs_sub (N * k) (-u)
      rw [abs_neg] at this
      have e : N * k - -u = u + N * k := by ring
      rw [e] at this; linarith
    · simp
    · have : (N : ℤ) ≤ |N * k| := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast hN)]
        have : 1 ≤ |k| := by rw [abs_of_pos hk]; omega
        nlinarith
      have := abs_sub_abs_le_abs_sub (N * k) (-u)
      rw [abs_neg] at this
      have e : N * k - -u = u + N * k := by ring
      rw [e] at this; linarith

/-! ## Toroidal distance and translates -/

lemma torus_le (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) (k : Fin 3 → ℤ) :
    (torusDist2 N x y : ℤ) ≤ ∑ c, ((y c : ℤ) - x c + N * k c) ^ 2 := by
  unfold torusDist2
  push_cast
  apply Finset.sum_le_sum
  intro c _
  have h := cres_le N hN ((y c : ℤ) - x c) (k c)
  have e : cres N ((x c : ℤ) - y c) = cres N ((y c : ℤ) - x c) := by
    rw [← cres_neg N hN]; ring_nf
  rw [e]
  have h0 : (0 : ℤ) ≤ cres N ((y c : ℤ) - x c) := by positivity
  calc ((cres N ((y c : ℤ) - x c) : ℕ) : ℤ) ^ 2 ≤ |(y c : ℤ) - x c + N * k c| ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = ((y c : ℤ) - x c + N * k c) ^ 2 := sq_abs _

lemma torus_exists (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) :
    ∃ k : Fin 3 → ℤ, (torusDist2 N x y : ℤ) = ∑ c, ((y c : ℤ) - x c + N * k c) ^ 2 := by
  have h : ∀ c : Fin 3, ∃ k : ℤ, (cres N ((y c : ℤ) - x c) : ℤ) = |(y c : ℤ) - x c + N * k| :=
    fun c => cres_exists N hN _
  choose k hk using h
  refine ⟨k, ?_⟩
  unfold torusDist2
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  have e : cres N ((x c : ℤ) - y c) = cres N ((y c : ℤ) - x c) := by
    rw [← cres_neg N hN]; ring_nf
  rw [e, hk c, sq_abs]

/-- The Euclidean distance bounds the toroidal one. -/
lemma torus_le_eucl (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) :
    (torusDist2 N x y : ℤ) ≤ ∑ c, ((y c : ℤ) - x c) ^ 2 := by
  simpa using torus_le N hN x y 0

/-! ## Heights -/

lemma height_const {q : ℕ} [NeZero q] {φ : (Fin 3 → ZMod q) → ℕ} (hφ : ∀ n, φ (n + 1) = φ n)
    (n : Fin 3 → ZMod q) (t : ZMod q) : φ (n + fun _ => t) = φ n := by
  have key : ∀ m : ℕ, φ (n + fun _ => (m : ZMod q)) = φ n := by
    intro m
    induction m with
    | zero =>
      have e : (n + fun _ => ((0 : ℕ) : ZMod q)) = n := by funext c; simp
      rw [e]
    | succ m ih =>
      have e : (n + fun _ => ((m + 1 : ℕ) : ZMod q)) = (n + fun _ => (m : ZMod q)) + 1 := by
        funext c; simp; ring
      rw [e, hφ, ih]
  have := key t.val
  rwa [ZMod.natCast_zmod_val] at this

/-! ## Digital column nets are column point sets -/

lemma coord3 (q : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod q)) (v : Fin 3 → ZMod q) :
    coord q 3 C v = ((C *ᵥ v) 0).val * q ^ 2 + ((C *ᵥ v) 1).val * q + ((C *ᵥ v) 2).val := by
  simp [coord, Fin.sum_univ_three]

lemma colGenW_mulVec (q : ℕ) (w ℓ : Fin 3 → ℤ) (c : Fin 3) (n : Fin 3 → ZMod q) :
    (colGenW q w ℓ c *ᵥ n) 0 = n c ∧ (colGenW q w ℓ c *ᵥ n) 1 = colH q w n ∧
      (colGenW q w ℓ c *ᵥ n) 2 = colJ q ℓ n := by
  refine ⟨?_, ?_, ?_⟩
  · simp [colGenW, mulVec, dotProduct, Pi.single_apply]
  · simp [colGenW, mulVec, dotProduct, colH]
  · simp [colGenW, mulVec, dotProduct, colJ]

lemma digPoint_colGenW (q : ℕ) (w ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) :
    digPoint q 3 (colGenW q w ℓ) n = colPt q (colPhi q w ℓ) n := by
  funext c
  obtain ⟨h0, h1, h2⟩ := colGenW_mulVec q w ℓ c n
  simp only [digPoint, coord3, h0, h1, h2, colPt, colPhi]
  ring

lemma sum_colA (q : ℕ) (w : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) :
    ∑ c, colA q w c = q := by
  have h : ∀ c, 3 * colA q w c = q + w c := fun c => Int.mul_ediv_cancel' (hw3 c)
  have := congrArg (fun f => ∑ c, f c) (funext h)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hw0] at this
  simp at this
  linarith

lemma colH_add_one (q : ℕ) (w : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c)
    (n : Fin 3 → ZMod q) : colH q w (n + 1) = colH q w n := by
  have hs := sum_colA q w hw0 hw3
  unfold colH
  simp only [Pi.add_apply, Pi.one_apply, mul_add, mul_one, Finset.sum_add_distrib]
  have : ∑ d, ((colA q w d : ℤ) : ZMod q) = 0 := by
    rw [← Int.cast_sum, hs]; simp
  rw [this, add_zero]

lemma colJ_add_one (q : ℕ) (ℓ : Fin 3 → ℤ) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c) (n : Fin 3 → ZMod q) :
    colJ q ℓ (n + 1) = colJ q ℓ n := by
  unfold colJ
  simp only [Pi.add_apply, Pi.one_apply, mul_add, mul_one, Finset.sum_add_distrib]
  have : ∑ d, ((ℓ d : ℤ) : ZMod q) = 0 := by
    rw [← Int.cast_sum]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hℓ
  rw [this, add_zero]

lemma colPhi_lt (q : ℕ) [NeZero q] (w ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) :
    colPhi q w ℓ n < q ^ 2 := by
  have h1 := ZMod.val_lt (colH q w n)
  have h2 := ZMod.val_lt (colJ q ℓ n)
  unfold colPhi
  calc q * (colH q w n).val + (colJ q ℓ n).val < q * (colH q w n).val + q := by omega
    _ = q * ((colH q w n).val + 1) := by ring
    _ ≤ q * q := Nat.mul_le_mul_left _ h1
    _ = q ^ 2 := by ring

lemma isHeight_colPhi (q : ℕ) [NeZero q] (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c) : IsHeight q (colPhi q w ℓ) :=
  ⟨colPhi_lt q w ℓ, fun n => by
    simp only [colPhi, colH_add_one q w hw0 hw3, colJ_add_one q ℓ hℓ]⟩

/-! ## A triangle inequality in `ℝ³` -/

lemma tri_lower (u r : Fin 3 → ℝ) (α β : ℝ) (hβ : 0 ≤ β) (hαβ : β ≤ α)
    (hu : α ^ 2 ≤ ∑ c, u c ^ 2) (hr : ∑ c, r c ^ 2 ≤ β ^ 2) :
    (α - β) ^ 2 ≤ ∑ c, (u c + r c) ^ 2 := by
  simp only [Fin.sum_univ_three] at hu hr ⊢
  set A := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 with hA
  set B := r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hcs : (u 0 * r 0 + u 1 * r 1 + u 2 * r 2) ^ 2 ≤ A * B := by
    nlinarith [sq_nonneg (u 0 * r 1 - u 1 * r 0), sq_nonneg (u 0 * r 2 - u 2 * r 0),
      sq_nonneg (u 1 * r 2 - u 2 * r 1)]
  have hdot : -(Real.sqrt A * Real.sqrt B) ≤ u 0 * r 0 + u 1 * r 1 + u 2 * r 2 := by
    rw [← Real.sqrt_mul hA0]
    exact (abs_le.1 (Real.abs_le_sqrt hcs)).1
  have hsA : α ≤ Real.sqrt A := Real.le_sqrt_of_sq_le hu
  have hsB : Real.sqrt B ≤ β := by
    rw [show β = Real.sqrt (β ^ 2) from (Real.sqrt_sq hβ).symm]
    exact Real.sqrt_le_sqrt hr
  have hsA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hsB2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hexp : (u 0 + r 0) ^ 2 + (u 1 + r 1) ^ 2 + (u 2 + r 2) ^ 2 =
      A + 2 * (u 0 * r 0 + u 1 * r 1 + u 2 * r 2) + B := by rw [hA, hB]; ring
  rw [hexp]
  have h1 : (α - β) ^ 2 ≤ (Real.sqrt A - Real.sqrt B) ^ 2 := by
    have : 0 ≤ α - β := by linarith
    have : α - β ≤ Real.sqrt A - Real.sqrt B := by linarith
    nlinarith
  nlinarith

end Z3NetC.Proofs
