/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Defs
public import Z3Net.DShift
public import Z3Net.FNie

@[expose] public section

/-!
# V14 stage S14′: `lem:lift` (A) and (B)

* `net_iff_boxInj`: a digitally shifted digital net over `F_b` is a `(0,M,3)`-net iff every box map
  `n ↦ (first d_c digits of C_c n)_c`, `∑ d_c = M`, is injective (`lem:nie`, `lem:shift`).
* `lift_net` (`lem:lift`(A)): admissible shifts give a digitally shifted digital `(0, M+3, 3)`-net, by the box case
  split of the printed proof (all `d_c ≥ 1`; exactly one `d_c = 0`, with the inner boxes `(e, M+1-e)` and the outer
  boxes `e = 0, M+1`; two `d_c = 0`).
* `lift_exists` (`lem:lift`(B)): if `2D ≤ M`, admissible shifts vanishing on the first `D` digits exist. The proof
  follows the printed one (the pivot digit `e` of `c` for `e > D`, digit `M + 1 - e` of `c'` for `e ≤ D`, both deep),
  in the form of a greedy choice: processing `e = D+1, …, M` and then `e = D, …, 1`, a pivot unit vector lies in
  `Z_{e'}` for every `e'` processed before, so adding it to a vector in `H_e` leaves the earlier conditions intact.
-/

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

/-! ## Two ring identities (stated without the field instance: `ring` normalizes `ZMod b` reliably only then) -/

lemma alg_inv {b : ℕ} (u X s t : ZMod b) (h : s * t = 1) : u = -s * X + s * (X + t * u) := by
  linear_combination (-u) * h

lemma alg_line {b : ℕ} (X a a' d : ZMod b) (h : X + a * -d + a' * d = 0) : X + d * (a' - a) = 0 := by
  linear_combination h

variable {b : ℕ} [Fact b.Prime]

/-! ## Box injectivity -/

/-- The box map of shape `d` is injective (kernel `0`). -/
def BoxInj {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (d : Fin 3 → ℕ) : Prop :=
  ∀ n : Fin M → ZMod b, (∀ (c : Fin 3) (j : Fin M), (j : ℕ) < d c → (C c *ᵥ n) j = 0) → n = 0

lemma boxMat_mulVec_zero_iff {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (d : Fin 3 → ℕ)
    (hd : ∑ c, d c = M) (n : Fin M → ZMod b) :
    Z3NetF.boxMatrix C d *ᵥ n = 0 ↔ ∀ (c : Fin 3) (j : Fin M), (j : ℕ) < d c → (C c *ᵥ n) j = 0 := by
  constructor
  · intro h c j hj
    have h1 := congrFun h ⟨Z3NetF.Proofs.pre d c + j, Z3NetF.Proofs.pre_add_lt d hd c j hj⟩
    have h2 := Z3NetF.Proofs.box_row_pre C d hd c j hj
    simp only [mulVec, Pi.zero_apply] at h1
    rw [h2] at h1
    exact h1
  · intro h
    funext r
    obtain ⟨c, i, hi, -, hr⟩ := Z3NetF.Proofs.box_row_get C d hd r
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [hr]
    exact h c ⟨i, lt_of_lt_of_le hi (Z3NetF.Proofs.le_of_sum d hd c)⟩ hi

lemma net_iff_boxInj_unshifted {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) :
    Z3NetF.IsNet0 3 b M (Z3NetF.digPoint b M C) ↔ ∀ d : Fin 3 → ℕ, ∑ c, d c = M → BoxInj C d := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  rw [Z3NetF.Proofs.nie_zmod]
  refine forall_congr' fun d => forall_congr' fun hd => ?_
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro hinj n hn
    apply hinj
    rw [(boxMat_mulVec_zero_iff C d hd n).2 hn, mulVec_zero]
  · intro hbox x y hxy
    have : x - y = 0 := hbox (x - y) ((boxMat_mulVec_zero_iff C d hd _).1 (by
      rw [mulVec_sub, hxy, sub_self]))
    exact sub_eq_zero.1 this

/-- A digital shift does not change the net property (both directions, `lem:shift`). -/
lemma net_shift_iff {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ : Fin 3 → Fin M → ZMod b) :
    Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ) ↔ Z3NetF.IsNet0 3 b M (Z3NetF.digPoint b M C) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  constructor
  · intro h
    have h2 := Z3NetF.Proofs.dshift_net (Z3NetF.digPointShift b M C σ)
      (fun v c => Z3NetF.Proofs.digPointShift_lt C σ v c) (-σ) h
    have e : (fun v => Z3NetF.dshiftPt b M (-σ) (Z3NetF.digPointShift b M C σ v)) =
        Z3NetF.digPoint b M C := by
      funext v c
      rw [Z3NetF.Proofs.digPointShift_eq_dshiftPt]
      simp only [Z3NetF.dshiftPt, Pi.neg_apply]
      exact Z3NetF.Proofs.dshiftCoord_neg M (σ c) _ (Z3NetF.Proofs.digPoint_lt C v c)
    rwa [e] at h2
  · exact Z3NetF.Proofs.digPointShift_net C σ

/-- **`lem:nie`** for digitally shifted digital nets over `F_b`: net iff every box map is injective. -/
theorem net_iff_boxInj {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ : Fin 3 → Fin M → ZMod b) :
    Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ) ↔ ∀ d : Fin 3 → ℕ, ∑ c, d c = M → BoxInj C d := by
  rw [net_shift_iff, net_iff_boxInj_unshifted]

/-! ## The rows of the lift applied to an index -/

section liftrows

variable {M : ℕ} (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (sA sB : Fin 3 → Fin M → ZMod b)
  (w : Fin (M + 3) → ZMod b)

/-- The `n`-part of an index of the lift. -/
def nOf (w : Fin (M + 3) → ZMod b) : Fin M → ZMod b := fun i => w (Fin.castAdd 3 i)

lemma liftGen_mulVec (c : Fin 3) (r : Fin (M + 3)) :
    (liftGen C sA sB c *ᵥ w) r =
      (∑ i : Fin M, liftGen C sA sB c r (Fin.castAdd 3 i) * w (Fin.castAdd 3 i)) +
        liftGen C sA sB c r ⟨M, by omega⟩ * w ⟨M, by omega⟩ +
        liftGen C sA sB c r ⟨M + 1, by omega⟩ * w ⟨M + 1, by omega⟩ +
        liftGen C sA sB c r ⟨M + 2, by omega⟩ * w ⟨M + 2, by omega⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_three]
  simp only [add_assoc]
  rfl

lemma liftGen_mulVec_top (c : Fin 3) :
    (liftGen C sA sB c *ᵥ w) ⟨0, by omega⟩ =
      liftTop M c M * w ⟨M, by omega⟩ + liftTop M c (M + 1) * w ⟨M + 1, by omega⟩ +
        liftTop M c (M + 2) * w ⟨M + 2, by omega⟩ := by
  rw [liftGen_mulVec]
  have h0 : ∀ i : Fin M, liftGen C sA sB c ⟨0, by omega⟩ (Fin.castAdd 3 i) = 0 := by
    intro i
    simp only [liftGen, liftTop, Fin.val_castAdd, dif_pos]
    have := i.isLt
    split_ifs <;> first | rfl | omega
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
  simp [liftGen]

lemma liftGen_block (c : Fin 3) (j : ℕ) (hj : j < M) (k : Fin (M + 3)) :
    liftGen C sA sB c ⟨j + 1, by omega⟩ k =
      if hk : (k : ℕ) < M then C c ⟨j, hj⟩ ⟨k, hk⟩
      else if (k : ℕ) = M + 1 then sA c ⟨j, hj⟩ else if (k : ℕ) = M + 2 then sB c ⟨j, hj⟩ else 0 := by
  simp only [liftGen]
  rw [dif_neg (by omega), dif_pos (by omega)]
  rfl

lemma liftGen_mulVec_block (c : Fin 3) (j : ℕ) (hj : j < M) :
    (liftGen C sA sB c *ᵥ w) ⟨j + 1, by omega⟩ =
      (C c *ᵥ nOf w) ⟨j, hj⟩ + sA c ⟨j, hj⟩ * w ⟨M + 1, by omega⟩ + sB c ⟨j, hj⟩ * w ⟨M + 2, by omega⟩ := by
  rw [liftGen_mulVec]
  have h1 : ∀ i : Fin M, liftGen C sA sB c ⟨j + 1, by omega⟩ (Fin.castAdd 3 i) = C c ⟨j, hj⟩ i := by
    intro i
    rw [liftGen_block C sA sB c j hj, dif_pos (by simp)]
    rfl
  simp only [h1]
  rw [liftGen_block C sA sB c j hj, liftGen_block C sA sB c j hj, liftGen_block C sA sB c j hj]
  simp only [show ¬ (M < M) by omega, show ¬ (M + 1 < M) by omega, show ¬ (M + 2 < M) by omega,
    show ¬ (M = M + 1) by omega, show ¬ (M = M + 2) by omega, show ¬ (M + 2 = M + 1) by omega,
    dite_false, if_false, if_true, zero_mul, add_zero]
  simp only [mulVec, dotProduct, nOf]

lemma liftGen_mulVec_jit (c : Fin 3) (t : ℕ) (ht : t < 2) :
    (liftGen C sA sB c *ᵥ w) ⟨M + 1 + t, by omega⟩ =
      liftJit M c t M * w ⟨M, by omega⟩ + liftJit M c t (M + 1) * w ⟨M + 1, by omega⟩ +
        liftJit M c t (M + 2) * w ⟨M + 2, by omega⟩ := by
  rw [liftGen_mulVec]
  have h0 : ∀ i : Fin M, liftGen C sA sB c ⟨M + 1 + t, by omega⟩ (Fin.castAdd 3 i) = 0 := by
    intro i
    simp only [liftGen, liftJit, Fin.val_castAdd]
    rw [dif_neg (by omega), dif_neg (by omega)]
    have := i.isLt
    split_ifs <;> first | rfl | omega
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
  have e : ∀ j (hj : j < M + 3), liftGen C sA sB c ⟨M + 1 + t, by omega⟩ ⟨j, hj⟩ = liftJit M c t j := by
    intro j hj
    simp only [liftGen]
    rw [dif_neg (by omega), dif_neg (by omega), show M + 1 + t - (M + 1) = t by omega]
  rw [e, e, e]

end liftrows

/-! ## `lem:lift`(A) -/

section liftA

variable {M : ℕ}

/-- The inner and outer boxes of one pair `(c, c')` of coordinates (the case "exactly one `d_c = 0`" of the proof of
`lem:lift`(A)), for the copies `P_cc' + t u` along the line `u`. -/
lemma pair_case (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (c c' : Fin 3)
    (u : (Fin M → ZMod b) × (Fin M → ZMod b))
    (hP : ∀ e ≤ M, ∀ n : Fin M → ZMod b, (∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j = 0) →
      (∀ j : Fin M, (j : ℕ) < M - e → (C c' *ᵥ n) j = 0) → n = 0)
    (hadm : ∀ e : ℕ, 1 ≤ e → e ≤ M → u ∉ pairSub C c c' ⊔ Zsub b M e)
    (n : Fin M → ZMod b) (t : ZMod b) (e : ℕ) (he : e ≤ M + 1)
    (hc : ∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j + t * u.1 j = 0)
    (hc' : ∀ j : Fin M, (j : ℕ) < M + 1 - e → (C c' *ᵥ n) j + t * u.2 j = 0)
    (hjit : e = 0 ∨ e = M + 1 → t = 0) : n = 0 ∧ t = 0 := by
  by_cases hE : e = 0 ∨ e = M + 1
  · have ht := hjit hE
    subst ht
    rcases hE with hE | hE
    · subst hE
      refine ⟨hP 0 (Nat.zero_le _) n (fun j hj => absurd hj (Nat.not_lt_zero _)) (fun j hj => ?_), rfl⟩
      have := hc' j (by omega); simpa using this
    · subst hE
      refine ⟨hP M le_rfl n (fun j hj => ?_) (fun j hj => absurd hj (by omega)), rfl⟩
      have := hc j (by omega); simpa using this
  · have he1 : 1 ≤ e := by omega
    have he2 : e ≤ M := by omega
    have ht : t = 0 := by
      by_contra ht
      apply hadm e he1 he2
      -- `u = t⁻¹ (z − (C_c n, C_c' n))` with `z ∈ Z_e`
      have hz : ((C c *ᵥ n) + t • u.1, (C c' *ᵥ n) + t • u.2) ∈ Zsub b M e :=
        ⟨fun j hj => by simpa [smul_eq_mul] using hc j hj, fun j hj => by simpa [smul_eq_mul] using hc' j hj⟩
      obtain ⟨sinv, hinv⟩ : ∃ sinv : ZMod b, sinv * t = 1 := ⟨t⁻¹, inv_mul_cancel₀ ht⟩
      have hp : ((C c *ᵥ ((-sinv) • n)), (C c' *ᵥ ((-sinv) • n))) ∈ pairSub C c c' := ⟨(-sinv) • n, rfl⟩
      have key : u = ((C c *ᵥ ((-sinv) • n)), (C c' *ᵥ ((-sinv) • n))) +
          sinv • ((C c *ᵥ n) + t • u.1, (C c' *ᵥ n) + t • u.2) := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
        ext j
        · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact alg_inv _ _ _ _ hinv
        · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact alg_inv _ _ _ _ hinv
      rw [key]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hz))
    subst ht
    refine ⟨hP e he2 n (fun j hj => by simpa using hc j hj) (fun j hj => by simpa using hc' j (by omega)), rfl⟩

/-- The box hypotheses of `pair_case` from the net property of `P`, for a pair `c ≠ c'`. -/
lemma pair_box (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b))
    (hP : ∀ d : Fin 3 → ℕ, ∑ c, d c = M → BoxInj C d) (c c' : Fin 3) (hcc : c ≠ c') :
    ∀ e ≤ M, ∀ n : Fin M → ZMod b, (∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j = 0) →
      (∀ j : Fin M, (j : ℕ) < M - e → (C c' *ᵥ n) j = 0) → n = 0 := by
  intro e he n h1 h2
  let d : Fin 3 → ℕ := fun k => if k = c then e else if k = c' then M - e else 0
  have hd : ∑ k, d k = M := by
    have : ∀ k, d k = (if k = c then e else 0) + (if k = c' then M - e else 0) := by
      intro k
      simp only [d]
      by_cases h : k = c
      · subst h; simp [hcc]
      · simp [h]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  apply hP d hd n
  intro k j hj
  by_cases hk : k = c
  · subst hk; simp only [d, if_pos rfl] at hj; exact h1 j hj
  · by_cases hk' : k = c'
    · subst hk'; simp only [d, if_neg hk, if_pos rfl] at hj; exact h2 j hj
    · simp only [d, if_neg hk, if_neg hk'] at hj; omega

/-- The full box `(M)` of one coordinate. -/
lemma full_box (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b))
    (hP : ∀ d : Fin 3 → ℕ, ∑ c, d c = M → BoxInj C d) (c : Fin 3) (n : Fin M → ZMod b)
    (h : ∀ j : Fin M, (C c *ᵥ n) j = 0) : n = 0 := by
  let d : Fin 3 → ℕ := fun k => if k = c then M else 0
  have hd : ∑ k, d k = M := by simp [d]
  apply hP d hd n
  intro k j hj
  by_cases hk : k = c
  · subst hk; exact h j
  · simp only [d, if_neg hk] at hj; omega

/-- An index of the lift is `0` once its `n`-part and `α, δ₁, δ₂` vanish. -/
lemma idx_eq_zero (w : Fin (M + 3) → ZMod b) (hn : nOf w = 0) (h0 : w ⟨M, by omega⟩ = 0)
    (h1 : w ⟨M + 1, by omega⟩ = 0) (h2 : w ⟨M + 2, by omega⟩ = 0) : w = 0 := by
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h : i < M
  · exact congrFun hn ⟨i, h⟩
  · have : i = M ∨ i = M + 1 ∨ i = M + 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2

/-- **`lem:lift`(A)**, box form: if every box map of `P` (`∑ d_c = M`) is injective and `s_A, s_B` are admissible,
every box map of the lift (`∑ d_c = M + 3`) is injective. -/
theorem lift_boxInj (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (sA sB : Fin 3 → Fin M → ZMod b)
    (hP : ∀ d : Fin 3 → ℕ, ∑ c, d c = M → BoxInj C d) (hadm : Admissible C sA sB) :
    ∀ d : Fin 3 → ℕ, ∑ c, d c = M + 3 → BoxInj (liftGen C sA sB) d := by
  intro d hd w hw
  rw [Fin.sum_univ_three] at hd
  set n := nOf w
  set α := w ⟨M, by omega⟩
  set δ₁ := w ⟨M + 1, by omega⟩
  set δ₂ := w ⟨M + 2, by omega⟩
  -- the facts read off the box
  have top : ∀ c : Fin 3, 1 ≤ d c → (liftGen C sA sB c *ᵥ w) ⟨0, by omega⟩ = 0 :=
    fun c hc => hw c ⟨0, by omega⟩ (by simp; omega)
  have blk : ∀ (c : Fin 3) (j : ℕ) (hj : j < M), j + 1 < d c →
      (C c *ᵥ n) ⟨j, hj⟩ + sA c ⟨j, hj⟩ * δ₁ + sB c ⟨j, hj⟩ * δ₂ = 0 := by
    intro c j hj hjd
    rw [← liftGen_mulVec_block C sA sB w c j hj]
    exact hw c _ (by simpa using hjd)
  have jit : ∀ (c : Fin 3) (t : ℕ) (ht : t < 2), M + 1 + t < d c →
      liftJit M c t M * α + liftJit M c t (M + 1) * δ₁ + liftJit M c t (M + 2) * δ₂ = 0 := by
    intro c t ht htd
    rw [← liftGen_mulVec_jit C sA sB w c t ht]
    exact hw c _ (by simpa using htd)
  have tp : ∀ c : Fin 3, 1 ≤ d c →
      liftTop M c M * α + liftTop M c (M + 1) * δ₁ + liftTop M c (M + 2) * δ₂ = 0 := by
    intro c hc
    rw [← liftGen_mulVec_top C sA sB w c]
    exact top c hc
  have hfin : n = 0 ∧ α = 0 ∧ δ₁ = 0 ∧ δ₂ = 0 → w = 0 := fun h =>
    idx_eq_zero w h.1 h.2.1 h.2.2.1 h.2.2.2
  apply hfin
  have t0 : 1 ≤ d 0 → α = 0 := fun h => by simpa [liftTop] using tp 0 h
  have t1 : 1 ≤ d 1 → α + δ₁ = 0 := fun h => by simpa [liftTop] using tp 1 h
  have t2 : 1 ≤ d 2 → α + δ₁ + δ₂ = 0 := fun h => by simpa [liftTop, add_assoc] using tp 2 h
  have j00 : M + 1 < d 0 → δ₂ = 0 := fun h => by simpa [liftJit] using jit 0 0 (by omega) h
  have j01 : M + 2 < d 0 → δ₁ = 0 := fun h => by simpa [liftJit] using jit 0 1 (by omega) h
  have j10 : M + 1 < d 1 → δ₁ + δ₂ = 0 := fun h => by simpa [liftJit] using jit 1 0 (by omega) h
  have j11 : M + 2 < d 1 → δ₁ = 0 := fun h => by simpa [liftJit] using jit 1 1 (by omega) h
  have j20 : M + 1 < d 2 → δ₁ = 0 := fun h => by simpa [liftJit] using jit 2 0 (by omega) h
  have j21 : M + 2 < d 2 → δ₂ = 0 := fun h => by simpa [liftJit] using jit 2 1 (by omega) h
  have hP0 := pair_box C hP
  by_cases h0 : 1 ≤ d 0 <;> by_cases h1 : 1 ≤ d 1 <;> by_cases h2 : 1 ≤ d 2
  · -- all `d_c ≥ 1`
    have ha : α = 0 := t0 h0
    have hd1 : δ₁ = 0 := by have := t1 h1; rw [ha, zero_add] at this; exact this
    have hd2 : δ₂ = 0 := by have := t2 h2; rw [ha, hd1, zero_add, zero_add] at this; exact this
    refine ⟨?_, ha, hd1, hd2⟩
    apply hP (fun c => d c - 1) (by rw [Fin.sum_univ_three]; omega) n
    intro c j hj
    have := blk c j j.isLt (by simp only at hj; omega)
    rw [hd1, hd2, mul_zero, mul_zero, add_zero, add_zero] at this
    exact this
  · -- `d_z = 0`: the pair `(x, y)` along `s_B`
    have hd2 : d 2 = 0 := by omega
    have ha : α = 0 := t0 h0
    have hd1 : δ₁ = 0 := by have := t1 h1; rw [ha, zero_add] at this; exact this
    obtain ⟨hn, ht⟩ := pair_case C 0 1 (sB 0, sB 1) (hP0 0 1 (by decide))
      (fun e he1 he2 => (hadm e he1 he2).2.1) n δ₂ (d 0 - 1) (by omega)
      (fun j hj => by
        have := blk 0 j j.isLt (by omega); rw [hd1, mul_zero, add_zero] at this
        rw [mul_comm]; exact this)
      (fun j hj => by
        have := blk 1 j j.isLt (by omega); rw [hd1, mul_zero, add_zero] at this
        rw [mul_comm]; exact this)
      (fun hE => by
        rcases hE with hE | hE
        · have := j10 (by omega); rw [hd1, zero_add] at this; exact this
        · exact j00 (by omega))
    exact ⟨hn, ha, hd1, ht⟩
  · -- `d_y = 0`: the pair `(x, z)` along `s_B − s_A`
    have ha : α = 0 := t0 h0
    have hsum : δ₁ + δ₂ = 0 := by have := t2 h2; rw [ha, zero_add] at this; exact this
    have hd1 : δ₁ = -δ₂ := eq_neg_of_add_eq_zero_left hsum
    obtain ⟨hn, ht⟩ := pair_case C 0 2 (sB 0 - sA 0, sB 2 - sA 2) (hP0 0 2 (by decide))
      (fun e he1 he2 => (hadm e he1 he2).2.2) n δ₂ (d 0 - 1) (by omega)
      (fun j hj => by
        have := blk 0 j j.isLt (by omega); rw [hd1] at this
        simp only [Pi.sub_apply]; exact alg_line _ _ _ _ this)
      (fun j hj => by
        have := blk 2 j j.isLt (by omega); rw [hd1] at this
        simp only [Pi.sub_apply]; exact alg_line _ _ _ _ this)
      (fun hE => by
        rcases hE with hE | hE
        · have := j20 (by omega); rw [hd1] at this; exact neg_eq_zero.1 this
        · exact j00 (by omega))
    refine ⟨hn, ha, by rw [ht, add_zero] at hsum; exact hsum, ht⟩
  · -- `d_y = d_z = 0`: `x` reads everything
    have hdx : d 0 = M + 3 := by omega
    have ha : α = 0 := t0 h0
    have hd2 : δ₂ = 0 := j00 (by omega)
    have hd1 : δ₁ = 0 := j01 (by omega)
    refine ⟨full_box C hP 0 n (fun j => ?_), ha, hd1, hd2⟩
    have := blk 0 j j.isLt (by omega)
    rw [hd1, hd2, mul_zero, mul_zero, add_zero, add_zero] at this; exact this
  · -- `d_x = 0`: the pair `(y, z)` along `s_A`
    have hsum1 : α + δ₁ = 0 := t1 h1
    have hd2 : δ₂ = 0 := by have := t2 h2; rw [hsum1, zero_add] at this; exact this
    obtain ⟨hn, ht⟩ := pair_case C 1 2 (sA 1, sA 2) (hP0 1 2 (by decide))
      (fun e he1 he2 => (hadm e he1 he2).1) n δ₁ (d 1 - 1) (by omega)
      (fun j hj => by
        have := blk 1 j j.isLt (by omega); rw [hd2, mul_zero, add_zero] at this
        rw [mul_comm]; exact this)
      (fun j hj => by
        have := blk 2 j j.isLt (by omega); rw [hd2, mul_zero, add_zero] at this
        rw [mul_comm]; exact this)
      (fun hE => by
        rcases hE with hE | hE
        · exact j20 (by omega)
        · have := j10 (by omega); rw [hd2, add_zero] at this; exact this)
    refine ⟨hn, by rw [ht, add_zero] at hsum1; exact hsum1, ht, hd2⟩
  · -- `d_x = d_z = 0`: `y` reads everything
    have hsum1 : α + δ₁ = 0 := t1 h1
    have hd1 : δ₁ = 0 := j11 (by omega)
    have hsum2 : δ₁ + δ₂ = 0 := j10 (by omega)
    have hd2 : δ₂ = 0 := by rw [hd1, zero_add] at hsum2; exact hsum2
    refine ⟨full_box C hP 1 n (fun j => ?_), by rw [hd1, add_zero] at hsum1; exact hsum1, hd1, hd2⟩
    have := blk 1 j j.isLt (by omega)
    rw [hd1, hd2, mul_zero, mul_zero, add_zero, add_zero] at this; exact this
  · -- `d_x = d_y = 0`: `z` reads everything
    have hd1 : δ₁ = 0 := j20 (by omega)
    have hd2 : δ₂ = 0 := j21 (by omega)
    have hsum : α + δ₁ + δ₂ = 0 := t2 h2
    refine ⟨full_box C hP 2 n (fun j => ?_), by rw [hd1, hd2, add_zero, add_zero] at hsum; exact hsum, hd1, hd2⟩
    have := blk 2 j j.isLt (by omega)
    rw [hd1, hd2, mul_zero, mul_zero, add_zero, add_zero] at this; exact this
  · omega

/-- **`lem:lift`(A)**: if `P` (generator matrices `C`, shift `σ`) is a digitally shifted digital `(0,M,3)`-net over
`F_b` and `s_A, s_B` are admissible, then the lift `L_D(P)` is a digitally shifted digital `(0, M+3, 3)`-net. -/
theorem lift_net (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ sA sB : Fin 3 → Fin M → ZMod b)
    (hP : Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ)) (hadm : Admissible C sA sB) :
    Z3NetF.IsNet0 3 b (M + 3) (Z3NetF.digPointShift b (M + 3) (liftGen C sA sB) (liftShift σ)) := by
  rw [net_iff_boxInj] at hP ⊢
  exact lift_boxInj C sA sB hP hadm

end liftA

/-! ## `lem:lift`(B) -/

section liftB

variable {M : ℕ}

/-- `u` vanishes on the first `D` digits of both components (the deep digits are those of index `≥ D`). -/
def DeepV (D : ℕ) (u : (Fin M → ZMod b) × (Fin M → ZMod b)) : Prop :=
  ∀ j : Fin M, (j : ℕ) < D → u.1 j = 0 ∧ u.2 j = 0

/-- One greedy step: if `u` avoids `W e'` for the processed `e'` and the pivot vector `p` avoids `W e` but lies in
every processed `W e'`, then `u` or `u + p` avoids `W e` and all processed `W e'`. -/
lemma greedy_step (W : ℕ → Submodule (ZMod b) ((Fin M → ZMod b) × (Fin M → ZMod b))) (S : ℕ → Prop)
    (D e : ℕ) (u p : (Fin M → ZMod b) × (Fin M → ZMod b)) (hu : DeepV D u) (huS : ∀ e', S e' → u ∉ W e')
    (hp : DeepV D p) (hpe : p ∉ W e) (hpS : ∀ e', S e' → p ∈ W e') :
    ∃ u', DeepV D u' ∧ u' ∉ W e ∧ ∀ e', S e' → u' ∉ W e' := by
  by_cases h : u ∈ W e
  · refine ⟨u + p, fun j hj => ?_, fun h' => hpe ?_, fun e' he' h' => huS e' he' ?_⟩
    · have h1 := hu j hj; have h2 := hp j hj
      simp [h1.1, h1.2, h2.1, h2.2]
    · exact (Submodule.add_mem_iff_right _ h).1 h'
    · exact (Submodule.add_mem_iff_left _ (hpS e' he')).1 h'
  · exact ⟨u, hu, h, huS⟩

/-- The pivot on digit `e` (index `e - 1`) of the first coordinate: not in `H_e` (the `(e-1, M+1-e)` box). -/
lemma pivot_fst (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (c c' : Fin 3)
    (hP : ∀ e ≤ M, ∀ n : Fin M → ZMod b, (∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j = 0) →
      (∀ j : Fin M, (j : ℕ) < M - e → (C c' *ᵥ n) j = 0) → n = 0)
    (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ M) :
    ((Pi.single (⟨e - 1, by omega⟩ : Fin M) (1 : ZMod b)), (0 : Fin M → ZMod b)) ∉
      pairSub C c c' ⊔ Zsub b M e := by
  intro hmem
  obtain ⟨y, ⟨n, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  have hy : ((C c).mulVecLin.prod (C c').mulVecLin) n = (C c *ᵥ n, C c' *ᵥ n) := rfl
  rw [hy] at hyz
  have h1 : C c *ᵥ n + z.1 = _ := congrArg Prod.fst hyz
  have h2 : C c' *ᵥ n + z.2 = _ := congrArg Prod.snd hyz
  dsimp only at h1 h2
  have hn : n = 0 := by
    apply hP (e - 1) (by omega) n
    · intro j hj
      have := congrFun h1 j
      rw [Pi.add_apply, hz.1 j (by omega), add_zero, Pi.single_apply, if_neg (by
        intro h; rw [h] at hj; simp at hj)] at this
      exact this
    · intro j hj
      have := congrFun h2 j
      rw [Pi.add_apply, hz.2 j (by omega), add_zero] at this
      exact this
  have := congrFun h1 ⟨e - 1, by omega⟩
  rw [Pi.add_apply, hz.1 _ (by simp; omega), add_zero, Pi.single_eq_same, hn, mulVec_zero] at this
  exact zero_ne_one this

/-- The pivot on digit `M + 1 - e` (index `M - e`) of the second coordinate: not in `H_e` (the `(e, M-e)` box). -/
lemma pivot_snd (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (c c' : Fin 3)
    (hP : ∀ e ≤ M, ∀ n : Fin M → ZMod b, (∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j = 0) →
      (∀ j : Fin M, (j : ℕ) < M - e → (C c' *ᵥ n) j = 0) → n = 0)
    (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ M) :
    ((0 : Fin M → ZMod b), (Pi.single (⟨M - e, by omega⟩ : Fin M) (1 : ZMod b))) ∉
      pairSub C c c' ⊔ Zsub b M e := by
  intro hmem
  obtain ⟨y, ⟨n, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  have hy : ((C c).mulVecLin.prod (C c').mulVecLin) n = (C c *ᵥ n, C c' *ᵥ n) := rfl
  rw [hy] at hyz
  have h1 : C c *ᵥ n + z.1 = _ := congrArg Prod.fst hyz
  have h2 : C c' *ᵥ n + z.2 = _ := congrArg Prod.snd hyz
  dsimp only at h1 h2
  have hn : n = 0 := by
    apply hP e he2 n
    · intro j hj
      have := congrFun h1 j
      rw [Pi.add_apply, hz.1 j hj, add_zero] at this
      exact this
    · intro j hj
      have := congrFun h2 j
      rw [Pi.add_apply, hz.2 j (by omega), add_zero, Pi.single_apply, if_neg (by
        intro h; rw [h] at hj; simp at hj)] at this
      exact this
  have := congrFun h2 ⟨M - e, by omega⟩
  rw [Pi.add_apply, hz.2 _ (by simp; omega), add_zero, Pi.single_eq_same, hn, mulVec_zero] at this
  exact zero_ne_one this

/-- **`lem:lift`(B) for one pair**: if `2D ≤ M`, some `u` vanishing on the first `D` digits of both coordinates of
the pair lies outside every `H_e = P_cc' ⊔ Z_e`, `1 ≤ e ≤ M`. -/
lemma pair_exists (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (c c' : Fin 3)
    (hP : ∀ e ≤ M, ∀ n : Fin M → ZMod b, (∀ j : Fin M, (j : ℕ) < e → (C c *ᵥ n) j = 0) →
      (∀ j : Fin M, (j : ℕ) < M - e → (C c' *ᵥ n) j = 0) → n = 0)
    (D : ℕ) (hD : 2 * D ≤ M) :
    ∃ u, DeepV D u ∧ ∀ e : ℕ, 1 ≤ e → e ≤ M → u ∉ pairSub C c c' ⊔ Zsub b M e := by
  set W : ℕ → Submodule (ZMod b) ((Fin M → ZMod b) × (Fin M → ZMod b)) := fun e => pairSub C c c' ⊔ Zsub b M e
  -- group 1: `e = D+1, …, D+k`, pivots on the first coordinate
  have g1 : ∀ k, k ≤ M - D → ∃ u, DeepV D u ∧ ∀ e', D < e' → e' ≤ D + k → u ∉ W e' := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨0, fun j _ => ⟨rfl, rfl⟩, fun e' h1 h2 => absurd h2 (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, huS⟩ := ih (by omega)
      have he1 : 1 ≤ D + k + 1 := by omega
      have he2 : D + k + 1 ≤ M := by omega
      obtain ⟨u', hu', hue, huS'⟩ := greedy_step W (fun e' => D < e' ∧ e' ≤ D + k) D (D + k + 1) u
        ((Pi.single (⟨D + k + 1 - 1, by omega⟩ : Fin M) (1 : ZMod b)), (0 : Fin M → ZMod b)) hu
        (fun e' h => huS e' h.1 h.2)
        (fun j hj => ⟨by dsimp only; rw [Pi.single_apply, if_neg (by intro h; rw [h] at hj; simp at hj; try omega)], rfl⟩)
        (pivot_fst C c c' hP _ he1 he2)
        (fun e' h => Submodule.mem_sup_right ⟨fun j hj => by
          dsimp only
          rw [Pi.single_apply, if_neg (by intro h'; rw [h'] at hj; simp at hj; try omega)], fun _ _ => rfl⟩)
      refine ⟨u', hu', fun e' h1 h2 => ?_⟩
      by_cases h : e' = D + k + 1
      · rw [h]; exact hue
      · exact huS' e' ⟨h1, by omega⟩
  -- group 2: `e = D, D-1, …`, pivots on the second coordinate
  have g2 : ∀ k, k ≤ D → ∃ u, DeepV D u ∧ (∀ e', D < e' → e' ≤ M → u ∉ W e') ∧
      ∀ e', D - k < e' → e' ≤ D → u ∉ W e' := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨u, hu, huS⟩ := g1 (M - D) le_rfl
      exact ⟨u, hu, fun e' h1 h2 => huS e' h1 (by omega), fun e' h1 h2 => absurd h1 (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, huS1, huS2⟩ := ih (by omega)
      have he1 : 1 ≤ D - k := by omega
      have he2 : D - k ≤ M := by omega
      obtain ⟨u', hu', hue, huS'⟩ := greedy_step W
        (fun e' => (D < e' ∧ e' ≤ M) ∨ (D - k < e' ∧ e' ≤ D)) D (D - k) u
        ((0 : Fin M → ZMod b), (Pi.single (⟨M - (D - k), by omega⟩ : Fin M) (1 : ZMod b))) hu
        (fun e' h => h.elim (fun h => huS1 e' h.1 h.2) (fun h => huS2 e' h.1 h.2))
        (fun j hj => ⟨rfl, by dsimp only; rw [Pi.single_apply, if_neg (by intro h; rw [h] at hj; simp at hj; try omega)]⟩)
        (pivot_snd C c c' hP _ he1 he2)
        (fun e' h => Submodule.mem_sup_right ⟨fun _ _ => rfl, fun j hj => by
          dsimp only
          rw [Pi.single_apply, if_neg (by
            intro h'; rw [h'] at hj; simp at hj; rcases h with h | h <;> omega)]⟩)
      refine ⟨u', hu', fun e' h1 h2 => huS' e' (Or.inl ⟨h1, h2⟩), fun e' h1 h2 => ?_⟩
      by_cases h : e' = D - k
      · rw [h]; exact hue
      · exact huS' e' (Or.inr ⟨by omega, h2⟩)
  obtain ⟨u, hu, h1, h2⟩ := g2 D le_rfl
  refine ⟨u, hu, fun e he1 he2 => ?_⟩
  by_cases h : D < e
  · exact h1 e h he2
  · exact h2 e (by omega) (by omega)

/-- **`lem:lift`(B)**: if `P` is a digitally shifted digital `(0,M,3)`-net over `F_b` and `2D ≤ M`, there are
admissible `s_A, s_B` vanishing on the first `D` digits of each coordinate. -/
theorem lift_exists (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ : Fin 3 → Fin M → ZMod b)
    (hP : Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ)) (D : ℕ) (hD : 2 * D ≤ M) :
    ∃ sA sB : Fin 3 → Fin M → ZMod b, VanishTop D sA ∧ VanishTop D sB ∧ Admissible C sA sB := by
  rw [net_iff_boxInj] at hP
  obtain ⟨u1, hu1, a1⟩ := pair_exists C 1 2 (pair_box C hP 1 2 (by decide)) D hD
  obtain ⟨u2, hu2, a2⟩ := pair_exists C 0 1 (pair_box C hP 0 1 (by decide)) D hD
  obtain ⟨u3, hu3, a3⟩ := pair_exists C 0 2 (pair_box C hP 0 2 (by decide)) D hD
  refine ⟨![u2.1 - u3.1, u1.1, u1.2], ![u2.1, u2.2, u1.2 + u3.2], ?_, ?_, ?_⟩
  · intro c j hj
    fin_cases c
    · simp [(hu2 j hj).1, (hu3 j hj).1]
    · simp [(hu1 j hj).1]
    · simp [(hu1 j hj).2]
  · intro c j hj
    fin_cases c
    · simp [(hu2 j hj).1]
    · simp [(hu2 j hj).2]
    · simp [(hu1 j hj).2, (hu3 j hj).2]
  · intro e he1 he2
    refine ⟨?_, ?_, ?_⟩
    · exact a1 e he1 he2
    · exact a2 e he1 he2
    · have : (![u2.1, u2.2, u1.2 + u3.2] 0 - ![u2.1 - u3.1, u1.1, u1.2] 0,
          ![u2.1, u2.2, u1.2 + u3.2] 2 - ![u2.1 - u3.1, u1.1, u1.2] 2) = u3 := by
        exact Prod.ext (sub_sub_cancel _ _) (add_sub_cancel_left _ _)
      rw [this]; exact a3 e he1 he2

end liftB

end Z3NetB23.Proofs
