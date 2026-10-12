/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `cor:allm`. Entry Dim3
(`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3CorA

@[expose] public section

/-!
# Entry Dim3, part 7: `cor:allm`

The four families: `thm:col` (`m = 3`, the column net `𝒞_p`, `Z3NetC.colGen`; V14 stage S9′, replacing
the former `thm:E1`), `thm:main` (`m = 3k`, `k ≥ 2`,
`Z3Net.PGen`), `thm:allm` (`m = 3k + 1`, `B1gen` with `ρ = rhoB1 p`), `thm:S1` at `s = 3`
(`m = 3k + 2`, `B2gen` with `ρ = ρ_3(p)`). Separation: the family bounds, each `≥ bndDim3 p`.
Covering: the elementary box of the coarse depths (`cover_box_dist`), and for `m ≡ 2` also
`thm:S1`(3) (`Z3NetS1.S1_cover`) with the constant `cor_allm_consts`.
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset Filter Topology

/-! ## Constants -/

lemma sqrt3_lt : Real.sqrt 3 < 1.7320509 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt3_gt : 1.73205 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma cP_ge (p : ℕ) (hp8 : 8 ≤ p) : 1 - 1 / (p : ℝ) ≤ Z3Net.cP p := by
  unfold Z3Net.cP
  have hx : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have hx8 : 1 / (p : ℝ) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; exact_mod_cast (by omega : 1 * 8 ≤ 1 * p)
  have h1 : 0 ≤ 1 - 1 / (p : ℝ) := by linarith
  rw [show 2 / (p : ℝ) = 2 * (1 / p) by ring, show 4 / (p : ℝ) = 4 * (1 / p) by ring,
    show 3 / (p : ℝ) = 3 * (1 / p) by ring]
  set x := 1 / (p : ℝ)
  apply Real.le_sqrt_of_sq_le
  apply le_min (le_refl _)
  apply le_min
  · nlinarith
  · nlinarith

lemma bndB2_gt_half (p : ℕ) (hp : p.Prime) (h28 : 28 ≤ p) : 1 / 2 < bndB2 p := by
  obtain ⟨-, -, -, h4, -, h6⟩ := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
  have h := h6 (by norm_num; omega)
  have e : bndB2 p = ((Z3NetS1.rhoS 3 p : ℝ) - 1) * (p : ℝ) ^ (-(1 / ((3 : ℕ) : ℝ))) := rfl
  rw [e]; linarith

lemma rhoB1_lt4 (p : ℕ) (hp : p < 80) : rhoB1 p < 4 := by
  by_contra h
  push Not at h
  have hs := rhoB1_spec p
  have h1 : 4 ^ 2 ≤ rhoB1 p ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : 4 ^ 2 * 5 ≤ rhoB1 p ^ 2 * (rhoB1 p + 1) := Nat.mul_le_mul h1 (by omega)
  omega

lemma bndB1_gt_small (p : ℕ) (h36 : 36 ≤ p) (h79 : p ≤ 79) : 0.2715 < bndB1 p := by
  have h3 : rhoB1 p = 3 := le_antisymm (by have := rhoB1_lt4 p (by omega); omega)
    (rhoB1_ge p 3 (by norm_num; omega))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold bndB1
  rw [h3]
  have e : (p : ℝ) ^ (-(((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) = ((p : ℝ) ^ 2) ^ (-(1 / (3 : ℝ))) := by
    rw [rpow_third_nat _ hp0]; norm_num
  rw [e]
  apply lt_mul_rpow_neg_third _ _ _ (by positivity) (by norm_num)
  have : (p : ℝ) ≤ 79 := by exact_mod_cast h79
  have : (p : ℝ) ^ 2 ≤ 6241 := by nlinarith
  norm_num
  nlinarith

lemma bndB1_gt_large (p : ℕ) (h80 : 80 ≤ p) : 0.4250 < bndB1 p := by
  have h4 : 4 ≤ rhoB1 p := rhoB1_ge p 4 (by norm_num; omega)
  have hlt := B1_g_lt p (by omega)
  have hmono : gB1 4 ≤ gB1 (rhoB1 p) := by
    apply gB1_strictMonoOn.monotoneOn (by norm_num)
      (by simp only [Set.mem_Ici]; exact_mod_cast (by omega : 3 ≤ rhoB1 p))
    exact_mod_cast h4
  have hg4 : gB1 4 = 48 / 625 := by unfold gB1; norm_num
  rw [hg4] at hmono
  obtain ⟨h0, -⟩ := bndB1_le_one p (by omega)
  by_contra hc
  push Not at hc
  have : bndB1 p ^ 3 ≤ 0.4250 ^ 3 := pow_le_pow_left₀ h0 hc 3
  norm_num at this
  linarith

/-! ## Rpow arithmetic for the covering constants -/

lemma Ninv (p : ℝ) (hp : 0 < p) (k r : ℕ) (a : ℝ) (ha : a - (r : ℝ) / 3 = 0) :
    p ^ a * (p ^ (3 * k + r)) ^ (-(1 / (3 : ℝ))) = (p ^ k)⁻¹ := by
  rw [rpow_third_nat _ hp, ← Real.rpow_add hp, ← Real.rpow_natCast, ← Real.rpow_neg hp.le]
  congr 1; push_cast; linarith

lemma sqrt_mul_inv_sq (A q : ℝ) (hA : 0 ≤ A) (hq : 0 < q) :
    Real.sqrt (A * (q⁻¹) ^ 2) = Real.sqrt A * q⁻¹ := by
  rw [Real.sqrt_mul hA, Real.sqrt_sq (by positivity)]

/-! ## The four families -/

lemma famCol (p : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) :
    IsNet0 p 3 (digPoint p 3 (Z3NetC.colGen p)) ∧
    (∀ v w : Fin 3 → ZMod p, v ≠ w →
      bndDim3 p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ 3) ((digPoint p 3 (Z3NetC.colGen p) v c : ℤ) -
          (digPoint p 3 (Z3NetC.colGen p) w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin 3 → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p 3 (Z3NetC.colGen p) v c : ℝ) / (p : ℝ) ^ 3) ^ 2) ≤
        Real.sqrt 3 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) := by
  refine ⟨col_isNet0 p hp (by omega), fun v w hvw => ?_, fun y hy => col_cover_dim3 p hp (by omega) y hy⟩
  refine le_trans ?_ (col_sep_dim3 p hp (by omega) v w hvw)
  gcongr
  unfold bndDim3; exact le_trans (min_le_left _ _) (min_le_left _ _)

lemma famP (p k : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hk : 2 ≤ k) :
    IsNet0 p (3 * k) (digPoint p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p))) ∧
    (∀ v w : Fin (3 * k) → ZMod p, v ≠ w →
      bndDim3 p * ((p : ℝ) ^ (3 * k)) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ (3 * k))
          ((digPoint p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p)) v c : ℤ) -
          (digPoint p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p)) w c : ℤ)) : ℝ)
            / (p : ℝ) ^ (3 * k)) ^ 2)) ∧
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin (3 * k) → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p (3 * k)
        (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p)) v c : ℝ) / (p : ℝ) ^ (3 * k)) ^ 2) ≤
        Real.sqrt 3 * ((p : ℝ) ^ (3 * k)) ^ (-(1 / (3 : ℝ)))) := by
  have hnet : IsNet0 p (3 * k)
      (digPoint p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p))) :=
    Z3Net.P_net p k (by omega) (by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨hnet, ?_, ?_⟩
  · intro v w hvw
    refine le_trans ?_ (Z3Net.P_sep_real p k (by omega) hk v w hvw)
    gcongr
    unfold bndDim3
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (cP_ge p (by omega)))
  · intro y hy
    obtain ⟨v, hv⟩ := cover_box_dist p (3 * k) hp.pos _ hnet (fun _ => k) (by ring) y hy
    refine ⟨v, le_trans hv (le_of_eq ?_)⟩
    simp only [Fin.sum_univ_three]
    have e := Ninv (p : ℝ) hp0 k 0 0 (by simp)
    simp only [add_zero, Real.rpow_zero, one_mul] at e
    rw [e, show ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
      3 * (((p : ℝ) ^ k)⁻¹) ^ 2 by ring, sqrt_mul_inv_sq 3 _ (by norm_num) (by positivity)]

lemma famB1 (p k : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hk : 1 ≤ k) :
    IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) (B1gen p k (rhoB1 p))) ∧
    (∀ v w : Fin (3 * k + 1) → ZMod p, v ≠ w →
      bndDim3 p * ((p : ℝ) ^ (3 * k + 1)) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ (3 * k + 1))
          ((digPoint p (3 * k + 1) (B1gen p k (rhoB1 p)) v c : ℤ) -
          (digPoint p (3 * k + 1) (B1gen p k (rhoB1 p)) w c : ℤ)) : ℝ) / (p : ℝ) ^ (3 * k + 1)) ^ 2)) ∧
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin (3 * k + 1) → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p (3 * k + 1) (B1gen p k (rhoB1 p)) v c : ℝ)
        / (p : ℝ) ^ (3 * k + 1)) ^ 2) ≤
        (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2) *
          ((p : ℝ) ^ (3 * k + 1)) ^ (-(1 / (3 : ℝ)))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h3 : 3 ≤ rhoB1 p := rhoB1_ge p 3 (by norm_num; omega)
  have hs := rhoB1_spec p
  have hlt : rhoB1 p < p := by
    have : rhoB1 p * 1 < rhoB1 p ^ 2 * (rhoB1 p + 1) := by nlinarith
    omega
  have hnd : ¬ p ∣ rhoB1 p := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  obtain ⟨hskel, hnet⟩ := B1gen_net p k (rhoB1 p) hp hk hnd
  refine ⟨hnet, ?_, ?_⟩
  · intro v w hvw
    refine le_trans ?_ (B1_sep_real p k (rhoB1 p) hp hk (by omega) hs _ hskel v w hvw)
    gcongr
    unfold bndDim3
    refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_of_eq ?_))
    unfold bndB1; norm_num
  · intro y hy
    obtain ⟨v, hv⟩ := cover_box_dist p (3 * k + 1) hp.pos _ hnet ![k + 1, k, k]
      (by simp; ring) y hy
    refine ⟨v, le_trans hv (le_of_eq ?_)⟩
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_comm ((p : ℝ) ^ (1 / (3 : ℝ))), mul_assoc,
      Ninv (p : ℝ) hp0 k 1 (1 / 3) (by norm_num)]
    have e : ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
        (2 + 1 / (p : ℝ) ^ 2) * (((p : ℝ) ^ k)⁻¹) ^ 2 := by
      field_simp; ring
    rw [e, sqrt_mul_inv_sq _ _ (by positivity) (by positivity)]

lemma famB2 (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 1 ≤ k) :
    IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p))) ∧
    IsKNskel 2 p k (skB2 (rhoS 3 p)) (B2gen p k (rhoS 3 p)) ∧
    (∀ v w : Fin (3 * k + 2) → ZMod p, v ≠ w →
      bndB2 p * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) v c : ℤ) -
          (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) w c : ℤ)) : ℝ) / (p : ℝ) ^ (3 * k + 2)) ^ 2)) ∧
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin (3 * k + 2) → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) v c : ℝ)
        / (p : ℝ) ^ (3 * k + 2)) ^ 2) ≤
        (p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2) *
          ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ)))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨h2, hρp, -, -, -, -⟩ := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
  have e : Z3NetS1.rhoS 3 p = rhoS 3 p := rfl
  rw [e] at h2 hρp
  have hlt : rhoS 3 p < p := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) _) hρp
  have hnd : ¬ p ∣ rhoS 3 p := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  obtain ⟨hskel, hnet⟩ := B2gen_net p k (rhoS 3 p) hp hk hnd
  refine ⟨hnet, hskel, ?_, ?_⟩
  · intro v w hvw
    refine le_trans (le_of_eq ?_) (B2_rem_sep_real p k (rhoS 3 p) hp (by omega) hρp _ hskel v w hvw)
    unfold bndB2; norm_num
  · intro y hy
    obtain ⟨v, hv⟩ := cover_box_dist p (3 * k + 2) hp.pos _ hnet ![k + 1, k + 1, k]
      (by simp; ring) y hy
    refine ⟨v, le_trans hv (le_of_eq ?_)⟩
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_comm ((p : ℝ) ^ (2 / (3 : ℝ))), mul_assoc,
      Ninv (p : ℝ) hp0 k 2 (2 / 3) (by norm_num)]
    have e : ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
        (1 + 2 / (p : ℝ) ^ 2) * (((p : ℝ) ^ k)⁻¹) ^ 2 := by
      field_simp; ring
    rw [e, sqrt_mul_inv_sq _ _ (by positivity) (by positivity)]

end Z3NetKN.Proofs.D3
