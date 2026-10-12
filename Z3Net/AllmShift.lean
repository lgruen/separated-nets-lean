/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.KNShift
public import Z3Net.S1Shift2
public import Z3Net.SepShift
public import Z3Net.D3CorMain

@[expose] public section

/-!
# V14 stage S10′: `cor:allmshift` for `m ≥ 4`

The nets of `cor:allm` for `m ≥ 4` (`𝒫_{k,p}` for `m = 3k`, `𝓑¹_{k,p,ρ}` for `m = 3k+1`,
`𝓑²_{k,p,ρ}` for `m = 3k+2`, `ρ` maximal) keep all their guarantees under every digital shift `τ`:
the `(0,m,3)`-property (`Z3NetF.Proofs.digPointShift_net`), the separation bound `bndDim3 p`
(`Z3Net.Proofs.P_sep_shift_real`, `B1_sep_shift_real_core`, `B2_rem_sep_shift_real_core`), the
covering radii of `cor:allm` (`cover_box_dist` needs only the net property; the constant `4.264` from
the shifted covering `Z3NetS1.Proofs.S1_cover_shift_core`), and an `ℓ^∞` bound: two distinct points
differ by at least `p^(m-κ)` (`κ = ⌊m/3⌋ + 1`) in some coordinate, toroidally (`P_sep_shift_main` for
`m ≡ 0`; for `m ≢ 0` pigeonhole from the integer bounds, `linf_of_sum`).
-/

namespace Z3NetKN.Proofs

open Matrix Finset Filter Topology D3

namespace D3

lemma isNet0_shift (p m : ℕ) [NeZero p] (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p))
    (h : IsNet0 p m (digPoint p m C)) (τ : Fin 3 → Fin m → ZMod p) :
    IsNet0 p m (Z3NetF.digPointShift p m C τ) := by
  have hF : Z3NetF.IsNet0 3 p m (Z3NetF.digPoint p m C) := by
    intro d hd a ha
    rw [Fin.sum_univ_three] at hd
    exact h d hd a ha
  have hS := Z3NetF.Proofs.digPointShift_net C τ hF
  intro d hd a ha
  exact hS d (by rw [Fin.sum_univ_three]; exact hd) a ha

/-- Pigeonhole: if `4 B² ≤ ∑_c f_c²` then some `f_c ≥ B`. -/
lemma linf_of_sum (f : Fin 3 → ℕ) (B : ℕ) (h : 4 * B ^ 2 ≤ ∑ c, f c ^ 2) : ∃ c, B ≤ f c := by
  by_contra hcon
  push_neg at hcon
  rw [Fin.sum_univ_three] at h
  have h0 := Nat.pow_lt_pow_left (hcon 0) (two_ne_zero)
  have h1 := Nat.pow_lt_pow_left (hcon 1) (two_ne_zero)
  have h2 := Nat.pow_lt_pow_left (hcon 2) (two_ne_zero)
  omega

end D3

/-- **`cor:allmshift`, `m ≥ 4`.** For every prime `p ≥ 37` and every `m ≥ 4` the net of `cor:allm`
keeps, under every digital shift `τ`, the `(0,m,3)`-property, the separation bound
`δ N^(1/3) ≥ bndDim3 p`, the covering bounds of `cor:allm`, and the `ℓ^∞` bound: any two distinct
points are at toroidal distance `≥ p^(m-κ)` (integer scale `p^m`, `κ = ⌊m/3⌋ + 1`) in some
coordinate. -/
theorem allmshift_core (p m : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 4 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsNet0 p m (Z3NetF.digPointShift p m C τ) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w →
        bndDim3 p * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) -
            (Z3NetF.digPointShift p m C τ w c : ℤ)) : ℝ) / (p : ℝ) ^ m) ^ 2)) ∧
      (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
        Real.sqrt (∑ c, (y c - (Z3NetF.digPointShift p m C τ v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
          (if m % 3 = 0 then Real.sqrt 3
           else if m % 3 = 1 then (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2)
           else min ((p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2)) 4.264) *
            ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ)))) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w → ∃ c : Fin 3,
        p ^ (m - (m / 3 + 1)) ≤ cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) -
          (Z3NetF.digPointShift p m C τ w c : ℤ))) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨-, -, hlB1, hlB2⟩ := bndDim3_le p
  rcases (show (m % 3 = 0 ∧ 6 ≤ m) ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with ⟨h, h6⟩ | h | h
  · -- `m = 3k`: the net `𝒫_{k,p}`
    obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
    have hk : 2 ≤ k := by omega
    obtain ⟨hn, -, -⟩ := famP p k hp hp37 hk
    refine ⟨fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p), fun τ => ?_⟩
    have hnS := isNet0_shift p (3 * k) _ hn τ
    refine ⟨hnS, fun v w hvw => ?_, fun y hy => ?_, fun v w hvw => ?_⟩
    · refine le_trans ?_ (Z3Net.Proofs.P_sep_shift_real p k (by omega) hk τ v w hvw)
      gcongr
      unfold bndDim3
      exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (cP_ge p (by omega)))
    · obtain ⟨v, hv⟩ := cover_box_dist p (3 * k) hp.pos _ hnS (fun _ => k) (by ring) y hy
      refine ⟨v, le_trans hv (le_of_eq ?_)⟩
      rw [if_pos (by omega)]
      simp only [Fin.sum_univ_three]
      have e := Ninv (p : ℝ) hp0 k 0 0 (by simp)
      simp only [add_zero, Real.rpow_zero, one_mul] at e
      rw [e, show ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
        3 * (((p : ℝ) ^ k)⁻¹) ^ 2 by ring, sqrt_mul_inv_sq 3 _ (by norm_num) (by positivity)]
    · obtain ⟨c, hc⟩ := (Z3Net.Sep.P_sep_shift_main p k (by omega) hk τ v w hvw).2
      refine ⟨c, ?_⟩
      rw [show 3 * k - (3 * k / 3 + 1) = 2 * k - 1 by omega]
      have hp3 : (1 : ℤ) ≤ (p : ℤ) - 3 := by
        have : (37 : ℤ) ≤ p := by exact_mod_cast hp37
        linarith
      have hpow : (0 : ℤ) ≤ (p : ℤ) ^ (2 * k - 1) := by positivity
      have h1 : ((p ^ (2 * k - 1) : ℕ) : ℤ) ≤ (cres (p ^ (3 * k))
          ((Z3NetF.digPointShift p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p)) τ v c : ℤ) -
          (Z3NetF.digPointShift p (3 * k) (fun c => (Z3Net.PGen k c).map (Int.cast : ℤ → ZMod p)) τ w c : ℤ)) : ℤ) := by
        push_cast
        refine le_trans ?_ hc
        nlinarith
      exact_mod_cast h1
  · -- `m = 3k+1`: the net `𝓑¹_{k,p,ρ}`
    obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
    have hk : 1 ≤ k := by omega
    have h3 : 3 ≤ rhoB1 p := rhoB1_ge p 3 (by norm_num; omega)
    have hs := rhoB1_spec p
    have hlt : rhoB1 p < p := by
      have : rhoB1 p * 1 < rhoB1 p ^ 2 * (rhoB1 p + 1) := by nlinarith
      omega
    have hnd : ¬ p ∣ rhoB1 p := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    obtain ⟨hskel, hnet⟩ := B1gen_net p k (rhoB1 p) hp hk hnd
    refine ⟨B1gen p k (rhoB1 p), fun τ => ?_⟩
    have hnS := isNet0_shift p (3 * k + 1) _ hnet τ
    refine ⟨hnS, fun v w hvw => ?_, fun y hy => ?_, fun v w hvw => ?_⟩
    · refine le_trans ?_ (B1_sep_shift_real_core p k (rhoB1 p) hp hk (by omega) hs _ hskel τ v w hvw)
      gcongr
      unfold bndDim3
      refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_of_eq ?_))
      unfold bndB1; norm_num
    · obtain ⟨v, hv⟩ := cover_box_dist p (3 * k + 1) hp.pos _ hnS ![k + 1, k, k]
        (by simp; ring) y hy
      refine ⟨v, le_trans hv (le_of_eq ?_)⟩
      rw [if_neg (by omega), if_pos (by omega)]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [mul_comm ((p : ℝ) ^ (1 / (3 : ℝ))), mul_assoc,
        Ninv (p : ℝ) hp0 k 1 (1 / 3) (by norm_num)]
      have e : ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
          (2 + 1 / (p : ℝ) ^ 2) * (((p : ℝ) ^ k)⁻¹) ^ 2 := by
        field_simp; ring
      rw [e, sqrt_mul_inv_sq _ _ (by positivity) (by positivity)]
    · have hZ := B1_sep_shift_core p k (rhoB1 p) hp hk (by omega) hs _ hskel τ v w hvw
      unfold torusDist2 at hZ
      rw [show 3 * k + 1 - ((3 * k + 1) / 3 + 1) = 2 * k by omega]
      refine linf_of_sum _ _ (le_trans ?_ hZ)
      have h5 : 5 ≤ rhoB1 p ^ 2 - 4 := by
        have : 9 ≤ rhoB1 p ^ 2 := by nlinarith
        omega
      have h25 : 4 ≤ (rhoB1 p ^ 2 - 4) ^ 2 := by nlinarith
      rw [← pow_mul, show 2 * k * 2 = 4 * k by ring]
      exact Nat.mul_le_mul_right _ h25
  · -- `m = 3k+2`: the net `𝓑²_{k,p,ρ}` (`thm:S1` at `s = 3`)
    obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
    have hk : 1 ≤ k := by omega
    obtain ⟨h2, hρp, -, -, -, -⟩ := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
    have e : Z3NetS1.rhoS 3 p = rhoS 3 p := rfl
    rw [e] at h2 hρp
    have h3 : 3 ≤ rhoS 3 p := by
      rw [← e]; exact Z3NetS1.Proofs.rhoS_ge 3 p 3 (by norm_num) (by norm_num; omega)
    obtain ⟨hn, hsk, -, -⟩ := famB2 p k hp (by omega) hk
    refine ⟨B2gen p k (rhoS 3 p), fun τ => ?_⟩
    have hnS := isNet0_shift p (3 * k + 2) _ hn τ
    refine ⟨hnS, fun v w hvw => ?_, fun y hy => ?_, fun v w hvw => ?_⟩
    · have hB2 : bndB2 p * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
            ((Z3NetF.digPointShift p (3 * k + 2) (B2gen p k (rhoS 3 p)) τ v c : ℤ) -
            (Z3NetF.digPointShift p (3 * k + 2) (B2gen p k (rhoS 3 p)) τ w c : ℤ)) : ℝ) /
              (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
        refine le_trans (le_of_eq ?_)
          (B2_rem_sep_shift_real_core p k (rhoS 3 p) hp (by omega) hρp _ hsk τ v w hvw)
        unfold bndB2; norm_num
      refine le_trans ?_ hB2
      gcongr
    · rw [if_neg (by omega), if_neg (by omega)]
      by_cases hA : (p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2) ≤ 4.264
      · obtain ⟨v, hv⟩ := cover_box_dist p (3 * k + 2) hp.pos _ hnS ![k + 1, k + 1, k]
          (by simp; ring) y hy
        refine ⟨v, le_trans hv (le_of_eq ?_)⟩
        rw [min_eq_left hA]
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [mul_comm ((p : ℝ) ^ (2 / (3 : ℝ))), mul_assoc,
          Ninv (p : ℝ) hp0 k 2 (2 / 3) (by norm_num)]
        have e : ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ (k + 1))⁻¹ ^ 2 + ((p : ℝ) ^ k)⁻¹ ^ 2 =
            (1 + 2 / (p : ℝ) ^ 2) * (((p : ℝ) ^ k)⁻¹) ^ 2 := by
          field_simp; ring
        rw [e, sqrt_mul_inv_sq _ _ (by positivity) (by positivity)]
      · push Not at hA
        rw [min_eq_right hA.le]
        have hS1 : Z3NetS1.IsS1skel 3 p k (Z3NetS1.rhoS 3 p) (B2gen p k (rhoS 3 p)) :=
          (B2_skel_iff p k _ _).2 hsk
        obtain ⟨v, hv⟩ :=
          Z3NetS1.Proofs.S1_cover_shift_core 3 p k (le_refl 3) hp (by norm_num; omega) _ hS1 τ y hy
        simp only [Nat.cast_ofNat] at hv
        refine ⟨v, le_trans hv.le ?_⟩
        have hc4 := (cor_allm_consts.1 p hp (by omega)).1
        have hq : 0 ≤ ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) := by positivity
        exact mul_le_mul_of_nonneg_right hc4.le hq
    · have hZ := B2_rem_sep_shift_core p k (rhoS 3 p) hp (by omega) hρp _ hsk τ v w hvw
      unfold torusDist2 at hZ
      rw [show 3 * k + 2 - ((3 * k + 2) / 3 + 1) = 2 * k + 1 by omega]
      refine linf_of_sum _ _ (le_trans ?_ hZ)
      have h4 : 4 ≤ (rhoS 3 p - 1) ^ 2 := by
        have : 2 ≤ rhoS 3 p - 1 := by omega
        nlinarith
      rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring]
      exact Nat.mul_le_mul_right _ h4

end Z3NetKN.Proofs
