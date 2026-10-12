/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.S1Main
public import Z3Net.DShift

@[expose] public section

/-!
# V14 stage S10′: `thm:S1`(1) under digital shifts (`prop:shift`)

The digits of coordinate `c` of the shifted point with index `v` are the digit vector
`x_c(v) = C_c v + τ_c`; as an integer it is the digital coordinate of the identity matrix at the
"index" `x_c(v)` (`shift_coord`), so Lemma T (`prefix_bound`) applies verbatim with `A = 1`. The
fine positions are `Pf k 1 (x_c v)`; the shift cancels in every residue of a fine-position difference
(`PfSh_mod`, `PfSh_div`), and equal shifted fine positions give equal unshifted ones (`PfSh_inj`).
With these three transfer lemmas the proof of `thm:S1`(1) (`S1_sep`) goes through unchanged
(`S1_sep_shift_core`, `S1_sep_shift_real_core`). The transfer lemmas are generic (any matrix, any
shift) and are reused for `thm:allm` (`Z3Net/KNShift.lean`).
-/

namespace Z3NetKN.Geom

open Finset Matrix

variable {p : ℕ}

/-! ## Transfer lemmas: shifted digits -/

lemma vz_add {m : ℕ} (x y : Fin m → ZMod p) (j : ℕ) : vz (x + y) j = vz x j + vz y j := by
  unfold vz; split_ifs <;> simp

/-- A shifted coordinate is the digital coordinate of the identity matrix at its digit vector. -/
lemma shift_coord {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (τ : Fin s → Fin m → ZMod p)
    (v : Fin m → ZMod p) (c : Fin s) :
    Z3NetF.digPointShift p m C τ v c = Z3NetKN.coord p m 1 (C c *ᵥ v + τ c) := by
  unfold Z3NetF.digPointShift Z3NetKN.coord
  rw [one_mulVec]

lemma Pf_mod_gen [NeZero p] {m k : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (u : Fin m → ZMod p) :
    ((Pf k A u % p : ℕ) : ZMod p) = vz (A *ᵥ u) k := by
  unfold Pf
  rw [pre_succ, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _)]
  simp [dg]

lemma Pf_div_gen [NeZero p] {m k : ℕ} (hk : 1 ≤ k) (A : Matrix (Fin m) (Fin m) (ZMod p))
    (u : Fin m → ZMod p) : ((Pf k A u / p % p : ℕ) : ZMod p) = vz (A *ᵥ u) (k - 1) := by
  have hp0 : 0 < p := Nat.pos_of_neZero p
  unfold Pf
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pre_succ, Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt (dg_lt _ _ _), add_zero,
    pre_succ, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _)]
  simp [dg]

/-- The shift cancels in the last-digit residue of a fine-position difference. -/
lemma PfSh_mod [NeZero p] {m k : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (t : Fin m → ZMod p)
    (v w : Fin m → ZMod p) :
    ((Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ v + t) % p : ℕ) : ZMod p) -
        ((Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ w + t) % p : ℕ) : ZMod p) =
      ((Pf k A v % p : ℕ) : ZMod p) - ((Pf k A w % p : ℕ) : ZMod p) := by
  rw [Pf_mod_gen, Pf_mod_gen, Pf_mod_gen, Pf_mod_gen, one_mulVec, one_mulVec, vz_add, vz_add]
  ring

/-- The shift cancels in the second-to-last-digit residue of a fine-position difference. -/
lemma PfSh_div [NeZero p] {m k : ℕ} (hk : 1 ≤ k) (A : Matrix (Fin m) (Fin m) (ZMod p))
    (t : Fin m → ZMod p) (v w : Fin m → ZMod p) :
    ((Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ v + t) / p % p : ℕ) : ZMod p) -
        ((Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ w + t) / p % p : ℕ) : ZMod p) =
      ((Pf k A v / p % p : ℕ) : ZMod p) - ((Pf k A w / p % p : ℕ) : ZMod p) := by
  rw [Pf_div_gen hk, Pf_div_gen hk, Pf_div_gen hk, Pf_div_gen hk, one_mulVec, one_mulVec, vz_add,
    vz_add]
  ring

/-- Equal shifted fine positions give equal unshifted fine positions. -/
lemma PfSh_inj [NeZero p] {m k : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (t : Fin m → ZMod p)
    (v w : Fin m → ZMod p)
    (h : Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ v + t) =
      Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (A *ᵥ w + t)) :
    Pf k A v = Pf k A w := by
  have hp0 : 0 < p := Nat.pos_of_neZero p
  unfold Pf at h ⊢
  refine pre_congr p _ _ (k + 1) fun j hj => ?_
  have hd := pre_inj_digit p hp0 _ _ (k + 1) (fun i _ => dg_lt _ _ i) (fun i _ => dg_lt _ _ i) h j hj
  have h1 := ZMod.val_injective p hd
  rw [one_mulVec, one_mulVec, vz_add, vz_add] at h1
  unfold dg
  rw [add_right_cancel h1]

end Z3NetKN.Geom

namespace Z3NetS1.Proofs

open Finset Matrix Z3NetKN.Geom

/-! ## `thm:S1`(1) under digital shifts -/

/-- **`prop:shift`, `thm:S1`(1), integer form**: the bound of `S1_sep` holds for every digitally
shifted net. -/
theorem S1_sep_shift_core (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p)
    (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (2 * ((s - 1) * (k + 1) - 1)) ≤
      torusDist2 (p ^ (s * k + (s - 1))) (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  have hkm : k + 1 ≤ s * k + (s - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  have hmk : s * k + (s - 1) - (k + 1) = (s - 1) * (k + 1) - 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e1 : (t + 1) * k = t * k + k := by ring
    have e2 : t * (k + 1) = t * k + t := by ring
    omega
  set I1 : Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p) := 1 with hI1
  set X : Fin s → (Fin (s * k + (s - 1)) → ZMod p) → Fin (s * k + (s - 1)) → ZMod p :=
    fun c u => C c *ᵥ u + τ c with hX
  set a : Fin s → ℤ := fun c => cen (p ^ (k + 1)) ((Pf k I1 (X c v) : ℤ) - Pf k I1 (X c w)) with ha
  have hcast : ∀ c, ((a c : ℤ) : ZMod p) = vz (C c *ᵥ v) k - vz (C c *ᵥ w) k := by
    intro c
    rw [ha]; simp only
    rw [cen_cast_mod (k + 1) _ _ (by omega), hX, hI1, PfSh_mod, Pf_mod_gen, Pf_mod_gen]
  have hfull : ∀ d : ℕ, ∀ hd : d + 1 < s, ((a ⟨d, by omega⟩ : ℤ) : ZMod p) =
      vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k) := by
    intro d hd
    have hdep : k < depth s k ⟨d, by omega⟩ := by unfold depth; rw [if_pos hd]; omega
    rw [hcast, coarse_digit hC v _ k hdep, coarse_digit hC w _ k hdep]; rfl
  set zc : Fin s := ⟨s - 1, by omega⟩ with hzc
  have hrel : ((a zc : ℤ) : ZMod p) = ∑ d ∈ range (s - 1),
      ((ρ ^ (d + 1) : ℕ) : ZMod p) * (vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k)) := by
    rw [hcast, skel_diff (by omega) hC zc (by simp [hzc]; omega) v w]
  set x : Fin (s - 1) → ℤ := fun i => a ⟨i, by omega⟩ with hx
  have hdiv : (p : ℤ) ∣ a zc - ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hrel, ← Fin.sum_univ_eq_sum_range
      (fun d => ((ρ ^ (d + 1) : ℕ) : ZMod p) * (vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k))),
      sub_eq_zero]
    refine sum_congr rfl fun i _ => ?_
    rw [hx]; simp only
    rw [hfull i (by omega)]; push_cast; ring
  have hne : ¬(x = 0 ∧ a zc = 0) := by
    rintro ⟨hx0, hz0⟩
    have hall : ∀ c : Fin s, a c = 0 := by
      intro c
      by_cases hc : (c : ℕ) + 1 < s
      · have := congrFun hx0 ⟨c, by omega⟩
        simpa [hx] using this
      · have : c = zc := Fin.ext (by simp [hzc]; omega)
        rw [this]; exact hz0
    apply hvw
    have hP : ∀ c, Pf k (C c) v = Pf k (C c) w := fun c =>
      PfSh_inj (C c) (τ c) v w (eq_of_cen_zero _ _ _ (Pf_lt _ _) (Pf_lt _ _) (hall c))
    funext col
    obtain ⟨c, j, hj, hcol⟩ := blocks_cover s k (by omega) col col.isLt
    have hjk : j < k + 1 := lt_of_lt_of_le hj (depth_le s k c)
    have hd := pre_inj_digit p hp0 _ _ (k + 1) (fun i _ => dg_lt _ v i) (fun i _ => dg_lt _ w i)
      (hP c) j hjk
    have h1 : vz (C c *ᵥ v) j = vz (C c *ᵥ w) j := ZMod.val_injective p hd
    rw [coarse_digit hC v c j hj, coarse_digit hC w c j hj, ← hcol] at h1
    simpa [vz, col.isLt] using h1
  obtain ⟨c, hc⟩ : ∃ c, (ρ : ℤ) ≤ |a c| := by
    rcases L2s_min s p ρ (by omega) hρp x (a zc) hdiv hne with h | ⟨i, h⟩
    · exact ⟨zc, h⟩
    · exact ⟨_, h⟩
  have hb : |a c| * ((p ^ (s * k + (s - 1) - (k + 1)) : ℕ) : ℤ) -
      (((p ^ (s * k + (s - 1) - (k + 1)) : ℕ) : ℤ) - 1) ≤
      (Z3NetKN.cres (p ^ (s * k + (s - 1)))
        ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) -
          Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c) : ℤ) := by
    rw [shift_coord, shift_coord]
    exact prefix_bound I1 (X c v) (X c w) (k + 1) hkm
  set f := p ^ (s * k + (s - 1) - (k + 1)) with hf
  set cr := Z3NetKN.cres (p ^ (s * k + (s - 1)))
    ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) -
      Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c)
  have h1 : (((ρ - 1) * f : ℕ) : ℤ) ≤ cr := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ ρ)]
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have := mul_le_mul_of_nonneg_right hc hf0
    linarith
  have h1' : (ρ - 1) * f ≤ cr := by exact_mod_cast h1
  calc (ρ - 1) ^ 2 * p ^ (2 * ((s - 1) * (k + 1) - 1)) = ((ρ - 1) * f) ^ 2 := by
        rw [hf, mul_pow, ← pow_mul, hmk, Nat.mul_comm 2]
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1' 2
    _ ≤ _ := cres_le_torus _ (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w) c

/-- **`prop:shift`, `thm:S1`(1), real form**: `δ ≥ (ρ - 1) p^(-1/s) N^(-1/s)` for every digitally
shifted net. -/
theorem S1_sep_shift_real_core (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
          ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  have hZ := S1_sep_shift_core s p k ρ hs hp hρ hρp C hC τ v w hvw
  unfold torusDist2 at hZ
  set S : ℝ := ∑ c, ((cres (p ^ (s * k + (s - 1))) ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c : ℤ)) : ℝ)) ^ 2
    with hS
  have hR : ((ρ - 1 : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) ≤ S := by
    have := (Nat.cast_le (α := ℝ)).mpr hZ
    push_cast at this
    rw [hS]; exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hm1 : (s * k + (s - 1)) + 1 = s * (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have hrp : (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) = 1 / (p : ℝ) ^ (k + 1) := by
    rw [← Real.mul_rpow hp0.le (by positivity), ← pow_succ', hm1, ← Real.rpow_natCast,
      ← Real.rpow_mul hp0.le, show ((s * (k + 1) : ℕ) : ℝ) * (-(1 / (s : ℝ))) = -((k + 1 : ℕ) : ℝ) by
        push_cast; field_simp, Real.rpow_neg hp0.le, Real.rpow_natCast, one_div]
  have hsum : ∑ c, ((cres (p ^ (s * k + (s - 1))) ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c : ℤ)) : ℝ)
      / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 = S / ((p : ℝ) ^ (s * k + (s - 1))) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum, mul_assoc, hrp]
  apply Real.le_sqrt_of_sq_le
  have hρ1 : ((ρ - 1 : ℕ) : ℝ) = (ρ : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ ρ)]; ring
  rw [← hρ1]
  have hpk : (0 : ℝ) < (p : ℝ) ^ (k + 1) := by positivity
  rw [mul_one_div, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmk : (s * k + (s - 1)) = ((s - 1) * (k + 1) - 1) + (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e1 : (t + 1) * k = t * k + k := by ring
    have e2 : t * (k + 1) = t * k + t := by ring
    have : 1 ≤ t * (k + 1) := by nlinarith
    omega
  have e1 : ((p : ℝ) ^ (s * k + (s - 1))) ^ 2 = (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) * ((p : ℝ) ^ (k + 1)) ^ 2 := by
    rw [hmk, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1]
  have hk2 : (0 : ℝ) ≤ ((p : ℝ) ^ (k + 1)) ^ 2 := by positivity
  calc ((ρ - 1 : ℕ) : ℝ) ^ 2 * ((p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) * ((p : ℝ) ^ (k + 1)) ^ 2)
      = (((ρ - 1 : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1))) * ((p : ℝ) ^ (k + 1)) ^ 2 := by
        ring
    _ ≤ S * ((p : ℝ) ^ (k + 1)) ^ 2 := mul_le_mul_of_nonneg_right hR hk2

end Z3NetS1.Proofs
