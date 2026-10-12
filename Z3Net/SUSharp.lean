/-
Proof module of entry U (stage 6): the first-order sharpness of `a_s` in `thm:U`(2).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsCeil
public import Z3Net.SUThm1
public import Z3Net.SURows
public import Z3Net.SUS6

@[expose] public section

/-!
# Sharpness of `a_s` (`thm:U`, proof, "Sharpness")

`sharp_core` is the counting step of `cor:ceils`(i) (`ObsCeil.ceil_core`) for a coordinate `a`
whose own block satisfies (H2) at level `k-1` (its offset rows below row `0` vanish there): then
the own-axis step `e_a` from a cell with `n_a = 0` and first offset digit `q - 1` moves coordinate
`a` by exactly `q^(sk-k-1) μ` integer units (`μ` the value of the diagonal entry), with no jitter.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep

noncomputable section

namespace USharp

variable {s q k : ℕ} [NeZero q]

theorem sharp_core (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (hμ : 1 ≤ (Z3NetF.ent (Φ a a) 0 (k - 1)).val)
    (hH2 : ∀ r, 1 ≤ r → Z3NetF.ent (Φ a a) r (k - 1) = 0) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (Z3NetF.gfPoint q k Φ w a : ℤ) - Z3NetF.gfPoint q k Φ v a =
          (q : ℤ) ^ (s * k - k - 1) * (Z3NetF.ent (Φ a a) 0 (k - 1)).val ∧
      ∀ u, u ≠ a → ∃ Δ : ℤ, |Δ| < (q : ℤ) ^ (s * k - k - 1) ∧
        (Z3NetF.gfPoint q k Φ w u : ℤ) - Z3NetF.gfPoint q k Φ v u =
          (q : ℤ) ^ (s * k - k - 1) * Z3NetF.Mt Φ u a + Δ := by
  classical
  have hk0 : 0 < k := by omega
  have hsk : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hC
  have hunit := ObsCeil.unit_of_net C hnet
  obtain ⟨v, hvA, hvB⟩ := exists_good C k hunit
    (fun c => if c = a then s * k - k - 1 else 0)
    (fun _ j => if j < k then {0} else if j = k then {-1} else univ)
    (fun c j _ => by split_ifs <;> simp)
    (univ.erase a)
    (by obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ a := by
          by_contra h; push Not at h
          have : Fintype.card (Fin s) ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => by
            rw [h x, h y]
          simp at this; omega
        exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩)
    (fun u hu => by simp [(mem_erase.mp hu).1])
    (by rw [Finset.sum_ite_eq']; simp only [mem_univ, if_true]; omega)
    (fun u => univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x)
    (by
      calc ∑ u ∈ univ.erase a, (univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x).card
          ≤ ∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs :=
            Finset.sum_le_sum fun u _ => card_wrap_le _
        _ < q := by
          have : ((∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs : ℕ) : ℤ) =
              ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| := by
            rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun u _ => Int.natCast_natAbs _
          omega)
  have hvA' : ∀ j < s * k - k - 1, dig (C a) v j ∈
      (if j < k then ({0} : Finset (ZMod q)) else if j = k then {-1} else univ) := by
    intro j hj
    have := hvA a j (by simp only [if_pos rfl]; exact hj)
    exact this
  have hcell0 : ∀ i (hi : i < k), v (Z3NetU.Proofs.ix k a ⟨i, hi⟩) = 0 := by
    intro i hi
    have := hvA' i (by omega)
    rw [if_pos hi, mem_singleton, dig_cell Φ a v i hi] at this
    exact this
  have hd0 : dig (C a) v k = -1 := by
    have := hvA' k (by omega)
    rwa [if_neg (by omega), if_pos rfl, mem_singleton] at this
  have hgood : ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C u) v k) := by
    intro u hu
    have := hvB u (mem_erase.mpr ⟨hu, mem_univ _⟩)
    simpa using this
  -- the neighbour
  set e : Fin s → ZMod q := Pi.single a 1 with he
  set w := v + stepVec hk0 e with hw
  have hstep : ∀ c (r : ℕ), r < s * k - k →
      dig (C c) w (k + r) = dig (C c) v (k + r) + Z3NetF.ent (Φ c a) r (k - 1) := by
    intro c r hr
    have h0 := dig_step_off Φ hk0 e c r hr
    rw [hw, dig_add, h0]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp [he]
    · intro d _ hd; simp [he, hd]
    · simp
  have hvw : v ≠ w := by
    intro h
    have h1 := congrFun h (Z3NetU.Proofs.ix k a ⟨k - 1, by omega⟩)
    rw [hw, Pi.add_apply, stepVec_apply, if_pos rfl] at h1
    simp only [he, Pi.single_eq_same] at h1
    exact one_ne_zero (by linear_combination -h1)
  refine ⟨v, w, hvw, ?_, ?_⟩
  · -- the moving coordinate `a`: exact displacement
    have hX := X_eq Φ (by omega) v a
    have hY := X_eq Φ (by omega) w a
    have hcl := cellN_step hk0 v e a
    rw [hcell0 (k - 1) (by omega)] at hcl
    simp only [he, Pi.single_eq_same, zero_add, ZMod.val_zero, ZMod.val_one] at hcl
    set μ := Z3NetF.ent (Φ a a) 0 (k - 1)
    have hμl := ZMod.val_lt μ
    have ho0w : ((dig (C a) w k).val : ℤ) = μ.val - 1 := by
      have := hstep a 0 (by omega)
      rw [add_zero] at this
      rw [this, hd0]
      have : (-1 : ZMod q) + μ = (-1 : ZMod q) + (((μ.val : ℤ)) : ZMod q) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, val_wrap_up]
      · rw [val_m1]; push_cast; omega
      · rw [val_m1]; push_cast; omega
      · rw [val_m1]; push_cast; omega
    have ho0v : ((dig (C a) v k).val : ℤ) = q - 1 := by
      rw [hd0, val_m1]; push_cast; omega
    -- equal tails, by (H2)
    have htl : tl Φ w a = tl Φ v a := by
      unfold tl TS
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      have := hstep a (j - k) (by omega)
      rw [show k + (j - k) = j by omega, hH2 (j - k) (by omega), add_zero] at this
      dsimp only
      rw [this]
    rw [hX, hY, htl]
    have hG : (q : ℤ) ^ (s * k - k) = (q : ℤ) ^ (s * k - k - 1) * q := by
      rw [← pow_succ]; congr 1; omega
    rw [hG, ho0w, ho0v]
    linear_combination (q : ℤ) ^ (s * k - k - 1) * (q : ℤ) * hcl
  · -- the transverse coordinates
    intro u hu
    have hX := X_eq Φ (by omega) v u
    have hY := X_eq Φ (by omega) w u
    have hcl := cellN_step hk0 v e u
    simp only [he, Pi.single_eq_of_ne hu, add_zero, sub_self] at hcl
    have hnw := hgood u hu
    unfold NoWrap at hnw
    have hMt : ((Z3NetF.Mt Φ u a : ℤ) : ZMod q) = Z3NetF.ent (Φ u a) 0 (k - 1) :=
      ZMod.coe_valMinAbs _
    rw [hMt] at hnw
    have ho0 : ((dig (C u) w k).val : ℤ) = (dig (C u) v k).val + Z3NetF.Mt Φ u a := by
      have := hstep u 0 (by omega)
      rw [add_zero] at this
      rw [this]; exact hnw
    have htv := tl_lt Φ (by omega) v u
    have htw := tl_lt Φ (by omega) w u
    refine ⟨(tl Φ w u : ℤ) - tl Φ v u, ?_, ?_⟩
    · rw [abs_lt]
      have h1 : (tl Φ v u : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htv
      have h2 : (tl Φ w u : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htw
      have : (tl Φ w u : ℤ) ≥ 0 := by positivity
      have : (tl Φ v u : ℤ) ≥ 0 := by positivity
      constructor <;> linarith
    · rw [hX, hY, ho0]
      linear_combination (q : ℤ) ^ (s * k - k) * hcl

end USharp

end

end Z3NetF.Proofs

namespace Z3NetU.Proofs

open Matrix Finset

noncomputable section

namespace USharp

lemma Foff0 (s : ℕ) (hs : 3 ≤ s) (c d : Fin s) : Foff s 0 c d =
    if (c : ℕ) = 0 then 1 else if (d : ℕ) = 0 then (Lcst s : ℤ) else (Lcst s : ℤ) / ((c : ℤ) - d) := by
  unfold Foff
  rw [if_neg (by omega)]
  simp

lemma Foff_abs_le (s : ℕ) (hs : 3 ≤ s) (u a : Fin s) :
    (Foff s 0 u a).natAbs ≤ Lcst s := by
  have hL := Lcst_pos s
  rw [Foff0 s hs]
  split_ifs
  · simp; omega
  · simp
  · exact (Int.natAbs_ediv_le_natAbs _ _).trans (by simp)

/-- Column `a` against row `a`: `|F_0[u][a]| ≤ |F_0[a][u]|` for finite `a`. -/
lemma Foff_col_le_row (s : ℕ) (hs : 3 ≤ s) (u a : Fin s) (ha : (a : ℕ) ≠ 0) :
    (Foff s 0 u a).natAbs ≤ (Foff s 0 a u).natAbs := by
  have hL := Lcst_pos s
  rw [Foff0 s hs, Foff0 s hs, if_neg ha]
  by_cases hu : (u : ℕ) = 0
  · simp [hu]; omega
  · rw [if_neg hu, if_neg ha, if_neg hu]
    have : (a : ℤ) - u = -((u : ℤ) - a) := by ring
    rw [this, Int.ediv_neg, Int.natAbs_neg]

lemma Foff_row_ge_one (s : ℕ) (hs : 3 ≤ s) (a d : Fin s) (had : d ≠ a) (ha : (a : ℕ) ≠ 0) :
    1 ≤ (Foff s 0 a d).natAbs := by
  have hL := Lcst_pos s
  rw [Foff0 s hs, if_neg ha]
  by_cases hd : (d : ℕ) = 0
  · simp [hd]; omega
  · rw [if_neg hd]
    obtain ⟨y, hy⟩ := lcm_dvd a d ha hd (Ne.symm had) 0 (by omega)
    rw [zero_add, pow_one] at hy
    have hne : (a : ℤ) - d ≠ 0 := by
      intro h; apply had; apply Fin.ext; omega
    rw [hy, Int.mul_ediv_cancel_left _ hne]
    have : y ≠ 0 := by
      rintro rfl
      have : (Lcst s : ℤ) = 0 := by rw [hy]; ring
      omega
    omega

lemma Msum0 (s : ℕ) (c d : Fin s) : Msum s 0 c d = Foff s 0 c d := by
  simp [Msum]

lemma Foff_le_sup (s : ℕ) (hs : 3 ≤ s) (c d : Fin s) :
    (Foff s 0 c d).natAbs ≤ (range (s - 1)).sup fun j => (Msum s j c d).natAbs := by
  rw [← Msum0]
  exact Finset.le_sup (f := fun j => (Msum s j c d).natAbs) (mem_range.mpr (by omega))

lemma col_le_acoef (s : ℕ) (hs : 3 ≤ s) (a : Fin s) (ha : (a : ℕ) ≠ 0) :
    ∑ u ∈ univ.erase a, (Foff s 0 u a).natAbs ≤ acoef s a := by
  unfold acoef
  rw [show univ.filter (fun d : Fin s => d ≠ a) = univ.erase a by ext; simp]
  exact Finset.sum_le_sum fun u hu =>
    (Foff_col_le_row s hs u a ha).trans (Foff_le_sup s hs a u)

lemma acoef_inf_le (s : ℕ) (hs : 3 ≤ s) : acoef s ⟨0, by omega⟩ ≤ s - 1 := by
  unfold acoef
  have h1 : ∀ d ∈ univ.filter (fun d : Fin s => d ≠ ⟨0, by omega⟩),
      ((range (s - 1)).sup fun j => (Msum s j ⟨0, by omega⟩ d).natAbs) ≤ 1 := by
    intro d _
    refine Finset.sup_le fun j _ => ?_
    unfold Msum
    rw [Finset.sum_eq_single 0]
    · simp [Foff]; split_ifs <;> simp
    · intro t _ ht; simp [Foff, ht]
    · simp
  calc _ ≤ ∑ _d ∈ univ.filter (fun d : Fin s => d ≠ ⟨0, by omega⟩), 1 := Finset.sum_le_sum h1
    _ = s - 1 := by
      rw [show univ.filter (fun d : Fin s => d ≠ ⟨0, by omega⟩) = univ.erase ⟨0, by omega⟩ by
        ext; simp]
      simp

lemma acoef_one_ge (s : ℕ) (hs : 3 ≤ s) : s - 1 ≤ acoef s ⟨1, by omega⟩ := by
  unfold acoef
  rw [show univ.filter (fun d : Fin s => d ≠ ⟨1, by omega⟩) = univ.erase ⟨1, by omega⟩ by
    ext; simp]
  calc s - 1 = ∑ _d ∈ univ.erase (⟨1, by omega⟩ : Fin s), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun d hd =>
      (Foff_row_ge_one s hs ⟨1, by omega⟩ d (mem_erase.mp hd).1 (by simp)).trans
        (Foff_le_sup s hs _ d)

/-- `a_s` is attained at a finite coordinate. -/
lemma exists_finite_max (s : ℕ) (hs : 3 ≤ s) :
    ∃ a : Fin s, (a : ℕ) ≠ 0 ∧ acoef s a = aU s := by
  have hne : (univ.filter (fun c : Fin s => (c : ℕ) ≠ 0)).Nonempty :=
    ⟨⟨1, by omega⟩, by simp⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image _ (acoef s) hne
  rw [mem_filter] at ha
  refine ⟨a, ha.2, le_antisymm (Finset.le_sup (f := acoef s) (mem_univ a)) ?_⟩
  refine Finset.sup_le fun c _ => ?_
  by_cases hc : (c : ℕ) = 0
  · have : c = ⟨0, by omega⟩ := Fin.ext hc
    rw [this]
    exact (acoef_inf_le s hs).trans ((acoef_one_ge s hs).trans
      (hmax _ (by simp)))
  · exact hmax c (by simp [hc])

lemma valMinAbs_eq (q : ℕ) [NeZero q] (y : ℤ) (hy : 2 * |y| < q) :
    ((y : ZMod q)).valMinAbs = y := by
  rw [ZMod.valMinAbs_spec]
  have h1 := neg_abs_le y
  have h2 := le_abs_self y
  refine ⟨rfl, ?_, ?_⟩ <;> omega

lemma sq_lt_of_abs {D G q t : ℝ} (hG : 0 < G) (hq : 0 < q) (ht : 0 ≤ t) (h : |D| < G * t) :
    (D / (G * q)) ^ 2 < (t / q) ^ 2 := by
  rw [div_pow, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 : D ^ 2 < (G * t) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
  calc D ^ 2 * q ^ 2 < (G * t) ^ 2 * q ^ 2 := by gcongr
    _ = t ^ 2 * (G * q) ^ 2 := by ring

end USharp

open USharp in
/-- **Sharpness of `a_s`** (`thm:U`(2)): two distinct points of `𝒫^s_{k,q}` at squared Euclidean and
toroidal distance, in cell units, `< (1 - a_s/q)² + (s-1)(L_s+1)²/q²`. -/
theorem U_sharp (s q k : ℕ) (hs : 3 ≤ s) (hq : Admissible s q) (hqa : 5 * aU s + 4 ≤ q)
    (hk : 2 ≤ k) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((Upoint s q k v c : ℝ) - Upoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aU s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aU s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  classical
  have : NeZero q := ⟨by have := hq.1; omega⟩
  have hsk : k ≤ s * k - k := by
    have : 2 * k ≤ s * k := Nat.mul_le_mul_right k (by omega); omega
  obtain ⟨a, ha0, haU⟩ := exists_finite_max s hs
  have hL1 := Lcst_pos s
  have hLa := U_aLower s hs
  set Φ := UPhi (ZMod q) (fun i => ((i : ℕ) : ZMod q)⁻¹) k with hΦ
  have hent0 : ∀ c d, Z3NetF.ent (Φ c d) 0 (k - 1) = ((Fdes s 0 c d : ℤ) : ZMod q) := by
    intro c d
    unfold Z3NetF.ent
    rw [dif_pos ⟨by omega, by omega⟩]
    have := row0 hs (ivOK_zmod s q hq) k c d ⟨0, by omega⟩ rfl ⟨k - 1, by omega⟩
    simp only at this
    rw [hΦ, this, Nat.sub_self]
  have hH2 : ∀ r, 1 ≤ r → Z3NetF.ent (Φ a a) r (k - 1) = 0 := by
    intro r hr
    unfold Z3NetF.ent
    split_ifs with h
    · have : r ≠ 0 := by omega
      simp [hΦ, UPhi, this]
    · rfl
  have hFoff : ∀ u, u ≠ a → Fdes s 0 u a = Foff s 0 u a := by
    intro u hu; simp [Fdes, hu]
  have hMt : ∀ u, u ≠ a → Z3NetF.Mt Φ u a = Foff s 0 u a := by
    intro u hu
    unfold Z3NetF.Mt
    rw [hent0, hFoff u hu]
    apply valMinAbs_eq
    have := Foff_abs_le s hs u a
    have h2 : |Foff s 0 u a| ≤ (Lcst s : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    have : (Lcst s : ℤ) ≤ aU s := by exact_mod_cast hLa
    have : (5 * aU s + 4 : ℤ) ≤ q := by exact_mod_cast hqa
    omega
  have hcolN := col_le_acoef s hs a ha0
  have hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q := by
    rw [Finset.sum_congr rfl fun u hu => by rw [hMt u (mem_erase.mp hu).1]]
    have : ∑ u ∈ univ.erase a, |Foff s 0 u a| = ((∑ u ∈ univ.erase a, (Foff s 0 u a).natAbs : ℕ) : ℤ) := by
      rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun u _ => (Int.natCast_natAbs _).symm
    rw [this]
    have : ∑ u ∈ univ.erase a, (Foff s 0 u a).natAbs < q := by omega
    exact_mod_cast this
  have hμval : (Z3NetF.ent (Φ a a) 0 (k - 1)).val = q - aU s := by
    rw [hent0]
    have hFd : Fdes s 0 a a = -((aU s : ℕ) : ℤ) := by simp [Fdes, haU]
    rw [hFd, Int.cast_neg, Int.cast_natCast, ZMod.neg_val, if_neg, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hμ : 1 ≤ (Z3NetF.ent (Φ a a) 0 (k - 1)).val := by rw [hμval]; omega
  have hpt : Z3NetF.gfPoint q k Φ = Upoint s q k := by
    unfold Z3NetF.gfPoint Upoint UGen
    rw [Z3NetF.Proofs.graphGenK_const]
    rfl
  have hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ) := by
    rw [hpt]; exact U_net s q k hs hq (by omega)
  obtain ⟨v, w, hvw, hXa, hXu⟩ :=
    Z3NetF.Proofs.USharp.sharp_core hs (by omega) hk Φ hnet a hcol hμ hH2
  rw [hpt, hμval] at hXa
  refine ⟨v, w, hvw, ?_⟩
  set X := Upoint s q k with hX
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set G : ℝ := (q : ℝ) ^ (s * k - k - 1) with hG
  have hGpos : 0 < G := by positivity
  have hQ : (q : ℝ) ^ (s * k) = G * q * (q : ℝ) ^ k := by
    rw [hG, mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
  have hk2 : ((q : ℝ) ^ k) ^ 2 = (q : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
  -- per-coordinate bounds in cell units
  have key : ∀ c, (q : ℝ) ^ (2 * k) * (((X v c : ℝ) - X w c) / (q : ℝ) ^ (s * k)) ^ 2 =
      (((X v c : ℝ) - X w c) / (G * q)) ^ 2 := by
    intro c
    rw [hQ, ← hk2]
    field_simp
  have hA : (((X v a : ℝ) - X w a) / (G * q)) ^ 2 = (1 - (aU s : ℝ) / q) ^ 2 := by
    have : ((X v a : ℝ) - X w a) = -(G * ((q : ℝ) - aU s)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXa
      push_cast [Nat.cast_sub (show aU s ≤ q by omega)] at this
      rw [hG]; linarith
    rw [this]
    field_simp
  have hU : ∀ u, u ≠ a → (((X v u : ℝ) - X w u) / (G * q)) ^ 2 < (((Lcst s : ℝ) + 1) / q) ^ 2 := by
    intro u hu
    obtain ⟨Δ, hΔ, hXΔ⟩ := hXu u hu
    rw [hpt] at hXΔ
    apply sq_lt_of_abs hGpos hq0 (by positivity)
    have e1 : ((X v u : ℝ) - X w u) = -(G * (Z3NetF.Mt Φ u a : ℝ) + Δ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXΔ
      push_cast at this
      rw [hG]; linarith
    rw [e1, abs_neg]
    have hF : |(Z3NetF.Mt Φ u a : ℝ)| ≤ Lcst s := by
      rw [hMt u hu]
      have := Foff_abs_le s hs u a
      have h2 : |Foff s 0 u a| ≤ (Lcst s : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast this
      exact_mod_cast h2
    have hΔ' : |(Δ : ℝ)| < G := by rw [hG]; exact_mod_cast hΔ
    calc |G * (Z3NetF.Mt Φ u a : ℝ) + Δ| ≤ G * |(Z3NetF.Mt Φ u a : ℝ)| + |(Δ : ℝ)| := by
          rw [← abs_of_pos hGpos, ← abs_mul, abs_of_pos hGpos]; exact abs_add_le _ _
      _ < G * Lcst s + G := by nlinarith
      _ = G * ((Lcst s : ℝ) + 1) := by ring
  have hsum : (q : ℝ) ^ (2 * k) * ∑ c, (((X v c : ℝ) - X w c) / (q : ℝ) ^ (s * k)) ^ 2 <
      (1 - (aU s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => key c, ← Finset.add_sum_erase _ _ (mem_univ a),
      hA]
    have hne : (univ.erase a).Nonempty := by
      obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ a := ⟨if (a : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
        split_ifs with h <;> intro h' <;> simp [Fin.ext_iff] at h' <;> omega⟩
      exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun u hu => hU u (mem_erase.mp hu).1
    have hcard : ∑ _u ∈ univ.erase a, (((Lcst s : ℝ) + 1) / q) ^ 2 =
        ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega)]
      push_cast; ring
    linarith
  refine ⟨hsum, lt_of_le_of_lt ?_ hsum⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun c _ => ?_
  rw [div_pow, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := Z3NetF.Proofs.ObsCount.cres_le_abs (q ^ (s * k)) (pow_pos (Nat.pos_of_neZero q) _)
    ((X v c : ℤ) - (X w c : ℤ))
  have h0 : (0 : ℤ) ≤ (cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) := by positivity
  have h1' : ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤ |((X v c : ℝ) - X w c)| := by
    have : ((Z3NetF.cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤
        (((|(X v c : ℤ) - (X w c : ℤ)|) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    exact this
  have h0' : (0 : ℝ) ≤ ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) := by positivity
  calc ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) ^ 2
      ≤ |((X v c : ℝ) - X w c)| ^ 2 := by
        apply pow_le_pow_left₀ h0'
        exact_mod_cast h1'
    _ = ((X v c : ℝ) - X w c) ^ 2 := sq_abs _

/-- **Sharpness of `a_s`, real form**: `δ N^(1/s) < 1 - a_s/q + (s-1)(L_s+1)²/q²` (toroidal, and
the same pair for the Euclidean distance). -/
theorem U_sharp_real (s q k : ℕ) (hs : 3 ≤ s) (hq : Admissible s q) (hqa : 5 * aU s + 4 ≤ q)
    (hk : 2 ≤ k) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aU s : ℝ) / q + ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  obtain ⟨v, w, hvw, -, hT⟩ := U_sharp s q k hs hq hqa hk
  refine ⟨v, w, hvw, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := hq.1; omega)
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hrp : ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((s * k : ℕ) : ℝ) * (-(1 / (s : ℝ))) =
      -(k : ℝ) by push_cast; field_simp, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]
  rw [hrp]
  set S := ∑ c, ((cres (q ^ (s * k)) ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2 with hS
  set α : ℝ := 1 - (aU s : ℝ) / q
  set β : ℝ := ((s : ℝ) - 1) * ((Lcst s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hα : (4 : ℝ) / 5 ≤ α := by
    have : (5 * aU s + 4 : ℝ) ≤ q := by exact_mod_cast hqa
    have : (aU s : ℝ) / q ≤ 1 / 5 := by
      rw [div_le_iff₀ hq0]; linarith
    linarith
  have hβ : 0 ≤ β := by
    have : (1 : ℝ) ≤ s - 1 := by
      have : (3 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    positivity
  have hS0 : 0 ≤ S := by positivity
  -- `q^(2k) S < α² + β ≤ (α + β)²`
  have h1 : (q : ℝ) ^ (2 * k) * S < (α + β) ^ 2 := by
    have : α ^ 2 + β ≤ (α + β) ^ 2 := by nlinarith
    linarith
  rw [Real.sqrt_lt' (by positivity)]
  have hk2 : (q : ℝ) ^ (2 * k) = ((q : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hk2] at h1
  rw [mul_one_div, div_pow, lt_div_iff₀ (by positivity)]
  linarith

end

end Z3NetU.Proofs
