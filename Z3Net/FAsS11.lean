/-
Proof module (stage 11, entry F): `prop:4DK2`, the covering bound of (1) and part (3).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FMain
public import Z3Net.ObsCeil

@[expose] public section

/-!
# Stage 11 additions to entry F: `prop:4DK2` (1) covering and (3)

* `As_covering` (`prop:4DK2`(1), `h ≤ 2 N^(-1/4)`): the box `(k, k, k, k)` of `As_net` gives one
  point in every cell, as in entry U's `U_covering`;
* `As_upper` (`prop:4DK2`(3), first sentence): `cor:ceils`(i) (entry Obs, `ObsCeil.ceils_neg`)
  applied to the graph form of `𝒫^{A♯}_{k,q}` with `a = 0` (the place `0`): by (H1) the geometric
  layer is `F_0` of `A♯` (`|F_0| ≤ 2 < q/2`), so `M̃_aa = -2` and the column `(-1, 1, -1)`;
* `As_two_sided` (`prop:4DK2`(3), second sentence): `As_sep` with `c♯(q) = 1 - 2/q` (`q ≥ 23`), the
  Euclidean distance `≥` the toroidal one, and `As_upper` with `q^(1-k) ≤ q^(-2)` (`k ≥ 3`).
-/

namespace Z3NetF.Proofs.AsS11

open Finset Z3NetF Z3NetF.Proofs.As

noncomputable section

/-- The blocks of the graph form of `𝒫^{A♯}_{k,q}`. -/
def PhiA (q k : ℕ) (ψ : R10 →+* ZMod q) (β : Fin 4 → ℕ → ℕ → R10) :
    Fin 4 → Fin 4 → Matrix (Fin (4 * k - k)) (Fin k) (ZMod q) :=
  fun c d => (PPhi k (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
    (fun c => (lamAs c : R10)) (fun d n' n => (UrAs d n' n : R10)) β c d).map ψ

lemma gen_eq {q : ℕ} (ψ : R10 →+* ZMod q) (k : ℕ) (β : Fin 4 → ℕ → ℕ → R10) :
    digPoint q (4 * k) (fun c => (PAs k β c).map ψ) = gfPoint q k (PhiA q k ψ β) := by
  have hgen : (fun c => (PAs k β c).map ψ) =
      graphGenK (m := 4 * k) (fun _ => k) (PhiA q k ψ β) := by
    funext c
    exact graphGenK_map ψ (m := 4 * k) (fun _ => k) _ c
  unfold gfPoint
  rw [hgen]

/-- (H1) at the level `k - 1` of row `0`: the entry is `F_0[c][d]` (diagonal included). -/
lemma PhiA_last {q : ℕ} (ψ : R10 →+* ZMod q) (k : ℕ) (hk : 2 ≤ k) (β : Fin 4 → ℕ → ℕ → R10)
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
      (fun c => (lamAs c : R10)) β) (c d : Fin 4) :
    ent (PhiA q k ψ β c d) 0 (k - 1) = ((FAs 0 c d : ℤ) : ZMod q) := by
  obtain ⟨hx, hres⟩ := As_residual_core
  have h0 : 0 < 4 * k - k := by omega
  have hk1 : k - 1 < k := by omega
  have he : ent (PhiA q k ψ β c d) 0 (k - 1) = PhiA q k ψ β c d ⟨0, h0⟩ ⟨k - 1, hk1⟩ := by
    unfold ent; rw [dif_pos ⟨h0, hk1⟩]
  rw [he]
  have hj : k - 1 - ((⟨k - 1, hk1⟩ : Fin k) : ℕ) = 0 := by simp
  simp only [PhiA, Matrix.map_apply]
  by_cases hcd : c = d
  · subst hcd
    have e1 : PPhi k (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
        (fun c => (lamAs c : R10)) (fun d n' n => (UrAs d n' n : R10)) β c c ⟨0, h0⟩ ⟨k - 1, hk1⟩ =
        if ((⟨0, h0⟩ : Fin (4 * k - k)) : ℕ) = 0 ∧ k - 1 - ((⟨k - 1, hk1⟩ : Fin k) : ℕ) < 4 - 1 then
          (FAs (k - 1 - ((⟨k - 1, hk1⟩ : Fin k) : ℕ)) c c : R10) else 0 := by
      simp [PPhi]
    rw [e1, if_pos ⟨rfl, by rw [hj]; norm_num⟩, hj, map_intCast]
  · have e1 : PPhi k (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
        (fun c => (lamAs c : R10)) (fun d n' n => (UrAs d n' n : R10)) β c d =
        Lmat k (2 : Fin 4) (fun c => (xAs c : R10)) (fun c => (lamAs c : R10)) c *
          frameGraph R10 k (2 : Fin 4) (fun c => (xAs c : R10)) c d *
          Ugauge k (2 : Fin 4) (fun c => (xAs c : R10)) (fun d n' n => (UrAs d n' n : R10)) β d := by
      simp [PPhi, hcd]
    rw [e1, Gs_row0_core k (2 : Fin 4) _ _ _ _ β hx hres hβ c d hcd ⟨0, h0⟩ rfl ⟨k - 1, hk1⟩,
      if_pos (by rw [hj]; norm_num), hj, map_intCast]

lemma FAs0_small (c d : Fin 4) : -2 ≤ FAs 0 c d ∧ FAs 0 c d ≤ 2 := by
  fin_cases c <;> fin_cases d <;> simp [FAs]

/-- The geometric layer of `𝒫^{A♯}_{k,q}` is `F_0` of `A♯` (`q ≥ 5`). -/
lemma Mt_PhiA {q : ℕ} [NeZero q] (hq : 5 ≤ q) (ψ : R10 →+* ZMod q) (k : ℕ) (hk : 2 ≤ k)
    (β : Fin 4 → ℕ → ℕ → R10)
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
      (fun c => (lamAs c : R10)) β) (c d : Fin 4) :
    Mt (PhiA q k ψ β) c d = FAs 0 c d := by
  unfold Mt
  rw [PhiA_last ψ k hk β hβ c d, ZMod.valMinAbs_spec]
  obtain ⟨h1, h2⟩ := FAs0_small c d
  refine ⟨rfl, ?_, ?_⟩ <;> push_cast <;> omega

lemma covering_core {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) (k : ℕ)
    (β : Fin 4 → ℕ → ℕ → R10) (x : Fin 4 → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤
        4 / ((q : ℝ) ^ k) ^ 2 := by
  set X := digPoint q (4 * k) (fun c => (PAs k β c).map ψ) with hXdef
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hG : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  let a : Fin 4 → ℕ := fun c => min ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1)
  have ha : ∀ c, a c < q ^ k := fun c => lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hnet := As_net_core ψ k β
  obtain ⟨v, hv, -⟩ := hnet (fun _ => k) (by simp) a ha
  refine ⟨v, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hGpos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqpos k
  have key : ∀ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 1 / ((q : ℝ) ^ k) ^ 2 := by
    intro c
    set Xc := X v c
    have hdiv : Xc / q ^ (4 * k - k) = a c := hv c
    set y := x c * (q : ℝ) ^ k
    set z := (Xc : ℝ) / (q : ℝ) ^ (4 * k - k)
    have hy0 : 0 ≤ y := mul_nonneg (hx c).1 hGpos.le
    have hay : (a c : ℝ) ≤ y := by
      have : a c ≤ ⌊y⌋₊ := min_le_left _ _
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0)
    have hya : y ≤ (a c : ℝ) + 1 := by
      by_cases hfl : ⌊y⌋₊ ≤ q ^ k - 1
      · have : a c = ⌊y⌋₊ := min_eq_left hfl
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · have hfl' : ¬ ⌊x c * (q : ℝ) ^ k⌋₊ ≤ q ^ k - 1 := hfl
        have : a c = q ^ k - 1 := min_eq_right (by omega)
        rw [this, Nat.cast_sub hG]
        have : y ≤ (q : ℝ) ^ k := by
          have := mul_le_mul_of_nonneg_right (hx c).2 hGpos.le
          simpa [y] using this
        push_cast; linarith
    have hQ : (0 : ℝ) < (q : ℝ) ^ (4 * k - k) := pow_pos hqpos _
    have hXeq : (Xc : ℝ) = (q : ℝ) ^ (4 * k - k) * (a c) + (Xc % q ^ (4 * k - k) : ℕ) := by
      have := Nat.div_add_mod Xc (q ^ (4 * k - k))
      rw [hdiv] at this
      exact_mod_cast this.symm
    have hrem : ((Xc % q ^ (4 * k - k) : ℕ) : ℝ) < (q : ℝ) ^ (4 * k - k) := by
      exact_mod_cast Nat.mod_lt _ (pow_pos (by omega) _)
    have haz : (a c : ℝ) ≤ z := by
      rw [le_div_iff₀ hQ, hXeq]
      have : (0 : ℝ) ≤ ((Xc % q ^ (4 * k - k) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hza : z ≤ (a c : ℝ) + 1 := by
      rw [div_le_iff₀ hQ, hXeq]
      nlinarith
    have hxz : x c - (Xc : ℝ) / (q : ℝ) ^ (4 * k) = (y - z) / (q : ℝ) ^ k := by
      have hpw : (q : ℝ) ^ (4 * k) = (q : ℝ) ^ (4 * k - k) * (q : ℝ) ^ k := by
        rw [← pow_add]; congr 1; omega
      simp only [y, z]
      rw [hpw]
      field_simp
    rw [hxz, div_pow, one_div, div_eq_mul_inv]
    have hsq : (y - z) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    calc (y - z) ^ 2 * (((q : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 * (((q : ℝ) ^ k) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (by positivity))
      _ = (((q : ℝ) ^ k) ^ 2)⁻¹ := by rw [one_mul]
  calc ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2
      ≤ ∑ _c : Fin 4, 1 / ((q : ℝ) ^ k) ^ 2 := Finset.sum_le_sum fun c _ => key c
    _ = 4 / ((q : ℝ) ^ k) ^ 2 := by simp; ring

lemma upper_core {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) (hq : 7 ≤ q) (k : ℕ) (hk : 2 ≤ k)
    (β : Fin 4 → ℕ → ℕ → R10)
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
      (fun c => (lamAs c : R10)) β) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2 <
        (1 - 2 / (q : ℝ) + 1 / (q : ℝ) ^ (k - 1)) ^ 2 + 12 / (q : ℝ) ^ 2 ∧
      (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) <
        (1 - 2 / (q : ℝ) + 1 / (q : ℝ) ^ (k - 1)) ^ 2 + 12 / (q : ℝ) ^ 2 := by
  have hM := Mt_PhiA (by omega) ψ k hk β hβ
  have hnet : IsNet0 4 q (4 * k) (gfPoint q k (PhiA q k ψ β)) := by
    rw [← gen_eq]; exact As_net_core ψ k β
  have hsum : ∀ f : Fin 4 → ℤ, ∑ u ∈ univ.erase (0 : Fin 4), f u = f 1 + f 2 + f 3 := by
    intro f
    rw [Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_four]; ring
  have hsumR : ∀ f : Fin 4 → ℝ, ∑ u ∈ univ.erase (0 : Fin 4), f u = f 1 + f 2 + f 3 := by
    intro f
    rw [Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_four]; ring
  have hcol : ∑ u ∈ univ.erase (0 : Fin 4), |Mt (PhiA q k ψ β) u 0| < q := by
    rw [hsum]; simp only [hM]; simp [FAs]; omega
  have ha : Mt (PhiA q k ψ β) 0 0 ≤ -1 := by rw [hM]; simp [FAs]
  have hP := ObsCeil.ceils_neg (s := 4) (by norm_num) (by omega) hk (PhiA q k ψ β) hnet 0 hcol ha
  rw [hsumR] at hP
  simp only [hM] at hP
  obtain ⟨v, w, hvw, h1, h2⟩ := hP
  refine ⟨v, w, hvw, ?_, ?_⟩
  · rw [gen_eq]
    unfold cellDist2 at h1
    refine lt_of_lt_of_eq h1 ?_
    norm_num [FAs]; ring
  · rw [gen_eq]
    refine lt_of_lt_of_eq h2 ?_
    norm_num [FAs]; ring

/-- `cres N u ≤ |u|` (`N > 0`): the toroidal distance is at most the Euclidean one. -/
lemma cres_le_abs (N : ℕ) (hN : 0 < N) (u : ℤ) : (cres N u : ℤ) ≤ |u| := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hm0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have hmN : u % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have hdm := Int.mul_ediv_add_emod u (N : ℤ)
  have ht : (((u % (N : ℤ)).toNat : ℕ) : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg hm0
  have htN : (u % (N : ℤ)).toNat ≤ N := by omega
  unfold cres
  rcases le_or_gt 0 u with hu | hu
  · have hd : 0 ≤ u / (N : ℤ) := Int.ediv_nonneg hu hN'.le
    have : ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) ≤
        (((u % (N : ℤ)).toNat : ℕ) : ℤ) := by exact_mod_cast min_le_left _ _
    rw [abs_of_nonneg hu]
    nlinarith
  · have hd : u / (N : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hu hN'
    have : ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) ≤
        ((N - (u % (N : ℤ)).toNat : ℕ) : ℤ) := by exact_mod_cast min_le_right _ _
    rw [Nat.cast_sub htN, ht] at this
    rw [abs_of_neg hu]
    nlinarith

lemma torus_le_euclid {q m k : ℕ} [NeZero q] (x y : Fin 4 → ℕ) :
    (torusDist2 (q ^ m) x y : ℝ) / (q : ℝ) ^ (2 * (m - k)) ≤
      ∑ c, (((x c : ℝ) - (y c : ℝ)) / (q : ℝ) ^ (m - k)) ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hN : 0 < q ^ m := pow_pos hq m
  have hP : (0 : ℝ) < (q : ℝ) ^ (m - k) := pow_pos (by exact_mod_cast hq) _
  rw [pow_mul', torusDist2]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := cres_le_abs (q ^ m) hN ((x c : ℤ) - (y c : ℤ))
  have h0 : (0 : ℤ) ≤ (cres (q ^ m) ((x c : ℤ) - (y c : ℤ)) : ℤ) := Nat.cast_nonneg _
  have hsq : ((cres (q ^ m) ((x c : ℤ) - (y c : ℤ)) : ℤ)) ^ 2 ≤ ((x c : ℤ) - (y c : ℤ)) ^ 2 := by
    rw [← sq_abs ((x c : ℤ) - (y c : ℤ))]
    exact pow_le_pow_left₀ h0 h 2
  have := (Int.cast_le (R := ℝ)).mpr hsq
  push_cast at this
  exact this

/-- `(1 - 2/q + q^(1-k))² + 12/q² < (1 - 2/q + 8/q²)²` for `q ≥ 23`, `k ≥ 3`. -/
lemma bound_23 {q : ℕ} (hq : 23 ≤ q) (k : ℕ) (hk : 3 ≤ k) :
    (1 - 2 / (q : ℝ) + 1 / (q : ℝ) ^ (k - 1)) ^ 2 + 12 / (q : ℝ) ^ 2 <
      (1 - 2 / (q : ℝ) + 8 / (q : ℝ) ^ 2) ^ 2 := by
  have hqR : (23 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set e : ℝ := 1 / (q : ℝ) with he
  have he0 : 0 < e := by positivity
  have he23 : e ≤ 1 / 23 := by rw [he]; exact one_div_le_one_div_of_le (by norm_num) hqR
  have hx0 : 0 ≤ 1 / (q : ℝ) ^ (k - 1) := by positivity
  have hx : 1 / (q : ℝ) ^ (k - 1) ≤ e ^ 2 := by
    rw [he, one_div_pow]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by linarith) (by omega))
  have e2 : 2 / (q : ℝ) = 2 * e := by rw [he]; ring
  have e12 : 12 / (q : ℝ) ^ 2 = 12 * e ^ 2 := by rw [he]; ring
  have e8 : 8 / (q : ℝ) ^ 2 = 8 * e ^ 2 := by rw [he]; ring
  rw [e2, e12, e8]
  set x := 1 / (q : ℝ) ^ (k - 1)
  have h1 : (1 - 2 * e + x) ^ 2 ≤ (1 - 2 * e + e ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (1 - 2 * e + e ^ 2) ^ 2 + 12 * e ^ 2 < (1 - 2 * e + 8 * e ^ 2) ^ 2 := by
    have hpos : 0 < e ^ 2 * (2 - 28 * e + 63 * e ^ 2) := by
      apply mul_pos (by positivity); nlinarith
    nlinarith
  linarith

lemma two_sided_core {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) (hq : 23 ≤ q) (k : ℕ) (hk : 3 ≤ k)
    (β : Fin 4 → ℕ → ℕ → R10)
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
      (fun c => (lamAs c : R10)) β) :
    (∀ v w : Fin (4 * k) → ZMod q, v ≠ w →
      (1 - 2 / (q : ℝ)) ^ 2 ≤
        (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) ∧
      (1 - 2 / (q : ℝ)) ^ 2 ≤
        ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2) ∧
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2 <
        (1 - 2 / (q : ℝ) + 8 / (q : ℝ) ^ 2) ^ 2 ∧
      (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) <
        (1 - 2 / (q : ℝ) + 8 / (q : ℝ) ^ 2) ^ 2 := by
  have hqR : (23 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hBAs : BAs q = ((q : ℤ) - 2) ^ 2 := by
    unfold BAs
    rw [if_neg (by omega)]
    apply min_eq_left
    have : (23 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith
  refine ⟨fun v w hvw => ?_, ?_⟩
  · have hS := As_sep_core ψ (by omega) k (by omega) β hβ v w hvw
    rw [hBAs] at hS
    have hR := (Int.cast_le (R := ℝ)).mpr hS
    push_cast at hR
    have hT : (1 - 2 / (q : ℝ)) ^ 2 ≤
        (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) := by
      have hP : (0 : ℝ) < (q : ℝ) ^ (2 * (4 * k - k)) := by positivity
      rw [le_div_iff₀ hP]
      have e : (1 - 2 / (q : ℝ)) ^ 2 = ((q : ℝ) - 2) ^ 2 / (q : ℝ) ^ 2 := by field_simp
      rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    exact ⟨hT, le_trans hT (torus_le_euclid (k := k) _ _)⟩
  · obtain ⟨v, w, hvw, h1, h2⟩ := upper_core ψ (by omega) k (by omega) β hβ
    have hB := bound_23 hq k hk
    exact ⟨v, w, hvw, h1.trans hB, h2.trans hB⟩

end

end Z3NetF.Proofs.AsS11

/-! ## Compared statements (same as `ChallengeF.lean`) -/

namespace Z3NetF

open Matrix Finset

/-- **`prop:4DK2` (1)**, covering radius: every cell `∏_i [n_i q^(-k), (n_i+1) q^(-k))` holds a
point (`As_net` with the box `(k, k, k, k)`), so every `x ∈ [0,1]⁴` has a point of
`𝒫^{A♯}_{k,q}` at Euclidean distance at most `2 q^(-k) = 2 N^(-1/4)` (`N = q^(4k)`), every `k`,
any `β`. -/
theorem As_covering {q : ℕ} [NeZero q] (ψ : Localization.Away (10 : ℤ) →+* ZMod q) (k : ℕ)
    (β : Fin 4 → ℕ → ℕ → Localization.Away (10 : ℤ)) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤
        4 / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.AsS11.covering_core ψ k β x hx

/-- **`prop:4DK2` (3)**, upper bound: for `k ≥ 2` and `q ≥ 7` (`gcd(q, 10) = 1`, forced by `ψ`), with
the coefficients `β` of `prop:Gs`, two distinct points of `𝒫^{A♯}_{k,q}` whose squared Euclidean
and squared toroidal distances, in cell units (`q^(-k) = N^(-1/4)`), are both
`< (1 - 2/q + q^(1-k))² + 12/q²`; i.e. `δ N^(1/4) < ((1 - 2/q + q^(1-k))² + 12/q²)^(1/2)`, toroidal
or Euclidean. -/
theorem As_upper {q : ℕ} [NeZero q] (ψ : Localization.Away (10 : ℤ) →+* ZMod q) (hq : 7 ≤ q)
    (k : ℕ) (hk : 2 ≤ k) (β : Fin 4 → ℕ → ℕ → Localization.Away (10 : ℤ))
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : Localization.Away (10 : ℤ)))
      (fun n c d => (FAs n c d : Localization.Away (10 : ℤ)))
      (fun c => (lamAs c : Localization.Away (10 : ℤ))) β) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2 <
        (1 - 2 / (q : ℝ) + 1 / (q : ℝ) ^ (k - 1)) ^ 2 + 12 / (q : ℝ) ^ 2 ∧
      (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) <
        (1 - 2 / (q : ℝ) + 1 / (q : ℝ) ^ (k - 1)) ^ 2 + 12 / (q : ℝ) ^ 2 :=
  Proofs.AsS11.upper_core ψ hq k hk β hβ

/-- **`prop:4DK2` (3)**, two-sided: for `k ≥ 3` and `q ≥ 23` (`gcd(q, 10) = 1`), with the
coefficients `β` of `prop:Gs`, `1 - 2/q ≤ δ N^(1/4) < 1 - 2/q + 8/q²`, toroidal or Euclidean: any
two distinct points have squared toroidal and squared Euclidean distance (cell units)
`≥ (1 - 2/q)²`, and some two distinct points have both `< (1 - 2/q + 8/q²)²`. -/
theorem As_two_sided {q : ℕ} [NeZero q] (ψ : Localization.Away (10 : ℤ) →+* ZMod q)
    (hq : 23 ≤ q) (k : ℕ) (hk : 3 ≤ k) (β : Fin 4 → ℕ → ℕ → Localization.Away (10 : ℤ))
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : Localization.Away (10 : ℤ)))
      (fun n c d => (FAs n c d : Localization.Away (10 : ℤ)))
      (fun c => (lamAs c : Localization.Away (10 : ℤ))) β) :
    (∀ v w : Fin (4 * k) → ZMod q, v ≠ w →
      (1 - 2 / (q : ℝ)) ^ 2 ≤
        (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) ∧
      (1 - 2 / (q : ℝ)) ^ 2 ≤
        ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2) ∧
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      ∑ c, (((digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v c : ℝ) -
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w c : ℝ)) / (q : ℝ) ^ (4 * k - k)) ^ 2 <
        (1 - 2 / (q : ℝ) + 8 / (q : ℝ) ^ 2) ^ 2 ∧
      (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
          (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℝ) / (q : ℝ) ^ (2 * (4 * k - k)) <
        (1 - 2 / (q : ℝ) + 8 / (q : ℝ) ^ 2) ^ 2 :=
  Proofs.AsS11.two_sided_core ψ hq k hk β hβ

end Z3NetF
