/-
Proof module of entry T3S4 (`prop:t3s4`, "Separation").
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.T3S4Defs
public import Z3Net.SkSepGraph

@[expose] public section

/-!
# Entry T3S4: the separation reduction (`prop:t3s4`, "Separation")

For a graph form with the skeleton digits of a design (`IsT3skel`, `k ≥ 1`) and two distinct
points with all `|a_c| < M_p` (`a` the centred fine difference, `aDiff`), `2 M_p ≤ p + 1` gives
`|a|_∞ < p/2`; `lem:skelred`(ii) (`skelred_carry`) gives the floor changes `ξ_{c,1}`, `ξ_{c,2}`
(`ξ_{c,2} = 0` at `k = 1`, where the levels `k - 2` do not exist), which are the changes of the
digits `k - 1`, `k - 2` modulo `p`; the change of the skeleton digit of `z_i` (row `k`), block by
block, is the congruence of the relaxation. So `(a, ξ1, ξ2)` solves `T3Rel`, and a lower bound
`M_p ≤ |a|_∞` for all nonzero solutions (the certificate) contradicts `|a|_∞ < M_p`. Then
`lem:skelred`(i) concludes (`t3_sep_int`, `t3_sep_real`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

open Z3NetKN.Geom (vz dg pre pre_digit dg_lt Pf)

variable {s p : ℕ}

/-- `⌊P_c / p²⌋ mod p` is digit `k - 2` of coordinate `c` (`k ≥ 2`). -/
lemma finePos_div2_mod [NeZero p] {m : ℕ} (k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (c : Fin s) :
    ((finePos p m k C v c / p ^ 2 % p : ℕ) : ZMod p) = vz (C c *ᵥ v) (k - 2) := by
  rw [finePos_eq k hkm]
  unfold Pf
  rw [pre_digit p (Nat.pos_of_neZero p) _ _ (fun j _ => dg_lt _ _ _) 2 (by omega), dg_cast,
    show k + 1 - 1 - 2 = k - 2 by omega]

end SkSep

namespace T3

open SkSep
open Z3NetKN.Geom (vz)

lemma xcoef_cast {R : Type*} [CommRing R] (D : T3Design) (k : ℕ) (i : Fin 3) (l : ℕ) :
    ((t3xCoef D k i l : ℤ) : R) = if l = k then (D.κ i : R) else if l + 1 = k then (D.β i : R)
      else if l + 2 = k then (D.η i : R) else 0 := by
  unfold t3xCoef; split_ifs <;> simp

lemma zcoef_cast {R : Type*} [CommRing R] (D : T3Design) (k : ℕ) (i j : Fin 3) (l : ℕ) :
    ((t3zCoef D k i j l : ℤ) : R) = if i = j then (if l + 1 = k then (D.o i : R) else 0)
      else if l + 1 = k then (D.g i j : R) else if l + 2 = k then (D.H i j : R) else 0 := by
  unfold t3zCoef; split_ifs <;> simp

/-- The block `x` of the change of a skeleton digit. -/
lemma sum_x {R : Type*} [CommRing R] (k : ℕ) (hk : 1 ≤ k) (A B E : R) (f : ℕ → R) :
    ∑ l ∈ range (k + 1), (if l = k then A else if l + 1 = k then B else if l + 2 = k then E else 0) *
      f l = A * f k + B * f (k - 1) + (if 2 ≤ k then E * f (k - 2) else 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rcases n with _ | n
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun l hl => by
        simp only [mem_range] at hl
        rw [if_neg (show ¬ l = n + 1 + 1 by omega), if_neg (show ¬ l + 1 = n + 1 + 1 by omega),
          if_neg (show ¬ l + 2 = n + 1 + 1 by omega), zero_mul])]
    simp only [show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all

/-- A block `z_j`, `j ≠ i`, of the change of a skeleton digit. -/
lemma sum_z {R : Type*} [CommRing R] (k : ℕ) (hk : 1 ≤ k) (G H : R) (f : ℕ → R) :
    ∑ l ∈ range k, (if l + 1 = k then G else if l + 2 = k then H else 0) * f l =
      G * f (k - 1) + (if 2 ≤ k then H * f (k - 2) else 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rcases n with _ | n
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all
  · rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun l hl => by
        simp only [mem_range] at hl
        rw [if_neg (show ¬ l + 1 = n + 1 + 1 by omega), if_neg (show ¬ l + 2 = n + 1 + 1 by omega),
          zero_mul])]
    simp only [show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all

/-- The own block `z_i` of the change of a skeleton digit. -/
lemma sum_o {R : Type*} [CommRing R] (k : ℕ) (hk : 1 ≤ k) (O : R) (f : ℕ → R) :
    ∑ l ∈ range k, (if l + 1 = k then O else 0) * f l = O * f (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun l hl => by
    simp only [mem_range] at hl
    rw [if_neg (by omega), zero_mul]), if_pos rfl, zero_add, Nat.add_sub_cancel]

/-- **The separation of `prop:t3s4`, core:** some coordinate has `|a_c| ≥ M_p`. -/
theorem t3_big (D : T3Design) (hp : D.p.Prime) (hM2 : 2 * D.M ≤ D.p + 1)
    (hrel : ∀ a ξ1 ξ2 : Fin 4 → ℤ, T3Rel D a ξ1 ξ2 → a ≠ 0 → (D.M : ℤ) ≤ t3MaxAbs a)
    (k : ℕ) (hk : 1 ≤ k) (C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p))
    (hC : IsT3skel D k C) (v w : Fin (4 * k + 1) → ZMod D.p) (hvw : v ≠ w) :
    ∃ c, (D.M : ℤ) ≤ |cmod (D.p ^ (k + 1))
      ((finePos D.p (4 * k + 1) k C w c : ℤ) - finePos D.p (4 * k + 1) k C v c)| := by
  have hp2 := hp.two_le
  have : NeZero D.p := ⟨by omega⟩
  have hr : 1 ≤ 4 := by norm_num
  have hkm : k + 1 ≤ 4 * k + 1 := by omega
  by_contra hcon
  push Not at hcon
  set a := aDiff D.p k C v w with ha
  have hlt : ∀ c, |a c| < D.M := fun c => hcon c
  have hM2' : 2 * (D.M : ℤ) ≤ D.p + 1 := by exact_mod_cast hM2
  have h2a : ∀ c, 2 * |a c| < D.p := fun c => by have := hlt c; omega
  have hap : ∀ c, |a c| < D.p := fun c => by have := h2a c; have := abs_nonneg (a c); omega
  -- the floor changes (`lem:skelred`(ii))
  have hcar : ∀ c : Fin 4, ∃ ξ : ℕ → ℤ, (∀ j, 1 ≤ j → j ≤ k →
      ((finePos D.p (4 * k + 1) k C w c / D.p ^ j : ℕ) : ℤ) -
          (finePos D.p (4 * k + 1) k C v c / D.p ^ j : ℕ) ≡ ξ j [ZMOD (D.p : ℤ) ^ (k + 1 - j)] ∧
        (ξ j = 0 ∨ ξ j = Int.sign (a c))) ∧ ∀ j, 2 ≤ j → j ≤ k → ξ j ≠ 0 → ξ (j - 1) ≠ 0 :=
    fun c => skelred_carry D.p k _ _ hp2 (finePos_lt k hkm C v c) (finePos_lt k hkm C w c) (hap c)
  choose ξ hξ hξc using hcar
  set ξ1 : Fin 4 → ℤ := fun c => ξ c 1 with hξ1
  set ξ2 : Fin 4 → ℤ := fun c => if 2 ≤ k then ξ c 2 else 0 with hξ2
  have hd1 : ∀ c, ((ξ1 c : ℤ) : ZMod D.p) = vz (C c *ᵥ w) (k - 1) - vz (C c *ᵥ v) (k - 1) := by
    intro c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (D.p : ℤ) (by omega : k + 1 - 1 ≠ 0))
      (hξ c 1 le_rfl hk).1
    have := (ZMod.intCast_eq_intCast_iff _ _ D.p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [hξ1]
    simp only
    rw [← this, ← ZMod.natCast_mod (finePos D.p (4 * k + 1) k C w c / D.p ^ 1) D.p,
      ← ZMod.natCast_mod (finePos D.p (4 * k + 1) k C v c / D.p ^ 1) D.p,
      finePos_div_mod k hk hkm, finePos_div_mod k hk hkm]
  have hd2 : 2 ≤ k → ∀ c, ((ξ2 c : ℤ) : ZMod D.p) = vz (C c *ᵥ w) (k - 2) - vz (C c *ᵥ v) (k - 2) := by
    intro hk2 c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (D.p : ℤ) (by omega : k + 1 - 2 ≠ 0))
      (hξ c 2 (by omega) hk2).1
    have := (ZMod.intCast_eq_intCast_iff _ _ D.p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [hξ2]
    simp only [if_pos hk2]
    rw [← this, ← ZMod.natCast_mod (finePos D.p (4 * k + 1) k C w c / D.p ^ 2) D.p,
      ← ZMod.natCast_mod (finePos D.p (4 * k + 1) k C v c / D.p ^ 2) D.p,
      finePos_div2_mod k hk2 hkm, finePos_div2_mod k hk2 hkm]
  have hd0 : ∀ c, ((a c : ℤ) : ZMod D.p) = vz (C c *ᵥ w) k - vz (C c *ᵥ v) k := fun c =>
    aDiff_cast k hkm C v w c
  have hg : ∀ (d : Fin 4) (l : ℕ), l < skDepth 1 k d →
      vz w (skOff 1 k (d : ℕ) + l) - vz v (skOff 1 k (d : ℕ) + l) =
        vz (C d *ᵥ w) l - vz (C d *ᵥ v) l := fun d l hl => by
    rw [graph_digit hr hC.1 w d l hl, graph_digit hr hC.1 v d l hl]
  -- the congruence of the relaxation
  have hrowz : ∀ i : Fin 3, ((a i.succ : ℤ) : ZMod D.p) =
      (((D.κ i * a 0 + D.β i * ξ1 0 + D.η i * ξ2 0 + ∑ j : Fin 3, (if j = i then D.o i * ξ1 j.succ
        else D.g i j * ξ1 j.succ + D.H i j * ξ2 j.succ) : ℤ)) : ZMod D.p) := by
    intro i
    rw [hd0, row_diff hr _ v w k (by omega), Fin.sum_univ_succ]
    have hx : ∑ l ∈ range (skDepth 1 k (0 : Fin 4)), ent (C i.succ) k (skOff 1 k ((0 : Fin 4) : ℕ) + l) *
        (vz w (skOff 1 k ((0 : Fin 4) : ℕ) + l) - vz v (skOff 1 k ((0 : Fin 4) : ℕ) + l)) =
        (D.κ i : ZMod D.p) * a 0 + (D.β i : ZMod D.p) * ξ1 0 + (D.η i : ZMod D.p) * ξ2 0 := by
      have hK : skDepth 1 k (0 : Fin 4) = k + 1 := by simp [skDepth]
      have hC0 : ∀ (l : ℕ), l < k + 1 →
          ent (C i.succ) k (skOff 1 k ((0 : Fin 4) : ℕ) + l) = ((t3xCoef D k i l : ℤ) : ZMod D.p) :=
        hC.2.1 i
      rw [Finset.sum_congr (by rw [hK]) (fun l hl => by
        simp only [mem_range] at hl
        rw [hC0 l hl, hg 0 l (by rw [hK]; exact hl), xcoef_cast])]
      rw [sum_x k hk, ← hd0 0, ← hd1 0]
      by_cases hk2 : 2 ≤ k
      · rw [if_pos hk2, ← hd2 hk2 0]
      · rw [if_neg hk2]
        simp [hξ2, hk2]
    have hz : ∀ j : Fin 3, ∑ l ∈ range (skDepth 1 k j.succ), ent (C i.succ) k (skOff 1 k (j.succ : ℕ) + l) *
        (vz w (skOff 1 k (j.succ : ℕ) + l) - vz v (skOff 1 k (j.succ : ℕ) + l)) =
        ((if j = i then D.o i * ξ1 j.succ else D.g i j * ξ1 j.succ + D.H i j * ξ2 j.succ : ℤ) :
          ZMod D.p) := by
      intro j
      have hK : skDepth 1 k j.succ = k := by simp [skDepth]
      rw [Finset.sum_congr (by rw [hK]) (fun l hl => by
        simp only [mem_range] at hl
        rw [hC.2.2 i j l hl, hg j.succ l (by rw [hK]; exact hl), zcoef_cast])]
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        rw [sum_o k hk, ← hd1]
        push_cast; ring
      · simp only [if_neg hij, if_neg (Ne.symm hij)]
        rw [sum_z k hk, ← hd1]
        by_cases hk2 : 2 ≤ k
        · rw [if_pos hk2, ← hd2 hk2]; push_cast; ring
        · rw [if_neg hk2]; simp [hξ2, hk2]
    rw [hx, Finset.sum_congr rfl (fun j _ => hz j)]
    push_cast
    ring
  -- the relaxation holds
  have hR : T3Rel D a ξ1 ξ2 := by
    refine ⟨h2a, fun c => ⟨?_, ?_, ?_⟩, fun i => ?_⟩
    · exact (hξ c 1 le_rfl hk).2
    · by_cases hk2 : 2 ≤ k
      · simp only [hξ2, if_pos hk2]; exact (hξ c 2 (by omega) hk2).2
      · simp [hξ2, hk2]
    · intro h2
      by_cases hk2 : 2 ≤ k
      · simp only [hξ2, if_pos hk2] at h2
        exact hξc c 2 le_rfl hk2 h2
      · simp [hξ2, hk2] at h2
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hrowz i, sub_self]
  have hne : a ≠ 0 := by
    obtain ⟨c, hc⟩ := ne_zero_of_ne hr hC.1 hkm v w hvw
    intro h; exact hc (by rw [← ha, h]; rfl)
  have := hrel a ξ1 ξ2 hR hne
  have hmax : t3MaxAbs a < D.M := by
    unfold t3MaxAbs
    exact max_lt (max_lt (hlt 0) (hlt 1)) (max_lt (hlt 2) (hlt 3))
  omega

end T3

end Z3NetF.Proofs
