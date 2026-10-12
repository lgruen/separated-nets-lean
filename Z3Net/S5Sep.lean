/-
Proof module of entry S5R2 (`prop:s5r2`, "Separation").
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S5Cert
public import Z3Net.T3Sep
public import Z3Net.SkSepS1E

@[expose] public section

/-!
# Entry S5R2: the separation reduction (`prop:s5r2`, "Separation")

For a graph form with the skeleton digits of a design (`IsS5skel`, `k ≥ 1`) and two distinct points
whose centred fine difference `a` (`aDiff`) has `|a|_∞ < p/2`, `lem:skelred`(ii) (`skelred_carry`)
gives the floor changes `ξ_{c,1}`, `ξ_{c,2}` (`ξ_{c,2} = 0` at `k = 1`, where the levels `k - 2` do
not exist), which are the changes of the digits `k - 1`, `k - 2` modulo `p`; the change of the
skeleton digit of `z_i` (row `k`), block by block, is the congruence of the relaxation. So
`(a, ξ1, ξ2)` solves `S5Rel` (`s5_rel`). In the maximum norm (`s5_bigM`): if all `|a_c| < M_p`,
`2 M_p ≤ p + 1` gives `|a|_∞ < p/2`, and the certificate's `|a|_∞ ≥ M_p` is a contradiction; then
`lem:skelred`(i). In the Euclidean norm (`s5_jit`): if `∑ (|a_c| - 1)₊² < J_p²`, then
`4 J_p² ≤ (p - 1)²` and `p` odd give `|a|_∞ < p/2`, and the certificate's `∑ (|a_c| - 1)₊² ≥ J_p²`
is a contradiction; then `lem:skelred`(i) in each coordinate (`jit_le_torus`, as for `prop:S1E`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace S5

open SkSep
open Z3NetKN.Geom (vz)

/-- The block `x_d` of the change of a skeleton digit. -/
lemma blk_x (D : S5Design) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (i : Fin 3) (d : Fin 2) (A X1 X2 : ZMod D.p)
    (hA : vz (C (s5x d) *ᵥ w) k - vz (C (s5x d) *ᵥ v) k = A)
    (h1 : vz (C (s5x d) *ᵥ w) (k - 1) - vz (C (s5x d) *ᵥ v) (k - 1) = X1)
    (h2 : 2 ≤ k → vz (C (s5x d) *ᵥ w) (k - 2) - vz (C (s5x d) *ᵥ v) (k - 2) = X2)
    (h2' : ¬ 2 ≤ k → X2 = 0) :
    ∑ l ∈ range (skDepth 2 k (s5x d)), ent (C (s5z i)) k (skOff 2 k ((s5x d : Fin 5) : ℕ) + l) *
      (vz w (skOff 2 k ((s5x d : Fin 5) : ℕ) + l) - vz v (skOff 2 k ((s5x d : Fin 5) : ℕ) + l)) =
      (D.κ i d : ZMod D.p) * A + (D.β i d : ZMod D.p) * X1 + (D.η i d : ZMod D.p) * X2 := by
  have hr : 2 ≤ 5 := by norm_num
  have hK : skDepth 2 k (s5x d) = k + 1 := by fin_cases d <;> simp [skDepth, s5x]
  have hv : ((s5x d : Fin 5) : ℕ) = (d : ℕ) := s5x_val d
  rw [Finset.sum_congr (by rw [hK]) (fun l hl => by
    simp only [mem_range] at hl
    rw [← graph_digit hr hC.1 w (s5x d) l (by rw [hK]; exact hl),
      ← graph_digit hr hC.1 v (s5x d) l (by rw [hK]; exact hl), hv, hC.2.1 i d l hl])]
  have e : ∀ l, ((s5xCoef D k i d l : ℤ) : ZMod D.p) = if l = k then (D.κ i d : ZMod D.p)
      else if l + 1 = k then (D.β i d : ZMod D.p) else if l + 2 = k then (D.η i d : ZMod D.p)
      else 0 := by
    intro l; unfold s5xCoef; split_ifs <;> simp
  simp only [e]
  rw [T3.sum_x k hk, hA, h1]
  by_cases hk2 : 2 ≤ k
  · rw [if_pos hk2, h2 hk2]
  · rw [if_neg hk2, h2' hk2, mul_zero, add_zero]

/-- The block `z_j` of the change of a skeleton digit. -/
lemma blk_z (D : S5Design) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (i j : Fin 3) (X1 X2 : ZMod D.p)
    (h1 : vz (C (s5z j) *ᵥ w) (k - 1) - vz (C (s5z j) *ᵥ v) (k - 1) = X1)
    (h2 : 2 ≤ k → vz (C (s5z j) *ᵥ w) (k - 2) - vz (C (s5z j) *ᵥ v) (k - 2) = X2)
    (h2' : ¬ 2 ≤ k → X2 = 0) :
    ∑ l ∈ range (skDepth 2 k (s5z j)), ent (C (s5z i)) k (skOff 2 k ((s5z j : Fin 5) : ℕ) + l) *
      (vz w (skOff 2 k ((s5z j : Fin 5) : ℕ) + l) - vz v (skOff 2 k ((s5z j : Fin 5) : ℕ) + l)) =
      if j = i then (D.o i : ZMod D.p) * X1
      else (D.g i j : ZMod D.p) * X1 + (D.H i j : ZMod D.p) * X2 := by
  have hr : 2 ≤ 5 := by norm_num
  have hK : skDepth 2 k (s5z j) = k := by fin_cases j <;> simp [skDepth, s5z]
  rw [Finset.sum_congr (by rw [hK]) (fun l hl => by
    simp only [mem_range] at hl
    rw [← graph_digit hr hC.1 w (s5z j) l (by rw [hK]; exact hl),
      ← graph_digit hr hC.1 v (s5z j) l (by rw [hK]; exact hl), hC.2.2 i j l hl])]
  have e : ∀ l, ((s5zCoef D k i j l : ℤ) : ZMod D.p) = if i = j then
      (if l + 1 = k then (D.o i : ZMod D.p) else 0) else if l + 1 = k then (D.g i j : ZMod D.p)
      else if l + 2 = k then (D.H i j : ZMod D.p) else 0 := by
    intro l; unfold s5zCoef; split_ifs <;> simp
  simp only [e]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    rw [T3.sum_o k hk, h1]
  · simp only [if_neg hij, if_neg (Ne.symm hij)]
    rw [T3.sum_z k hk, h1]
    by_cases hk2 : 2 ≤ k
    · rw [if_pos hk2, h2 hk2]
    · rw [if_neg hk2, h2' hk2, mul_zero, add_zero]

/-- **The separation of `prop:s5r2`, relaxation:** a pair of distinct points of a graph form with
the skeleton digits of the design, with `|a|_∞ < p/2`, gives a nonzero solution of `S5Rel`. -/
theorem s5_rel (D : S5Design) (hp : D.p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (h2a : ∀ c, 2 * |aDiff D.p k C v w c| < D.p) :
    ∃ ξ1 ξ2 : Fin 5 → ℤ, S5Rel D (aDiff D.p k C v w) ξ1 ξ2 := by
  have hp2 := hp.two_le
  have : NeZero D.p := ⟨by omega⟩
  have hkm : k + 1 ≤ 5 * k + 2 := by omega
  set a := aDiff D.p k C v w with ha
  have hap : ∀ c, |a c| < D.p := fun c => by have := h2a c; have := abs_nonneg (a c); omega
  have hcar : ∀ c : Fin 5, ∃ ξ : ℕ → ℤ, (∀ j, 1 ≤ j → j ≤ k →
      ((finePos D.p (5 * k + 2) k C w c / D.p ^ j : ℕ) : ℤ) -
          (finePos D.p (5 * k + 2) k C v c / D.p ^ j : ℕ) ≡ ξ j [ZMOD (D.p : ℤ) ^ (k + 1 - j)] ∧
        (ξ j = 0 ∨ ξ j = Int.sign (a c))) ∧ ∀ j, 2 ≤ j → j ≤ k → ξ j ≠ 0 → ξ (j - 1) ≠ 0 :=
    fun c => skelred_carry D.p k _ _ hp2 (finePos_lt k hkm C v c) (finePos_lt k hkm C w c) (hap c)
  choose ξ hξ hξc using hcar
  set ξ1 : Fin 5 → ℤ := fun c => ξ c 1 with hξ1
  set ξ2 : Fin 5 → ℤ := fun c => if 2 ≤ k then ξ c 2 else 0 with hξ2
  have hd1 : ∀ c, vz (C c *ᵥ w) (k - 1) - vz (C c *ᵥ v) (k - 1) = ((ξ1 c : ℤ) : ZMod D.p) := by
    intro c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (D.p : ℤ) (by omega : k + 1 - 1 ≠ 0))
      (hξ c 1 le_rfl hk).1
    have := (ZMod.intCast_eq_intCast_iff _ _ D.p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [hξ1]
    simp only
    rw [← this, ← ZMod.natCast_mod (finePos D.p (5 * k + 2) k C w c / D.p ^ 1) D.p,
      ← ZMod.natCast_mod (finePos D.p (5 * k + 2) k C v c / D.p ^ 1) D.p,
      finePos_div_mod k hk hkm, finePos_div_mod k hk hkm]
  have hd2 : 2 ≤ k → ∀ c,
      vz (C c *ᵥ w) (k - 2) - vz (C c *ᵥ v) (k - 2) = ((ξ2 c : ℤ) : ZMod D.p) := by
    intro hk2 c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (D.p : ℤ) (by omega : k + 1 - 2 ≠ 0))
      (hξ c 2 (by omega) hk2).1
    have := (ZMod.intCast_eq_intCast_iff _ _ D.p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [hξ2]
    simp only [if_pos hk2]
    rw [← this, ← ZMod.natCast_mod (finePos D.p (5 * k + 2) k C w c / D.p ^ 2) D.p,
      ← ZMod.natCast_mod (finePos D.p (5 * k + 2) k C v c / D.p ^ 2) D.p,
      finePos_div2_mod k hk2 hkm, finePos_div2_mod k hk2 hkm]
  have hd2' : ¬ 2 ≤ k → ∀ c, ((ξ2 c : ℤ) : ZMod D.p) = 0 := by
    intro hk2 c; simp [hξ2, hk2]
  have hd0 : ∀ c, vz (C c *ᵥ w) k - vz (C c *ᵥ v) k = ((a c : ℤ) : ZMod D.p) := fun c =>
    (aDiff_cast k hkm C v w c).symm
  -- the congruence of the relaxation
  have hrowz : ∀ i : Fin 3, ((a (s5z i) : ℤ) : ZMod D.p) =
      (((∑ d : Fin 2, (D.κ i d * a (s5x d) + D.β i d * ξ1 (s5x d) + D.η i d * ξ2 (s5x d)) +
        ∑ j : Fin 3, (if j = i then D.o i * ξ1 (s5z j)
          else D.g i j * ξ1 (s5z j) + D.H i j * ξ2 (s5z j)) : ℤ)) : ZMod D.p) := by
    intro i
    rw [← hd0, row_diff (by norm_num : 2 ≤ 5) _ v w k (by omega), Fin.sum_univ_five]
    have hx : ∀ d : Fin 2, _ := fun d => blk_x D k hk C hC v w i d _ _ _ (hd0 (s5x d))
      (hd1 (s5x d)) (fun hk2 => hd2 hk2 (s5x d)) (fun hk2 => hd2' hk2 (s5x d))
    have hz : ∀ j : Fin 3, _ := fun j => blk_z D k hk C hC v w i j _ _ (hd1 (s5z j))
      (fun hk2 => hd2 hk2 (s5z j)) (fun hk2 => hd2' hk2 (s5z j))
    have hx0 := hx 0
    have hx1 := hx 1
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    simp only [s5x_zero, s5x_one, s5z_zero, s5z_one, s5z_two] at hx0 hx1 hz0 hz1 hz2
    rw [hx0, hx1, hz0, hz1, hz2]
    rw [Fin.sum_univ_two, Fin.sum_univ_three]
    simp only [s5x_zero, s5x_one, s5z_zero, s5z_one, s5z_two]
    push_cast
    split_ifs <;> ring
  refine ⟨ξ1, ξ2, h2a, fun c => ⟨?_, ?_, ?_⟩, fun i => ?_⟩
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

lemma aDiff_ne (D : S5Design) (hp : D.p.Prime) (k : ℕ)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) : aDiff D.p k C v w ≠ 0 := by
  have : NeZero D.p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := ne_zero_of_ne (by norm_num : 2 ≤ 5) hC.1 (by omega) v w hvw
  intro h; exact hc (by rw [h]; rfl)

/-- **The separation of `prop:s5r2` in the maximum norm, core:** some `|a_c| ≥ M_p`. -/
theorem s5_bigM (D : S5Design) (hp : D.p.Prime) (hM2 : 2 * D.M ≤ D.p + 1)
    (hrel : ∀ a ξ1 ξ2 : Fin 5 → ℤ, S5Rel D a ξ1 ξ2 → a ≠ 0 → (D.M : ℤ) ≤ s5MaxAbs a)
    (k : ℕ) (hk : 1 ≤ k) (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p))
    (hC : IsS5skel D k C) (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    ∃ c, (D.M : ℤ) ≤ |cmod (D.p ^ (k + 1))
      ((finePos D.p (5 * k + 2) k C w c : ℤ) - finePos D.p (5 * k + 2) k C v c)| := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ c, |aDiff D.p k C v w c| < D.M := fun c => hcon c
  have hM2' : 2 * (D.M : ℤ) ≤ D.p + 1 := by exact_mod_cast hM2
  have h2a : ∀ c, 2 * |aDiff D.p k C v w c| < D.p := fun c => by have := hlt c; omega
  obtain ⟨ξ1, ξ2, hR⟩ := s5_rel D hp k hk C hC v w h2a
  have := hrel _ ξ1 ξ2 hR (aDiff_ne D hp k C hC v w hvw)
  have hmax : s5MaxAbs (aDiff D.p k C v w) < D.M := by
    unfold s5MaxAbs
    exact max_lt (max_lt (max_lt (hlt 0) (hlt 1)) (max_lt (hlt 2) (hlt 3))) (hlt 4)
  omega

/-- **The separation of `prop:s5r2` in the Euclidean norm, core:** `∑ (|a_c| - 1)₊² ≥ J_p²`. -/
theorem s5_jit (D : S5Design) (hp : D.p.Prime) (hJ : 4 * D.J2 ≤ (D.p - 1) ^ 2)
    (hodd : D.p % 2 = 1)
    (hrel : ∀ a ξ1 ξ2 : Fin 5 → ℤ, S5Rel D a ξ1 ξ2 → a ≠ 0 → D.J2 ≤ jitNorm2 a)
    (k : ℕ) (hk : 1 ≤ k) (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p))
    (hC : IsS5skel D k C) (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    D.J2 ≤ jitNorm2 (aDiff D.p k C v w) := by
  by_contra hcon
  push Not at hcon
  have h2a : ∀ c, 2 * |aDiff D.p k C v w c| < D.p := by
    intro c
    have h1 := (jit_ge (aDiff D.p k C v w) c).trans_lt hcon
    set n := (aDiff D.p k C v w c).natAbs with hn
    have h4 : 4 * (n - 1) ^ 2 < (D.p - 1) ^ 2 := by omega
    have h5 : 2 * (n - 1) < D.p - 1 := by
      by_contra h6
      push Not at h6
      have := Nat.pow_le_pow_left h6 2
      rw [mul_pow] at this
      omega
    have h6 : 2 * n < D.p := by omega
    have : ((2 * n : ℕ) : ℤ) < (D.p : ℤ) := by exact_mod_cast h6
    rw [hn] at this
    push_cast at this
    simpa [Int.natCast_natAbs] using this
  obtain ⟨ξ1, ξ2, hR⟩ := s5_rel D hp k hk C hC v w h2a
  have := hrel _ ξ1 ξ2 hR (aDiff_ne D hp k C hC v w hvw)
  omega

end S5

end Z3NetF.Proofs
