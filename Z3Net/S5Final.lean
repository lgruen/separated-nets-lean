/-
Proof module of entry S5R2: the statements of `prop:s5r2` and `tab:s5r2`, from the generic modules
and the certificates.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S5Reach
public import Z3Net.S5Sep
public import Z3Net.S5Wit
public import Z3Net.S5CertA
public import Z3Net.S5CertB

@[expose] public section

/-!
# Entry S5R2: final assembly

`chk_all` collects the per-prime relaxation certificates (`Z3Net/S5Cert{A,B}.lean`), `small_all`
(`Z3Net/S5Wit.lean`) the cheap checks; `reach_of` (`Z3Net/S5Reach.lean`) and `s5_bigM`, `s5_jit`
(`Z3Net/S5Sep.lean`) are the generic arguments.
-/

namespace Z3NetF.Proofs

open Finset Matrix S5

namespace S5

theorem chk_all : ∀ D ∈ s5r2Table, chk D (witOf D) = true := by
  simp only [s5r2Table, List.mem_cons, List.not_mem_nil, or_false]
  rintro D (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [chk31, chk37, chk53, chk71, chk101, chk151, chk199]

theorem table_p : s5r2Table.map S5Design.p = [31, 37, 53, 71, 101, 151, 199] := rfl

theorem prime_all : ∀ D ∈ s5r2Table, D.p.Prime := by
  intro D hD
  have h : D.p ∈ s5r2Table.map S5Design.p := List.mem_map_of_mem hD
  rw [table_p] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;> rw [h] <;> norm_num

theorem facts (D : S5Design) (hD : D ∈ s5r2Table) : Small D (witOf D) :=
  small_sound D (witOf D) (small_all D hD)

theorem rel_bound (D : S5Design) (hD : D ∈ s5r2Table) (a ξ1 ξ2 : Fin 5 → ℤ) (hR : S5Rel D a ξ1 ξ2)
    (ha : a ≠ 0) : (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a :=
  chk_sound D (witOf D) (facts D hD).side (chk_all D hD) a ξ1 ξ2 hR ha

lemma rpow_neg35_pow5 (x : ℝ) (hx : 0 < x) : (x ^ (-(3 / 5 : ℝ))) ^ 5 = (x ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_natCast, ← Real.rpow_neg hx.le]
  norm_num

lemma rpow35_pow5 (x : ℝ) (hx : 0 < x) : (x ^ (3 / 5 : ℝ)) ^ 5 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- The printed truncation of `(M_p - 1) p^(-3/5)`. -/
lemma tabM_real (p M t : ℕ) (hp : 0 < p) (hM : 1 ≤ M) (h1 : t ^ 5 * p ^ 3 ≤ (M - 1) ^ 5 * 10 ^ 15)
    (h2 : (M - 1) ^ 5 * 10 ^ 15 < (t + 1) ^ 5 * p ^ 3) :
    (t : ℝ) / 1000 ≤ ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 5 : ℝ)) < ((t : ℝ) + 1) / 1000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hy : (0 : ℝ) < (p : ℝ) ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM]; simp
  set X := ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 5 : ℝ)) with hX
  have hX0 : 0 ≤ X := mul_nonneg (by rw [← hM1]; positivity) hy.le
  have hX5 : X ^ 5 = ((M - 1 : ℕ) : ℝ) ^ 5 / (p : ℝ) ^ 3 := by
    rw [hX, mul_pow, rpow_neg35_pow5 _ hp0, hM1, div_eq_mul_inv]
  have hp3 : (0 : ℝ) < (p : ℝ) ^ 3 := by positivity
  have r1 : ((t : ℝ) ^ 5) * (p : ℝ) ^ 3 ≤ ((M - 1 : ℕ) : ℝ) ^ 5 * 10 ^ 15 := by exact_mod_cast h1
  have r2 : ((M - 1 : ℕ) : ℝ) ^ 5 * 10 ^ 15 < ((t : ℝ) + 1) ^ 5 * (p : ℝ) ^ 3 := by
    exact_mod_cast h2
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) hX0 (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hX5, div_pow, div_le_div_iff₀ (by norm_num) hp3]
    nlinarith
  · apply (pow_lt_pow_iff_left₀ hX0 (by positivity) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hX5, div_pow, div_lt_div_iff₀ hp3 (by norm_num)]
    nlinarith

/-- The printed truncation of `J_p p^(-3/5)`. -/
lemma tabJ_real (p J t : ℕ) (hp : 0 < p) (h1 : t ^ 10 * p ^ 6 ≤ J ^ 5 * 10 ^ 30)
    (h2 : J ^ 5 * 10 ^ 30 < (t + 1) ^ 10 * p ^ 6) :
    (t : ℝ) / 1000 ≤ Real.sqrt (J : ℝ) * (p : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      Real.sqrt (J : ℝ) * (p : ℝ) ^ (-(3 / 5 : ℝ)) < ((t : ℝ) + 1) / 1000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hy : (0 : ℝ) < (p : ℝ) ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  set Y := Real.sqrt (J : ℝ) * (p : ℝ) ^ (-(3 / 5 : ℝ)) with hY
  have hY0 : 0 ≤ Y := mul_nonneg (Real.sqrt_nonneg _) hy.le
  have hs : Real.sqrt (J : ℝ) ^ 10 = (J : ℝ) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  have hY10 : Y ^ 10 = (J : ℝ) ^ 5 / ((p : ℝ) ^ 3) ^ 2 := by
    rw [hY, mul_pow, hs, show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, rpow_neg35_pow5 _ hp0,
      inv_pow, div_eq_mul_inv]
  have hp6 : (0 : ℝ) < ((p : ℝ) ^ 3) ^ 2 := by positivity
  have r1 : ((t : ℝ) ^ 10) * ((p : ℝ) ^ 3) ^ 2 ≤ (J : ℝ) ^ 5 * 10 ^ 30 := by
    rw [← pow_mul]; exact_mod_cast h1
  have r2 : (J : ℝ) ^ 5 * 10 ^ 30 < ((t : ℝ) + 1) ^ 10 * ((p : ℝ) ^ 3) ^ 2 := by
    rw [← pow_mul]; exact_mod_cast h2
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) hY0 (by norm_num : (10 : ℕ) ≠ 0)).mp
    rw [hY10, div_pow, div_le_div_iff₀ (by norm_num) hp6]
    nlinarith
  · apply (pow_lt_pow_iff_left₀ hY0 (by positivity) (by norm_num : (10 : ℕ) ≠ 0)).mp
    rw [hY10, div_pow, div_lt_div_iff₀ hp6 (by norm_num)]
    nlinarith

/-- `⌊p^(3/5)⌋` from the integer inequalities. -/
lemma pig_real (p g : ℕ) (hp : 0 < p) (h1 : g ^ 5 ≤ p ^ 3) (h2 : p ^ 3 < (g + 1) ^ 5) :
    (g : ℝ) ≤ (p : ℝ) ^ (3 / 5 : ℝ) ∧ (p : ℝ) ^ (3 / 5 : ℝ) < (g : ℝ) + 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hz : 0 ≤ (p : ℝ) ^ (3 / 5 : ℝ) := (Real.rpow_pos_of_pos hp0 _).le
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) hz (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [rpow35_pow5 _ hp0]; exact_mod_cast h1
  · apply (pow_lt_pow_iff_left₀ hz (by positivity) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [rpow35_pow5 _ hp0]; exact_mod_cast h2

end S5

/-! ## The compared statements -/

theorem s5r2_table :
    s5r2Table.map S5Design.p = [31, 37, 53, 71, 101, 151, 199] ∧
    s5r2Table.map (fun D => (D.lat, D.pig, D.M, D.tabM, D.J2, D.tabJ)) =
      [(6, 7, 4, 382, 18, 540), (7, 8, 5, 458, 30, 627), (9, 10, 6, 461, 54, 678), (10, 12, 7, 464, 97, 763), (13, 15, 8, 439, 149, 765), (16, 20, 14, 640, 283, 828), (19, 23, 16, 626, 456, 891)] ∧
    (∀ D ∈ s5r2Table, D.p.Prime) ∧
    (∀ D ∈ s5r2Table, D.pl 2 = 0 ∧ D.pl 3 = 1) ∧
    (∀ D ∈ s5r2Table, ∀ i j : Fin 3, i ≠ j → D.g i j = 1 ∨ D.g i j = -1) ∧
    (∀ D ∈ s5r2Table, ∀ (i : Fin 3) (d : Fin 2), D.η i d = if i = 0 then 1 else 0) ∧
    (∀ D ∈ s5r2Table, ∀ j : Fin 3, ∃ i : Fin 3, i ≠ j ∧ D.H i j = 1 ∧ ∀ i' : Fin 3, i' ≠ i → D.H i' j = 0) ∧
    (∀ D ∈ s5r2Table, ∀ (i : Fin 3) (d : Fin 2), ¬ (D.p : ℤ) ∣ D.κ i d) ∧
    (∀ D ∈ s5r2Table, ∀ i i' : Fin 3, i ≠ i' →
      ¬ (D.p : ℤ) ∣ D.κ i 0 * D.κ i' 1 - D.κ i 1 * D.κ i' 0) :=
  ⟨S5.table_p, rfl, S5.prime_all, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem s5r2_reach (D : S5Design) (hD : D ∈ s5r2Table) :
    (∀ c d : Fin 5, c ≠ d → (D.pl c : ZMod D.p) ≠ (D.pl d : ZMod D.p)) ∧
    PlacesOK 0 (s5Places D) ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin 5) → Matrix (Fin (5 * k + 2 - skDepth 2 k c))
          (Fin (5 * k + 2 - skDepth 2 k c)) (ZMod D.p))
        (U : (d : Fin 5) → Matrix (Fin (skDepth 2 k d)) (Fin (skDepth 2 k d)) (ZMod D.p))
        (Φ : (c d : Fin 5) → Matrix (Fin (5 * k + 2 - skDepth 2 k c)) (Fin (skDepth 2 k d))
          (ZMod D.p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod D.p) (5 * k + 2) (skDepth 2 k) 0 (s5Places D) c d * U d) ∧
        (∀ (i : Fin 3) (d : Fin 2) (l : Fin (skDepth 2 k (s5x d))),
          ent (Φ (s5z i) (s5x d)) 0 l = ((s5xCoef D k i d l : ℤ) : ZMod D.p)) ∧
        (∀ (i j : Fin 3) (l : Fin (skDepth 2 k (s5z j))),
          ent (Φ (s5z i) (s5z j)) 0 l = ((s5zCoef D k i j l : ℤ) : ZMod D.p)) ∧
        IsNet0 5 D.p (5 * k + 2)
          (digPoint D.p (5 * k + 2) (graphGenK (m := 5 * k + 2) (skDepth 2 k) Φ)) :=
  S5.reach_of D (S5.witOf D) (S5.prime_all D hD) (S5.wchk_sound D _ (S5.facts D hD).w)

theorem s5r2_net (D : S5Design) (hD : D ∈ s5r2Table) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p),
      IsS5skel D k C ∧ IsNet0 5 D.p (5 * k + 2) (digPoint D.p (5 * k + 2) C) := by
  obtain ⟨-, -, H⟩ := s5r2_reach D hD
  obtain ⟨L, U, Φ, -, -, -, hx, hz, hnet⟩ := H k hk
  have hB := skel_graphGen 5 2 D.p k (by norm_num) Φ
  refine ⟨_, ⟨hB.1, fun i d l hl => ?_, fun i j l hl => ?_⟩, hnet⟩
  · have hl' : l < skDepth 2 k (s5x d) := by fin_cases d <;> simp [skDepth, s5x] <;> omega
    have h2 : 2 ≤ ((s5z i : Fin 5) : ℕ) := by rw [S5.s5z_val]; omega
    have := (hB.2 (s5z i) (s5x d) h2 ⟨l, hl'⟩).trans (hx i d ⟨l, hl'⟩)
    rwa [S5.s5x_val] at this
  · have hl' : l < skDepth 2 k (s5z j) := by fin_cases j <;> simp [skDepth, s5z] <;> omega
    have h2 : 2 ≤ ((s5z i : Fin 5) : ℕ) := by rw [S5.s5z_val]; omega
    exact (hB.2 (s5z i) (s5z j) h2 ⟨l, hl'⟩).trans (hz i j ⟨l, hl'⟩)

theorem s5r2_sep (D : S5Design) (hD : D ∈ s5r2Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    (D.M - 1) ^ 2 * D.p ^ (2 * (4 * k + 1)) ≤
      torusDist2 (D.p ^ (5 * k + 2)) (digPoint D.p (5 * k + 2) C v)
        (digPoint D.p (5 * k + 2) C w) := by
  have hp := S5.prime_all D hD
  rw [show 2 * (4 * k + 1) = 2 * (5 * k + 2 - (k + 1)) by omega]
  exact skelred_sep D.p (5 * k + 2) k D.M hp.two_le (by omega) C v w
    (S5.s5_bigM D hp (S5.facts D hD).M2 (fun a ξ1 ξ2 hR ha => (S5.rel_bound D hD a ξ1 ξ2 hR ha).1)
      k hk C hC v w hvw)

theorem s5r2_sepJ (D : S5Design) (hD : D ∈ s5r2Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    D.J2 * D.p ^ (2 * (4 * k + 1)) ≤
      torusDist2 (D.p ^ (5 * k + 2)) (digPoint D.p (5 * k + 2) C v)
        (digPoint D.p (5 * k + 2) C w) := by
  have hp := S5.prime_all D hD
  have hF := S5.facts D hD
  have hJ := S5.s5_jit D hp hF.J2p hF.podd
    (fun a ξ1 ξ2 hR ha => (S5.rel_bound D hD a ξ1 ξ2 hR ha).2) k hk C hC v w hvw
  have := SkSep.jit_le_torus D.p (5 * k + 2) k hp.one_lt.le (by omega) C v w
  rw [show 5 * k + 2 - (k + 1) = 4 * k + 1 by omega] at this
  exact le_trans (Nat.mul_le_mul_right _ hJ) this

theorem s5r2_sep_real (D : S5Design) (hD : D ∈ s5r2Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) * ((D.p : ℝ) ^ (5 * k + 2)) ^ (-(1 / 5 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (D.p ^ (5 * k + 2))
          ((digPoint D.p (5 * k + 2) C v c : ℤ) - (digPoint D.p (5 * k + 2) C w c : ℤ)) : ℝ)
          / (D.p : ℝ) ^ (5 * k + 2)) ^ 2) := by
  have hp := S5.prime_all D hD
  have h := skelred_sep_real (s := 5) D.p 2 k D.M hp.two_le (by norm_num) (by norm_num) (by omega)
    C v w (S5.s5_bigM D hp (S5.facts D hD).M2
      (fun a ξ1 ξ2 hR ha => (S5.rel_bound D hD a ξ1 ξ2 hR ha).1) k hk C hC v w hvw)
  have e1 : (-(((5 - 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) = -(3 / 5 : ℝ) := by norm_num
  have e2 : (-(1 / ((5 : ℕ) : ℝ))) = -(1 / 5 : ℝ) := by norm_num
  rw [e1, e2] at h
  exact h

theorem s5r2_sepJ_real (D : S5Design) (hD : D ∈ s5r2Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p)) (hC : IsS5skel D k C)
    (v w : Fin (5 * k + 2) → ZMod D.p) (hvw : v ≠ w) :
    Real.sqrt (D.J2 : ℝ) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) * ((D.p : ℝ) ^ (5 * k + 2)) ^ (-(1 / 5 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (D.p ^ (5 * k + 2))
          ((digPoint D.p (5 * k + 2) C v c : ℤ) - (digPoint D.p (5 * k + 2) C w c : ℤ)) : ℝ)
          / (D.p : ℝ) ^ (5 * k + 2)) ^ 2) := by
  have hp := S5.prime_all D hD
  have hsc := SkSep.rpow_scale D.p 5 2 k hp.one_lt.le (by norm_num) (by norm_num) (by omega)
  have e1 : (-(((5 - 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) = -(3 / 5 : ℝ) := by norm_num
  have e2 : (-(1 / ((5 : ℕ) : ℝ))) = -(1 / 5 : ℝ) := by norm_num
  rw [e1, e2] at hsc
  rw [mul_assoc, hsc]
  apply SkSep.sqrt_bound _ _ _ _ (by have := hp.pos; positivity)
  have hZ := s5r2_sepJ D hD k hk C hC v w hvw
  unfold torusDist2 at hZ
  have := (Nat.cast_le (α := ℝ)).mpr hZ
  push_cast at this
  rw [Real.sq_sqrt (by positivity), show 5 * k + 2 - (k + 1) = 4 * k + 1 by omega, ← pow_mul,
    Nat.mul_comm (4 * k + 1) 2]
  exact this

theorem s5r2_M (D : S5Design) (hD : D ∈ s5r2Table) :
    IsLeast {n : ℤ | ∃ a ξ1 ξ2 : Fin 5 → ℤ, S5Rel D a ξ1 ξ2 ∧ a ≠ 0 ∧ n = s5MaxAbs a}
      (D.M : ℤ) := by
  have hF := S5.facts D hD
  refine ⟨⟨_, _, _, S5.relB_sound D _ _ _ hF.rM, hF.aM, by rw [hF.mM]⟩, ?_⟩
  rintro n ⟨a, ξ1, ξ2, hR, hne, rfl⟩
  exact (S5.rel_bound D hD a ξ1 ξ2 hR hne).1

theorem s5r2_J (D : S5Design) (hD : D ∈ s5r2Table) :
    IsLeast {n : ℕ | ∃ a ξ1 ξ2 : Fin 5 → ℤ, S5Rel D a ξ1 ξ2 ∧ a ≠ 0 ∧ n = jitNorm2 a} D.J2 := by
  have hF := S5.facts D hD
  refine ⟨⟨_, _, _, S5.relB_sound D _ _ _ hF.rJ, hF.aJ, by rw [hF.mJ]⟩, ?_⟩
  rintro n ⟨a, ξ1, ξ2, hR, hne, rfl⟩
  exact (S5.rel_bound D hD a ξ1 ξ2 hR hne).2

theorem s5r2_lat (D : S5Design) (hD : D ∈ s5r2Table) :
    IsLeast {n : ℤ | ∃ u : Fin 5 → ℤ, u ≠ 0 ∧
      (∀ i : Fin 3, (D.p : ℤ) ∣ u (s5z i) - ∑ d : Fin 2, D.κ i d * u (s5x d)) ∧
      n = s5MaxAbs u} (D.lat : ℤ) := by
  have hF := S5.facts D hD
  refine ⟨⟨_, hF.u0, S5.latB_sound D _ hF.lB, by rw [hF.mu]⟩, ?_⟩
  rintro n ⟨u, hne, hL, rfl⟩
  exact S5.latchk_sound D hF.p0 hF.lc hF.lat1 hF.lat2 u hne hL

theorem s5r2_tab (D : S5Design) (hD : D ∈ s5r2Table) :
    (D.tabM : ℝ) / 1000 ≤ ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) < ((D.tabM : ℝ) + 1) / 1000 ∧
      (D.tabJ : ℝ) / 1000 ≤ Real.sqrt (D.J2 : ℝ) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      Real.sqrt (D.J2 : ℝ) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) < ((D.tabJ : ℝ) + 1) / 1000 ∧
      (D.pig : ℝ) ≤ (D.p : ℝ) ^ (3 / 5 : ℝ) ∧ (D.p : ℝ) ^ (3 / 5 : ℝ) < (D.pig : ℝ) + 1 ∧
      D.lat ≤ D.pig := by
  have hF := S5.facts D hD
  have hM := S5.tabM_real D.p D.M D.tabM hF.p0 (by have := hF.M2'; omega) hF.tM1 hF.tM2
  have hJ := S5.tabJ_real D.p D.J2 D.tabJ hF.p0 hF.tJ1 hF.tJ2
  have hg := S5.pig_real D.p D.pig hF.p0 hF.pg1 hF.pg2
  exact ⟨hM.1, hM.2, hJ.1, hJ.2, hg.1, hg.2, hF.latpig⟩

theorem s5r2_main (p : ℕ) (hp : p ∈ [31, 37, 53, 71, 101, 151, 199]) :
    ∃ D ∈ s5r2Table, D.p = p ∧ (∀ c d : Fin 5, c ≠ d → (D.pl c : ZMod D.p) ≠ (D.pl d : ZMod D.p)) ∧
      2 ≤ D.M ∧ 1 ≤ D.J2 ∧ ∀ k, 1 ≤ k →
      (∃ C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p),
        IsS5skel D k C ∧ IsNet0 5 D.p (5 * k + 2) (digPoint D.p (5 * k + 2) C)) ∧
      ∀ C : Fin 5 → Matrix (Fin (5 * k + 2)) (Fin (5 * k + 2)) (ZMod D.p), IsS5skel D k C →
        ∀ v w : Fin (5 * k + 2) → ZMod D.p, v ≠ w →
          Real.sqrt (D.J2 : ℝ) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) * ((D.p : ℝ) ^ (5 * k + 2)) ^ (-(1 / 5 : ℝ)) ≤ Real.sqrt (∑ c, ((cres (D.p ^ (5 * k + 2))
          ((digPoint D.p (5 * k + 2) C v c : ℤ) - (digPoint D.p (5 * k + 2) C w c : ℤ)) : ℝ)
          / (D.p : ℝ) ^ (5 * k + 2)) ^ 2) ∧
          ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 5 : ℝ)) * ((D.p : ℝ) ^ (5 * k + 2)) ^ (-(1 / 5 : ℝ)) ≤ Real.sqrt (∑ c, ((cres (D.p ^ (5 * k + 2))
          ((digPoint D.p (5 * k + 2) C v c : ℤ) - (digPoint D.p (5 * k + 2) C w c : ℤ)) : ℝ)
          / (D.p : ℝ) ^ (5 * k + 2)) ^ 2) := by
  have hm : p ∈ s5r2Table.map S5Design.p := by rw [S5.table_p]; exact hp
  obtain ⟨D, hD, hDp⟩ := List.mem_map.mp hm
  have hF := S5.facts D hD
  exact ⟨D, hD, hDp, (s5r2_reach D hD).1, hF.M2', hF.J1, fun k hk =>
    ⟨s5r2_net D hD k hk, fun C hC v w hvw =>
      ⟨s5r2_sepJ_real D hD k hk C hC v w hvw, s5r2_sep_real D hD k hk C hC v w hvw⟩⟩⟩

end Z3NetF.Proofs
