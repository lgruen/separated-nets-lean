/-
Proof module of entry T3S4: the statements of `prop:t3s4`, `tab:t3s4` and `cor:dim4` (residue
`m ≡ 1 (mod 4)` and the complete corollary), from the generic modules and the certificates.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.T3Reach
public import Z3Net.T3Sep
public import Z3Net.T3Wit
public import Z3Net.T3CertA
public import Z3Net.T3CertB
public import Z3Net.T3CertC
public import Z3Net.SkD4Final

@[expose] public section

/-!
# Entry T3S4: final assembly

`chk_all` collects the per-prime relaxation certificates (`Z3Net/T3Cert{A,B,C}.lean`), `small_all`
(`Z3Net/T3Wit.lean`) the cheap checks; `reach_of` (`Z3Net/T3Reach.lean`) and `t3_big`
(`Z3Net/T3Sep.lean`) are the generic arguments.
-/

namespace Z3NetF.Proofs

open Finset Matrix T3

namespace T3

theorem chk_all : ∀ D ∈ t3s4Table, chk D = true := by
  simp only [t3s4Table, List.mem_cons, List.not_mem_nil, or_false]
  rintro D (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [chk5, chk7, chk11, chk13, chk17, chk19, chk23, chk29, chk31, chk37, chk41, chk43, chk47, chk53, chk59, chk61, chk67, chk71, chk73, chk79, chk83]

theorem table_p : t3s4Table.map T3Design.p = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83] := rfl

theorem prime_all : ∀ D ∈ t3s4Table, D.p.Prime := by
  intro D hD
  have h : D.p ∈ t3s4Table.map T3Design.p := List.mem_map_of_mem hD
  rw [table_p] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] <;> norm_num

theorem facts (D : T3Design) (hD : D ∈ t3s4Table) :
    wchk D (witOf D) = true ∧ relB D (witOf D).a (witOf D).ξ1 (witOf D).ξ2 = true ∧
      (witOf D).a ≠ 0 ∧ t3MaxAbs (witOf D).a = D.M ∧
      latB D (witOf D).u = true ∧ (witOf D).u ≠ 0 ∧ t3MaxAbs (witOf D).u = D.lat ∧
      latchk D = true ∧ 2 * D.M ≤ D.p + 1 ∧ 2 * D.lat ≤ D.p + 1 ∧ 0 < D.p ∧
      D.tab ^ 4 * D.p ^ 3 ≤ (D.M - 1) ^ 4 * 10 ^ 12 ∧
      (D.M - 1) ^ 4 * 10 ^ 12 < (D.tab + 1) ^ 4 * D.p ^ 3 ∧ D.lat ≤ D.M + 2 ∧ 1 ≤ D.M ∧
      (7 ≤ D.p → 2 ≤ D.M) ∧ (23 ≤ D.p → 180 ≤ D.tab) :=
  small_sound D (witOf D) (small_all D hD)

theorem rel_bound (D : T3Design) (hD : D ∈ t3s4Table) :
    ∀ a ξ1 ξ2 : Fin 4 → ℤ, T3Rel D a ξ1 ξ2 → a ≠ 0 → (D.M : ℤ) ≤ t3MaxAbs a :=
  chk_sound D (facts D hD).2.2.2.2.2.2.2.2.2.2.1 (chk_all D hD)

/-- `(p^(-3/4))⁴ = 1/p³`, and the printed truncations. -/
lemma tab_real (p M t : ℕ) (hp : 0 < p) (hM : 1 ≤ M) (h1 : t ^ 4 * p ^ 3 ≤ (M - 1) ^ 4 * 10 ^ 12)
    (h2 : (M - 1) ^ 4 * 10 ^ 12 < (t + 1) ^ 4 * p ^ 3) :
    (t : ℝ) / 1000 ≤ ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 4 : ℝ)) < ((t : ℝ) + 1) / 1000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hy : (0 : ℝ) < (p : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  have hy4 : ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ 4 = ((p : ℝ) ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le]
    norm_num
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM]; simp
  set X := ((M : ℝ) - 1) * (p : ℝ) ^ (-(3 / 4 : ℝ)) with hX
  have hX0 : 0 ≤ X := mul_nonneg (by rw [← hM1]; positivity) hy.le
  have hX4 : X ^ 4 = ((M - 1 : ℕ) : ℝ) ^ 4 / (p : ℝ) ^ 3 := by
    rw [hX, mul_pow, hy4, hM1, div_eq_mul_inv]
  have hp3 : (0 : ℝ) < (p : ℝ) ^ 3 := by positivity
  have r1 : ((t : ℝ) ^ 4) * (p : ℝ) ^ 3 ≤ ((M - 1 : ℕ) : ℝ) ^ 4 * 10 ^ 12 := by exact_mod_cast h1
  have r2 : ((M - 1 : ℕ) : ℝ) ^ 4 * 10 ^ 12 < ((t : ℝ) + 1) ^ 4 * (p : ℝ) ^ 3 := by exact_mod_cast h2
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) hX0 (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hX4, div_pow, div_le_div_iff₀ (by norm_num) hp3]
    nlinarith
  · apply (pow_lt_pow_iff_left₀ hX0 (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hX4, div_pow, div_lt_div_iff₀ hp3 (by norm_num)]
    nlinarith

lemma quarter_4k1 (x : ℝ) (hx : 0 < x) (k : ℕ) :
    x ^ (1 / 4 : ℝ) * (x ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ)) = (x ^ k)⁻¹ := by
  rw [SkD4.rpow_quarter x hx, ← Real.rpow_add hx, ← Real.rpow_natCast x k, ← Real.rpow_neg hx.le]
  push_cast; ring_nf

/-- Covering for `s = 4`, `m = 4k + 1`: the elementary box with depths `(k+1, k, k, k)` around `y`
gives a net point within `2 p^(-k) = 2 p^(1/4) N^(-1/4)`. -/
theorem cover_4k1 {p k : ℕ} (hp : 1 ≤ p) (X : (Fin (4 * k + 1) → ZMod p) → Fin 4 → ℕ)
    (hX : IsNet0 4 p (4 * k + 1) X) (y : Fin 4 → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin (4 * k + 1) → ZMod p,
      Real.sqrt (∑ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 1)) ^ 2) ≤
        2 * (p : ℝ) ^ (1 / 4 : ℝ) * (((p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨v, hv⟩ := SkD4.box_cover hp X hX ![k + 1, k, k, k]
    (by simp [Fin.sum_univ_four]; ring) y hy
  refine ⟨v, ?_⟩
  rw [mul_assoc, quarter_4k1 _ hp0]
  set t : ℝ := ((p : ℝ) ^ k)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have hc : ∀ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 1)) ^ 2 ≤ t ^ 2 := by
    intro c
    have h1 := hv c
    have h2 : ((p : ℝ) ^ (![k + 1, k, k, k] c))⁻¹ ≤ t := by
      rw [ht]
      apply inv_anti₀ (pow_pos hp0 _)
      apply pow_le_pow_right₀ hp1
      fin_cases c <;> simp
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.le.trans h2) 2
  have hsum : ∑ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 1)) ^ 2 ≤ (2 * t) ^ 2 := by
    calc _ ≤ ∑ _c : Fin 4, t ^ 2 := Finset.sum_le_sum (fun c _ => hc c)
      _ = (2 * t) ^ 2 := by simp; ring
  calc _ ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * t := Real.sqrt_sq (by positivity)

lemma inv_sqrt31_le : 1 / Real.sqrt 31 ≤ (180 : ℝ) / 1000 := by
  have h : (1000 / 180 : ℝ) ≤ Real.sqrt 31 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs : (0 : ℝ) < Real.sqrt 31 := by positivity
  rw [div_le_div_iff₀ hs (by norm_num)]
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 180)
  nlinarith

end T3

/-! ## The compared statements -/

theorem t3s4_table :
    t3s4Table.map T3Design.p = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83] ∧
    t3s4Table.map (fun D => (D.p, D.M, D.lat, D.tab)) =
      [(5, 1, 2, 0), (7, 2, 3, 232), (11, 3, 4, 331), (13, 4, 5, 438), (17, 5, 6, 477), (19, 6, 7, 549), (23, 6, 8, 476), (29, 8, 10, 560), (31, 8, 10, 532), (37, 11, 12, 666), (41, 12, 12, 678), (43, 13, 13, 714), (47, 13, 14, 668), (53, 15, 15, 712), (59, 17, 17, 751), (61, 17, 17, 733), (67, 17, 19, 683), (71, 18, 20, 695), (73, 18, 19, 680), (79, 21, 21, 754), (83, 22, 23, 763)] ∧
    (∀ D ∈ t3s4Table, D.p.Prime) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → p ≤ 83 → ∃ D ∈ t3s4Table, D.p = p) ∧
    (∀ D ∈ t3s4Table, ∀ i j : Fin 3, i ≠ j → D.g i j = 1 ∨ D.g i j = -1) ∧
    (t3s4Table.filter (fun D => D.a3 = 3)).length = 11 := by
  refine ⟨T3.table_p, rfl, T3.prime_all, ?_, by decide +kernel, by decide +kernel⟩
  intro p hp h5 h83
  interval_cases p <;> first | decide +kernel | (exfalso; norm_num at hp)

theorem t3s4_reach (D : T3Design) (hD : D ∈ t3s4Table) :
    PlacesOK 0 (t3Places D) ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin 4) → Matrix (Fin (4 * k + 1 - skDepth 1 k c))
          (Fin (4 * k + 1 - skDepth 1 k c)) (ZMod D.p))
        (U : (d : Fin 4) → Matrix (Fin (skDepth 1 k d)) (Fin (skDepth 1 k d)) (ZMod D.p))
        (Φ : (c d : Fin 4) → Matrix (Fin (4 * k + 1 - skDepth 1 k c)) (Fin (skDepth 1 k d))
          (ZMod D.p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod D.p) (4 * k + 1) (skDepth 1 k) 0 (t3Places D) c d * U d) ∧
        (∀ (i : Fin 3) (l : Fin (skDepth 1 k (0 : Fin 4))),
          ent (Φ i.succ 0) 0 l = ((t3xCoef D k i l : ℤ) : ZMod D.p)) ∧
        (∀ (i j : Fin 3) (l : Fin (skDepth 1 k j.succ)),
          ent (Φ i.succ j.succ) 0 l = ((t3zCoef D k i j l : ℤ) : ZMod D.p)) ∧
        IsNet0 4 D.p (4 * k + 1)
          (digPoint D.p (4 * k + 1) (graphGenK (m := 4 * k + 1) (skDepth 1 k) Φ)) :=
  T3.reach_of D (T3.witOf D) (T3.prime_all D hD) (T3.wchk_sound D _ (T3.facts D hD).1)

theorem t3s4_net (D : T3Design) (hD : D ∈ t3s4Table) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p),
      IsT3skel D k C ∧ IsNet0 4 D.p (4 * k + 1) (digPoint D.p (4 * k + 1) C) := by
  obtain ⟨-, H⟩ := t3s4_reach D hD
  obtain ⟨L, U, Φ, -, -, -, hx, hz, hnet⟩ := H k hk
  have hB := skel_graphGen 4 1 D.p k (by norm_num) Φ
  refine ⟨_, ⟨hB.1, fun i l hl => ?_, fun i j l hl => ?_⟩, hnet⟩
  · have hl' : l < skDepth 1 k (0 : Fin 4) := by simp [skDepth]; omega
    exact (hB.2 i.succ 0 (by simp) ⟨l, hl'⟩).trans (hx i ⟨l, hl'⟩)
  · have hl' : l < skDepth 1 k j.succ := by simp [skDepth]; omega
    exact (hB.2 i.succ j.succ (by simp) ⟨l, hl'⟩).trans (hz i j ⟨l, hl'⟩)

theorem t3s4_sep (D : T3Design) (hD : D ∈ t3s4Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p)) (hC : IsT3skel D k C)
    (v w : Fin (4 * k + 1) → ZMod D.p) (hvw : v ≠ w) :
    (D.M - 1) ^ 2 * D.p ^ (2 * (3 * k)) ≤
      torusDist2 (D.p ^ (4 * k + 1)) (digPoint D.p (4 * k + 1) C v)
        (digPoint D.p (4 * k + 1) C w) := by
  have hp := T3.prime_all D hD
  rw [show 2 * (3 * k) = 2 * (4 * k + 1 - (k + 1)) by omega]
  exact skelred_sep D.p (4 * k + 1) k D.M hp.two_le (by omega) C v w
    (T3.t3_big D hp (T3.facts D hD).2.2.2.2.2.2.2.2.1 (T3.rel_bound D hD) k hk C hC v w hvw)

theorem t3s4_sep_real (D : T3Design) (hD : D ∈ t3s4Table) (k : ℕ) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p)) (hC : IsT3skel D k C)
    (v w : Fin (4 * k + 1) → ZMod D.p) (hvw : v ≠ w) :
    ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 4 : ℝ)) * ((D.p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (D.p ^ (4 * k + 1))
          ((digPoint D.p (4 * k + 1) C v c : ℤ) - (digPoint D.p (4 * k + 1) C w c : ℤ)) : ℝ)
          / (D.p : ℝ) ^ (4 * k + 1)) ^ 2) := by
  have hp := T3.prime_all D hD
  have h := skelred_sep_real (s := 4) D.p 1 k D.M hp.two_le (by norm_num) (by norm_num) (by omega)
    C v w (T3.t3_big D hp (T3.facts D hD).2.2.2.2.2.2.2.2.1 (T3.rel_bound D hD) k hk C hC v w hvw)
  have e1 : (-(((4 - 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) = -(3 / 4 : ℝ) := by norm_num
  have e2 : (-(1 / ((4 : ℕ) : ℝ))) = -(1 / 4 : ℝ) := by norm_num
  rw [e1, e2] at h
  exact h

theorem t3s4_M (D : T3Design) (hD : D ∈ t3s4Table) :
    IsLeast {n : ℤ | ∃ a ξ1 ξ2 : Fin 4 → ℤ, T3Rel D a ξ1 ξ2 ∧ a ≠ 0 ∧ n = t3MaxAbs a}
      (D.M : ℤ) := by
  obtain ⟨-, hr, ha, hm, -⟩ := T3.facts D hD
  refine ⟨⟨_, _, _, T3.relB_sound D _ _ _ hr, ha, by rw [hm]⟩, ?_⟩
  rintro n ⟨a, ξ1, ξ2, hR, hne, rfl⟩
  exact T3.rel_bound D hD a ξ1 ξ2 hR hne

theorem t3s4_lat (D : T3Design) (hD : D ∈ t3s4Table) :
    IsLeast {n : ℤ | ∃ u : Fin 4 → ℤ, u ≠ 0 ∧ (∀ i : Fin 3, (D.p : ℤ) ∣ u i.succ - D.κ i * u 0) ∧
      n = t3MaxAbs u} (D.lat : ℤ) := by
  obtain ⟨-, -, -, -, hl, hu, hm, hc, -, h2, hp, -⟩ := T3.facts D hD
  refine ⟨⟨_, hu, T3.latB_sound D _ hl, by rw [hm]⟩, ?_⟩
  rintro n ⟨u, hne, hL, rfl⟩
  exact T3.latchk_sound D hp hc h2 u hne hL

theorem t3s4_tab (D : T3Design) (hD : D ∈ t3s4Table) :
    (D.tab : ℝ) / 1000 ≤ ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 4 : ℝ)) < ((D.tab : ℝ) + 1) / 1000 ∧
      D.lat ≤ D.M + 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hp, h1, h2, hl, hM, -⟩ := T3.facts D hD
  exact ⟨(T3.tab_real D.p D.M D.tab hp hM h1 h2).1, (T3.tab_real D.p D.M D.tab hp hM h1 h2).2, hl⟩

theorem t3s4_main (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (h83 : p ≤ 83) :
    ∃ D ∈ t3s4Table, D.p = p ∧ 2 ≤ D.M ∧ ∀ k, 1 ≤ k →
      (∃ C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p),
        IsT3skel D k C ∧ IsNet0 4 D.p (4 * k + 1) (digPoint D.p (4 * k + 1) C)) ∧
      ∀ C : Fin 4 → Matrix (Fin (4 * k + 1)) (Fin (4 * k + 1)) (ZMod D.p), IsT3skel D k C →
        ∀ v w : Fin (4 * k + 1) → ZMod D.p, v ≠ w →
          ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 4 : ℝ)) * ((D.p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ))
            ≤ Real.sqrt (∑ c, ((cres (D.p ^ (4 * k + 1))
                ((digPoint D.p (4 * k + 1) C v c : ℤ) - (digPoint D.p (4 * k + 1) C w c : ℤ)) : ℝ)
                / (D.p : ℝ) ^ (4 * k + 1)) ^ 2) := by
  obtain ⟨D, hD, hDp⟩ := t3s4_table.2.2.2.1 p hp (by omega) h83
  refine ⟨D, hD, hDp, (T3.facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega), fun k hk =>
    ⟨t3s4_net D hD k hk, fun C hC v w hvw => t3s4_sep_real D hD k hk C hC v w hvw⟩⟩

theorem dim4_one (p : ℕ) [Fact p.Prime] (h23 : 23 ≤ p) (h83 : p ≤ 83) :
    ∃ Cp : ℝ, ∀ m : ℕ, 5 ≤ m → m % 4 = 1 →
      ∃ C : Fin 4 → Matrix (Fin m) (Fin m) (ZMod p), IsNet0 4 p m (digPoint p m C) ∧
        (∀ v w : Fin m → ZMod p, v ≠ w →
          1 / Real.sqrt 31 * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) ≤
            Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ m) ^ 2)) ∧
        ∀ y : Fin 4 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
          Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
            Cp * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨D, hD, hDp⟩ := t3s4_table.2.2.2.1 p hpp (by omega) h83
  subst hDp
  refine ⟨2 * (D.p : ℝ) ^ (1 / 4 : ℝ), fun m hm5 hm1 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨C, hC, hnet⟩ := t3s4_net D hD k hk
  refine ⟨C, hnet, fun v w hvw => ?_, fun y hy => cover_4k1 hpp.one_lt.le _ hnet y hy⟩
  have h := t3s4_sep_real D hD k hk C hC v w hvw
  have htab := (t3s4_tab D hD).1
  have h180 := (T3.facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h23
  have h180' : (180 : ℝ) / 1000 ≤ (D.tab : ℝ) / 1000 := by
    have : (180 : ℝ) ≤ D.tab := by exact_mod_cast h180
    linarith
  have hN : (0 : ℝ) ≤ ((D.p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ)) := by positivity
  calc 1 / Real.sqrt 31 * ((D.p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ))
      ≤ ((D.M : ℝ) - 1) * (D.p : ℝ) ^ (-(3 / 4 : ℝ)) * ((D.p : ℝ) ^ (4 * k + 1)) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (T3.inv_sqrt31_le.trans (h180'.trans htab)) hN
    _ ≤ _ := h

theorem dim4_full (p : ℕ) [Fact p.Prime] (h23 : 23 ≤ p) (h83 : p ≤ 83) :
    ∃ Cp : ℝ, ∀ m : ℕ, 3 ≤ m → m ≠ 4 →
      ∃ C : Fin 4 → Matrix (Fin m) (Fin m) (ZMod p), IsNet0 4 p m (digPoint p m C) ∧
        (∀ v w : Fin m → ZMod p, v ≠ w →
          1 / Real.sqrt 31 * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) ≤
            Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ m) ^ 2)) ∧
        ∀ y : Fin 4 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
          Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
            Cp * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C1, h1⟩ := dim4 p h23 h83
  obtain ⟨C2, h2⟩ := dim4_one p h23 h83
  refine ⟨max C1 C2, fun m hm3 hm4 => ?_⟩
  have hpp : p.Prime := Fact.out
  have hN : (0 : ℝ) ≤ ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) := by
    have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    positivity
  by_cases hm : m % 4 = 1
  · obtain ⟨C, hnet, hsep, hcov⟩ := h2 m (by omega) hm
    refine ⟨C, hnet, hsep, fun y hy => ?_⟩
    obtain ⟨v, hv⟩ := hcov y hy
    exact ⟨v, hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hN)⟩
  · obtain ⟨C, hnet, hsep, hcov⟩ := h1 m hm3 hm4 hm
    refine ⟨C, hnet, hsep, fun y hy => ?_⟩
    obtain ⟨v, hv⟩ := hcov y hy
    exact ⟨v, hv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN)⟩

end Z3NetF.Proofs
