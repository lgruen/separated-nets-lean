module
public import Mathlib
public import Z3Net.SkSepS2
public import Z3Net.SkGLat
public import Z3Net.SkGGauss

@[expose] public section

/-!
# Entry S2, separation (`thm:S2`(1)–(3))

`S2_core` with the lattice minima of `lem:skellat`: `λ_∞ ≥ ρ - 1` (`skellat_T`, `s = 4`, `F = 2`)
and `λ_∞ ≥ B(p) + 1` (`skellat_G` at `c = cG (B p)`, `s ≥ 5`; its hypotheses follow from the
definition of `B(p)`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

/-- Real form of an integer separation bound `B² p^(2e) ≤ N² δ²`: `B' (p^e / N) ≤ δ` for `B' ≤ B`. -/
lemma real_of_int_sep {s : ℕ} (p m e B : ℕ) (hp : 1 ≤ p) (X Y : Fin s → ℕ) (Br : ℝ) (hBr : Br ≤ B)
    (hZ : B ^ 2 * p ^ (2 * e) ≤ torusDist2 (p ^ m) X Y) :
    Br * ((p : ℝ) ^ e / (p : ℝ) ^ m) ≤
      Real.sqrt (∑ c, ((cres (p ^ m) ((X c : ℤ) - (Y c : ℤ)) : ℝ) / (p : ℝ) ^ m) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rcases le_or_gt Br 0 with h0 | h0
  · have : 0 ≤ (p : ℝ) ^ e / (p : ℝ) ^ m := by positivity
    have := Real.sqrt_nonneg (∑ c, ((cres (p ^ m) ((X c : ℤ) - (Y c : ℤ)) : ℝ) / (p : ℝ) ^ m) ^ 2)
    nlinarith
  apply sqrt_bound _ _ _ _ (by positivity)
  unfold torusDist2 at hZ
  have h1 := (Nat.cast_le (α := ℝ)).mpr hZ
  push_cast at h1
  have h2 : Br ^ 2 ≤ (B : ℝ) ^ 2 := pow_le_pow_left₀ h0.le hBr 2
  have h3 : (0 : ℝ) ≤ ((p : ℝ) ^ e) ^ 2 := by positivity
  calc Br ^ 2 * ((p : ℝ) ^ e) ^ 2 ≤ (B : ℝ) ^ 2 * ((p : ℝ) ^ e) ^ 2 := mul_le_mul_of_nonneg_right h2 h3
    _ = (B : ℝ) ^ 2 * (p : ℝ) ^ (2 * e) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := h1

lemma two_le_rhoT (p : ℕ) (hp : 5 ≤ p) : 2 ≤ rhoT p :=
  Nat.le_findGreatest (P := fun ρ => ρ ^ 2 < p + 4) (by omega) (by norm_num; omega)

lemma rhoT_sq (p : ℕ) (hp : 5 ≤ p) : rhoT p ^ 2 < p + 4 :=
  Nat.findGreatest_spec (P := fun ρ => ρ ^ 2 < p + 4) (m := 2) (by omega) (by norm_num; omega)

end SkSep

open SkSep

/-- **`thm:S2`(1)**, separation (integer form). -/
theorem S2_sep4 (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (rhoT p - 4) ^ 2 * p ^ (2 * (3 * k + 1)) ≤
      torusDist2 (p ^ (4 * k + 2)) (digPoint p (4 * k + 2) C v) (digPoint p (4 * k + 2) C w) := by
  have hρ2 := two_le_rhoT p hp
  have hρp := rhoT_sq p hp
  have hcore := S2_core 4 p k (rhoT p - 1) Fact.out le_rfl hk {1} (by decide) (by decide)
    (fun x z hz hne => by
      have h0 := hz 0
      have h1 := hz 1
      simp only [S2A, if_true, AT, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
        Fin.val_zero, Fin.val_succ, Fin.val_one] at h0 h1
      norm_num at h0 h1
      have hc : (((rhoT p - 1 : ℕ)) : ℤ) = (rhoT p : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ rhoT p)]; ring
      rw [hc]
      rcases skellat_T p (rhoT p) hρ2 hρp x z (by simpa [add_comm] using h0) (by simpa using h1) hne with
        h | h | h | h
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inr (Or.inr ⟨1, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    C hC v w hvw
  have e1 : rhoT p - 1 - Fs 4 - 1 = rhoT p - 4 := by simp only [Fs]; omega
  rw [e1] at hcore
  exact hcore

/-- **`thm:S2`(1)**, separation (real form). -/
theorem S2_sep4_real (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * ((p : ℝ) ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (4 * k + 2))
          ((digPoint p (4 * k + 2) C v c : ℤ) - (digPoint p (4 * k + 2) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (4 * k + 2)) ^ 2) := by
  have hsc := rpow_scale p 4 2 k (by omega) (by norm_num) (by norm_num) (by omega)
  have e1 : (-(((4 - 2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) = -(1 / 2 : ℝ) := by norm_num
  have e2 : (-(1 / ((4 : ℕ) : ℝ))) = -(1 / 4 : ℝ) := by norm_num
  rw [e1, e2] at hsc
  rw [mul_assoc, hsc]
  have hZ := S2_sep4 p k hp hk C hC v w hvw
  rw [show 2 * (3 * k + 1) = 2 * (4 * k + 2 - (k + 1)) by omega] at hZ
  refine real_of_int_sep p _ _ _ (by omega) _ _ _ ?_ hZ
  have : (rhoT p : ℝ) - 4 ≤ ((rhoT p - 4 : ℕ) : ℝ) := by
    rcases le_or_gt 4 (rhoT p) with h | h
    · push_cast [Nat.cast_sub h]; rfl
    · have : (rhoT p : ℝ) < 4 := by exact_mod_cast h
      have : (0 : ℝ) ≤ ((rhoT p - 4 : ℕ) : ℝ) := by positivity
      linarith
  exact this

namespace SkSep

/-- The hypotheses of `skellat_G` at `c = cG (B p)` hold whenever `B(p) ≥ 1`. -/
lemma skellatG_at_Bp (s p : ℕ) (hs : 5 ≤ s) (hB : 1 ≤ Bp s p) (x : Fin (s - 2) → ℤ) (z : Fin 2 → ℤ)
    (hz : ∀ i, (p : ℤ) ∣ z i - ∑ d : Fin (s - 2), S2A s p i (d : ℕ) * x d) (hne : ¬(x = 0 ∧ z = 0)) :
    ((Bp s p + 1 : ℕ) : ℤ) ≤ |z 0| ∨ ((Bp s p + 1 : ℕ) : ℤ) ≤ |z 1| ∨
      ∃ d, ((Bp s p + 1 : ℕ) : ℤ) ≤ |x d| := by
  set B := Bp s p with hBdef
  have hS : S2A s p = AG s B := by unfold S2A; rw [if_neg (by omega)]
  rw [hS] at hz
  have hc1 : Real.sqrt 2 * (B : ℝ) < (cG B 0 : ℝ) := by
    have h := SkG.cG0_sq_gt B
    have hpos : (0 : ℝ) < (cG B 0 : ℝ) := by exact_mod_cast SkG.cG_pos B 0
    have h' : 2 * (B : ℝ) ^ 2 < (cG B 0 : ℝ) ^ 2 := by exact_mod_cast h
    have e : Real.sqrt 2 * (B : ℝ) = Real.sqrt (2 * (B : ℝ) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    rw [e, Real.sqrt_lt' hpos]
    exact h'
  have hc : ∀ l, 1 ≤ l → l + 2 ≤ s - 2 → (B : ℤ) < cG B l ^ 2 + 1 := by
    intro l hl _
    have := SkG.cGj_sq_gt B l (by omega)
    linarith
  have hspec := SkG.Bp_spec s p hB
  have hp : ∀ i : Fin 2, (B : ℤ) * (1 + ∑ d ∈ range (s - 2), |gaussA (s - 2) (cG B) i d|) < p := by
    intro i
    have hrow : ∑ d ∈ range (s - 2), |gaussA (s - 2) (cG B) i d| ≤ normA s B := by
      unfold normA AG
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hB0 : (0 : ℤ) ≤ B := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add_left hrow 1) hB0
    linarith
  have h := skellat_G (s - 2) p B (by omega) hB (cG B) hc1 hc hp x z (fun i => hz i) hne
  push_cast
  exact h

end SkSep

/-- The two complementary halves have at most `F - 1` elements. -/
lemma SkSep.card_D (s : ℕ) (hs : 5 ≤ s) (D1 : Finset ℕ) (hD1 : D1 ⊆ range (s - 2))
    (hD1c : D1.card = (s - 2) / 2) :
    ((range (s - 2)).filter (· ∈ D1)).card + 1 ≤ Fs s ∧
      ((range (s - 2)).filter (· ∉ D1)).card + 1 ≤ Fs s := by
  have e1 : (range (s - 2)).filter (· ∈ D1) = D1 := by
    ext d; simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨mem_range.mp (hD1 h), h⟩⟩
  have e2 := Finset.card_filter_add_card_filter_not (s := range (s - 2)) (fun d => d ∈ D1)
  rw [e1, card_range] at e2
  rw [e1]
  unfold Fs
  omega

/-- **`thm:S2`(2), (3)**, separation (integer form). -/
theorem S2_sep (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    (Bp s p - Fs s) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
      torusDist2 (p ^ (s * k + (s - 2))) (digPoint p (s * k + (s - 2)) C v)
        (digPoint p (s * k + (s - 2)) C w) := by
  rcases Nat.eq_zero_or_pos (Bp s p) with h0 | hB
  · have : Bp s p - Fs s = 0 := by omega
    rw [this]; simp
  obtain ⟨c1, c2⟩ := SkSep.card_D s hs D1 hD1 hD1c
  have hcore := S2_core s p k (Bp s p + 1) Fact.out (by omega) hk D1 c1 c2
    (fun x z hz hne => skellatG_at_Bp s p hs hB x z hz hne) C hC v w hvw
  rw [show Bp s p + 1 - Fs s - 1 = Bp s p - Fs s by omega] at hcore
  exact hcore

/-- **`thm:S2`(2), (3)**, separation (real form). -/
theorem S2_sep_real (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    ((Bp s p : ℝ) - Fs s) * (p : ℝ) ^ (-(2 / (s : ℝ))) *
        ((p : ℝ) ^ (s * k + (s - 2))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 2)))
          ((digPoint p (s * k + (s - 2)) C v c : ℤ) - (digPoint p (s * k + (s - 2)) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 2))) ^ 2) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hkm : k + 1 ≤ s * k + (s - 2) := by nlinarith
  have hsc := rpow_scale p s (s - 2) k (by omega) (by omega) (Nat.sub_le _ _) hkm
  have e1 : ((s - (s - 2) : ℕ) : ℝ) = 2 := by rw [show s - (s - 2) = 2 by omega]; norm_num
  rw [e1] at hsc
  rw [mul_assoc, hsc]
  have hZ := S2_sep s p k hs hk D1 hD1 hD1c C hC v w hvw
  have hmk : (s - 1) * k + s - 3 = s * k + (s - 2) - (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 5 := ⟨s - 5, by omega⟩
    have e1 : (t + 5) * k = t * k + 5 * k := by ring
    have e2 : (t + 5 - 1) * k = t * k + 4 * k := by rw [show t + 5 - 1 = t + 4 by omega]; ring
    omega
  rw [hmk] at hZ
  refine real_of_int_sep p _ _ _ (by omega) _ _ _ ?_ hZ
  rcases le_or_gt (Fs s) (Bp s p) with h | h
  · push_cast [Nat.cast_sub h]; rfl
  · have : (Bp s p : ℝ) < Fs s := by exact_mod_cast h
    have : (0 : ℝ) ≤ ((Bp s p - Fs s : ℕ) : ℝ) := by positivity
    linarith

end Z3NetF.Proofs
