module
public import Mathlib
public import Z3Net.S2Defs
public import Z3Net.SkGBase

@[expose] public section

/-!
# Entry S2, `thm:S2`(2): the thresholds `B(p) ≥ F + 1 ⟺ p > 132, 440, 2170, 6095`

* `BnormA_sq_ge`: `(B ‖A(B)‖)² ≥ 2 B^s` (from `‖A_j‖₁ ≥ |Ω_{r-1}|` and `N(Ω_{r-1}) ≥ 2 B^r`);
* `g(B) = B (1 + ‖A(B)‖) ≥ g(F + 1)` for `B ≥ F + 1` (`s = 5..8`): kernel evaluation (`decide`)
  for `F + 1 ≤ B < B₁` and the bound above for `B ≥ B₁` (`B₁ = 7, 7, 9, 9`);
* `S2_thr`.
-/

namespace Z3NetF.Proofs

open Finset

namespace SkG

/-- `(B ‖A(B)‖)² ≥ 2 B^s` for `s ≥ 5`. -/
lemma BnormA_sq_ge (s B : ℕ) (hs : 5 ≤ s) : 2 * (B : ℤ) ^ s ≤ ((B : ℤ) * normA s B) ^ 2 := by
  have hT := normA_ge s B (by omega)
  have hN := norm_le_abs_sq (gaussOmega (cG B) (s - 3))
  have hG := norm_gaussOmega_ge B (s - 4)
  rw [show s - 4 + 1 = s - 3 by omega, show s - 4 + 2 = s - 2 by omega] at hG
  have h0 : 0 ≤ |(gaussOmega (cG B) (s - 3)).re| + |(gaussOmega (cG B) (s - 3)).im| := by
    positivity
  have h1 : 2 * (B : ℤ) ^ (s - 2) ≤ normA s B ^ 2 := by nlinarith
  calc 2 * (B : ℤ) ^ s = (B : ℤ) ^ 2 * (2 * (B : ℤ) ^ (s - 2)) := by
        rw [← mul_assoc, mul_comm ((B : ℤ) ^ 2) 2, mul_assoc, ← pow_add,
          show 2 + (s - 2) = s by omega]
    _ ≤ (B : ℤ) ^ 2 * normA s B ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((B : ℤ) * normA s B) ^ 2 := by ring

/-- For `B ≥ B₁` with `T² ≤ 2 B₁^s`: `T ≤ B (1 + ‖A(B)‖)`. -/
lemma g_ge_big (s B B1 T : ℕ) (hs : 5 ≤ s) (hB : B1 ≤ B) (hT : T ^ 2 ≤ 2 * B1 ^ s) :
    (T : ℤ) ≤ B * (1 + normA s B) := by
  have h1 := BnormA_sq_ge s B hs
  have h2 : (B1 : ℤ) ^ s ≤ (B : ℤ) ^ s := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hB) s
  have hT' : (T : ℤ) ^ 2 ≤ 2 * (B1 : ℤ) ^ s := by exact_mod_cast hT
  have hn := normA_nonneg s B
  have h3 : (T : ℤ) ^ 2 ≤ ((B : ℤ) * normA s B) ^ 2 := by linarith
  have h4 : (T : ℤ) ≤ B * normA s B :=
    (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg (by positivity) hn) two_ne_zero).mp h3
  nlinarith

/-- Explicit parameter sequence `c_0 = a`, `c_j = b` (`j ≥ 1`). -/
def cc (a b : ℤ) : ℕ → ℤ := fun j => if j = 0 then a else b

lemma sqrt_eq_of (n a : ℕ) (h1 : a * a ≤ n) (h2 : n < (a + 1) * (a + 1)) : Nat.sqrt n = a :=
  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr h2)) (Nat.le_sqrt.mpr h1)

lemma cG_eq_cc (B a b : ℕ) (ha : Nat.sqrt (2 * B ^ 2) = a) (hb : Nat.sqrt B = b) :
    cG B = cc ((a + 1 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ) := by
  funext j
  unfold cG cc
  split_ifs <;> simp [ha, hb]

lemma normA_cc (s B a b : ℕ) (ha : Nat.sqrt (2 * B ^ 2) = a) (hb : Nat.sqrt B = b) :
    normA s B = max (∑ d ∈ range (s - 2), |gaussA (s - 2) (cc ((a + 1 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ)) 0 d|)
      (∑ d ∈ range (s - 2), |gaussA (s - 2) (cc ((a + 1 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ)) 1 d|) := by
  unfold normA AG
  rw [cG_eq_cc B a b ha hb]

lemma sq4 : Nat.sqrt (2 * 4 ^ 2) = 5 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma sq5 : Nat.sqrt (2 * 5 ^ 2) = 7 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma sq6 : Nat.sqrt (2 * 6 ^ 2) = 8 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma sq7 : Nat.sqrt (2 * 7 ^ 2) = 9 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma sq8 : Nat.sqrt (2 * 8 ^ 2) = 11 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma r4 : Nat.sqrt 4 = 2 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma r5 : Nat.sqrt 5 = 2 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma r6 : Nat.sqrt 6 = 2 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma r7 : Nat.sqrt 7 = 2 := sqrt_eq_of _ _ (by norm_num) (by norm_num)
lemma r8 : Nat.sqrt 8 = 2 := sqrt_eq_of _ _ (by norm_num) (by norm_num)

/-- The threshold criterion: if `g(F₁) = T` and `g(B) ≥ T` for all `B ≥ F₁`, then
`F₁ ≤ B(p) ⟺ T < p`. -/
lemma thr_iff (s p F1 T : ℕ) (hF1 : 1 ≤ F1) (hval : (F1 : ℤ) * (1 + normA s F1) = T)
    (hlow : ∀ B, F1 ≤ B → (T : ℤ) ≤ B * (1 + normA s B)) : F1 ≤ Bp s p ↔ T < p := by
  constructor
  · intro h
    have h1 := Bp_spec s p (by omega)
    have h2 := hlow _ h
    exact_mod_cast lt_of_le_of_lt h2 h1
  · intro h
    exact le_Bp s p F1 hF1 (by rw [hval]; exact_mod_cast h)

lemma thr5 (p : ℕ) : 4 ≤ Bp 5 p ↔ 132 < p := by
  refine thr_iff 5 p 4 132 (by norm_num) ?_ ?_
  · rw [normA_cc 5 4 5 2 sq4 r4]; decide
  · intro B hB
    rcases (show B = 4 ∨ B = 5 ∨ B = 6 ∨ 7 ≤ B by omega) with h | h | h | h
    · subst h; rw [normA_cc 5 4 5 2 sq4 r4]; decide
    · subst h; rw [normA_cc 5 5 7 2 sq5 r5]; decide
    · subst h; rw [normA_cc 5 6 8 2 sq6 r6]; decide
    · exact g_ge_big 5 B 7 132 (by norm_num) h (by norm_num)

lemma thr6 (p : ℕ) : 4 ≤ Bp 6 p ↔ 440 < p := by
  refine thr_iff 6 p 4 440 (by norm_num) ?_ ?_
  · rw [normA_cc 6 4 5 2 sq4 r4]; decide
  · intro B hB
    rcases (show B = 4 ∨ B = 5 ∨ B = 6 ∨ 7 ≤ B by omega) with h | h | h | h
    · subst h; rw [normA_cc 6 4 5 2 sq4 r4]; decide
    · subst h; rw [normA_cc 6 5 7 2 sq5 r5]; decide
    · subst h; rw [normA_cc 6 6 8 2 sq6 r6]; decide
    · exact g_ge_big 6 B 7 440 (by norm_num) h (by norm_num)

lemma thr7 (p : ℕ) : 5 ≤ Bp 7 p ↔ 2170 < p := by
  refine thr_iff 7 p 5 2170 (by norm_num) ?_ ?_
  · rw [normA_cc 7 5 7 2 sq5 r5]; decide
  · intro B hB
    rcases (show B = 5 ∨ B = 6 ∨ B = 7 ∨ B = 8 ∨ 9 ≤ B by omega) with h | h | h | h | h
    · subst h; rw [normA_cc 7 5 7 2 sq5 r5]; decide
    · subst h; rw [normA_cc 7 6 8 2 sq6 r6]; decide
    · subst h; rw [normA_cc 7 7 9 2 sq7 r7]; decide
    · subst h; rw [normA_cc 7 8 11 2 sq8 r8]; decide
    · exact g_ge_big 7 B 9 2170 (by norm_num) h (by norm_num)

lemma thr8 (p : ℕ) : 5 ≤ Bp 8 p ↔ 6095 < p := by
  refine thr_iff 8 p 5 6095 (by norm_num) ?_ ?_
  · rw [normA_cc 8 5 7 2 sq5 r5]; decide
  · intro B hB
    rcases (show B = 5 ∨ B = 6 ∨ B = 7 ∨ B = 8 ∨ 9 ≤ B by omega) with h | h | h | h | h
    · subst h; rw [normA_cc 8 5 7 2 sq5 r5]; decide
    · subst h; rw [normA_cc 8 6 8 2 sq6 r6]; decide
    · subst h; rw [normA_cc 8 7 9 2 sq7 r7]; decide
    · subst h; rw [normA_cc 8 8 11 2 sq8 r8]; decide
    · exact g_ge_big 8 B 9 6095 (by norm_num) h (by norm_num)

end SkG

theorem S2_thr (s p : ℕ) (hs5 : 5 ≤ s) (hs8 : s ≤ 8) :
    (Fs s + 1 ≤ Bp s p ↔ S2thr s < p) ∧ (p.Prime → (S2thr s < p ↔ S2pthr s ≤ p)) := by
  interval_cases s
  · refine ⟨by simpa [Fs, S2thr] using SkG.thr5 p, fun hp => ?_⟩
    show (132 < p ↔ 137 ≤ p)
    constructor
    · intro h; by_contra h'; interval_cases p <;> norm_num at hp
    · intro h; omega
  · refine ⟨by simpa [Fs, S2thr] using SkG.thr6 p, fun hp => ?_⟩
    show (440 < p ↔ 443 ≤ p)
    constructor
    · intro h; by_contra h'; interval_cases p <;> norm_num at hp
    · intro h; omega
  · refine ⟨by simpa [Fs, S2thr] using SkG.thr7 p, fun hp => ?_⟩
    show (2170 < p ↔ 2179 ≤ p)
    constructor
    · intro h; by_contra h'; interval_cases p <;> norm_num at hp
    · intro h; omega
  · refine ⟨by simpa [Fs, S2thr] using SkG.thr8 p, fun hp => ?_⟩
    show (6095 < p ↔ 6101 ≤ p)
    constructor
    · intro h; by_contra h'; interval_cases p <;> norm_num at hp
    · intro h; omega

end Z3NetF.Proofs
