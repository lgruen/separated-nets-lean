module
public import Mathlib
public import Z3Net.SkSepGraph

@[expose] public section

/-!
# Entry Skel, separation part 3: `prop:S1E` (Euclidean form of `thm:S1`(1))

For a graph form with depths `(k+1, …, k+1, k)` and skeleton digit `S_z = ∑_d κ_d x_{d,k}`
(`IsS1Kskel`) the centred difference `a ≠ 0` of the fine positions of two distinct points lies in
`Λ_κ` (`InLatK`); `lem:skelred`(i) in each coordinate gives `cres_c ≥ (|a_c| - 1)₊ f`, so the
squared distance is at least `f² ‖(|a| - 𝟏)₊‖² ≥ f² λ_jit(κ)²` (`S1E_sep`, `S1E_sep_real`); and
`‖(|a| - 𝟏)₊‖₂ ≥ ‖a‖₂ - √s` (`S1E_lam2`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

open Z3NetKN.Geom (vz)

/-- `cres_c ≥ (|a_c| - 1)₊ f` for every coordinate, summed: `f² ‖(|a| - 𝟏)₊‖² ≤ N² δ²`. -/
lemma jit_le_torus {s : ℕ} (p m k : ℕ) (hp : 1 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p) :
    jitNorm2 (aDiff p k C v w) * p ^ (2 * (m - (k + 1))) ≤
      torusDist2 (p ^ m) (digPoint p m C v) (digPoint p m C w) := by
  unfold jitNorm2 torusDist2
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  have hb := skelred_coord_dig p m k hp hkm C v w c
  set f := p ^ (m - (k + 1))
  set cr := cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ))
  have h1 : ((aDiff p k C v w c).natAbs - 1) * f ≤ cr := by
    rcases Nat.eq_zero_or_pos (aDiff p k C v w c).natAbs with h0 | h0
    · simp [h0]
    · have : ((((aDiff p k C v w c).natAbs - 1) * f : ℕ) : ℤ) ≤ cr := by
        push_cast [Nat.cast_sub h0, Int.natCast_natAbs]
        exact hb
      exact_mod_cast this
  calc ((aDiff p k C v w c).natAbs - 1) ^ 2 * p ^ (2 * (m - (k + 1)))
      = (((aDiff p k C v w c).natAbs - 1) * f) ^ 2 := by rw [mul_pow, ← pow_mul, Nat.mul_comm 2]
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1 2

variable {s p k : ℕ} {κ : ℕ → ZMod p}
  {C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p)}

lemma hkm_S1 (hs : 2 ≤ s) : k + 1 ≤ s * k + (s - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  have : (t + 2) * k = t * k + 2 * k := by ring
  omega

/-- The centred difference lies in `Λ_κ`. -/
lemma aDiff_inLat [NeZero p] (hs : 2 ≤ s) (hC : IsS1Kskel s p k κ C)
    (v w : Fin (s * k + (s - 1)) → ZMod p) : InLatK p κ (aDiff p k C v w) := by
  have hkm := hkm_S1 (k := k) hs
  have hr : s - 1 ≤ s := Nat.sub_le s 1
  set a := aDiff p k C v w with ha
  have hfull : ∀ d : Fin s, (d : ℕ) + 1 < s → ((a d : ℤ) : ZMod p) =
      vz w (skOff (s - 1) k (d : ℕ) + k) - vz v (skOff (s - 1) k (d : ℕ) + k) := by
    intro d hd
    have hdep : k < skDepth (s - 1) k d := by unfold skDepth; rw [if_pos (by omega)]; omega
    rw [ha, aDiff_cast k hkm, graph_digit hr hC.1 w d k hdep, graph_digit hr hC.1 v d k hdep]
  set zc : Fin s := ⟨s - 1, by omega⟩ with hzc
  have hz : ((a zc : ℤ) : ZMod p) = ∑ d : Fin s, if (d : ℕ) + 1 < s then κ d * ((a d : ℤ) : ZMod p) else 0 := by
    rw [ha, aDiff_cast k hkm, row_diff hr _ v w k (by omega)]
    refine sum_congr rfl fun d _ => ?_
    have hent : ∀ l < skDepth (s - 1) k d, ent (C zc) k (skOff (s - 1) k (d : ℕ) + l) =
        if (d : ℕ) + 1 < s ∧ l = k then κ d else 0 := fun l hl => hC.2 zc d (by simp [hzc]; omega) l hl
    by_cases hd : (d : ℕ) + 1 < s
    · rw [if_pos hd, ← ha, hfull d hd]
      have hdep : k < skDepth (s - 1) k d := by unfold skDepth; rw [if_pos (by omega)]; omega
      rw [sum_eq_single k]
      · rw [hent k hdep, if_pos ⟨hd, rfl⟩]
      · intro l hl hlk
        simp only [mem_range] at hl
        rw [hent l hl, if_neg (fun h => hlk h.2), zero_mul]
      · intro h; exact absurd (mem_range.mpr hdep) h
    · rw [if_neg hd]
      refine sum_eq_zero fun l hl => ?_
      simp only [mem_range] at hl
      rw [hent l hl, if_neg (fun h => hd h.1), zero_mul]
  unfold InLatK
  have e : ∀ c : Fin s, (if (c : ℕ) + 1 < s then κ c * ((a c : ℤ) : ZMod p) else -((a c : ℤ) : ZMod p)) =
      (if (c : ℕ) + 1 < s then κ c * ((a c : ℤ) : ZMod p) else 0) +
        (if (c : ℕ) + 1 < s then 0 else -((a c : ℤ) : ZMod p)) := by
    intro c; split_ifs <;> simp
  rw [sum_congr rfl fun c _ => e c, sum_add_distrib, ← hz, sum_eq_single zc]
  · rw [if_neg (by simp [hzc]; omega)]; ring
  · intro c _ hc
    rw [if_pos]
    have : (c : ℕ) ≠ s - 1 := fun h => hc (Fin.ext (by simp [hzc, h]))
    omega
  · intro h; exact absurd (mem_univ _) h

end SkSep

open SkSep

/-- **`prop:S1E`, separation (integer form).** -/
theorem S1E_sep (p : ℕ) [Fact p.Prime] (s k : ℕ) (hs : 2 ≤ s) (κ : ℕ → ZMod p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1Kskel s p k κ C) (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    lamJit2 s p κ * p ^ (2 * ((s - 1) * (k + 1) - 1)) ≤
      torusDist2 (p ^ (s * k + (s - 1))) (digPoint p (s * k + (s - 1)) C v)
        (digPoint p (s * k + (s - 1)) C w) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have : NeZero p := ⟨by omega⟩
  have hkm := hkm_S1 (k := k) hs
  have hmk : s * k + (s - 1) - (k + 1) = (s - 1) * (k + 1) - 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    simp only [show t + 2 - 1 = t + 1 by omega]
    have e1 : (t + 2) * k = t * k + 2 * k := by ring
    have e2 : (t + 1) * (k + 1) = t * k + t + k + 1 := by ring
    omega
  have hlat := aDiff_inLat hs hC v w
  obtain ⟨c, hc⟩ := ne_zero_of_ne (Nat.sub_le s 1) hC.1 hkm v w hvw
  have hne : aDiff p k C v w ≠ 0 := fun h => hc (by rw [h]; rfl)
  have hle : lamJit2 s p κ ≤ jitNorm2 (aDiff p k C v w) := Nat.sInf_le ⟨_, hlat, hne, rfl⟩
  have := jit_le_torus p (s * k + (s - 1)) k (by omega) hkm C v w
  rw [hmk] at this
  exact le_trans (Nat.mul_le_mul_right _ hle) this

/-- **`prop:S1E`, separation (real form)**. -/
theorem S1E_sep_real (p : ℕ) [Fact p.Prime] (s k : ℕ) (hs : 2 ≤ s) (κ : ℕ → ZMod p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1Kskel s p k κ C) (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    Real.sqrt (lamJit2 s p κ) * (p : ℝ) ^ (-(1 / (s : ℝ))) *
        ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
          ((digPoint p (s * k + (s - 1)) C v c : ℤ) - (digPoint p (s * k + (s - 1)) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hkm := hkm_S1 (k := k) hs
  have hsc := rpow_scale p s (s - 1) k (by omega) (by omega) (Nat.sub_le s 1) hkm
  rw [show ((s - (s - 1) : ℕ) : ℝ) = 1 by rw [show s - (s - 1) = 1 by omega]; simp] at hsc
  rw [mul_assoc, hsc]
  apply sqrt_bound _ _ _ _ (by positivity)
  have hZ := S1E_sep p s k hs κ C hC v w hvw
  have hmk : s * k + (s - 1) - (k + 1) = (s - 1) * (k + 1) - 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    simp only [show t + 2 - 1 = t + 1 by omega]
    have e1 : (t + 2) * k = t * k + 2 * k := by ring
    have e2 : (t + 1) * (k + 1) = t * k + t + k + 1 := by ring
    omega
  unfold torusDist2 at hZ
  have := (Nat.cast_le (α := ℝ)).mpr hZ
  push_cast at this
  rw [Real.sq_sqrt (by positivity), hmk, ← pow_mul, Nat.mul_comm (_ - 1) 2]
  exact this

/-- **`prop:S1E`**, the second inequality: `λ_jit(κ) ≥ λ₂(Λ_κ) - √s`. -/
theorem S1E_lam2 (p : ℕ) [Fact p.Prime] (s : ℕ) (κ : ℕ → ZMod p) :
    Real.sqrt (lam2Sq s p κ) - Real.sqrt s ≤ Real.sqrt (lamJit2 s p κ) := by
  set S := {n | ∃ a : Fin s → ℤ, InLatK p κ a ∧ a ≠ 0 ∧ jitNorm2 a = n} with hS
  rcases Set.eq_empty_or_nonempty S with h0 | hne
  · have e2 : {n | ∃ a : Fin s → ℤ, InLatK p κ a ∧ a ≠ 0 ∧ ∑ c, (a c).natAbs ^ 2 = n} = ∅ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, h1, h2, -⟩
      have : jitNorm2 a ∈ S := ⟨a, h1, h2, rfl⟩
      rw [h0] at this; exact this
    have : lam2Sq s p κ = 0 := by unfold lam2Sq; rw [e2, Nat.sInf_empty]
    rw [this]; simp only [Nat.cast_zero, Real.sqrt_zero, zero_sub]
    have := Real.sqrt_nonneg (lamJit2 s p κ : ℝ)
    have := Real.sqrt_nonneg (s : ℝ)
    linarith
  obtain ⟨a, hlat, ha0, hJ⟩ := Nat.sInf_mem hne
  have hJ' : lamJit2 s p κ = jitNorm2 a := hJ.symm
  have hle : lam2Sq s p κ ≤ ∑ c, (a c).natAbs ^ 2 := Nat.sInf_le ⟨a, hlat, ha0, rfl⟩
  have hLr : (lam2Sq s p κ : ℝ) ≤ ∑ c, ((a c).natAbs : ℝ) ^ 2 := by exact_mod_cast hle
  set x : Fin s → ℝ := fun c => ((a c).natAbs : ℝ)
  set b : Fin s → ℝ := fun c => (((a c).natAbs - 1 : ℕ) : ℝ)
  have hJr : (lamJit2 s p κ : ℝ) = ∑ c, b c ^ 2 := by rw [hJ']; unfold jitNorm2; push_cast; rfl
  have hxb : ∀ c, x c ≤ b c + 1 := by
    intro c
    have : (a c).natAbs ≤ ((a c).natAbs - 1) + 1 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this; exact this
  have hb0 : ∀ c, 0 ≤ b c := fun c => by positivity
  have hx0 : ∀ c, 0 ≤ x c := fun c => by positivity
  set J := ∑ c, b c ^ 2
  have hJ0 : 0 ≤ J := by positivity
  have hCS : (∑ c, b c) ^ 2 ≤ J * s := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ b (fun _ => (1 : ℝ))
    simpa using this
  have hsb : ∑ c, b c ≤ Real.sqrt J * Real.sqrt s := by
    rw [← Real.sqrt_mul hJ0]
    have h := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_sq (Finset.sum_nonneg fun c _ => hb0 c)] at h
  have hsum : ∑ c, x c ^ 2 ≤ (Real.sqrt J + Real.sqrt s) ^ 2 := by
    calc ∑ c, x c ^ 2 ≤ ∑ c, (b c + 1) ^ 2 :=
          Finset.sum_le_sum fun c _ => pow_le_pow_left₀ (hx0 c) (hxb c) 2
      _ = J + 2 * ∑ c, b c + s := by
          simp only [add_sq, Finset.sum_add_distrib, mul_one, one_pow, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ J + 2 * (Real.sqrt J * Real.sqrt s) + s := by linarith
      _ = (Real.sqrt J + Real.sqrt s) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hJ0, Real.sq_sqrt (by positivity)]; ring
  have h1 : Real.sqrt (lam2Sq s p κ) ≤ Real.sqrt J + Real.sqrt s := by
    calc Real.sqrt (lam2Sq s p κ) ≤ Real.sqrt ((Real.sqrt J + Real.sqrt s) ^ 2) :=
          Real.sqrt_le_sqrt (le_trans hLr hsum)
      _ = Real.sqrt J + Real.sqrt s := Real.sqrt_sq (by positivity)
  rw [hJr]; linarith

end Z3NetF.Proofs
