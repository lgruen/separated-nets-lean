module
public import Mathlib
public import Z3Net.KNSepNear

@[expose] public section

/-!
# KN separation, part 7: the reduction theorem `sep_of_cert`

For a design `D = ⟨p, r, Rg, R⟩` whose finite relaxation certificate holds
(`checkAll D T`, `sideOK D T`), every KN net `C` with rows `R` (any `k ≥ 2`) and any two
distinct indices `v ≠ w` satisfy `T · u² ≤ N² δ²` with the sub-fine unit `u = p^(m-k-2)`.

* far case (some centred coarse step outside the step box): one coordinate alone is far,
  by `far_bound` and the range cover of `sideOK`;
* near case: carry chains of every block (`carry`), the near bound `near_term` per coordinate,
  and the soundness of the enumeration (`checkAll_sound`).
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p r k : ℕ}

lemma vv_cast [NeZero p] {m : ℕ} (v : Fin m → ZMod p) (j : ℕ) : ((vv v j : ℕ) : ZMod p) = vz v j := by
  simp [vv, ZMod.natCast_zmod_val]

lemma cres_le_torus (N : ℕ) (x y : Fin 3 → ℕ) (c : Fin 3) :
    cres N ((x c : ℤ) - (y c : ℤ)) ^ 2 ≤ torusDist2 N x y := by
  unfold torusDist2
  exact Finset.single_le_sum (f := fun c => cres N ((x c : ℤ) - (y c : ℤ)) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

/-- Digit patterns of all three blocks in the near case. -/
lemma near_patterns [NeZero p] (hp : 2 ≤ p) (hr : r = 1 ∨ r = 2) (hk : 1 ≤ k)
    (v w : Fin (3 * k + r) → ZMod p) (δ : Fin 3 → ℤ)
    (hδ : ∀ d, δ d = cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d))
    (hsmall : ∀ d, |δ d| < p) :
    ∃ ch : Fin 3 → ℕ, (∀ d, ch d < min (depth r k d) (win r d)) ∧ (∀ d, δ d = 0 → ch d = 0) ∧
      ∀ d : Fin 3, ∀ l < depth r k d, depth r k d - 1 - l < win r d →
        vz v (off r k d + l) - vz w (off r k d + l) =
          ((pat (δ d) (ch d) (depth r k d - 1 - l) : ℤ) : ZMod p) := by
  have hc : ∀ d : Fin 3, ∃ c, c < min (depth r k d) (win r d) ∧ (δ d = 0 → c = 0) ∧
      ∀ l < depth r k d, depth r k d - 1 - l < win r d →
        vz v (off r k d + l) - vz w (off r k d + l) =
          ((pat (δ d) c (depth r k d - 1 - l) : ℤ) : ZMod p) := by
    intro d
    have hK : 1 ≤ depth r k d := le_trans hk (depth_ge r k d)
    have hL1 : 1 ≤ win r d := by unfold win; split_ifs <;> omega
    have hL4 : win r d ≤ 4 := by unfold win; split_ifs <;> omega
    obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d)
    rw [← hδ d] at hz
    obtain ⟨c, hc1, hc2, hc3⟩ := carry p (depth r k d) (win r d) (by omega) hK hL1 hL4
      (nC r k v d) (nC r k w d) (nC_lt v d) (nC_lt w d) (δ d) z (hsmall d) hz
    refine ⟨c, hc1, hc2, fun l hl hlw => ?_⟩
    have := hc3 (depth r k d - 1 - l) (lt_min (by omega) hlw)
    rw [nC_digit v d _ (by omega), nC_digit w d _ (by omega),
      show depth r k d - 1 - (depth r k d - 1 - l) = l by omega, vv_cast, vv_cast] at this
    exact this
  choose ch h1 h2 h3 using hc
  exact ⟨ch, h1, h2, h3⟩

/-- **Reduction theorem.** -/
theorem sep_of_cert (hr : r = 1 ∨ r = 2) (hk : 2 ≤ k) (hp : 2 ≤ p) (R : Rows) (Rg : Fin 3 → ℕ)
    (T : ℕ) (hcert : checkAll ⟨p, r, Rg, R⟩ T = true) (hside : sideOK ⟨p, r, Rg, R⟩ T = true)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (digPoint p (3 * k + r) C v) (digPoint p (3 * k + r) C w) := by
  haveI : NeZero p := ⟨by omega⟩
  set u := p ^ (3 * k + r - (k + 2)) with hu
  have hu0 : 0 < u := by positivity
  set δ : Fin 3 → ℤ := fun d => cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d) with hδdef
  have hδ : ∀ d, δ d = cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d) := fun d => rfl
  have hS := fun c => sideOK_sound _ T hside c
  by_cases hfar : ∃ c, (Rg c : ℤ) < |δ c|
  · obtain ⟨c, hc⟩ := hfar
    have hfb := far_bound hr R.sk C hC.1 v w c
    rw [← hδ c] at hfb
    -- the coordinate alone carries the bound
    have hcres : T * u ^ 2 ≤ cres (p ^ (3 * k + r))
        ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) ^ 2 := by
      set cr := cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w)
      by_cases hcr : (c : ℕ) < r
      · have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hcr]
        have hU : p ^ (3 * k + r - depth r k c) = p * u := by
          rw [hd, hu, ← pow_succ']; congr 1; omega
        rw [hU] at hfb
        have hT := (hS c).2.2.2.1 (by simp [Design.full, hcr])
        -- |δ| ≥ Rg + 1 ⇒ cr ≥ Rg · p · u
        have h1 : ((Rg c * p * u : ℕ) : ℤ) ≤ cr := by
          push_cast at hfb ⊢
          have hδ1 : (Rg c : ℤ) + 1 ≤ |δ c| := by omega
          have hpu : (0 : ℤ) ≤ (p : ℤ) * u := by positivity
          nlinarith
        have h2 : Rg c * p * u ≤ cr := by exact_mod_cast h1
        calc T * u ^ 2 ≤ (p * Rg c) ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hT
          _ = (Rg c * p * u) ^ 2 := by ring
          _ ≤ cr ^ 2 := Nat.pow_le_pow_left h2 2
      · have hd : depth r k c = k := by unfold depth; rw [if_neg hcr]
        have hU : p ^ (3 * k + r - depth r k c) = p * p * u := by
          rw [hd, hu, mul_assoc, ← pow_succ', ← pow_succ']; congr 1; omega
        rw [hU] at hfb
        obtain ⟨hR1, hT⟩ := (hS c).2.2.2.2 (by simp [Design.full, hcr])
        have h1 : ((p * p * u : ℕ) : ℤ) ≤ cr := by
          push_cast at hfb ⊢
          have hR1' : Rg c = 1 := hR1
          rw [hR1'] at hc
          have hδ1 : (2 : ℤ) ≤ |δ c| := by push_cast at hc; omega
          have hpu : (0 : ℤ) ≤ (p : ℤ) * p * u := by positivity
          nlinarith
        have h2 : p * p * u ≤ cr := by exact_mod_cast h1
        calc T * u ^ 2 ≤ (p * p) ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hT
          _ = (p * p * u) ^ 2 := by ring
          _ ≤ cr ^ 2 := Nat.pow_le_pow_left h2 2
    exact le_trans hcres (cres_le_torus _ (digPoint p (3 * k + r) C v) (digPoint p (3 * k + r) C w) c)
  · push_neg at hfar
    have hsmall : ∀ d, |δ d| < p := fun d => lt_of_le_of_lt (hfar d) (by exact_mod_cast (hS d).1)
    obtain ⟨ch, hch, hch0, hD⟩ := near_patterns hp hr (by omega) v w δ hδ hsmall
    have hRs : ∀ d : Fin 3, r ≤ (d : ℕ) → Rg d = 1 := fun d hd =>
      ((hS d).2.2.2.2 (by simp [Design.full]; omega)).1
    have hterm := fun c => near_term hr hk hp R Rg C hC v w δ hδ hfar (fun d => (hS d).1) hRs ch hch hD c
    -- not all steps vanish
    have hne : ¬(δ 0 = 0 ∧ δ 1 = 0 ∧ δ 2 = 0) := by
      rintro ⟨h0, h1, h2⟩
      apply hvw
      refine eq_of_nC_eq hr v w fun d => nC_eq_of_cen_zero v w d ?_
      rw [← hδ d]
      fin_cases d <;> assumption
    have hT := checkAll_sound _ T hcert δ ch (fun d => abs_le.mp (hfar d))
      (fun d => mem_chains _ _ _ (hch0 d) (lt_of_lt_of_le (hch d) (min_le_right _ _))) hne
    have hsq : ∀ c : Fin 3, term ⟨p, r, Rg, R⟩ δ ch c ^ 2 * u ^ 2 ≤
        cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) ^ 2 := by
      intro c
      have h := hterm c
      have h' : term ⟨p, r, Rg, R⟩ δ ch c * u ≤
          cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) := by
        exact_mod_cast h
      calc term ⟨p, r, Rg, R⟩ δ ch c ^ 2 * u ^ 2 = (term ⟨p, r, Rg, R⟩ δ ch c * u) ^ 2 := by ring
        _ ≤ _ := Nat.pow_le_pow_left h' 2
    unfold torusDist2 digPoint
    rw [Fin.sum_univ_three]
    unfold total at hT
    calc T * u ^ 2 ≤ (term ⟨p, r, Rg, R⟩ δ ch 0 ^ 2 + term ⟨p, r, Rg, R⟩ δ ch 1 ^ 2 +
          term ⟨p, r, Rg, R⟩ δ ch 2 ^ 2) * u ^ 2 := Nat.mul_le_mul_right _ hT
      _ = term ⟨p, r, Rg, R⟩ δ ch 0 ^ 2 * u ^ 2 + term ⟨p, r, Rg, R⟩ δ ch 1 ^ 2 * u ^ 2 +
          term ⟨p, r, Rg, R⟩ δ ch 2 ^ 2 * u ^ 2 := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add (hsq 0) (hsq 1)) (hsq 2)

end Z3NetKN.Geom
