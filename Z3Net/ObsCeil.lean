/-
Proof module of entry Obs: `cor:ceils` (the first-order ceiling in every dimension over `ℤ/qℤ`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsStep

@[expose] public section

/-!
# Entry Obs: `cor:ceils`

The proof of `prop:ceil` with all counts multiplied by `q^((s-3)k)` (`exists_good`): a cell with
`n_a = 0`, the first `k - 1` offset digits of `a` equal to `q - 1`, and no wrap of the first offset
digit of any `u ≠ a`; its neighbour along `e_a`.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep

noncomputable section

namespace ObsCeil

lemma PairBelow_mono {s q m k : ℕ} {X : (Fin m → ZMod q) → Fin s → ℕ} {B B' : ℝ} (h : B ≤ B')
    (hP : Z3NetF.PairBelow q m k X B) : Z3NetF.PairBelow q m k X B' := by
  obtain ⟨v, w, hvw, h1, h2⟩ := hP
  exact ⟨v, w, hvw, lt_of_lt_of_le h1 h, lt_of_lt_of_le h2 h⟩

lemma val_of_valMinAbs {q : ℕ} [NeZero q] (x : ZMod q) :
    (x.val : ℤ) = if 0 ≤ x.valMinAbs then x.valMinAbs else x.valMinAbs + q := by
  have := ZMod.val_lt x
  rw [ZMod.valMinAbs_def_pos]
  split_ifs with h1 h2 h2 <;> push_cast at * <;> omega

lemma natAbs_valMinAbs_lt {q : ℕ} [NeZero q] (x : ZMod q) (hq : 2 ≤ q) :
    (x.valMinAbs.natAbs : ℤ) + 1 ≤ q := by
  have := ZMod.natAbs_valMinAbs_le x
  have : q / 2 + 1 ≤ q := by omega
  omega

lemma unit_of_net {s q m : ℕ} [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m C)) :
    ∀ d : Fin s → ℕ, ∑ c, d c = m → IsUnit (Z3NetF.boxMatrix C d).det :=
  (nie_zmod q C).1 hnet

variable {s q k : ℕ} [NeZero q]

/-- The core of `cor:ceils`: a pair of neighbouring cells along `e_a` with the coordinate
differences `X_a(w) - X_a(v) = g μ + Δ_a`, `-g < Δ_a < q^(sk-2k+1)` (`μ` the value of the
diagonal entry), and `X_u(w) - X_u(v) = g M̃_ua + Δ_u`, `|Δ_u| < g`, where `g = q^(sk-k-1)`. -/
theorem ceil_core (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (hμ : 1 ≤ (Z3NetF.ent (Φ a a) 0 (k - 1)).val) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (∃ Δ : ℤ, -((q : ℤ) ^ (s * k - k - 1)) < Δ ∧ Δ < (q : ℤ) ^ (s * k - 2 * k + 1) ∧
        (Z3NetF.gfPoint q k Φ w a : ℤ) - Z3NetF.gfPoint q k Φ v a =
          (q : ℤ) ^ (s * k - k - 1) * (Z3NetF.ent (Φ a a) 0 (k - 1)).val + Δ) ∧
      ∀ u, u ≠ a → ∃ Δ : ℤ, |Δ| < (q : ℤ) ^ (s * k - k - 1) ∧
        (Z3NetF.gfPoint q k Φ w u : ℤ) - Z3NetF.gfPoint q k Φ v u =
          (q : ℤ) ^ (s * k - k - 1) * Z3NetF.Mt Φ u a + Δ := by
  classical
  have hk0 : 0 < k := by omega
  have hsk : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hC
  have hunit := unit_of_net C hnet
  -- the cell
  obtain ⟨v, hvA, hvB⟩ := exists_good C k hunit
    (fun c => if c = a then s * k - k - 1 else 0)
    (fun _ j => if j < k then {0} else if j < 2 * k - 1 then {-1} else univ)
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
      (if j < k then ({0} : Finset (ZMod q)) else if j < 2 * k - 1 then {-1} else univ) := by
    intro j hj
    have := hvA a j (by simp only [if_pos rfl]; exact hj)
    exact this
  have hcell0 : ∀ i (hi : i < k), v (Z3NetU.Proofs.ix k a ⟨i, hi⟩) = 0 := by
    intro i hi
    have := hvA' i (by omega)
    rw [if_pos hi, mem_singleton, dig_cell Φ a v i hi] at this
    exact this
  have hoff : ∀ j, k ≤ j → j < 2 * k - 1 → dig (C a) v j = -1 := by
    intro j h1 h2
    have := hvA' j (by omega)
    rwa [if_neg (by omega), if_pos h2, mem_singleton] at this
  have hgood : ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C u) v k) := by
    intro u hu
    have := hvB u (mem_erase.mpr ⟨hu, mem_univ _⟩)
    simpa using this
  -- the neighbour
  set e : Fin s → ZMod q := Pi.single a 1 with he
  set w := v + stepVec hk0 e with hw
  have hstep : ∀ c, dig (C c) w k = dig (C c) v k + Z3NetF.ent (Φ c a) 0 (k - 1) := by
    intro c
    have h0 := dig_step_off Φ hk0 e c 0 (by omega)
    simp only [add_zero] at h0
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
  · -- the moving coordinate `a`
    have hX := X_eq Φ (by omega) v a
    have hY := X_eq Φ (by omega) w a
    have hcl := cellN_step hk0 v e a
    rw [hcell0 (k - 1) (by omega)] at hcl
    simp only [he, Pi.single_eq_same, zero_add, ZMod.val_zero, ZMod.val_one] at hcl
    -- first offset digit
    set μ := Z3NetF.ent (Φ a a) 0 (k - 1)
    have hd0 : dig (C a) v k = -1 := hoff k le_rfl (by omega)
    have hμl := ZMod.val_lt μ
    have ho0w : ((dig (C a) w k).val : ℤ) = μ.val - 1 := by
      rw [hstep, hd0]
      have : (-1 : ZMod q) + μ = (-1 : ZMod q) + (((μ.val : ℤ)) : ZMod q) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, val_wrap_up]
      · rw [val_m1]; push_cast; omega
      · rw [val_m1]; push_cast; omega
      · rw [val_m1]; push_cast; omega
    have ho0v : ((dig (C a) v k).val : ℤ) = q - 1 := by
      rw [hd0, val_m1]; push_cast; omega
    -- tails
    have htv := tl_lt Φ (by omega) v a
    have htw := tl_lt Φ (by omega) w a
    have htge : q ^ (s * k - k - 1) ≤ tl Φ v a + q ^ (s * k - (2 * k - 1)) := by
      have := TS_ge (Nat.pos_of_neZero q)
        (fun j => (dig (C a) v j).val) (k - 2) (k + 1) (2 * k - 1) (s * k) (by omega) (by omega)
        (fun j h1 h2 => by
          rw [hoff j (by omega) h2, val_m1])
      rwa [show s * k - (k + 1) = s * k - k - 1 by omega] at this
    refine ⟨(tl Φ w a : ℤ) - tl Φ v a, ?_, ?_, ?_⟩
    · have : (tl Φ w a : ℤ) ≥ 0 := by positivity
      have : (tl Φ v a : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htv
      linarith
    · have h1 : ((q ^ (s * k - k - 1) : ℕ) : ℤ) ≤ tl Φ v a + ((q ^ (s * k - (2 * k - 1)) : ℕ) : ℤ) := by
        exact_mod_cast htge
      have h2 : (tl Φ w a : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htw
      push_cast at h1
      rw [show s * k - 2 * k + 1 = s * k - (2 * k - 1) by omega]
      linarith
    · rw [hX, hY]
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
      rw [hstep]; exact hnw
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

lemma pow_split (q : ℕ) (a b : ℕ) : (q : ℝ) ^ (a + b) = (q : ℝ) ^ a * (q : ℝ) ^ b := pow_add _ _ _

lemma trans_bound {q : ℕ} (hq : 0 < q) {g : ℝ} (hg : 0 < g) (σ Δ : ℤ) (x : ℝ)
    (hx : x = g * σ + Δ) (hΔ : |(Δ : ℝ)| < g) :
    |x| < (((|σ| : ℤ) : ℝ) + 1) / q * (g * q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [hx]
  calc |g * (σ : ℝ) + Δ| ≤ g * |(σ : ℝ)| + |(Δ : ℝ)| := by
        rw [← abs_of_pos hg, ← abs_mul, abs_of_pos hg]
        exact abs_add_le _ _
    _ < g * |(σ : ℝ)| + g := by linarith
    _ = (((|σ| : ℤ) : ℝ) + 1) / q * (g * q) := by push_cast; field_simp

theorem ceils_neg (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : Z3NetF.Mt Φ a a ≤ -1) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - ((|Z3NetF.Mt Φ a a| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ (k - 1)) ^ 2 +
        ∑ u ∈ univ.erase a, (((|Z3NetF.Mt Φ u a| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  have hsk : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
  set μ := Z3NetF.ent (Φ a a) 0 (k - 1) with hμdef
  have hMt : Z3NetF.Mt Φ a a = μ.valMinAbs := rfl
  have hμv : (μ.val : ℤ) = Z3NetF.Mt Φ a a + q := by
    have := val_of_valMinAbs μ
    rw [if_neg (by rw [← hMt]; omega)] at this
    rw [hMt]; exact this
  have hMlt := natAbs_valMinAbs_lt μ (by omega)
  have hμ1 : 1 ≤ μ.val := by
    have : (1 : ℤ) ≤ μ.val := by
      rw [hμv, hMt]
      have : (μ.valMinAbs.natAbs : ℤ) = -μ.valMinAbs := by
        rw [Int.natCast_natAbs, abs_of_neg (by rw [← hMt]; omega)]
      omega
    exact_mod_cast this
  obtain ⟨v, w, hvw, ⟨Δ, hΔ1, hΔ2, hXa⟩, hXu⟩ := ceil_core hs hq hk Φ hnet a hcol hμ1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set g : ℝ := (q : ℝ) ^ (s * k - k - 1) with hg
  have hG : (q : ℝ) ^ (s * k - k) = g * q := by
    rw [hg, ← pow_succ]; congr 1; omega
  have hG2 : (q : ℝ) ^ (s * k - k) = (q : ℝ) ^ (s * k - 2 * k + 1) * (q : ℝ) ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  have hqk : (0 : ℝ) < (q : ℝ) ^ (k - 1) := by positivity
  set b : Fin s → ℝ := fun c => if c = a then 1 - ((|Z3NetF.Mt Φ a a| : ℤ) : ℝ) / q +
    1 / (q : ℝ) ^ (k - 1) else (((|Z3NetF.Mt Φ c a| : ℤ) : ℝ) + 1) / q with hb
  have key := ObsCount.pair_of_bounds (X := Z3NetF.gfPoint q k Φ) (k := k) (by omega)
    (by omega) v w hvw b (fun c => by
      by_cases hc : c = a
      · subst hc
        simp only [hb, if_pos rfl]
        have hX : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
            g * (μ.val : ℝ) + Δ := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hXa
          push_cast at this; rw [hg]; exact this
        have hμr : (μ.val : ℝ) = q - ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ) := by
          have : ((μ.val : ℤ) : ℝ) = ((Z3NetF.Mt Φ c c + q : ℤ) : ℝ) := by rw [hμv]
          push_cast at this; rw [this, abs_of_neg (by omega)]; push_cast; ring
        have hΔ1' : -g < (Δ : ℝ) := by rw [hg]; exact_mod_cast hΔ1
        have hΔ2' : (Δ : ℝ) < (q : ℝ) ^ (s * k - 2 * k + 1) := by exact_mod_cast hΔ2
        have hμ1' : (1 : ℝ) ≤ μ.val := by exact_mod_cast hμ1
        have hgpos : 0 < g := by positivity
        rw [hX, abs_of_pos (by nlinarith)]
        have e1 : (q : ℝ) ^ (s * k - k) / q = g := by rw [hG]; field_simp
        have e2 : (q : ℝ) ^ (s * k - k) / (q : ℝ) ^ (k - 1) = (q : ℝ) ^ (s * k - 2 * k + 1) := by
          rw [hG2]; field_simp
        rw [show (1 - ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ (k - 1)) *
            (q : ℝ) ^ (s * k - k) = g * (q - ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ)) +
              (q : ℝ) ^ (s * k - 2 * k + 1) by
          calc (1 - ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ (k - 1)) *
                (q : ℝ) ^ (s * k - k) = (q : ℝ) ^ (s * k - k) -
                  ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ) * ((q : ℝ) ^ (s * k - k) / q) +
                  (q : ℝ) ^ (s * k - k) / (q : ℝ) ^ (k - 1) := by ring
            _ = g * (q - ((|Z3NetF.Mt Φ c c| : ℤ) : ℝ)) + (q : ℝ) ^ (s * k - 2 * k + 1) := by
              rw [e1, e2, hG]; ring]
        rw [← hμr]; linarith
      · simp only [hb, if_neg hc]
        obtain ⟨Δu, hΔu, hXu'⟩ := hXu c hc
        have hX : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
            g * (Z3NetF.Mt Φ c a : ℝ) + Δu := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hXu'
          push_cast at this; rw [hg]; exact this
        have hΔu' : |(Δu : ℝ)| < g := by rw [hg]; exact_mod_cast hΔu
        rw [hX, hG]
        calc |g * (Z3NetF.Mt Φ c a : ℝ) + Δu| ≤ g * |(Z3NetF.Mt Φ c a : ℝ)| + |(Δu : ℝ)| := by
              rw [← abs_of_pos (show 0 < g by positivity), ← abs_mul,
                abs_of_pos (show 0 < g by positivity)]
              exact abs_add_le _ _
          _ < g * |(Z3NetF.Mt Φ c a : ℝ)| + g := by linarith
          _ = (((|Z3NetF.Mt Φ c a| : ℤ) : ℝ) + 1) / q * (g * q) := by
              push_cast; field_simp)
  convert key using 1
  rw [← Finset.add_sum_erase _ _ (mem_univ a)]
  simp only [hb, if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [if_neg (mem_erase.mp hu).1, div_pow]

theorem ceils_pos (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : 1 ≤ Z3NetF.Mt Φ a a) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      (((((Z3NetF.Mt Φ a a + 1 : ℤ)) : ℝ) ^ 2 +
        ∑ u ∈ univ.erase a, (((|Z3NetF.Mt Φ u a| : ℤ) : ℝ) + 1) ^ 2) / (q : ℝ) ^ 2) := by
  have hsk : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
  set μ := Z3NetF.ent (Φ a a) 0 (k - 1) with hμdef
  have hMt : Z3NetF.Mt Φ a a = μ.valMinAbs := rfl
  have hμv : (μ.val : ℤ) = Z3NetF.Mt Φ a a := by
    have := val_of_valMinAbs μ
    rw [if_pos (by rw [← hMt]; omega)] at this
    rw [hMt]; exact this
  have hμ1 : 1 ≤ μ.val := by
    have : (1 : ℤ) ≤ μ.val := by rw [hμv]; exact ha
    exact_mod_cast this
  obtain ⟨v, w, hvw, ⟨Δ, hΔ1, hΔ2, hXa⟩, hXu⟩ := ceil_core hs hq hk Φ hnet a hcol hμ1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set g : ℝ := (q : ℝ) ^ (s * k - k - 1) with hg
  have hgpos : 0 < g := by positivity
  have hG : (q : ℝ) ^ (s * k - k) = g * q := by
    rw [hg, ← pow_succ]; congr 1; omega
  have hPg : (q : ℝ) ^ (s * k - 2 * k + 1) ≤ g := by
    rw [hg]; exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ q by omega)) (by omega)
  set b : Fin s → ℝ := fun c => if c = a then (((Z3NetF.Mt Φ a a + 1 : ℤ)) : ℝ) / q
    else (((|Z3NetF.Mt Φ c a| : ℤ) : ℝ) + 1) / q with hb
  have key := ObsCount.pair_of_bounds (X := Z3NetF.gfPoint q k Φ) (k := k) (by omega)
    (by omega) v w hvw b (fun c => by
      by_cases hc : c = a
      · subst hc
        simp only [hb, if_pos rfl]
        have hX : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
            g * (μ.val : ℝ) + Δ := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hXa
          push_cast at this; rw [hg]; exact this
        have hμr : (μ.val : ℝ) = ((Z3NetF.Mt Φ c c : ℤ) : ℝ) := by exact_mod_cast hμv
        have hΔ1' : -g < (Δ : ℝ) := by rw [hg]; exact_mod_cast hΔ1
        have hΔ2' : (Δ : ℝ) < (q : ℝ) ^ (s * k - 2 * k + 1) := by exact_mod_cast hΔ2
        have hμ1' : (1 : ℝ) ≤ μ.val := by exact_mod_cast hμ1
        rw [hX, abs_of_pos (by nlinarith), hG]
        push_cast
        rw [← hμr]
        field_simp
        nlinarith
      · simp only [hb, if_neg hc]
        obtain ⟨Δu, hΔu, hXu'⟩ := hXu c hc
        rw [hG]
        exact trans_bound (by omega) hgpos _ Δu _ (by
          have := congrArg (fun z : ℤ => (z : ℝ)) hXu'
          push_cast at this; rw [hg]; exact this) (by rw [hg]; exact_mod_cast hΔu))
  convert key using 1
  rw [← Finset.add_sum_erase _ _ (mem_univ a)]
  simp only [hb, if_pos rfl]
  rw [add_div, Finset.sum_div, div_pow]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [if_neg (mem_erase.mp hu).1, div_pow]

theorem ceils_pos_C {C : ℕ} (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (ha : 1 ≤ Z3NetF.Mt Φ a a)
    (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ) (s * ((C : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  refine PairBelow_mono ?_ (ceils_pos hs hq hk Φ hnet a hcol ha)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb : ∀ c d, (((|Z3NetF.Mt Φ c d| : ℤ) : ℝ) + 1) ^ 2 ≤ ((C : ℝ) + 1) ^ 2 := by
    intro c d
    have : ((|Z3NetF.Mt Φ c d| : ℤ) : ℝ) ≤ C := by exact_mod_cast hC c d
    have : (0 : ℝ) ≤ ((|Z3NetF.Mt Φ c d| : ℤ) : ℝ) := by positivity
    nlinarith
  have ha' : (((Z3NetF.Mt Φ a a + 1 : ℤ)) : ℝ) ^ 2 ≤ ((C : ℝ) + 1) ^ 2 := by
    have := hb a a
    rw [abs_of_pos (show (0 : ℤ) < Z3NetF.Mt Φ a a by omega)] at this
    push_cast; exact this
  calc (((Z3NetF.Mt Φ a a + 1 : ℤ)) : ℝ) ^ 2 + ∑ u ∈ univ.erase a,
        (((|Z3NetF.Mt Φ u a| : ℤ) : ℝ) + 1) ^ 2
      ≤ ((C : ℝ) + 1) ^ 2 + ∑ u ∈ univ.erase a, ((C : ℝ) + 1) ^ 2 :=
        add_le_add ha' (Finset.sum_le_sum fun u _ => hb u a)
    _ = ∑ u : Fin s, ((C : ℝ) + 1) ^ 2 :=
        Finset.add_sum_erase univ (fun _ => ((C : ℝ) + 1) ^ 2) (mem_univ a)
    _ = s * ((C : ℝ) + 1) ^ 2 := by simp

end ObsCeil


end

end Z3NetF.Proofs
