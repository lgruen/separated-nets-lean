/-
Proof module of entry Skel (`prop:skelcomp`(iii): two skeleton coordinates).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkCompII

@[expose] public section

/-!
# Entry Skel: `prop:skelcomp`(iii) (`ℓ = 2`, `s = r + 2`)

The places: `z_1 = ∞` (coordinate `r`), `z_2` at `0` (coordinate `r + 1`), and the full
coordinate `x_d` at `b_d = -A_1d/A_2d` (the paper's `b_d = a_2 - Λ A_1d/A_2d` with `a_2 = 0`,
`Λ = 1`); they are distinct by (N1). Then `w_{z_1 d} = 1`, `y_{z_1 d} = 0` and
`w_{z_2 d} = y_{z_2 d} = A_2d/A_1d =: t_d`, and the residual problem on the rows `S = {z_1, z_2}`
is solved with `λ' = 1` and, on a full column, `U'_d = [[A_1d, β_1d], [0, (β_2d - t_d β_1d)/t_d²]]`
(a unit by (N3)), on a skeleton column `U'_d = (g)` (a unit by (N2)). `skel_Gs` then gives the
column gauges, move (a) sets the own blocks, and `SkComp.frame_gauge_net` the net.
-/

namespace Z3NetF.Proofs

namespace SkComp

open Finset Matrix in
/-- `prop:skelcomp`(iii) over any field, without the net property. -/
theorem iii_core {𝕜 : Type*} [Field 𝕜] (r : ℕ) (hr : 1 ≤ r) (A β : Fin 2 → ℕ → 𝕜)
    (g o : Fin 2 → 𝕜) (hA : ∀ i d, d < r → A i d ≠ 0)
    (hA2 : ∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0)
    (hg : ∀ i, g i ≠ 0) (hβ : ∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) :
    ∃ (inf : Fin (r + 2)) (x : Fin (r + 2) → 𝕜), PlacesOK inf x ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin ((r + 2) * k + r - skDepth r k c)) (𝕜))
        (U : (d : Fin (r + 2)) → Matrix (Fin (skDepth r k d)) (Fin (skDepth r k d)) (𝕜))
        (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin (skDepth r k d)) (𝕜)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (𝕜) ((r + 2) * k + r) (skDepth r k) inf x c d * U d) ∧
        (∀ i : Fin 2, ∀ d : Fin (r + 2), ∀ l : Fin (skDepth r k d),
          ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ)) := by
  classical
  set z1 : Fin (r + 2) := ⟨r, by omega⟩ with hz1
  set z2 : Fin (r + 2) := ⟨r + 1, by omega⟩ with hz2
  have hz12 : z1 ≠ z2 := by simp [hz1, hz2, Fin.ext_iff]
  set x : Fin (r + 2) → 𝕜 := fun c => if (c : ℕ) < r then -(A 0 c / A 1 c) else 0 with hxdef
  have hxz2 : x z2 = 0 := by simp [hxdef, hz2]
  have hxd : ∀ d : Fin (r + 2), (d : ℕ) < r → x d = -(A 0 d / A 1 d) := by
    intro d hd; simp [hxdef, hd]
  -- the coordinates `≥ r` are `z1`, `z2`
  have hsk : ∀ d : Fin (r + 2), ¬ (d : ℕ) < r → d = z1 ∨ d = z2 := by
    intro d hd
    have := d.isLt
    rcases (show (d : ℕ) = r ∨ (d : ℕ) = r + 1 by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hfull_ne1 : ∀ d : Fin (r + 2), (d : ℕ) < r → d ≠ z1 := by
    intro d hd h; rw [h] at hd; simp [hz1] at hd
  have hfull_ne2 : ∀ d : Fin (r + 2), (d : ℕ) < r → d ≠ z2 := by
    intro d hd h; rw [h] at hd; simp [hz2] at hd
  have hx : PlacesOK z1 x := by
    intro c d hc hd hcd
    refine isUnit_iff_ne_zero.mpr ?_
    by_cases hc' : (c : ℕ) < r
    · by_cases hd' : (d : ℕ) < r
      · rw [hxd c hc', hxd d hd']
        intro h
        have h' : A 0 c / A 1 c = A 0 d / A 1 d := by linear_combination -h
        rw [div_eq_div_iff (hA 1 c hc') (hA 1 d hd')] at h'
        exact hA2 c d hc' hd' (fun h'' => hcd (Fin.ext h'')) (sub_eq_zero.mpr h')
      · have hdz : d = z2 := (hsk d hd').resolve_left hd
        rw [hdz, hxz2, hxd c hc', sub_zero, neg_ne_zero]
        exact div_ne_zero (hA 0 c hc') (hA 1 c hc')
    · have hcz : c = z2 := (hsk c hc').resolve_left hc
      have hd' : (d : ℕ) < r := by
        by_contra hd'
        exact hcd (hcz.trans ((hsk d hd').resolve_left hd).symm)
      rw [hcz, hxz2, hxd d hd', zero_sub, neg_neg]
      exact div_ne_zero (hA 0 d hd') (hA 1 d hd')
  refine ⟨z1, x, hx, fun k hk => ?_⟩
  set K : Fin (r + 2) → ℕ := skDepth r k with hKdef
  have hK : ∑ c, K c = (r + 2) * k + r := sum_skDepth' r k (by omega)
  have hKfull : ∀ d : Fin (r + 2), (d : ℕ) < r → K d = k + 1 := by
    intro d hd; simp only [hKdef, skDepth, if_pos hd]
  have hKskel : ∀ d : Fin (r + 2), ¬ (d : ℕ) < r → K d = k := by
    intro d hd; simp only [hKdef, skDepth, if_neg hd]
  -- the rows
  set S : Finset (Fin (r + 2)) := {z1, z2} with hSdef
  have hmemS : ∀ c ∈ S, c = z1 ∨ c = z2 := by
    intro c hc; simpa [hSdef] using hc
  have hcardF : ∀ d : Fin (r + 2), (d : ℕ) < r → (S.erase d).card = 2 := by
    intro d hd
    rw [Finset.erase_eq_of_notMem (by simp [hSdef, hfull_ne1 d hd, hfull_ne2 d hd]),
      Finset.card_pair hz12]
  have hcard1 : (S.erase z1).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨z2, ?_⟩
    ext e; simp only [hSdef, mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · intro h; exact ⟨h ▸ hz12.symm, Or.inr h⟩
  have hcard2 : (S.erase z2).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨z1, ?_⟩
    ext e; simp only [hSdef, mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · intro h; exact ⟨h ▸ hz12, Or.inl h⟩
  -- `w`, `y` on the rows
  set t : ℕ → 𝕜 := fun d => A 1 d / A 0 d with htdef
  have hw1 : ∀ d, wN z1 x z1 d = 1 := by intro d; simp [wN]
  have hy1 : ∀ d, yN z1 x z1 d = 0 := by intro d; simp [yN]
  have hw2 : ∀ d : Fin (r + 2), (d : ℕ) < r → wN z1 x z2 d = t d := by
    intro d hd
    simp only [wN, if_neg (show ¬ (z2 = z1 ∨ d = z1) by
      rintro (h | h); exact hz12 h.symm; exact hfull_ne1 d hd h)]
    rw [hxz2, hxd d hd, zero_sub, neg_neg, Ring.inverse_eq_inv', inv_div]
  have hy2 : ∀ d : Fin (r + 2), (d : ℕ) < r → yN z1 x z2 d = t d := by
    intro d hd
    simp only [yN, if_neg hz12.symm, if_neg (hfull_ne1 d hd)]
    rw [hxz2, hxd d hd, zero_sub, neg_neg, Ring.inverse_eq_inv', inv_div]
  have hw21 : wN z1 x z2 z1 = 1 := by simp [wN]
  have ht0 : ∀ d, d < r → t d ≠ 0 := fun d hd => div_ne_zero (hA 1 d hd) (hA 0 d hd)
  -- the design, the row scalars and the residual gauge
  set sk : Fin (r + 2) → Fin 2 := fun c => if (c : ℕ) = r then 0 else 1 with hskdef
  have hsk1 : sk z1 = 0 := by simp [hskdef, hz1]
  have hsk2 : sk z2 = 1 := by simp [hskdef, hz2]
  set F : ℕ → Fin (r + 2) → Fin (r + 2) → 𝕜 := fun n c d =>
    if (d : ℕ) < r then (if n = 0 then A (sk c) d else β (sk c) d) else g (sk c) with hFdef
  set lam : Fin (r + 2) → 𝕜 := fun _ => 1 with hlamdef
  set Ur : Fin (r + 2) → ℕ → ℕ → 𝕜 := fun d n' n =>
    if (d : ℕ) < r then
      (if n' = 0 ∧ n = 0 then A 0 d else if n' = 0 ∧ n = 1 then β 0 d
       else if n' = 1 ∧ n = 1 then (β 1 d - t d * β 0 d) / t d ^ 2 else 0)
    else if d = z1 then g 1 else g 0 with hUrdef
  have hres : ResidualSk z1 x S F lam Ur := by
    refine ⟨fun _ _ => isUnit_one, ?_, ?_, ?_⟩
    · intro d n' n h1 h2
      by_cases hd : (d : ℕ) < r
      · rw [hcardF d hd] at h2
        simp only [hUrdef, if_pos hd]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rcases hsk d hd with h | h <;> subst h
        · rw [hcard1] at h2; omega
        · rw [hcard2] at h2; omega
    · intro d n hn
      refine isUnit_iff_ne_zero.mpr ?_
      by_cases hd : (d : ℕ) < r
      · rw [hcardF d hd] at hn
        simp only [hUrdef, if_pos hd]
        rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · rw [if_pos ⟨rfl, rfl⟩]; exact hA 0 d hd
        · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, rfl⟩]
          refine div_ne_zero ?_ (pow_ne_zero _ (ht0 d hd))
          intro h0
          apply hβ d hd
          have e : A 0 d * β 1 d - β 0 d * A 1 d = A 0 d * (β 1 d - t d * β 0 d) := by
            simp only [htdef]; field_simp [hA 0 d hd]
          rw [e, h0, mul_zero]
      · simp only [hUrdef, if_neg hd]
        split_ifs
        · exact hg 1
        · exact hg 0
    · intro c hc d hcd n hn
      simp only [hlamdef, one_mul]
      by_cases hd : (d : ℕ) < r
      · rw [hcardF d hd] at hn
        rcases hmemS c hc with rfl | rfl
        · simp only [hw1, hy1, hFdef, hUrdef, if_pos hd, hsk1]
          rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
          · simp
          · simp [Finset.sum_range_succ]
        · simp only [hw2 d hd, hy2 d hd, hFdef, hUrdef, if_pos hd, hsk2]
          rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
          · simp [Finset.sum_range_succ, htdef, hA 0 d hd]
          · simp [Finset.sum_range_succ, htdef, hA 0 d hd, hA 1 d hd] <;>
              field_simp [ht0 d hd, hA 0 d hd, hA 1 d hd] <;> ring
      · rcases hsk d hd with rfl | rfl
        · rw [hcard1] at hn
          obtain rfl : n = 0 := by omega
          rcases hmemS c hc with rfl | rfl
          · exact absurd rfl hcd
          · simp [hFdef, hUrdef, hd, hsk2, hw21, Finset.sum_range_succ]
        · rw [hcard2] at hn
          obtain rfl : n = 0 := by omega
          rcases hmemS c hc with rfl | rfl
          · simp [hFdef, hUrdef, hd, hz12.symm, hsk1, hw1, Finset.sum_range_succ]
          · exact absurd rfl hcd
  obtain ⟨U, hU, hrow⟩ := skel_Gs K hK z1 x hx S F lam Ur hres
  set L : (c : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - K c)) (Fin ((r + 2) * k + r - K c))
      (𝕜) :=
    fun c => Lgauge ((r + 2) * k + r - K c) (lam c * Ring.inverse (QfK K z1 x c)) with hLdef
  set Dg : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - K c)) (Fin (K d)) (𝕜) :=
    fun c _ a l => if (a : ℕ) = 0 ∧ (l : ℕ) + 1 = k then o (sk c) else 0 with hDgdef
  set Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - K c)) (Fin (K d)) (𝕜) :=
    fun c d => if c = d then Dg c d
      else L c * frameGraphK (𝕜) ((r + 2) * k + r) K z1 x c d * U d with hΦdef
  have hL : ∀ c, IsLTU (L c) := fun c =>
    Lgauge_LTU _ _ (isUnit_one.mul (QfK_unit K z1 x hx c).ringInverse)
  have hΦ : ∀ c d, c ≠ d → Φ c d = L c * frameGraphK (𝕜) ((r + 2) * k + r) K z1 x c d * U d :=
    fun c d hcd => by simp only [hΦdef, if_neg hcd]
  refine ⟨L, U, Φ, hL, hU, hΦ, ?_⟩
  -- the skeleton rows
  have hval : ∀ c ∈ S, (c : ℕ) = r + ((sk c : Fin 2) : ℕ) := by
    intro c hc
    rcases hmemS c hc with rfl | rfl
    · rw [hsk1]; simp [hz1]
    · rw [hsk2]; simp [hz2]
  have key : ∀ c ∈ S, ∀ d : Fin (r + 2), ∀ l : Fin (K d),
      ent (Φ c d) 0 l = sk2Coef r k A β g o (sk c) (d : ℕ) (l : ℕ) := by
    intro c hc d l
    have hcv := hval c hc
    have hl := l.isLt
    by_cases hcd : c = d
    · subst hcd
      have hKc : K c = k := hKskel c (by omega)
      have h0 : 0 < (r + 2) * k + r - K c := by
        have : k ≤ (r + 2) * k := Nat.le_mul_of_pos_left k (by omega)
        omega
      have hent : ent (Φ c c) 0 l = if (l : ℕ) + 1 = k then o (sk c) else 0 := by
        unfold ent
        rw [dif_pos ⟨h0, l.isLt⟩]
        simp [hΦdef, hDgdef]
      rw [hent]
      simp only [sk2Coef, if_neg (show ¬ (c : ℕ) < r by omega), if_pos hcv]
    · rw [hΦ c d hcd]
      have h := hrow c hc d hcd l
      simp only [hLdef] at *
      rw [h]
      by_cases hd : (d : ℕ) < r
      · have hKd := hKfull d hd
        rw [hcardF d hd]
        simp only [sk2Coef, if_pos hd, hFdef]
        by_cases hlk : (l : ℕ) = k
        · rw [if_pos (by omega), if_pos (by omega), if_pos hlk]
        · by_cases hlk1 : (l : ℕ) + 1 = k
          · rw [if_pos (by omega), if_neg (by omega), if_neg hlk, if_pos hlk1]
          · rw [if_neg (by omega), if_neg hlk, if_neg hlk1]
      · have hdS : d ∈ S := by rcases hsk d hd with rfl | rfl <;> simp [hSdef]
        have hdv := hval d hdS
        have hcard : (S.erase d).card = 1 := by
          rcases hsk d hd with rfl | rfl
          · exact hcard1
          · exact hcard2
        have hKd := hKskel d hd
        rw [hcard]
        have hne : (d : ℕ) ≠ r + ((sk c : Fin 2) : ℕ) := fun h => hcd (Fin.ext (hcv.trans h.symm))
        simp only [sk2Coef, if_neg hd, if_neg hne, hFdef]
        by_cases hlk1 : (l : ℕ) + 1 = k
        · rw [if_pos (by omega), if_pos hlk1]
        · rw [if_neg (by omega), if_neg hlk1]
  intro i d l
  have hiS : Fin.natAdd r i ∈ S := by
    fin_cases i
    · simp [hSdef, hz1, Fin.ext_iff]
    · simp [hSdef, hz2, Fin.ext_iff]
  have hski : sk (Fin.natAdd r i) = i := by
    fin_cases i <;> simp [hskdef]
  rw [key _ hiS d l, hski]

end SkComp

open SkComp in
/-- **`prop:skelcomp`(iii)** (`ℓ = 2`, `s = r + 2`). -/
theorem skelcomp_iii (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (A β : Fin 2 → ℕ → ZMod p)
    (g o : Fin 2 → ZMod p) (hA : ∀ i d, d < r → A i d ≠ 0)
    (hA2 : ∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0)
    (hg : ∀ i, g i ≠ 0) (hβ : ∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) :
    ∃ (inf : Fin (r + 2)) (x : Fin (r + 2) → ZMod p), PlacesOK inf x ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin ((r + 2) * k + r - skDepth r k c)) (ZMod p))
        (U : (d : Fin (r + 2)) → Matrix (Fin (skDepth r k d)) (Fin (skDepth r k d)) (ZMod p))
        (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin (skDepth r k d)) (ZMod p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod p) ((r + 2) * k + r) (skDepth r k) inf x c d * U d) ∧
        (∀ i : Fin 2, ∀ d : Fin (r + 2), ∀ l : Fin (skDepth r k d),
          ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ)) ∧
        IsNet0 (r + 2) p ((r + 2) * k + r)
          (digPoint p ((r + 2) * k + r) (graphGenK (m := (r + 2) * k + r) (skDepth r k) Φ)) := by
  obtain ⟨inf, x, hx, H⟩ := iii_core (𝕜 := ZMod p) r hr A β g o hA hA2 hg hβ
  refine ⟨inf, x, hx, fun k hk => ?_⟩
  obtain ⟨L, U, Φ, hL, hU, hΦ, hkey⟩ := H k hk
  exact ⟨L, U, Φ, hL, hU, hΦ, hkey,
    frame_gauge_net p _ (sum_skDepth' r k (by omega)) inf x hx L U hL hU Φ hΦ⟩

end Z3NetF.Proofs
