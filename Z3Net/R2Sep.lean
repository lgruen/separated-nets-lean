/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.HLGFDom
public import Z3Net.Q5Defs

@[expose] public section

/-!
# V14 stage S11′: `lem:R2`, the two-digit relaxation

The proof of `prop:Hk`(1) (`relaxG`, `GF_relax_core`, `Z3Net/HLGF.lean`, `Z3Net/HLGFDom.lean`) at `k = 1`, with the
second offset digit split off the tail: in cell units coordinate `c` is `n_c + r_c/q + (d_c + g_c)/q²`
(`XG_decomp2`). Far steps (`|E_c| ≥ 3`) are as before; on a near step `E` the first digit changes by `Δr_c` with
`2Δr_c ≡ 2β_c (mod q)` (`DgG_off_sub`) and the second by `Δd_c ≡ v_c = (D₁E)_c (mod q)` (`DgG_off1_sub`), so
`2Δr_c` is one of the options of `prop:Hk` (`opt_odd`, `opt_even`) and `Δd_c ∈ {v_c, v_c − q sgn v_c}`
(`opt_u`), and `q² |D_c| ≥ max(0, |q²E_c + qΔr_c + Δd_c| − 1) ≥ b_c` (`bR2_le`).
-/

namespace Z3NetHL.Proofs

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

variable (s q : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))

variable [NeZero q]

/-- Second offset digit (digit `2`) of coordinate `c`. -/
def o1G (x : Fin (s * 1) → ZMod q) (c : Fin s) : ℕ := dv s q 1 (DgG s q 1 Φ c x) 2

/-- The digits after the second offset digit. -/
def tl2G (x : Fin (s * 1) → ZMod q) (c : Fin s) : ℕ :=
  ∑ j ∈ Ico 3 (s * 1), dv s q 1 (DgG s q 1 Φ c x) j * q ^ (s * 1 - 1 - j)

lemma tlG_split (hs : 3 ≤ s) (x : Fin (s * 1) → ZMod q) (c : Fin s) :
    tlG s q 1 Φ x c = q ^ (s * 1 - 1 - 1 - 1) * o1G s q Φ x c + tl2G s q Φ x c := by
  unfold tlG tail o1G tl2G
  rw [Finset.sum_eq_sum_Ico_succ_bot (show 1 + 1 < s * 1 by omega)]
  rw [show s * 1 - 1 - (1 + 1) = s * 1 - 1 - 1 - 1 by omega, mul_comm]

lemma tl2G_lt (hs : 3 ≤ s) (x : Fin (s * 1) → ZMod q) (c : Fin s) :
    tl2G s q Φ x c < q ^ (s * 1 - 1 - 1 - 1) := by
  unfold tl2G
  rw [sum_Ico_eq_sum_range, show s * 1 - 3 = s * 1 - 1 - 1 - 1 by omega]
  have := Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) (fun t => dv s q 1 (DgG s q 1 Φ c x) (3 + t))
    (fun t => dv_lt s q 1 _ _) (s * 1 - 1 - 1 - 1)
  convert this using 2 with t ht
  simp only [mem_range] at ht
  rw [show s * 1 - 1 - (3 + t) = s * 1 - 1 - 1 - 1 - 1 - t by omega]

lemma XG_decomp2 (hs : 3 ≤ s) (x : Fin (s * 1) → ZMod q) (c : Fin s) :
    (GFpoint s q 1 Φ x c : ℤ) = (q : ℤ) ^ (s * 1 - 1) * cellN s q 1 x c +
      (q : ℤ) ^ (s * 1 - 1 - 1) * o0G s q 1 Φ x c + (q : ℤ) ^ (s * 1 - 1 - 1 - 1) * o1G s q Φ x c +
        tl2G s q Φ x c := by
  rw [XG_decomp s q 1 Φ (by omega) x c, tlG_split s q Φ hs x c]
  push_cast; ring

lemma o1G_cast (hs : 3 ≤ s) (x : Fin (s * 1) → ZMod q) (c : Fin s) (r : Fin (s * 1 - 1)) (hr : (r : ℕ) = 1) :
    ((o1G s q Φ x c : ℕ) : ZMod q) = DgG s q 1 Φ c x ⟨1 + r, sk_sub_add r⟩ := by
  have hk : 2 < s * 1 := by omega
  simp only [o1G, dv, dif_pos hk, ZMod.natCast_zmod_val, hr]

lemma o1G_bound (x y : Fin (s * 1) → ZMod q) (c : Fin s) :
    |(o1G s q Φ x c : ℤ) - o1G s q Φ y c| < q := by
  have h1 := dv_lt s q 1 (DgG s q 1 Φ c x) 2
  have h2 := dv_lt s q 1 (DgG s q 1 Φ c y) 2
  simp only [o1G]
  rw [abs_lt]; constructor <;> omega

/-- Change of the second offset digit: `d_c(y) − d_c(x) = (D₁ E)_c` in `ℤ/qℤ`. -/
lemma DgG_off1_sub (hs : 3 ≤ s) (D1 : Fin s → Fin s → ℤ) (hrow1 : Row1Design s q Φ D1) (c : Fin s)
    (x y : Fin (s * 1) → ZMod q) (E : Fin s → ℤ)
    (hstep : ∀ d, AxisStep2 s q 1 x y d (E d) 0) (r : Fin (s * 1 - 1)) (hr : (r : ℕ) = 1) :
    DgG s q 1 Φ c y ⟨1 + r, sk_sub_add r⟩ - DgG s q 1 Φ c x ⟨1 + r, sk_sub_add r⟩ =
      ((∑ d, D1 c d * E d : ℤ) : ZMod q) := by
  rw [DgG_off, DgG_off, ← sum_sub_distrib]
  push_cast
  refine sum_congr rfl fun d _ => ?_
  rw [Fin.sum_univ_one, Fin.sum_univ_one, ← mul_sub, hrow1 c d r hr]
  have := hstep d 0 (by omega)
  simp only [Fin.val_zero, Nat.sub_self, ite_true] at this
  rw [this]

/-- The second-digit options: `Δd ≡ v (mod q)`, `|Δd| < q`, `|v| < q` give `Δd ∈ {v, v − q sgn v}`. -/
lemma opt_u (q Δ v : ℤ) (hq : 0 < q) (hdvd : q ∣ Δ - v) (hΔ : |Δ| < q) (hv : |v| < q) :
    Δ = v ∨ Δ = v - q * Int.sign v := by
  obtain ⟨t, ht⟩ := hdvd
  rw [abs_lt] at hΔ hv
  have h1 : t < 2 := by by_contra h; push Not at h; nlinarith
  have h2 : -2 < t := by by_contra h; push Not at h; nlinarith
  have : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases this with h | h | h <;> subst h
  · right
    have hpos : 0 < v := by nlinarith
    rw [Int.sign_eq_one_of_pos hpos]; linarith
  · left; linarith
  · right
    have hneg : v < 0 := by nlinarith
    rw [Int.sign_eq_neg_one_of_neg hneg]; linarith

lemma oR2_eq (e t u : ℤ) : oR2 q e (2 * t) u = 2 * max 0 (|(q : ℤ) ^ 2 * e + q * t + u| - 1) := by
  unfold oR2
  have : 2 * (q : ℤ) ^ 2 * e + q * (2 * t) + 2 * u = 2 * ((q : ℤ) ^ 2 * e + q * t + u) := by ring
  rw [this, abs_mul, abs_two]
  rcases le_total (|(q : ℤ) ^ 2 * e + q * t + u| - 1) 0 with h | h
  · rw [max_eq_left (by linarith), max_eq_left h]; ring
  · rw [max_eq_right (by linarith), max_eq_right h]; ring

lemma oR2_nonneg (e t u : ℤ) : 0 ≤ oR2 q e t u := le_max_left _ _

lemma bR2_nonneg {s : ℕ} (F2 D1 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    0 ≤ bR2 q F2 D1 E c := by
  unfold bR2; split_ifs <;>
    exact le_min (le_min (oR2_nonneg q _ _ _) (oR2_nonneg q _ _ _)) (le_min (oR2_nonneg q _ _ _) (oR2_nonneg q _ _ _))

/-- **The options of `lem:R2`**: `2b_c ≤ 2 max(0, |q²E_c + qΔr + Δd| − 1)`. -/
lemma bR2_le {s : ℕ} (hqodd : Odd q) (F2 D1 : Fin s → Fin s → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (E : Fin s → ℤ) (c : Fin s) (Δr Δd : ℤ)
    (hdvd : (q : ℤ) ∣ 2 * Δr - dotR F2 E c) (hΔr : |Δr| < q) (hβ : |dotR F2 E c| < q)
    (hdvd1 : (q : ℤ) ∣ Δd - dotR D1 E c) (hΔd : |Δd| < q) (hv : |dotR D1 E c| < q) :
    bR2 q F2 D1 E c ≤ 2 * max 0 (|(q : ℤ) ^ 2 * E c + q * Δr + Δd| - 1) := by
  have hq' : (0 : ℤ) < q := by have := hqodd.pos; exact_mod_cast this
  have hqodd' : Odd (q : ℤ) := by
    obtain ⟨t, ht⟩ := hqodd; exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hpar : Even (dotR F2 E c - ∑ d, E d) := by
    unfold dotR; rw [← sum_sub_distrib]
    refine Finset.even_sum _ fun d _ => ?_
    obtain ⟨a, ha⟩ := hodd c d
    exact ⟨a * E d, by rw [ha]; ring⟩
  have key : ∀ T U : ℤ, T = 2 * Δr → U = Δd →
      oR2 q (E c) T U = 2 * max 0 (|(q : ℤ) ^ 2 * E c + q * Δr + Δd| - 1) := by
    intro T U hT hU; rw [hT, hU, oR2_eq]
  rcases opt_u (q : ℤ) Δd (dotR D1 E c) hq' hdvd1 hΔd hv with hu | hu
  · unfold bR2
    split_ifs with hs
    · have hσodd : Odd (dotR F2 E c) := by
        have hE : Odd (∑ d, E d) := Int.odd_iff.mpr hs
        have : dotR F2 E c = (dotR F2 E c - ∑ d, E d) + ∑ d, E d := by ring
        rw [this]; exact hpar.add_odd hE
      rcases opt_odd q (E c) Δr _ hq' hσodd hdvd hΔr hβ with h | h
      · exact ((min_le_left _ _).trans (min_le_left _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
    · have hσeven : Even (dotR F2 E c) := by
        have hE : Even (∑ d, E d) := by
          rw [Int.even_iff]; have := Int.emod_two_eq_zero_or_one (∑ d, E d); omega
        have : dotR F2 E c = (dotR F2 E c - ∑ d, E d) + ∑ d, E d := by ring
        rw [this]; exact hpar.add hE
      rcases opt_even q (E c) Δr _ hq' hqodd' hσeven hdvd hΔr hβ with h | h
      · exact ((min_le_left _ _).trans (min_le_left _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
  · unfold bR2
    split_ifs with hs
    · have hσodd : Odd (dotR F2 E c) := by
        have hE : Odd (∑ d, E d) := Int.odd_iff.mpr hs
        have : dotR F2 E c = (dotR F2 E c - ∑ d, E d) + ∑ d, E d := by ring
        rw [this]; exact hpar.add_odd hE
      rcases opt_odd q (E c) Δr _ hq' hσodd hdvd hΔr hβ with h | h
      · exact ((min_le_left _ _).trans (min_le_right _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
    · have hσeven : Even (dotR F2 E c) := by
        have hE : Even (∑ d, E d) := by
          rw [Int.even_iff]; have := Int.emod_two_eq_zero_or_one (∑ d, E d); omega
        have : dotR F2 E c = (dotR F2 E c - ∑ d, E d) + ∑ d, E d := by ring
        rw [this]; exact hpar.add hE
      rcases opt_even q (E c) Δr _ hq' hqodd' hσeven hdvd hΔr hβ with h | h
      · exact ((min_le_left _ _).trans (min_le_right _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (le_of_eq (key _ _ (by linarith) hu.symm))

lemma sig2_k1 {s : ℕ} (F2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    sig2 (fun _ => F2) E (fun _ => 0) c = dotR F2 E c := by
  unfold sig2 dotR
  refine sum_congr rfl fun d _ => ?_
  rw [Finset.Icc_eq_empty_of_lt (by norm_num), sum_empty, mul_zero, add_zero, mul_comm]

/-- **The two-digit relaxation** (`lem:R2`, `k = 1`): either some step is far, or there is a near step `E` with the
first-digit changes `Δr` (`2Δr ≡ 2β`) and the second-digit changes `Δd` (`Δd ≡ D₁E`) and
`q^(2(s−3)) ∑_c max(0, |q²E_c + qΔr_c + Δd_c| − 1)² ≤ ∑_c cres²`. -/
theorem relaxR2 (hs : 3 ≤ s) (hq7 : 7 ≤ q) (F2 D1 : Fin s → Fin s → ℤ)
    (hrow : RowDesign s q 1 Φ (fun _ => F2)) (hrow1 : Row1Design s q Φ D1)
    (x y : Fin (s * 1) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * 1 - 1)) ≤ ∑ c : Fin s,
        ((Z3NetU.cres (q ^ (s * 1)) ((GFpoint s q 1 Φ x c : ℤ) -
          (GFpoint s q 1 Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 ∨
      ∃ (E Δr Δd : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δr c - dotR F2 E c) ∧ (∀ c, |Δr c| < q) ∧
        (∀ c, (q : ℤ) ∣ Δd c - dotR D1 E c) ∧ (∀ c, |Δd c| < q) ∧
        (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) *
            ∑ c, (max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1)) ^ 2 ≤
          ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * 1)) ((GFpoint s q 1 Φ x c : ℤ) -
            (GFpoint s q 1 Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have hsk : 1 + 1 ≤ s * 1 := by omega
  set U : ℤ := (q : ℤ) ^ ((s * 1 - 1) - 1) with hU_def
  have hU : 0 < U := by positivity
  have hpow : (q : ℤ) ^ (s * 1 - 1) = U * q := by rw [hU_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * 1) : ℕ) : ℤ) = (q : ℤ) ^ (s * 1 - 1) * (q : ℤ) ^ 1 := by
    push_cast; rw [← pow_add]; congr 1; omega
  set X := GFpoint s q 1 Φ with hXdef
  have hX : ∀ c, (X x c : ℤ) - X y c =
      (q : ℤ) ^ (s * 1 - 1) * ((cellN s q 1 x c : ℤ) - cellN s q 1 y c) +
      (U * ((o0G s q 1 Φ x c : ℤ) - o0G s q 1 Φ y c) +
        ((tlG s q 1 Φ x c : ℤ) - tlG s q 1 Φ y c)) := by
    intro c; rw [hXdef, XG_decomp s q 1 Φ hsk, XG_decomp s q 1 Φ hsk]; ring
  have htl : ∀ c, |(tlG s q 1 Φ x c : ℤ) - tlG s q 1 Φ y c| < U := by
    intro c
    have h1 := tlG_lt s q 1 Φ hsk x c
    have h2 := tlG_lt s q 1 Φ hsk y c
    have h1' : ((tlG s q 1 Φ x c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h1
    have h2' : ((tlG s q 1 Φ y c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far3 s q 1 y x c
  · left
    obtain ⟨c, hc⟩ := hfar
    have ho0 := oG_bound s q 1 Φ x y c
    have hR : |U * ((o0G s q 1 Φ x c : ℤ) - o0G s q 1 Φ y c) +
        ((tlG s q 1 Φ x c : ℤ) - tlG s q 1 Φ y c)| < (q : ℤ) ^ (s * 1 - 1) := by
      have a2 := abs_add_le (U * ((o0G s q 1 Φ x c : ℤ) - o0G s q 1 Φ y c))
        ((tlG s q 1 Φ x c : ℤ) - tlG s q 1 Φ y c)
      rw [abs_mul, abs_of_pos hU] at a2
      have := htl c
      have b1 : |(o0G s q 1 Φ x c : ℤ) - o0G s q 1 Φ y c| ≤ q - 1 := by omega
      rw [hpow]; nlinarith
    have hf := far_gen3 (q ^ (s * 1)) ((q : ℤ) ^ (s * 1 - 1)) ((q : ℤ) ^ 1) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : (2 * (q : ℤ) ^ (s * 1 - 1)) ^ 2 ≤
        ((Z3NetU.cres (q ^ (s * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc 4 * (q : ℤ) ^ (2 * (s * 1 - 1)) = (2 * (q : ℤ) ^ (s * 1 - 1)) ^ 2 := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ _ := hsq.trans hsingle
  · right
    push Not at hfar
    choose E J hE hJs hJk hstep hz hE0 using fun c => axis_classify2 s q 1 hq7 le_rfl y x c (hfar c)
    have hJ0 : ∀ d, J d = 0 := fun d => by have := hJk d; omega
    have hstep0 : ∀ d, AxisStep2 s q 1 y x d (E d) 0 := fun d => by rw [← hJ0 d]; exact hstep d
    have hne : ∃ c, E c ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hxy (eq_of_cellN' s q 1 hq1 y x (fun d => hE0 d (hall d)))
    set Δr : Fin s → ℤ := fun c => (o0G s q 1 Φ x c : ℤ) - o0G s q 1 Φ y c with hΔr
    set Δd : Fin s → ℤ := fun c => (o1G s q Φ x c : ℤ) - o1G s q Φ y c with hΔd
    refine ⟨E, Δr, Δd, hE, hne, ?_, fun c => oG_bound s q 1 Φ x y c, ?_, fun c => o1G_bound s q Φ x y c, ?_⟩
    · intro c
      have h := DgG_off_sub s q 1 Φ (by omega) (fun _ => F2) hrow c y x E J hJk hJs hstep ⟨0, by omega⟩ rfl
      rw [← o0G_cast s q 1 Φ x c ⟨0, by omega⟩ rfl,
        ← o0G_cast s q 1 Φ y c ⟨0, by omega⟩ rfl] at h
      have hJf : J = fun _ => 0 := funext hJ0
      rw [hJf, sig2_k1] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [hΔr]
      push_cast
      rw [h]; ring
    · intro c
      have h := DgG_off1_sub s q Φ hs D1 hrow1 c y x E hstep0 ⟨1, by omega⟩ rfl
      rw [← o1G_cast s q Φ hs x c ⟨1, by omega⟩ rfl, ← o1G_cast s q Φ hs y c ⟨1, by omega⟩ rfl] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [hΔd]
      push_cast
      rw [h]; unfold dotR; push_cast; ring
    · set U2 : ℤ := (q : ℤ) ^ (s * 1 - 1 - 1 - 1) with hU2_def
      have hU2 : 0 < U2 := by positivity
      have hU2q : U = U2 * q := by rw [hU_def, hU2_def, ← pow_succ]; congr 1; omega
      set V : Fin s → ℤ := fun c => (q : ℤ) ^ 2 * E c + q * Δr c + Δd c with hV
      have htl2 : ∀ c, |(tl2G s q Φ x c : ℤ) - tl2G s q Φ y c| < U2 := by
        intro c
        have h1 := tl2G_lt s q Φ hs x c
        have h2 := tl2G_lt s q Φ hs y c
        have h1' : ((tl2G s q Φ x c : ℕ) : ℤ) < U2 := by rw [hU2_def]; exact_mod_cast h1
        have h2' : ((tl2G s q Φ y c : ℕ) : ℤ) < U2 := by rw [hU2_def]; exact_mod_cast h2
        rw [abs_lt]; constructor <;> omega
      have hVb : ∀ c, |V c| ≤ 3 * (q : ℤ) ^ 2 - 1 := by
        intro c
        have h1 := oG_bound s q 1 Φ x y c
        have h2 := o1G_bound s q Φ x y c
        have b1 : |Δr c| ≤ q - 1 := by simp only [hΔr]; omega
        have b2 : |Δd c| ≤ q - 1 := by simp only [hΔd]; omega
        have b0 : |E c| ≤ 2 := hE c
        have := abs_add_le ((q : ℤ) ^ 2 * E c + q * Δr c) (Δd c)
        have := abs_add_le ((q : ℤ) ^ 2 * E c) (q * Δr c)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (q : ℤ) ^ 2)] at this
        have h3 : |(q : ℤ) * Δr c| = q * |Δr c| := by rw [abs_mul, abs_of_pos (by positivity)]
        simp only [hV]
        nlinarith
      have hXV : ∀ c, ∃ z : ℤ, (X x c : ℤ) - X y c =
          U2 * V c + ((tl2G s q Φ x c : ℤ) - tl2G s q Φ y c) + z * ((q ^ (s * 1) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hz c
        refine ⟨z, ?_⟩
        rw [hXdef, XG_decomp2 s q Φ hs x c, XG_decomp2 s q Φ hs y c, hN]
        have e1 : (q : ℤ) ^ (s * 1 - 1) = U2 * q ^ 2 := by rw [hpow, hU2q]; ring
        have e2 : (q : ℤ) ^ (s * 1 - 1 - 1) = U2 * q := by rw [← hU_def, hU2q]
        have hc : (cellN s q 1 x c : ℤ) = cellN s q 1 y c + E c + z * (q : ℤ) ^ 1 := by linarith
        rw [hc, e1, e2]
        simp only [hV, hΔr, hΔd]
        ring
      set xc : Fin s → ℤ := fun c =>
        ((Z3NetU.cres (q ^ (s * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) / U2 with hxc_def
      have hnear : ∀ c, 0 ≤ xc c ∧ |V c| - 1 ≤ xc c ∧
          U2 * xc c ≤ ((Z3NetU.cres (q ^ (s * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hXV c
        simp only [hxc_def]
        rw [hzc]
        have := Z3NetU.Proofs.near_gen (q ^ (s * 1)) U2 (V c) _ z hU2 (htl2 c) (by
          rw [hN]
          have := abs_add_le (U2 * V c) ((tl2G s q Φ x c : ℤ) - tl2G s q Φ y c)
          rw [abs_mul, abs_of_pos hU2] at this
          have := hVb c; have := htl2 c
          have e1 : (q : ℤ) ^ (s * 1 - 1) * (q : ℤ) ^ 1 = U2 * (q : ℤ) ^ 2 * q := by
            rw [hpow, hU2q]; ring
          rw [e1]
          have hq7' : (7 : ℤ) ≤ q := by exact_mod_cast hq7
          have h0 : 0 < U2 * (q : ℤ) ^ 2 := by positivity
          nlinarith)
        exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hsq : ∀ c, (U2 * max 0 (|V c| - 1)) ^ 2 ≤
          ((Z3NetU.cres (q ^ (s * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        intro c
        obtain ⟨h1, h2, h3⟩ := hnear c
        have hm : max 0 (|V c| - 1) ≤ xc c := max_le h1 h2
        have hm0 : 0 ≤ max 0 (|V c| - 1) := le_max_left _ _
        exact pow_le_pow_left₀ (mul_nonneg hU2.le hm0) ((mul_le_mul_of_nonneg_left hm hU2.le).trans h3) 2
      have hU22 : (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) = U2 ^ 2 := by rw [hU2_def, ← pow_mul]; ring_nf
      calc (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) *
            ∑ c, (max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1)) ^ 2
          = ∑ c, (U2 * max 0 (|V c| - 1)) ^ 2 := by
            rw [hU22, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by simp only [hV]; ring
        _ ≤ _ := Finset.sum_le_sum fun c _ => hsq c

/-- **`lem:R2`**: for every odd `q` and every graph form over `ℤ/qℤ` with depths `(1, …, 1)`, half-integral first
offset rows `F₀ = F2/2` and integer second offset rows `D₁` (deeper rows arbitrary), if `q > |2β_c|` and
`q > |v_c|` on all steps `E ∈ {-2, …, 2}^s`, then `δ N^(1/s) ≥ LB₂(q)` (toroidal distance). -/
theorem R2_sep_core (s q : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (F2 D1 : Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q)
    (hrow : RowDesign s q 1 Φ (fun _ => F2)) (hrow1 : Row1Design s q Φ D1) (hodd : ∀ c d, Odd (F2 c d))
    (hβ : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR F2 E c| < q)
    (hv : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR D1 E c| < q)
    (x y : Fin (s * 1) → ZMod q) (hxy : x ≠ y) :
    LB2R q F2 D1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * 1))
          ((GFpoint s q 1 Φ x c : ℤ) - (GFpoint s q 1 Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * 1)) ^ 2) := by
  -- `q ≥ 7`
  have hq7 : 7 ≤ q := by
    set c0 : Fin s := ⟨0, by omega⟩
    have h := hβ (fun d => 2 * Int.sign (F2 c0 d)) c0
      (fun d => by rcases Int.sign_trichotomy (F2 c0 d) with h | h | h <;> rw [h] <;> norm_num)
    have hval : dotR F2 (fun d => 2 * Int.sign (F2 c0 d)) c0 = ∑ d, 2 * |F2 c0 d| := by
      unfold dotR
      refine sum_congr rfl fun d _ => ?_
      rw [show F2 c0 d * (2 * (F2 c0 d).sign) = 2 * ((F2 c0 d).sign * F2 c0 d) by ring,
        Int.sign_mul_self_eq_abs]
    rw [hval] at h
    have hge : (s : ℤ) * 2 ≤ ∑ d, 2 * |F2 c0 d| := by
      have : ∑ _d : Fin s, (2 : ℤ) ≤ ∑ d, 2 * |F2 c0 d| := Finset.sum_le_sum fun d _ => by
        obtain ⟨t, ht⟩ := hodd c0 d
        have : (1 : ℤ) ≤ |F2 c0 d| := Int.one_le_abs (by omega)
        linarith
      simpa [mul_comm] using this
    have hs' : (3 : ℤ) ≤ s := by exact_mod_cast hs
    have : abs (∑ d, 2 * |F2 c0 d|) = ∑ d, 2 * |F2 c0 d| :=
      abs_of_nonneg (Finset.sum_nonneg fun d _ => by positivity)
    rw [this] at h
    have : (6 : ℤ) < q := by linarith
    obtain ⟨t, ht⟩ := hqodd
    omega
  haveI : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set S : ℝ := ∑ c, ((cres (q ^ (s * 1))
      ((GFpoint s q 1 Φ x c : ℤ) - (GFpoint s q 1 Φ y c : ℤ)) : ℝ)) ^ 2 with hS
  rw [sum_div_sq, ← hS]
  have hSZ : (S : ℝ) = ((∑ c : Fin s, ((Z3NetU.cres (q ^ (s * 1)) ((GFpoint s q 1 Φ x c : ℤ) -
      (GFpoint s q 1 Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) := by
    rw [hS]; push_cast; rfl
  have hN : (0 : ℝ) < ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) := by positivity
  -- `LB₂` is below the value of every step
  have hLBE : ∀ E : Fin s → ℤ, (∀ d, |E d| ≤ 2) → (∃ d, E d ≠ 0) →
      LB2R q F2 D1 ≤ Real.sqrt (∑ c, ((bR2 q F2 D1 E c : ℤ) : ℝ) ^ 2) / (2 * (q : ℝ) ^ 2) := by
    intro E hE hne
    have hmem : E ∈ halfSteps s := by
      simp only [halfSteps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
      refine ⟨fun d => abs_le.mp (hE d), fun h0 => ?_⟩
      obtain ⟨d, hd⟩ := hne; exact hd (by rw [h0]; rfl)
    refine (min_le_right _ _).trans ?_
    exact ciInf_le (f := fun E : halfSteps s =>
      Real.sqrt (∑ c, ((bR2 q F2 D1 (E : Fin s → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (q : ℝ) ^ 2))
      ⟨0, fun _ ⟨_, h⟩ => h ▸ by positivity⟩ ⟨E, hmem⟩
  rcases relaxR2 s q Φ hs hq7 F2 D1 hrow hrow1 x y hxy with hfar |
      ⟨E, Δr, Δd, hE, hne, hdvd, hΔr, hdvd1, hΔd, hbd⟩
  · have hR : (q : ℝ) ^ (2 * (s * 1 - 1 - 1)) * min ((4 * (q : ℝ)) ^ 2) ((4 * (q : ℝ)) ^ 2) ≤ 4 * S := by
      rw [min_self, hSZ]
      have := (Int.cast_le (R := ℝ)).mpr hfar
      push_cast at this ⊢
      have hM : (q : ℝ) ^ (2 * (s * 1 - 1)) = (q : ℝ) ^ (2 * (s * 1 - 1 - 1)) * (q : ℝ) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [hM] at this
      nlinarith
    have h := real_form s q 1 (by omega) le_rfl hq1 S (by positivity) _ _ hR
    rw [min_self, show 4 * (q : ℝ) / (2 * q) = 2 by field_simp; ring] at h
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hN.le).trans h
  · set a : ℝ := Real.sqrt (∑ c, ((bR2 q F2 D1 E c : ℤ) : ℝ) ^ 2) / q with ha
    have hcoord : ∀ c, bR2 q F2 D1 E c ≤ 2 * max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1) :=
      fun c => bR2_le q hqodd F2 D1 hodd E c (Δr c) (Δd c) (hdvd c) (hΔr c) (hβ E c hE) (hdvd1 c) (hΔd c)
        (hv E c hE)
    have hsumZ : ∑ c, (bR2 q F2 D1 E c) ^ 2 ≤
        4 * ∑ c, (max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have := hcoord c
      have h0 := bR2_nonneg q F2 D1 E c
      nlinarith
    have hR : (q : ℝ) ^ (2 * (s * 1 - 1 - 1)) * min (a ^ 2) (a ^ 2) ≤ 4 * S := by
      rw [min_self, ha, div_pow, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _), hSZ]
      have h1 : (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) * ∑ c, (bR2 q F2 D1 E c) ^ 2 ≤
          4 * ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * 1)) ((GFpoint s q 1 Φ x c : ℤ) -
            (GFpoint s q 1 Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        calc (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) * ∑ c, (bR2 q F2 D1 E c) ^ 2 ≤
            (q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) *
              (4 * ∑ c, (max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1)) ^ 2) :=
              mul_le_mul_of_nonneg_left hsumZ (by positivity)
          _ = 4 * ((q : ℤ) ^ (2 * (s * 1 - 1 - 1 - 1)) *
              ∑ c, (max 0 (|(q : ℤ) ^ 2 * E c + q * Δr c + Δd c| - 1)) ^ 2) := by ring
          _ ≤ _ := by linarith
      have := (Int.cast_le (R := ℝ)).mpr h1
      push_cast at this ⊢
      have hM : (q : ℝ) ^ (2 * (s * 1 - 1 - 1)) = (q : ℝ) ^ (2 * (s * 1 - 1 - 1 - 1)) * (q : ℝ) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [hM]
      have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      rw [show (q : ℝ) ^ (2 * (s * 1 - 1 - 1 - 1)) * (q : ℝ) ^ 2 *
          ((∑ c, ((bR2 q F2 D1 E c : ℤ) : ℝ) ^ 2) / (q : ℝ) ^ 2) =
          (q : ℝ) ^ (2 * (s * 1 - 1 - 1 - 1)) * ∑ c, ((bR2 q F2 D1 E c : ℤ) : ℝ) ^ 2 by
        field_simp]
      exact this
    have h := real_form s q 1 (by omega) le_rfl hq1 S (by positivity) _ _ hR
    rw [min_self] at h
    have hLBa : LB2R q F2 D1 ≤ a / (2 * q) := by
      rw [ha, div_div, show (q : ℝ) * (2 * q) = 2 * (q : ℝ) ^ 2 by ring]
      exact hLBE E hE hne
    exact (mul_le_mul_of_nonneg_right hLBa hN.le).trans h

end

end Z3NetHL.Proofs
