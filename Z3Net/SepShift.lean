/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Sep
public import Z3Net.DShift

@[expose] public section

/-!
# V14 stage S10′: `thm:sep` under digital shifts (`prop:shift`) and the maximum norm (`prop:linf`)

The proof of `thm:sep` (`Z3Net/Sep.lean`, `P_sep_main`) for `𝒫_{k,q} ⊕ τ`: the digits of coordinate
`c` are `D_c v + τ_c` (`digS`). Every step of the proof uses only the cells, the residues of digit
differences, the bounds `|digit difference| < q` and `|tail difference| < q^(2k-1)`, and the vanishing
of a digit difference whose residue vanishes; the shift cancels in every difference. The geometric
relation `prop:cell`(a) acquires a constant (`hgeo`), which cancels in `σ`. The same case analysis
gives the `ℓ^∞` bound of `prop:linf` (`sep_core_inf`: in every step pattern of the sign lemma some
coordinate is backward with `|σ| ≤ 2`, or only one axis moves).
-/

namespace Z3Net.Sep

open Matrix

/-- **`prop:linf`, the integer core**: under the hypotheses of `sep_core`, some coordinate has
`|e_c q B + s_c B + F_c| ≥ B (q - 3)`. -/
theorem sep_core_inf (q B : ℤ) (hq : 4 ≤ q) (hB : 0 < B)
    (e0 e1 e2 κ0 κ1 κ2 s0 s1 s2 F0 F1 F2 : ℤ)
    (he0 : e0 = -1 ∨ e0 = 0 ∨ e0 = 1) (he1 : e1 = -1 ∨ e1 = 0 ∨ e1 = 1)
    (he2 : e2 = -1 ∨ e2 = 0 ∨ e2 = 1)
    (hκ0 : κ0 = 0 ∨ κ0 = 1) (hκ1 : κ1 = 0 ∨ κ1 = 1) (hκ2 : κ2 = 0 ∨ κ2 = 1)
    (hne : e0 ≠ 0 ∨ e1 ≠ 0 ∨ e2 ≠ 0)
    (hs0 : |s0| < q) (hs1 : |s1| < q) (hs2 : |s2| < q)
    (hd0 : q ∣ s0 - sg e0 e1 e2 κ2) (hd1 : q ∣ s1 - sg e1 e2 e0 κ0)
    (hd2 : q ∣ s2 - sg e2 e0 e1 κ1)
    (hF0 : |F0| < B) (hF1 : |F1| < B) (hF2 : |F2| < B)
    (hj0 : e1 = 0 → e2 = 0 → F0 = 0) (hj1 : e2 = 0 → e0 = 0 → F1 = 0)
    (hj2 : e0 = 0 → e1 = 0 → F2 = 0) :
    (B * (q - 3)) ^ 2 ≤ (e0 * q * B + s0 * B + F0) ^ 2 ∨
      (B * (q - 3)) ^ 2 ≤ (e1 * q * B + s1 * B + F1) ^ 2 ∨
      (B * (q - 3)) ^ 2 ≤ (e2 * q * B + s2 * B + F2) ^ 2 := by
  have mem3 : ∀ {e : ℤ}, (e = -1 ∨ e = 0 ∨ e = 1) → e ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro e h; rcases h with rfl | rfl | rfl <;> decide
  have mem2 : ∀ {e : ℤ}, (e = 0 ∨ e = 1) → e ∈ ({0, 1} : Finset ℤ) := by
    intro e h; rcases h with rfl | rfl <;> decide
  have pm1 : ∀ {e : ℤ}, (e = -1 ∨ e = 0 ∨ e = 1) → e ≠ 0 → (e = 1 ∨ e = -1) := by
    intro e h h0; omega
  have e2' : (B * (q - 1 - 2)) ^ 2 = (B * (q - 3)) ^ 2 := by ring
  by_cases hw : (e0 ≠ 0 ∧ e1 ≠ 0) ∨ (e1 ≠ 0 ∧ e2 ≠ 0) ∨ (e0 ≠ 0 ∧ e2 ≠ 0)
  · have hC := signLemma e0 (mem3 he0) e1 (mem3 he1) e2 (mem3 he2) κ0 (mem2 hκ0)
      κ1 (mem2 hκ1) κ2 (mem2 hκ2) hw
    have b0 : bw e0 (sg e0 e1 e2 κ2) → |sg e0 e1 e2 κ2| ≤ 2 →
        (B * (q - 3)) ^ 2 ≤ (e0 * q * B + s0 * B + F0) ^ 2 := fun hb hj => by
      have := coord_bound_j q B e0 _ s0 F0 2 hq hB hb (pm1 he0 hb.1) hj (by norm_num) hs0 hd0 hF0
      nlinarith
    have b1 : bw e1 (sg e1 e2 e0 κ0) → |sg e1 e2 e0 κ0| ≤ 2 →
        (B * (q - 3)) ^ 2 ≤ (e1 * q * B + s1 * B + F1) ^ 2 := fun hb hj => by
      have := coord_bound_j q B e1 _ s1 F1 2 hq hB hb (pm1 he1 hb.1) hj (by norm_num) hs1 hd1 hF1
      nlinarith
    have b2 : bw e2 (sg e2 e0 e1 κ1) → |sg e2 e0 e1 κ1| ≤ 2 →
        (B * (q - 3)) ^ 2 ≤ (e2 * q * B + s2 * B + F2) ^ 2 := fun hb hj => by
      have := coord_bound_j q B e2 _ s2 F2 2 hq hB hb (pm1 he2 hb.1) hj (by norm_num) hs2 hd2 hF2
      nlinarith
    rcases hC with ⟨ha, ha1, -⟩ | ⟨ha, ha1, -⟩ | ⟨ha, ha1, -⟩ | ⟨ha, ha2, -⟩
    · exact Or.inl (b0 ha (by linarith))
    · exact Or.inr (Or.inl (b1 ha (by linarith)))
    · exact Or.inr (Or.inr (b2 ha (by linarith)))
    · exact Or.inl (b0 ha ha2)
  · push Not at hw
    have one : ∀ a : ℤ, (B * (q - 1)) ^ 2 ≤ a → (B * (q - 3)) ^ 2 ≤ a := by
      intro a ha
      have h1 : 0 ≤ B * (q - 3) := mul_nonneg hB.le (by linarith)
      have h2 : B * (q - 3) ≤ B * (q - 1) := by nlinarith
      nlinarith [pow_le_pow_left₀ h1 h2 2]
    rcases hne with h | h | h
    · have h1 : e1 = 0 := hw.1 h
      have h2 : e2 = 0 := hw.2.2 h
      have hF := hj0 h1 h2
      subst hF h1 h2
      have hd : q ∣ s0 - -e0 := by simpa [sg] using hd0
      exact Or.inl (one _ (coord_bound_still q B e0 s0 hq hB (pm1 he0 h) hs0 hd))
    · have h0 : e0 = 0 := by by_contra h'; exact h (hw.1 h')
      have h2 : e2 = 0 := hw.2.1 h
      have hF := hj1 h2 h0
      subst hF h0 h2
      have hd : q ∣ s1 - -e1 := by simpa [sg] using hd1
      exact Or.inr (Or.inl (one _ (coord_bound_still q B e1 s1 hq hB (pm1 he1 h) hs1 hd)))
    · have h0 : e0 = 0 := by by_contra h'; exact h (hw.2.2 h')
      have h1 : e1 = 0 := by by_contra h'; exact h (hw.2.1 h')
      have hF := hj2 h0 h1
      subst hF h0 h1
      have hd : q ∣ s2 - -e2 := by simpa [sg] using hd2
      exact Or.inr (Or.inr (one _ (coord_bound_still q B e2 s2 hq hB (pm1 he2 h) hs2 hd)))

section Shift

variable {q k : ℕ}

/-- Digit `j` of coordinate `c` of the point with index `v` of `𝒫_{k,q} ⊕ τ`. -/
noncomputable def digS (q k : ℕ) (τ : Fin 3 → Fin (3 * k) → ZMod q) (v : Fin (3 * k) → ZMod q)
    (c : Fin 3) (j : ℕ) : ℕ :=
  if h : j < 3 * k then (Dg k c v ⟨j, h⟩ + τ c ⟨j, h⟩).val else 0

/-- The integer point of `𝒫_{k,q} ⊕ τ`. -/
noncomputable def PpS (q k : ℕ) (τ : Fin 3 → Fin (3 * k) → ZMod q) (v : Fin (3 * k) → ZMod q) :
    Fin 3 → ℕ :=
  Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v

theorem digS_lt [NeZero q] (τ : Fin 3 → Fin (3 * k) → ZMod q) (v : Fin (3 * k) → ZMod q) (c : Fin 3)
    (j : ℕ) : digS q k τ v c j < q := by
  unfold digS; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_ne_zero (NeZero.ne q)

theorem digS_cast [NeZero q] (τ : Fin 3 → Fin (3 * k) → ZMod q) (v : Fin (3 * k) → ZMod q) (c : Fin 3)
    (j : Fin (3 * k)) : ((digS q k τ v c j : ℕ) : ZMod q) = Dg k c v j + τ c j := by
  unfold digS; rw [dif_pos j.isLt]; simp

theorem PpS_eq_S (τ : Fin 3 → Fin (3 * k) → ZMod q) (v : Fin (3 * k) → ZMod q) (c : Fin 3) :
    PpS q k τ v c = S q (digS q k τ v c) (3 * k) := by
  unfold PpS Z3NetF.digPointShift S
  rw [← Fin.sum_univ_eq_sum_range (fun j => digS q k τ v c j * q ^ (3 * k - 1 - j))]
  apply Finset.sum_congr rfl
  intro j _
  simp [digS, Dg]

theorem PpS_split (τ : Fin 3 → Fin (3 * k) → ZMod q) (hk : 1 ≤ k) (v : Fin (3 * k) → ZMod q)
    (c : Fin 3) :
    PpS q k τ v c = S q (digS q k τ v c) k * (q * q ^ (2 * k - 1)) + digS q k τ v c k * q ^ (2 * k - 1)
      + S q (fun j => digS q k τ v c (k + 1 + j)) (2 * k - 1) := by
  rw [PpS_eq_S, show 3 * k = k + (1 + (2 * k - 1)) by omega, S_add, S_add, S_one, pow_add, pow_one]
  simp only [add_zero, add_assoc]

theorem cell_eq_digitsS [NeZero q] (τ : Fin 3 → Fin (3 * k) → ZMod q) (v w : Fin (3 * k) → ZMod q)
    (c : Fin 3) (h : S q (digS q k τ v c) k = S q (digS q k τ w c) k) :
    ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k c v j = Dg k c w j := by
  intro j hj
  have := S_inj q _ _ k (fun j _ => digS_lt τ v c j) (fun j _ => digS_lt τ w c j) h j hj
  have e := congrArg (fun n : ℕ => (n : ZMod q)) this
  simp only [digS_cast τ v c j, digS_cast τ w c j] at e
  exact add_right_cancel e

theorem tail_eqS [NeZero q] (τ : Fin 3 → Fin (3 * k) → ZMod q) (v w : Fin (3 * k) → ZMod q)
    (c : Fin 3) (h : ∀ j : Fin (3 * k), k < (j : ℕ) → Dg k c v j = Dg k c w j) :
    S q (fun j => digS q k τ v c (k + 1 + j)) (2 * k - 1) =
      S q (fun j => digS q k τ w c (k + 1 + j)) (2 * k - 1) := by
  apply S_congr
  intro j hj
  unfold digS
  by_cases hh : k + 1 + j < 3 * k
  · rw [dif_pos hh, dif_pos hh, h ⟨k + 1 + j, hh⟩ (by simp; omega)]
  · rw [dif_neg hh, dif_neg hh]

set_option maxHeartbeats 1000000 in
/-- **`prop:shift`, `thm:sep`** for every digital shift `τ`, exact integer form, and the `ℓ^∞` bound of
`prop:linf`: some coordinate has toroidal distance `≥ (q - 3) q^(2k-1)` (`= (1 - 3/q) q^(-k)` at unit
scale). -/
theorem P_sep_shift_main (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * minC q ≤ (q : ℤ) ^ 2 * ∑ c : Fin 3,
      ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) ^ 2 ∧
    ∃ c : Fin 3, ((q : ℤ) - 3) * (q : ℤ) ^ (2 * k - 1) ≤
      ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) := by
  have : NeZero q := ⟨by omega⟩
  have : Fact (1 < q) := ⟨by omega⟩
  have hk1 : 1 ≤ k := by omega
  -- scales
  set B : ℕ := q ^ (2 * k - 1) with hBdef
  set G : ℕ := q ^ k with hGdef
  have hBpos : 0 < B := by positivity
  have hqB : (q : ℤ) * B = (q : ℤ) ^ (2 * k) := by
    rw [hBdef]; push_cast; rw [← pow_succ']; congr 1; omega
  have hN : ((q ^ (3 * k) : ℕ) : ℤ) = (G : ℤ) * ((q : ℤ) * B) := by
    rw [hqB, hGdef]; push_cast; rw [← pow_add]; congr 1; omega
  have hNpos : 0 < q ^ (3 * k) := by positivity
  have hq4k : (q : ℤ) ^ (4 * k) = (q : ℤ) ^ 2 * (B : ℤ) ^ 2 := by
    rw [hBdef]; push_cast; rw [← pow_mul, ← pow_add]; congr 1; omega
  have hQdvd : (q : ℤ) ∣ (q : ℤ) ^ (k - 1) := dvd_pow_self _ (by omega)
  have hGQ : (G : ℤ) = (q : ℤ) ^ (k - 1) * q := by
    rw [hGdef]; push_cast; rw [← pow_succ]; congr 1; omega
  -- digit data
  let n : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digS q k τ x c) k
  let N1 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digS q k τ x c) (k - 1)
  let N2 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digS q k τ x c) (k - 2)
  let F : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ :=
    fun x c => S q (fun j => digS q k τ x c (k + 1 + j)) (2 * k - 1)
  have hX : ∀ x c, (PpS q k τ x c : ℤ) =
      (n x c : ℤ) * ((q : ℤ) * B) + (digS q k τ x c k : ℤ) * B + (F x c : ℤ) := by
    intro x c
    simp only [n, F]
    rw [PpS_split τ hk1, ← hBdef]; push_cast; ring
  have hnG : ∀ x c, n x c < G := fun x c => S_lt q _ k (fun j _ => digS_lt τ x c j)
  have hFB : ∀ x c, F x c < B := fun x c => S_lt q _ _ (fun j _ => digS_lt τ x c _)
  have hn1 : ∀ x c, n x c = N1 x c * q + digS q k τ x c (k - 1) := fun x c =>
    (cell_split hk (digS q k τ x c)).1
  have hn2 : ∀ x c, N1 x c = N2 x c * q + digS q k τ x c (k - 2) := fun x c =>
    (cell_split hk (digS q k τ x c)).2
  -- the toroidal shifts
  have hzex : ∀ c : Fin 3, ∃ z : ℤ,
      ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) =
        |((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) - z * ((q ^ (3 * k) : ℕ) : ℤ)| :=
    fun c => cres_eq_abs _ hNpos _
  choose z hz using hzex
  let E : Fin 3 → ℤ := fun c => (n v c : ℤ) - n w c - z c * G
  let s : Fin 3 → ℤ := fun c => (digS q k τ v c k : ℤ) - digS q k τ w c k
  let Fd : Fin 3 → ℤ := fun c => (F v c : ℤ) - F w c
  have hu : ∀ c, ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) =
      |E c * q * B + s c * B + Fd c| := by
    intro c; rw [hz c, hX v c, hX w c, hN]; congr 1; simp only [E, s, Fd]; ring
  have hsq : ∀ c, |s c| < q := by
    intro c; have := digS_lt τ v c k; have := digS_lt τ w c k; simp only [s]; rw [abs_lt]
    constructor <;> omega
  have hFd : ∀ c, |Fd c| < B := by
    intro c; have := hFB v c; have := hFB w c; simp only [Fd]; rw [abs_lt]
    constructor <;> omega
  have hsum_nonneg : ∀ c, 0 ≤ ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) -
      (PpS q k τ w c : ℤ)) : ℕ) : ℤ) ^ 2 := fun c => sq_nonneg _
  have hmin1 := minC_le1 (q : ℤ)
  have hq0 : (0 : ℤ) ≤ q := by positivity
  -- Case 1: some cell difference of size ≥ 2
  by_cases hbig : ∃ c, 2 ≤ |E c|
  · obtain ⟨c, hc⟩ := hbig
    have hlow : (q : ℤ) * B ≤ ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) -
        (PpS q k τ w c : ℤ)) : ℕ) : ℤ) := by
      rw [hu c]
      have h1 : |s c * B + Fd c| < (q : ℤ) * B := by
        have := hsq c; have := hFd c
        calc |s c * B + Fd c| ≤ |s c| * B + |Fd c| := by
              refine le_trans (abs_add_le _ _) ?_
              rw [abs_mul, abs_of_pos (show (0 : ℤ) < B by exact_mod_cast hBpos)]
          _ < (q : ℤ) * B := by
              have : |s c| ≤ (q : ℤ) - 1 := by omega
              nlinarith
      have h2 : 2 * ((q : ℤ) * B) ≤ |E c * q * B| := by
        rw [show E c * q * B = E c * (q * B) by ring, abs_mul,
          abs_of_pos (by positivity : (0 : ℤ) < q * B)]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      have := abs_sub_abs_le_abs_sub (E c * q * B) (-(s c * B + Fd c))
      rw [abs_neg, sub_neg_eq_add] at this
      rw [add_assoc]; linarith
    have hqBpos : (0 : ℤ) ≤ q * B := by positivity
    have hsq' : ((q : ℤ) * B) ^ 2 ≤ ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) -
        (PpS q k τ w c : ℤ)) : ℕ) : ℤ) ^ 2 := pow_le_pow_left₀ hqBpos hlow 2
    have hone : ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) ^ 2
        ≤ ∑ c' : Fin 3, ((cres (q ^ (3 * k)) ((PpS q k τ v c' : ℤ) -
          (PpS q k τ w c' : ℤ)) : ℕ) : ℤ) ^ 2 :=
      Finset.single_le_sum (fun c' _ => hsum_nonneg c') (Finset.mem_univ c)
    have hm : minC (q : ℤ) ≤ (q : ℤ) ^ 2 := le_trans hmin1 (by nlinarith)
    refine ⟨?_, c, le_trans ?_ hlow⟩
    swap
    · have e : (q : ℤ) ^ (2 * k - 1) = (B : ℤ) := by rw [hBdef]; push_cast; ring
      have : (0 : ℤ) < B := by exact_mod_cast hBpos
      rw [e]; nlinarith
    rw [hq4k]
    have hB2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 * (B : ℤ) ^ 2 := by positivity
    calc (q : ℤ) ^ 2 * (B : ℤ) ^ 2 * minC q ≤ (q : ℤ) ^ 2 * (B : ℤ) ^ 2 * (q : ℤ) ^ 2 :=
          mul_le_mul_of_nonneg_left hm hB2
      _ = (q : ℤ) ^ 2 * ((q : ℤ) * B) ^ 2 := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (le_trans hsq' hone) (by positivity)
  push Not at hbig
  have hE3 : ∀ c, E c = -1 ∨ E c = 0 ∨ E c = 1 := by
    intro c; have := hbig c; rw [abs_lt] at this; omega
  -- cells agree where `E = 0`
  have hcell : ∀ c, E c = 0 → n v c = n w c := by
    intro c hc
    have hv := hnG v c
    have hw := hnG w c
    have hGpos : (0 : ℤ) < G := by positivity
    have hzc : z c = 0 := by
      have h : (n v c : ℤ) - n w c = z c * G := by simp only [E] at hc; linarith
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · have : z c * G ≤ -G := by nlinarith
        omega
      · have : (G : ℤ) ≤ z c * G := by nlinarith
        omega
    simp only [E, hzc, zero_mul, sub_zero, sub_eq_zero] at hc
    exact_mod_cast hc
  by_cases hzero : ∀ c, E c = 0
  · exfalso
    apply hvw
    exact Dg_inj k hk v w (fun c => cell_eq_digitsS τ v w c (hcell c (hzero c)))
  push Not at hzero
  -- carries
  have hcarry : ∀ c, ∃ κ : ℤ, (κ = 0 ∨ κ = 1) ∧
      (q : ℤ) ∣ (digS q k τ v c (k - 1) : ℤ) - (digS q k τ w c (k - 1) + E c) ∧
      (q : ℤ) ∣ (N1 v c : ℤ) - (N1 w c + κ * E c) := by
    intro c
    have hℓv := digS_lt τ v c (k - 1)
    have hℓw := digS_lt τ w c (k - 1)
    apply carry q ((q : ℤ) ^ (k - 1)) (N1 w c) (digS q k τ w c (k - 1)) (N1 v c) (digS q k τ v c (k - 1))
      (E c) (z c) (by positivity) hQdvd (by positivity) (by exact_mod_cast hℓw) (by positivity)
      (by exact_mod_cast hℓv) (hE3 c)
    have e1 : ((n v c : ℕ) : ℤ) = (N1 v c : ℤ) * q + digS q k τ v c (k - 1) := by
      rw [hn1 v c]; push_cast; ring
    have e2 : ((n w c : ℕ) : ℤ) = (N1 w c : ℤ) * q + digS q k τ w c (k - 1) := by
      rw [hn1 w c]; push_cast; ring
    have e3 : E c = (n v c : ℤ) - n w c - z c * G := rfl
    rw [hGQ] at e3
    linear_combination -e1 + e2 - e3
  choose κ hκ01 hℓ hN1 using hcarry
  -- the geometric digit: `s_c ≡ σ_c (mod q)`
  have hcastℓ : ∀ c, ((digS q k τ v c (k - 1) : ℕ) : ZMod q) =
      ((digS q k τ w c (k - 1) : ℕ) : ZMod q) + (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hℓ c)
    push_cast at this
    linear_combination this
  have hcasth : ∀ c, ((digS q k τ v c (k - 2) : ℕ) : ZMod q) =
      ((digS q k τ w c (k - 2) : ℕ) : ZMod q) + (κ c : ZMod q) * (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hN1 c)
    have ev : ((N1 v c : ℕ) : ZMod q) = ((digS q k τ v c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 v c]; push_cast; simp
    have ew : ((N1 w c : ℕ) : ZMod q) = ((digS q k τ w c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 w c]; push_cast; simp
    push_cast at this
    rw [ev, ew] at this
    linear_combination this
  have hgeo : ∀ (x : Fin (3 * k) → ZMod q) (c : Fin 3), ((digS q k τ x c k : ℕ) : ZMod q) =
      -((digS q k τ x c (k - 1) : ℕ) : ZMod q) - ((digS q k τ x (c + 1) (k - 1) : ℕ) : ZMod q)
      + ((digS q k τ x (c + 2) (k - 1) : ℕ) : ZMod q) - ((digS q k τ x (c + 2) (k - 2) : ℕ) : ZMod q)
      + (τ c ⟨k, by omega⟩ + τ c ⟨k - 1, by omega⟩ + τ (c + 1) ⟨k - 1, by omega⟩
        - τ (c + 2) ⟨k - 1, by omega⟩ + τ (c + 2) ⟨k - 2, by omega⟩) := by
    intro x c
    have h := Dg_geo k hk c x
    rw [digS_cast τ x c ⟨k, by omega⟩, digS_cast τ x c ⟨k - 1, by omega⟩,
      digS_cast τ x (c + 1) ⟨k - 1, by omega⟩, digS_cast τ x (c + 2) ⟨k - 1, by omega⟩,
      digS_cast τ x (c + 2) ⟨k - 2, by omega⟩, h]
    ring
  have hσ : ∀ c, (q : ℤ) ∣ s c - sg (E c) (E (c + 1)) (E (c + 2)) (κ (c + 2)) := by
    intro c
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [s, sg]
    push_cast
    rw [hgeo v c, hgeo w c, hcastℓ c, hcastℓ (c + 1), hcastℓ (c + 2), hcasth (c + 2)]
    ring
  -- the jitter vanishes when only axis `c` moves
  have hjit : ∀ c, E (c + 1) = 0 → E (c + 2) = 0 → Fd c = 0 := by
    intro c h1 h2
    have := tail_eqS τ v w c (Dg_jit k hk c v w (cell_eq_digitsS τ v w _ (hcell _ h1))
      (cell_eq_digitsS τ v w _ (hcell _ h2)))
    simp only [Fd, F]; rw [this, sub_self]
  -- the core
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e02 : (0 : Fin 3) + 2 = 2 := rfl
  have e11 : (1 : Fin 3) + 1 = 2 := rfl
  have e12 : (1 : Fin 3) + 2 = 0 := rfl
  have e21 : (2 : Fin 3) + 1 = 0 := rfl
  have e22 : (2 : Fin 3) + 2 = 1 := rfl
  have hσ0 := hσ 0; have hσ1 := hσ 1; have hσ2 := hσ 2
  have hj0 := hjit 0; have hj1 := hjit 1; have hj2 := hjit 2
  rw [e01, e02] at hσ0 hj0
  rw [e11, e12] at hσ1 hj1
  rw [e21, e22] at hσ2 hj2
  have hne : E 0 ≠ 0 ∨ E 1 ≠ 0 ∨ E 2 ≠ 0 := by
    obtain ⟨c, hc⟩ := hzero
    fin_cases c
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)
  have core := sep_core (q : ℤ) (B : ℤ) (by exact_mod_cast hq) (by exact_mod_cast hBpos)
    (E 0) (E 1) (E 2) (κ 0) (κ 1) (κ 2) (s 0) (s 1) (s 2) (Fd 0) (Fd 1) (Fd 2)
    (hE3 0) (hE3 1) (hE3 2) (hκ01 0) (hκ01 1) (hκ01 2) hne (hsq 0) (hsq 1) (hsq 2)
    hσ0 hσ1 hσ2 (hFd 0) (hFd 1) (hFd 2) hj0 hj1 hj2
  have coreInf := sep_core_inf (q : ℤ) (B : ℤ) (by exact_mod_cast hq) (by exact_mod_cast hBpos)
    (E 0) (E 1) (E 2) (κ 0) (κ 1) (κ 2) (s 0) (s 1) (s 2) (Fd 0) (Fd 1) (Fd 2)
    (hE3 0) (hE3 1) (hE3 2) (hκ01 0) (hκ01 1) (hκ01 2) hne (hsq 0) (hsq 1) (hsq 2)
    hσ0 hσ1 hσ2 (hFd 0) (hFd 1) (hFd 2) hj0 hj1 hj2
  refine ⟨?_, ?_⟩
  · rw [Fin.sum_univ_three, hu 0, hu 1, hu 2, sq_abs, sq_abs, sq_abs, hq4k]
    have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
    calc (q : ℤ) ^ 2 * (B : ℤ) ^ 2 * minC q = (q : ℤ) ^ 2 * ((B : ℤ) ^ 2 * minC q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left core hq2
  · have hq3 : (0 : ℤ) ≤ (q : ℤ) - 3 := by have : (4 : ℤ) ≤ q := by exact_mod_cast hq
                                           linarith
    have hB0 : (0 : ℤ) ≤ B := by positivity
    have key : ∀ c : Fin 3, (B * ((q : ℤ) - 3)) ^ 2 ≤ (E c * q * B + s c * B + Fd c) ^ 2 →
        ((q : ℤ) - 3) * (q : ℤ) ^ (2 * k - 1) ≤
          ((cres (q ^ (3 * k)) ((PpS q k τ v c : ℤ) - (PpS q k τ w c : ℤ)) : ℕ) : ℤ) := by
      intro c hc
      rw [hu c]
      have h0 : (0 : ℤ) ≤ B * ((q : ℤ) - 3) := mul_nonneg hB0 hq3
      have h1 : B * ((q : ℤ) - 3) ≤ |E c * q * B + s c * B + Fd c| :=
        (sq_le_sq₀ h0 (abs_nonneg _)).mp (by rw [sq_abs]; exact hc)
      have e : ((q : ℤ) - 3) * (q : ℤ) ^ (2 * k - 1) = B * ((q : ℤ) - 3) := by
        rw [hBdef]; push_cast; ring
      rw [e]; exact h1
    rcases coreInf with h | h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
    · exact ⟨2, key 2 h⟩


end Shift

end Z3Net.Sep

namespace Z3Net.Proofs

open Z3Net Z3Net.Sep

theorem P_sep_shift (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v) (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w) : ℤ) := by
  have h := (P_sep_shift_main q k hq hk τ v w hvw).1
  unfold torusDist2
  push_cast
  exact h

theorem P_sep_shift_ge8 (q k : ℕ) (hq : 8 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) - 1) ^ 2
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v) (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w) : ℤ) := by
  have h := P_sep_shift q k (by omega) hk τ v w hvw
  have hq8 : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hmin : min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2)
      (3 * ((q : ℤ) - 3) ^ 2)) = ((q : ℤ) - 1) ^ 2 := by
    apply min_eq_left
    apply le_min <;> nlinarith
  rwa [hmin] at h

theorem P_sep_shift_real (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    cP q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v c : ℤ) - (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hint := P_sep_shift q k hq hk τ v w hvw
  set T : ℝ := ∑ c : Fin 3, ((cres (q ^ (3 * k)) ((Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v c : ℤ) - (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w c : ℤ)) :
    ℕ) : ℝ) ^ 2 with hT
  set mR : ℝ := min (((q : ℝ) - 1) ^ 2) (min (((q : ℝ) - 2) ^ 2 + ((q : ℝ) - 4) ^ 2)
    (3 * ((q : ℝ) - 3) ^ 2)) with hmR
  have hR : (q : ℝ) ^ (4 * k) * mR ≤ (q : ℝ) ^ 2 * T := by
    have := (Int.cast_le (R := ℝ)).mpr hint
    unfold torusDist2 at this
    push_cast at this
    rw [hmR, hT]
    exact this
  have hpow : ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ)) = ((q : ℝ) ^ k)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      show ((3 * k : ℕ) : ℝ) * (-(1 / 3 : ℝ)) = -(k : ℝ) by push_cast; ring,
      Real.rpow_neg hq0.le, Real.rpow_natCast]
  have hm : min ((1 - 1 / (q : ℝ)) ^ 2)
      (min ((1 - 2 / (q : ℝ)) ^ 2 + (1 - 4 / (q : ℝ)) ^ 2) (3 * (1 - 3 / (q : ℝ)) ^ 2)) =
      mR / (q : ℝ) ^ 2 := by
    have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
    rw [hmR, ← min_div_div_right hq2, ← min_div_div_right hq2]
    have hqne : (q : ℝ) ≠ 0 := hq0.ne'
    congr 1
    · field_simp
    · congr 1
      · field_simp
      · field_simp
  have hmR0 : 0 ≤ mR := by
    rw [hmR]; apply le_min (sq_nonneg _) (le_min (by positivity) (by positivity))
  unfold cP
  rw [hpow, hm]
  have hsum : ∑ c : Fin 3, ((cres (q ^ (3 * k)) ((Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v c : ℤ) - (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (3 * k)) ^ 2 = T / ((q : ℝ) ^ (3 * k)) ^ 2 := by
    rw [hT, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [div_pow]
  rw [hsum]
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  rw [show Real.sqrt (mR / (q : ℝ) ^ 2) * ((q : ℝ) ^ k)⁻¹ =
      Real.sqrt (mR / (q : ℝ) ^ 2 * (((q : ℝ) ^ k)⁻¹) ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have key : mR / (q : ℝ) ^ 2 * (((q : ℝ) ^ k)⁻¹) ^ 2 = mR / ((q : ℝ) ^ 2 * ((q : ℝ) ^ k) ^ 2) := by
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have e3 : ((q : ℝ) ^ (3 * k)) ^ 2 = (q : ℝ) ^ (4 * k) * ((q : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e3]
  have hk2 : (0 : ℝ) ≤ ((q : ℝ) ^ k) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hR hk2]

end Z3Net.Proofs
