/-
`rem:projlines`, the remedy for `𝒫_{k,q}`: `thm:sep` holds verbatim after rescaling a row `r ≥ k + 1` (the proof of
`thm:sep` re-run for an abstract digit map). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ProjDefs
public import Z3Net.Sep

@[expose] public section

/-!
# `rem:projlines`: `thm:sep` for the rescaled `𝒫_{k,q}` (V14 stage S13′)

The proof of `thm:sep` (`Z3Net.Sep.P_sep_main`) uses the digits of `𝒫_{k,q}` only through three facts: the cells
determine the index (`Dg_inj`), the geometric digit relation (`prop:cell`(a), `Dg_geo`), and the digits below the
geometric digit of a coordinate depend only on the cells of the other two (`prop:cell`(b), `Dg_jit`). `P_sep_gen` is the
same proof for any digit map with these three properties (the proof text of `P_sep_main`, with the digits abstracted);
`P_sep_rowScale_core` applies it to `𝒫_{k,q}` with row `r ≥ k + 1` of every generator matrix rescaled.
-/

namespace Z3Net.Sep

open Matrix

section Gen

variable {q k : ℕ}

/-- Digit `j` of coordinate `c` of the point with index `v` for the digit map `D`, as a natural number. -/
noncomputable def digD (D : (Fin (3 * k) → ZMod q) → Fin 3 → Fin (3 * k) → ZMod q)
    (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : ℕ) : ℕ :=
  if h : j < 3 * k then (D v c ⟨j, h⟩).val else 0

/-- The integer coordinate `∑_j digD j · q^(3k-1-j)`. -/
noncomputable def ptD (q k : ℕ) (D : (Fin (3 * k) → ZMod q) → Fin 3 → Fin (3 * k) → ZMod q)
    (v : Fin (3 * k) → ZMod q) (c : Fin 3) : ℕ :=
  S q (digD D v c) (3 * k)

variable (D : (Fin (3 * k) → ZMod q) → Fin 3 → Fin (3 * k) → ZMod q)

theorem digD_lt [NeZero q] (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : ℕ) : digD D v c j < q := by
  unfold digD; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_ne_zero (NeZero.ne q)

theorem digD_cast [NeZero q] (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : Fin (3 * k)) :
    ((digD D v c j : ℕ) : ZMod q) = D v c j := by
  unfold digD; rw [dif_pos j.isLt]; simp

theorem ptD_split (hk : 1 ≤ k) (v : Fin (3 * k) → ZMod q) (c : Fin 3) :
    ptD q k D v c = S q (digD D v c) k * (q * q ^ (2 * k - 1)) + digD D v c k * q ^ (2 * k - 1)
      + S q (fun j => digD D v c (k + 1 + j)) (2 * k - 1) := by
  rw [ptD, show 3 * k = k + (1 + (2 * k - 1)) by omega, S_add, S_add, S_one, pow_add, pow_one]
  simp only [add_zero, add_assoc]

theorem cell_eq_digitsD [NeZero q] (v w : Fin (3 * k) → ZMod q) (c : Fin 3)
    (h : S q (digD D v c) k = S q (digD D w c) k) :
    ∀ j : Fin (3 * k), (j : ℕ) < k → D v c j = D w c j := by
  intro j hj
  have := S_inj q _ _ k (fun j _ => digD_lt D v c j) (fun j _ => digD_lt D w c j) h j hj
  rw [← digD_cast D v c j, ← digD_cast D w c j, this]

theorem tail_eqD (v w : Fin (3 * k) → ZMod q) (c : Fin 3)
    (h : ∀ j : Fin (3 * k), k < (j : ℕ) → D v c j = D w c j) :
    S q (fun j => digD D v c (k + 1 + j)) (2 * k - 1) =
      S q (fun j => digD D w c (k + 1 + j)) (2 * k - 1) := by
  apply S_congr
  intro j hj
  unfold digD
  by_cases hh : k + 1 + j < 3 * k
  · rw [dif_pos hh, dif_pos hh, h ⟨k + 1 + j, hh⟩ (by simp; omega)]
  · rw [dif_neg hh, dif_neg hh]

set_option maxHeartbeats 1000000 in
/-- **`thm:sep` for an abstract digit map** (the proof of `P_sep_main`): if the cells determine the index (`hinj`), the
geometric digit satisfies `prop:cell`(a) (`hgeo`) and the digits below it satisfy `prop:cell`(b) (`hjit`), the bound
of `thm:sep` holds. -/
theorem P_sep_gen (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k)
    (D : (Fin (3 * k) → ZMod q) → Fin 3 → Fin (3 * k) → ZMod q)
    (hgeo : ∀ (x : Fin (3 * k) → ZMod q) (c : Fin 3), D x c ⟨k, by omega⟩ = -D x c ⟨k - 1, by omega⟩ -
      D x (c + 1) ⟨k - 1, by omega⟩ + D x (c + 2) ⟨k - 1, by omega⟩ - D x (c + 2) ⟨k - 2, by omega⟩)
    (hjit : ∀ (c : Fin 3) (v w : Fin (3 * k) → ZMod q),
      (∀ j : Fin (3 * k), (j : ℕ) < k → D v (c + 1) j = D w (c + 1) j) →
      (∀ j : Fin (3 * k), (j : ℕ) < k → D v (c + 2) j = D w (c + 2) j) →
      ∀ j : Fin (3 * k), k < (j : ℕ) → D v c j = D w c j)
    (hinj : ∀ v w : Fin (3 * k) → ZMod q,
      (∀ c : Fin 3, ∀ j : Fin (3 * k), (j : ℕ) < k → D v c j = D w c j) → v = w)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * minC q ≤ (q : ℤ) ^ 2 * ∑ c : Fin 3,
      ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) - (ptD q k D w c : ℤ)) : ℕ) : ℤ) ^ 2 := by
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
  let n : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digD D x c) k
  let N1 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digD D x c) (k - 1)
  let N2 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (digD D x c) (k - 2)
  let F : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ :=
    fun x c => S q (fun j => digD D x c (k + 1 + j)) (2 * k - 1)
  have hX : ∀ x c, (ptD q k D x c : ℤ) =
      (n x c : ℤ) * ((q : ℤ) * B) + (digD D x c k : ℤ) * B + (F x c : ℤ) := by
    intro x c
    simp only [n, F]
    rw [ptD_split D hk1, ← hBdef]; push_cast; ring
  have hnG : ∀ x c, n x c < G := fun x c => S_lt q _ k (fun j _ => digD_lt D x c j)
  have hFB : ∀ x c, F x c < B := fun x c => S_lt q _ _ (fun j _ => digD_lt D x c _)
  have hn1 : ∀ x c, n x c = N1 x c * q + digD D x c (k - 1) := fun x c =>
    (cell_split hk (digD D x c)).1
  have hn2 : ∀ x c, N1 x c = N2 x c * q + digD D x c (k - 2) := fun x c =>
    (cell_split hk (digD D x c)).2
  -- the toroidal shifts
  have hzex : ∀ c : Fin 3, ∃ z : ℤ,
      ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) - (ptD q k D w c : ℤ)) : ℕ) : ℤ) =
        |((ptD q k D v c : ℤ) - (ptD q k D w c : ℤ)) - z * ((q ^ (3 * k) : ℕ) : ℤ)| :=
    fun c => cres_eq_abs _ hNpos _
  choose z hz using hzex
  let E : Fin 3 → ℤ := fun c => (n v c : ℤ) - n w c - z c * G
  let s : Fin 3 → ℤ := fun c => (digD D v c k : ℤ) - digD D w c k
  let Fd : Fin 3 → ℤ := fun c => (F v c : ℤ) - F w c
  have hu : ∀ c, ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) - (ptD q k D w c : ℤ)) : ℕ) : ℤ) =
      |E c * q * B + s c * B + Fd c| := by
    intro c; rw [hz c, hX v c, hX w c, hN]; congr 1; simp only [E, s, Fd]; ring
  have hsq : ∀ c, |s c| < q := by
    intro c; have := digD_lt D v c k; have := digD_lt D w c k; simp only [s]; rw [abs_lt]
    constructor <;> omega
  have hFd : ∀ c, |Fd c| < B := by
    intro c; have := hFB v c; have := hFB w c; simp only [Fd]; rw [abs_lt]
    constructor <;> omega
  have hsum_nonneg : ∀ c, 0 ≤ ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) -
      (ptD q k D w c : ℤ)) : ℕ) : ℤ) ^ 2 := fun c => sq_nonneg _
  have hmin1 := minC_le1 (q : ℤ)
  have hq0 : (0 : ℤ) ≤ q := by positivity
  -- Case 1: some cell difference of size ≥ 2
  by_cases hbig : ∃ c, 2 ≤ |E c|
  · obtain ⟨c, hc⟩ := hbig
    have hlow : (q : ℤ) * B ≤ ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) -
        (ptD q k D w c : ℤ)) : ℕ) : ℤ) := by
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
    have hsq' : ((q : ℤ) * B) ^ 2 ≤ ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) -
        (ptD q k D w c : ℤ)) : ℕ) : ℤ) ^ 2 := pow_le_pow_left₀ hqBpos hlow 2
    have hone : ((cres (q ^ (3 * k)) ((ptD q k D v c : ℤ) - (ptD q k D w c : ℤ)) : ℕ) : ℤ) ^ 2
        ≤ ∑ c' : Fin 3, ((cres (q ^ (3 * k)) ((ptD q k D v c' : ℤ) -
          (ptD q k D w c' : ℤ)) : ℕ) : ℤ) ^ 2 :=
      Finset.single_le_sum (fun c' _ => hsum_nonneg c') (Finset.mem_univ c)
    have hm : minC (q : ℤ) ≤ (q : ℤ) ^ 2 := le_trans hmin1 (by nlinarith)
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
    exact hinj v w (fun c => cell_eq_digitsD D v w c (hcell c (hzero c)))
  push Not at hzero
  -- carries
  have hcarry : ∀ c, ∃ κ : ℤ, (κ = 0 ∨ κ = 1) ∧
      (q : ℤ) ∣ (digD D v c (k - 1) : ℤ) - (digD D w c (k - 1) + E c) ∧
      (q : ℤ) ∣ (N1 v c : ℤ) - (N1 w c + κ * E c) := by
    intro c
    have hℓv := digD_lt D v c (k - 1)
    have hℓw := digD_lt D w c (k - 1)
    apply carry q ((q : ℤ) ^ (k - 1)) (N1 w c) (digD D w c (k - 1)) (N1 v c) (digD D v c (k - 1))
      (E c) (z c) (by positivity) hQdvd (by positivity) (by exact_mod_cast hℓw) (by positivity)
      (by exact_mod_cast hℓv) (hE3 c)
    have e1 : ((n v c : ℕ) : ℤ) = (N1 v c : ℤ) * q + digD D v c (k - 1) := by
      rw [hn1 v c]; push_cast; ring
    have e2 : ((n w c : ℕ) : ℤ) = (N1 w c : ℤ) * q + digD D w c (k - 1) := by
      rw [hn1 w c]; push_cast; ring
    have e3 : E c = (n v c : ℤ) - n w c - z c * G := rfl
    rw [hGQ] at e3
    linear_combination -e1 + e2 - e3
  choose κ hκ01 hℓ hN1 using hcarry
  -- the geometric digit: `s_c ≡ σ_c (mod q)`
  have hcastℓ : ∀ c, ((digD D v c (k - 1) : ℕ) : ZMod q) =
      ((digD D w c (k - 1) : ℕ) : ZMod q) + (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hℓ c)
    push_cast at this
    linear_combination this
  have hcasth : ∀ c, ((digD D v c (k - 2) : ℕ) : ZMod q) =
      ((digD D w c (k - 2) : ℕ) : ZMod q) + (κ c : ZMod q) * (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hN1 c)
    have ev : ((N1 v c : ℕ) : ZMod q) = ((digD D v c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 v c]; push_cast; simp
    have ew : ((N1 w c : ℕ) : ZMod q) = ((digD D w c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 w c]; push_cast; simp
    push_cast at this
    rw [ev, ew] at this
    linear_combination this
  have hgeo : ∀ (x : Fin (3 * k) → ZMod q) (c : Fin 3), ((digD D x c k : ℕ) : ZMod q) =
      -((digD D x c (k - 1) : ℕ) : ZMod q) - ((digD D x (c + 1) (k - 1) : ℕ) : ZMod q)
      + ((digD D x (c + 2) (k - 1) : ℕ) : ZMod q) - ((digD D x (c + 2) (k - 2) : ℕ) : ZMod q) := by
    intro x c
    have h := hgeo x c
    rw [← digD_cast D x c ⟨k, by omega⟩, ← digD_cast D x c ⟨k - 1, by omega⟩,
      ← digD_cast D x (c + 1) ⟨k - 1, by omega⟩, ← digD_cast D x (c + 2) ⟨k - 1, by omega⟩,
      ← digD_cast D x (c + 2) ⟨k - 2, by omega⟩] at h
    exact h
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
    have := tail_eqD D v w c (hjit c v w (cell_eq_digitsD D v w _ (hcell _ h1))
      (cell_eq_digitsD D v w _ (hcell _ h2)))
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
  rw [Fin.sum_univ_three, hu 0, hu 1, hu 2, sq_abs, sq_abs, sq_abs, hq4k]
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
  calc (q : ℤ) ^ 2 * (B : ℤ) ^ 2 * minC q = (q : ℤ) ^ 2 * ((B : ℤ) ^ 2 * minC q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left core hq2

end Gen

/-- **`rem:projlines`, the remedy for `𝒫_{k,q}`**: `thm:sep` (exact integer form, as `P_sep`) for `𝒫_{k,q}` with row
`r ≥ k + 1` of each of the three generator matrices multiplied by an arbitrary `ρ_c ∈ ℤ/qℤ`. -/
theorem P_sep_rowScale_core (q k r : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (hr : k + 1 ≤ r) (ρ : Fin 3 → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k))
          (digPoint q (3 * k) (Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ) v)
          (digPoint q (3 * k) (Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ) w) :
            ℤ) := by
  have : NeZero q := ⟨by omega⟩
  have : Fact (1 < q) := ⟨by omega⟩
  set C := Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ with hC
  set D : (Fin (3 * k) → ZMod q) → Fin 3 → Fin (3 * k) → ZMod q := fun x c => C c *ᵥ x with hDdef
  have hD : ∀ x c (j : Fin (3 * k)), D x c j = if (j : ℕ) = r then ρ c * Dg k c x j else Dg k c x j := by
    intro x c j
    simp only [hDdef, hC, Dg, mulVec, dotProduct, Z3NetF.rowScale]
    split_ifs
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    · rfl
  have hlow : ∀ x c (j : Fin (3 * k)), (j : ℕ) ≤ k → D x c j = Dg k c x j := by
    intro x c j hj; rw [hD, if_neg (by omega)]
  have hpt : ∀ x c, digPoint q (3 * k) C x c = ptD q k D x c := by
    intro x c
    unfold digPoint coord ptD S
    rw [← Fin.sum_univ_eq_sum_range (fun j => digD D x c j * q ^ (3 * k - 1 - j))]
    apply Finset.sum_congr rfl
    intro j _
    simp [digD, hDdef]
  have hgeo : ∀ (x : Fin (3 * k) → ZMod q) (c : Fin 3), D x c ⟨k, by omega⟩ = -D x c ⟨k - 1, by omega⟩ -
      D x (c + 1) ⟨k - 1, by omega⟩ + D x (c + 2) ⟨k - 1, by omega⟩ - D x (c + 2) ⟨k - 2, by omega⟩ := by
    intro x c
    rw [hlow x c _ le_rfl, hlow x c _ (by simp), hlow x (c + 1) _ (by simp), hlow x (c + 2) _ (by simp),
      hlow x (c + 2) _ (by simp)]
    exact Dg_geo k hk c x
  have hjit : ∀ (c : Fin 3) (v w : Fin (3 * k) → ZMod q),
      (∀ j : Fin (3 * k), (j : ℕ) < k → D v (c + 1) j = D w (c + 1) j) →
      (∀ j : Fin (3 * k), (j : ℕ) < k → D v (c + 2) j = D w (c + 2) j) →
      ∀ j : Fin (3 * k), k < (j : ℕ) → D v c j = D w c j := by
    intro c v w h1 h2 j hj
    have e := Dg_jit k hk c v w
      (fun j hj' => by rw [← hlow v _ j (by omega), ← hlow w _ j (by omega)]; exact h1 j hj')
      (fun j hj' => by rw [← hlow v _ j (by omega), ← hlow w _ j (by omega)]; exact h2 j hj') j hj
    rw [hD, hD, e]
  have hinj : ∀ v w : Fin (3 * k) → ZMod q,
      (∀ c : Fin 3, ∀ j : Fin (3 * k), (j : ℕ) < k → D v c j = D w c j) → v = w := by
    intro v w h
    exact Dg_inj k hk v w (fun c j hj => by
      rw [← hlow v c j (by omega), ← hlow w c j (by omega)]; exact h c j hj)
  have h := P_sep_gen q k hq hk D hgeo hjit hinj v w hvw
  unfold torusDist2
  push_cast
  simp only [hpt]
  exact h

end Z3Net.Sep
