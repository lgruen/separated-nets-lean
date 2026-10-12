/-
Separation bound of Theorem `thm:sep` (Theorem 1(3)) for the nets `𝒫_{k,q}`.
(Paper: Well-separated (0,3k,3)-nets in every base q ≥ 4; cite by `\label`.)
-/
module
public import Z3Net.SepArith
public import Z3Net.SepDig

@[expose] public section

/-!
# Theorem `thm:sep`

## Architecture
* `Z3Net.SepArith` — integer core: step formula `eq:sigma` (`sg`), sign lemma (`decide` over
  `{-1,0,1}³ × {0,1}³`), per-coordinate bounds, `sep_core`, toroidal residue `cres_eq_abs`,
  carries `carry`.
* `Z3Net.SepPoly`, `Z3Net.SepBridge` — polynomial model: `τ` as `(reflect N ·).comp (1 - X)`
  (graded multiplicative), `K` as multiplication by `(1-t)^(-k)` in `R⟦X⟧`, and the generator
  matrices of Definition `def:net` expressed through them.
* `Z3Net.SepCell` — Proposition `prop:cell` (a), (b) and cell injectivity, via the CRT
  decomposition `V = A (t-1)^k + B t^k + Q t^k (t-1)^k`, over any nontrivial commutative ring.
* `Z3Net.SepDig` — the same at the level of digit vectors, all three coordinates (`T³ = 1`).
* this file — digit sums (`S`), the integer coordinate as `n · q^(2k) + r · q^(2k-1) + F`,
  and the proof of `P_sep`, `P_sep_ge8`, `P_sep_real`.

Note: the cell injectivity (the `(k,k,k)` box of `thm:t0`) is proved here directly
(`Dg_inj`), so no hypothesis on the net property is needed.
-/

namespace Z3Net.Sep

open Matrix

/-! ## Digit sums -/

/-- `S q f a = ∑_{j<a} f j · q^(a-1-j)` (digit `0` most significant). -/
def S (q : ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ := ∑ j ∈ Finset.range a, f j * q ^ (a - 1 - j)

theorem S_zero (q : ℕ) (f : ℕ → ℕ) : S q f 0 = 0 := by simp [S]

theorem S_succ (q : ℕ) (f : ℕ → ℕ) (a : ℕ) : S q f (a + 1) = S q f a * q + f a := by
  unfold S
  rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [mul_assoc, ← pow_succ]
  congr 2
  omega

theorem S_add (q : ℕ) (f : ℕ → ℕ) (a b : ℕ) :
    S q f (a + b) = S q f a * q ^ b + S q (fun j => f (a + j)) b := by
  induction b with
  | zero => simp [S]
  | succ b ih => rw [← add_assoc, S_succ, ih, S_succ, pow_succ]; ring

theorem S_one (q : ℕ) (f : ℕ → ℕ) : S q f 1 = f 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, S_succ, S_zero]; simp

theorem S_lt (q : ℕ) (f : ℕ → ℕ) (a : ℕ) (hf : ∀ j < a, f j < q) : S q f a < q ^ a := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
    rw [S_succ, pow_succ]
    have h1 := ih (fun j hj => hf j (by omega))
    have h2 := hf a (by omega)
    have : S q f a + 1 ≤ q ^ a := h1
    nlinarith

theorem S_congr (q : ℕ) (f g : ℕ → ℕ) (a : ℕ) (h : ∀ j < a, f j = g j) : S q f a = S q g a := by
  unfold S
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [h j hj]

theorem S_inj (q : ℕ) (f g : ℕ → ℕ) (a : ℕ) (hf : ∀ j < a, f j < q) (hg : ∀ j < a, g j < q)
    (h : S q f a = S q g a) : ∀ j < a, f j = g j := by
  induction a with
  | zero => intro j hj; omega
  | succ a ih =>
    rw [S_succ, S_succ] at h
    have hfa := hf a (by omega)
    have hga := hg a (by omega)
    have hq : 0 < q := by omega
    have h1 : f a = g a := by
      have := congrArg (· % q) h
      simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hfa,
        Nat.mod_eq_of_lt hga] at this
      exact this
    have h2 : S q f a = S q g a := by
      rw [h1] at h
      exact Nat.eq_of_mul_eq_mul_right hq (by omega)
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)) h2 j hj
    · exact h1

/-! ## The digits of a point of `𝒫_{k,q}` -/

section Point

variable {q k : ℕ}

/-- Digit `j` of coordinate `c` of the point with index `v`, as a natural number. -/
noncomputable def dig (q k : ℕ) (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : ℕ) : ℕ :=
  if h : j < 3 * k then (Dg k c v ⟨j, h⟩).val else 0

theorem dig_lt [NeZero q] (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : ℕ) : dig q k v c j < q := by
  unfold dig; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_ne_zero (NeZero.ne q)

theorem dig_cast [NeZero q] (v : Fin (3 * k) → ZMod q) (c : Fin 3) (j : Fin (3 * k)) :
    ((dig q k v c j : ℕ) : ZMod q) = Dg k c v j := by
  unfold dig; rw [dif_pos j.isLt]; simp

theorem Ppoint_eq_S (v : Fin (3 * k) → ZMod q) (c : Fin 3) :
    Ppoint q k v c = S q (dig q k v c) (3 * k) := by
  unfold Ppoint digPoint coord S
  rw [← Fin.sum_univ_eq_sum_range (fun j => dig q k v c j * q ^ (3 * k - 1 - j))]
  apply Finset.sum_congr rfl
  intro j _
  simp [dig, Dg]

/-- `X = n · q^(2k) + r · q^(2k-1) + F`. -/
theorem Ppoint_split (hk : 1 ≤ k) (v : Fin (3 * k) → ZMod q) (c : Fin 3) :
    Ppoint q k v c = S q (dig q k v c) k * (q * q ^ (2 * k - 1)) + dig q k v c k * q ^ (2 * k - 1)
      + S q (fun j => dig q k v c (k + 1 + j)) (2 * k - 1) := by
  rw [Ppoint_eq_S, show 3 * k = k + (1 + (2 * k - 1)) by omega, S_add, S_add, S_one, pow_add,
    pow_one]
  simp only [add_zero, add_assoc]

theorem cell_split (hk : 2 ≤ k) (f : ℕ → ℕ) :
    S q f k = S q f (k - 1) * q + f (k - 1) ∧ S q f (k - 1) = S q f (k - 2) * q + f (k - 2) := by
  constructor
  · conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [S_succ]
  · conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega]
    rw [S_succ]

theorem cell_eq_digits [NeZero q] (v w : Fin (3 * k) → ZMod q) (c : Fin 3)
    (h : S q (dig q k v c) k = S q (dig q k w c) k) :
    ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k c v j = Dg k c w j := by
  intro j hj
  have := S_inj q _ _ k (fun j _ => dig_lt v c j) (fun j _ => dig_lt w c j) h j hj
  rw [← dig_cast v c j, ← dig_cast w c j, this]

theorem tail_eq [NeZero q] (v w : Fin (3 * k) → ZMod q) (c : Fin 3)
    (h : ∀ j : Fin (3 * k), k < (j : ℕ) → Dg k c v j = Dg k c w j) :
    S q (fun j => dig q k v c (k + 1 + j)) (2 * k - 1) =
      S q (fun j => dig q k w c (k + 1 + j)) (2 * k - 1) := by
  apply S_congr
  intro j hj
  unfold dig
  by_cases hh : k + 1 + j < 3 * k
  · rw [dif_pos hh, dif_pos hh, h ⟨k + 1 + j, hh⟩ (by simp; omega)]
  · rw [dif_neg hh, dif_neg hh]

end Point

/-! ## The separation bound -/

theorem cres_cast (N : ℕ) (u : ℤ) :
    ((cres N u : ℕ) : ℤ) = ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) := rfl

set_option maxHeartbeats 1000000 in
/-- **Theorem `thm:sep`**, exact integer form (with `minC q = q² c(q)²`). -/
theorem P_sep_main (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * minC q ≤ (q : ℤ) ^ 2 * ∑ c : Fin 3,
      ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℕ) : ℤ) ^ 2 := by
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
  let n : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (dig q k x c) k
  let N1 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (dig q k x c) (k - 1)
  let N2 : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ := fun x c => S q (dig q k x c) (k - 2)
  let F : (Fin (3 * k) → ZMod q) → Fin 3 → ℕ :=
    fun x c => S q (fun j => dig q k x c (k + 1 + j)) (2 * k - 1)
  have hX : ∀ x c, (Ppoint q k x c : ℤ) =
      (n x c : ℤ) * ((q : ℤ) * B) + (dig q k x c k : ℤ) * B + (F x c : ℤ) := by
    intro x c
    simp only [n, F]
    rw [Ppoint_split hk1, ← hBdef]; push_cast; ring
  have hnG : ∀ x c, n x c < G := fun x c => S_lt q _ k (fun j _ => dig_lt x c j)
  have hFB : ∀ x c, F x c < B := fun x c => S_lt q _ _ (fun j _ => dig_lt x c _)
  have hn1 : ∀ x c, n x c = N1 x c * q + dig q k x c (k - 1) := fun x c =>
    (cell_split hk (dig q k x c)).1
  have hn2 : ∀ x c, N1 x c = N2 x c * q + dig q k x c (k - 2) := fun x c =>
    (cell_split hk (dig q k x c)).2
  -- the toroidal shifts
  have hzex : ∀ c : Fin 3, ∃ z : ℤ,
      ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℕ) : ℤ) =
        |((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) - z * ((q ^ (3 * k) : ℕ) : ℤ)| :=
    fun c => cres_eq_abs _ hNpos _
  choose z hz using hzex
  let E : Fin 3 → ℤ := fun c => (n v c : ℤ) - n w c - z c * G
  let s : Fin 3 → ℤ := fun c => (dig q k v c k : ℤ) - dig q k w c k
  let Fd : Fin 3 → ℤ := fun c => (F v c : ℤ) - F w c
  have hu : ∀ c, ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℕ) : ℤ) =
      |E c * q * B + s c * B + Fd c| := by
    intro c; rw [hz c, hX v c, hX w c, hN]; congr 1; simp only [E, s, Fd]; ring
  have hsq : ∀ c, |s c| < q := by
    intro c; have := dig_lt v c k; have := dig_lt w c k; simp only [s]; rw [abs_lt]
    constructor <;> omega
  have hFd : ∀ c, |Fd c| < B := by
    intro c; have := hFB v c; have := hFB w c; simp only [Fd]; rw [abs_lt]
    constructor <;> omega
  have hsum_nonneg : ∀ c, 0 ≤ ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) -
      (Ppoint q k w c : ℤ)) : ℕ) : ℤ) ^ 2 := fun c => sq_nonneg _
  have hmin1 := minC_le1 (q : ℤ)
  have hq0 : (0 : ℤ) ≤ q := by positivity
  -- Case 1: some cell difference of size ≥ 2
  by_cases hbig : ∃ c, 2 ≤ |E c|
  · obtain ⟨c, hc⟩ := hbig
    have hlow : (q : ℤ) * B ≤ ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) -
        (Ppoint q k w c : ℤ)) : ℕ) : ℤ) := by
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
    have hsq' : ((q : ℤ) * B) ^ 2 ≤ ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) -
        (Ppoint q k w c : ℤ)) : ℕ) : ℤ) ^ 2 := pow_le_pow_left₀ hqBpos hlow 2
    have hone : ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℕ) : ℤ) ^ 2
        ≤ ∑ c' : Fin 3, ((cres (q ^ (3 * k)) ((Ppoint q k v c' : ℤ) -
          (Ppoint q k w c' : ℤ)) : ℕ) : ℤ) ^ 2 :=
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
    exact Dg_inj k hk v w (fun c => cell_eq_digits v w c (hcell c (hzero c)))
  push Not at hzero
  -- carries
  have hcarry : ∀ c, ∃ κ : ℤ, (κ = 0 ∨ κ = 1) ∧
      (q : ℤ) ∣ (dig q k v c (k - 1) : ℤ) - (dig q k w c (k - 1) + E c) ∧
      (q : ℤ) ∣ (N1 v c : ℤ) - (N1 w c + κ * E c) := by
    intro c
    have hℓv := dig_lt v c (k - 1)
    have hℓw := dig_lt w c (k - 1)
    apply carry q ((q : ℤ) ^ (k - 1)) (N1 w c) (dig q k w c (k - 1)) (N1 v c) (dig q k v c (k - 1))
      (E c) (z c) (by positivity) hQdvd (by positivity) (by exact_mod_cast hℓw) (by positivity)
      (by exact_mod_cast hℓv) (hE3 c)
    have e1 : ((n v c : ℕ) : ℤ) = (N1 v c : ℤ) * q + dig q k v c (k - 1) := by
      rw [hn1 v c]; push_cast; ring
    have e2 : ((n w c : ℕ) : ℤ) = (N1 w c : ℤ) * q + dig q k w c (k - 1) := by
      rw [hn1 w c]; push_cast; ring
    have e3 : E c = (n v c : ℤ) - n w c - z c * G := rfl
    rw [hGQ] at e3
    linear_combination -e1 + e2 - e3
  choose κ hκ01 hℓ hN1 using hcarry
  -- the geometric digit: `s_c ≡ σ_c (mod q)`
  have hcastℓ : ∀ c, ((dig q k v c (k - 1) : ℕ) : ZMod q) =
      ((dig q k w c (k - 1) : ℕ) : ZMod q) + (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hℓ c)
    push_cast at this
    linear_combination this
  have hcasth : ∀ c, ((dig q k v c (k - 2) : ℕ) : ZMod q) =
      ((dig q k w c (k - 2) : ℕ) : ZMod q) + (κ c : ZMod q) * (E c : ZMod q) := by
    intro c
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hN1 c)
    have ev : ((N1 v c : ℕ) : ZMod q) = ((dig q k v c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 v c]; push_cast; simp
    have ew : ((N1 w c : ℕ) : ZMod q) = ((dig q k w c (k - 2) : ℕ) : ZMod q) := by
      rw [hn2 w c]; push_cast; simp
    push_cast at this
    rw [ev, ew] at this
    linear_combination this
  have hgeo : ∀ (x : Fin (3 * k) → ZMod q) (c : Fin 3), ((dig q k x c k : ℕ) : ZMod q) =
      -((dig q k x c (k - 1) : ℕ) : ZMod q) - ((dig q k x (c + 1) (k - 1) : ℕ) : ZMod q)
      + ((dig q k x (c + 2) (k - 1) : ℕ) : ZMod q) - ((dig q k x (c + 2) (k - 2) : ℕ) : ZMod q) := by
    intro x c
    have h := Dg_geo k hk c x
    rw [← dig_cast x c ⟨k, by omega⟩, ← dig_cast x c ⟨k - 1, by omega⟩,
      ← dig_cast x (c + 1) ⟨k - 1, by omega⟩, ← dig_cast x (c + 2) ⟨k - 1, by omega⟩,
      ← dig_cast x (c + 2) ⟨k - 2, by omega⟩] at h
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
    have := tail_eq v w c (Dg_jit k hk c v w (cell_eq_digits v w _ (hcell _ h1))
      (cell_eq_digits v w _ (hcell _ h2)))
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

end Z3Net.Sep

namespace Z3Net.Proofs

open Z3Net Z3Net.Sep

theorem P_sep (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Ppoint q k v) (Ppoint q k w) : ℤ) := by
  have h := P_sep_main q k hq hk v w hvw
  unfold torusDist2
  push_cast
  exact h

theorem P_sep_ge8 (q k : ℕ) (hq : 8 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) - 1) ^ 2
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Ppoint q k v) (Ppoint q k w) : ℤ) := by
  have h := P_sep q k (by omega) hk v w hvw
  have hq8 : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hmin : min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2)
      (3 * ((q : ℤ) - 3) ^ 2)) = ((q : ℤ) - 1) ^ 2 := by
    apply min_eq_left
    apply le_min <;> nlinarith
  rwa [hmin] at h

theorem P_sep_real (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    cP q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hint := P_sep q k hq hk v w hvw
  set T : ℝ := ∑ c : Fin 3, ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) :
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
  have hsum : ∑ c : Fin 3, ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℝ)
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
