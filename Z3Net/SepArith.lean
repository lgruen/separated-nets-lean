/-
Separation bound of Theorem `thm:sep`: the purely arithmetic part.
(Paper: Well-separated (0,3k,3)-nets in every base q ≥ 4; cite by `\label`.)
-/
module
public import Mathlib

@[expose] public section

/-!
# Arithmetic core of `thm:sep`

Everything here is integer arithmetic, independent of the construction:

* `Sep.sg` is the step formula `eq:sigma`:
  `σ_i = -e_i - e_{i+1} + (1 - κ_{i+2}) e_{i+2}`.
* `Sep.signLemma` checks, by `decide` over all `e ∈ {-1,0,1}³` with at least two moving
  axes and all `κ ∈ {0,1}³`, a consequence of the sign lemma of the proof of `thm:sep` that
  is sufficient for the bound `c(q)` (it is not the paper's lemma (ii)–(iv) verbatim).
* `Sep.coord_bound` is the per-coordinate bound for a backward coordinate,
  `Sep.coord_bound_still` the jitter-free bound of case (i).
* `Sep.sep_core` combines them: `B² · min{(q-1)², (q-2)²+(q-4)², 3(q-3)²} ≤ ∑ u_c²`
  where `u_c = e_c q B + s_c B + F_c` is the coordinate difference at scale
  `B = q^(2k-1)` (one sub-cell).
* `Sep.cres_eq_abs` (the toroidal residue is `|u - zN|` for some `z`) and
  `Sep.carry` (the carry `κ` of the last two cell digits, including the torus wrap).
-/

namespace Z3Net.Sep

/-- The step formula `eq:sigma` for coordinate `i`, with `e0 = e_i`, `e1 = e_{i+1}`,
`e2 = e_{i+2}`, `κ2 = κ_{i+2}`. -/
def sg (e0 e1 e2 κ2 : ℤ) : ℤ := -e0 - e1 + (1 - κ2) * e2

/-- A moving coordinate is *backward* if `e σ ≤ 0`. -/
def bw (e s : ℤ) : Prop := e ≠ 0 ∧ e * s ≤ 0

instance (e s : ℤ) : Decidable (bw e s) := by unfold bw; infer_instance

/-- Conclusion of the sign lemma: either two distinct backward coordinates with
`|σ| ≤ 1` and `|σ| ≤ 3`, or three backward coordinates with `|σ| ≤ 2`. -/
def Concl (ex ey ez sx sy sz : ℤ) : Prop :=
    ((bw ex sx ∧ |sx| ≤ 1 ∧ ((bw ey sy ∧ |sy| ≤ 3) ∨ (bw ez sz ∧ |sz| ≤ 3))) ∨
     (bw ey sy ∧ |sy| ≤ 1 ∧ ((bw ex sx ∧ |sx| ≤ 3) ∨ (bw ez sz ∧ |sz| ≤ 3))) ∨
     (bw ez sz ∧ |sz| ≤ 1 ∧ ((bw ex sx ∧ |sx| ≤ 3) ∨ (bw ey sy ∧ |sy| ≤ 3))) ∨
     (bw ex sx ∧ |sx| ≤ 2 ∧ bw ey sy ∧ |sy| ≤ 2 ∧ bw ez sz ∧ |sz| ≤ 2))

instance (ex ey ez sx sy sz : ℤ) : Decidable (Concl ex ey ez sx sy sz) := by
  unfold Concl; infer_instance

/-- **Sign-lemma consequence** (proof of `thm:sep`): if at least two axes move, the backward
coordinates realise one of the two patterns of `Concl`. This is a consequence of the paper's sign
lemma sufficient for the bound `c(q)`, not the lemma itself. Checked over all `3³ · 2³` cases. -/
theorem signLemma : ∀ ex ∈ ({-1, 0, 1} : Finset ℤ), ∀ ey ∈ ({-1, 0, 1} : Finset ℤ),
    ∀ ez ∈ ({-1, 0, 1} : Finset ℤ), ∀ kx ∈ ({0, 1} : Finset ℤ), ∀ ky ∈ ({0, 1} : Finset ℤ),
    ∀ kz ∈ ({0, 1} : Finset ℤ),
    ((ex ≠ 0 ∧ ey ≠ 0) ∨ (ey ≠ 0 ∧ ez ≠ 0) ∨ (ex ≠ 0 ∧ ez ≠ 0)) →
    Concl ex ey ez (sg ex ey ez kz) (sg ey ez ex kx) (sg ez ex ey ky) := by
  decide

/-- **Per-coordinate bound** for a backward coordinate: `|Δ| ≥ a_{|σ|+1}`, at scale `B`. -/
theorem coord_bound (q B e σ s F : ℤ) (hq : 4 ≤ q) (hB : 0 < B) (he : e ≠ 0)
    (he1 : e = 1 ∨ e = -1) (hbw : e * σ ≤ 0) (hσ : |σ| ≤ 3) (hs : |s| < q)
    (hd : q ∣ s - σ) (hF : |F| < B) :
    (B * (q - |σ| - 1)) ^ 2 ≤ (e * q * B + s * B + F) ^ 2 := by
  obtain ⟨t, ht⟩ := hd
  rw [abs_lt] at hs hF
  rw [abs_le] at hσ
  have hnn : 0 ≤ B * (q - |σ| - 1) := by
    apply mul_nonneg hB.le
    rcases abs_cases σ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> linarith
  rcases he1 with rfl | rfl
  · -- e = 1, σ ≤ 0
    have hσ0 : σ ≤ 0 := by linarith
    have ht0 : 0 ≤ t := by
      by_contra h
      push Not at h
      have : q * t ≤ -q := by nlinarith
      linarith
    have hsσ : σ ≤ s := by nlinarith
    have key : B * (q - |σ| - 1) ≤ 1 * q * B + s * B + F := by
      rw [abs_of_nonpos hσ0]; nlinarith
    exact pow_le_pow_left₀ hnn key 2
  · -- e = -1, σ ≥ 0
    have hσ0 : 0 ≤ σ := by linarith
    have ht0 : t ≤ 0 := by
      by_contra h
      push Not at h
      have : q ≤ q * t := by nlinarith
      linarith
    have hsσ : s ≤ σ := by nlinarith
    have key : B * (q - |σ| - 1) ≤ -(-1 * q * B + s * B + F) := by
      rw [abs_of_nonneg hσ0]; nlinarith
    have := pow_le_pow_left₀ hnn key 2
    have e : (-(-1 * q * B + s * B + F)) ^ 2 = (-1 * q * B + s * B + F) ^ 2 := by ring
    linarith

/-- Jitter-free bound of case (i): if only axis `i` moves then `σ_i = -e_i` and the tails agree,
so `|Δ_i| ≥ 1 - 1/q`. -/
theorem coord_bound_still (q B e s : ℤ) (hq : 4 ≤ q) (hB : 0 < B)
    (he1 : e = 1 ∨ e = -1) (hs : |s| < q) (hd : q ∣ s - -e) :
    (B * (q - 1)) ^ 2 ≤ (e * q * B + s * B + 0) ^ 2 := by
  obtain ⟨t, ht⟩ := hd
  rw [abs_lt] at hs
  have hnn : 0 ≤ B * (q - 1) := mul_nonneg hB.le (by linarith)
  rcases he1 with rfl | rfl
  · have ht0 : 0 ≤ t := by
      by_contra h
      push Not at h
      have : q * t ≤ -q := by nlinarith
      linarith
    have key : B * (q - 1) ≤ 1 * q * B + s * B + 0 := by nlinarith
    exact pow_le_pow_left₀ hnn key 2
  · have ht0 : t ≤ 0 := by
      by_contra h
      push Not at h
      have : q ≤ q * t := by nlinarith
      linarith
    have key : B * (q - 1) ≤ -(-1 * q * B + s * B + 0) := by nlinarith
    have := pow_le_pow_left₀ hnn key 2
    have e : (-(-1 * q * B + s * B + 0)) ^ 2 = (-1 * q * B + s * B + 0) ^ 2 := by ring
    linarith

/-- Weakened per-coordinate bound with a uniform `j ≥ |σ|`. -/
theorem coord_bound_j (q B e σ s F j : ℤ) (hq : 4 ≤ q) (hB : 0 < B)
    (hbw : bw e σ) (he1 : e = 1 ∨ e = -1) (hσj : |σ| ≤ j) (hj : j ≤ 3) (hs : |s| < q)
    (hd : q ∣ s - σ) (hF : |F| < B) :
    B ^ 2 * (q - 1 - j) ^ 2 ≤ (e * q * B + s * B + F) ^ 2 := by
  have h1 := coord_bound q B e σ s F hq hB hbw.1 he1 hbw.2 (le_trans hσj hj) hs hd hF
  have h0 : 0 ≤ B * (q - 1 - j) := mul_nonneg hB.le (by linarith)
  have h2 : B * (q - 1 - j) ≤ B * (q - |σ| - 1) := by nlinarith
  have := pow_le_pow_left₀ h0 h2 2
  nlinarith

/-- The constant `q² c(q)²`. -/
def minC (q : ℤ) : ℤ := min ((q - 1) ^ 2) (min ((q - 2) ^ 2 + (q - 4) ^ 2) (3 * (q - 3) ^ 2))

theorem minC_le1 (q : ℤ) : minC q ≤ (q - 1) ^ 2 := min_le_left _ _
theorem minC_le2 (q : ℤ) : minC q ≤ (q - 2) ^ 2 + (q - 4) ^ 2 :=
  le_trans (min_le_right _ _) (min_le_left _ _)
theorem minC_le3 (q : ℤ) : minC q ≤ 3 * (q - 3) ^ 2 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

private theorem mem3 {e : ℤ} (h : e = -1 ∨ e = 0 ∨ e = 1) : e ∈ ({-1, 0, 1} : Finset ℤ) := by
  rcases h with rfl | rfl | rfl <;> decide

private theorem mem2 {e : ℤ} (h : e = 0 ∨ e = 1) : e ∈ ({0, 1} : Finset ℤ) := by
  rcases h with rfl | rfl <;> decide

private theorem pm1 {e : ℤ} (h : e = -1 ∨ e = 0 ∨ e = 1) (h0 : e ≠ 0) : e = 1 ∨ e = -1 := by
  omega

/-- **Core of `thm:sep`** (scale `B` = one sub-cell, cell side `q B`): for a nonzero step
`e ∈ {-1,0,1}³` with carries `κ`, geometric-digit differences `s_c ≡ σ_c (mod q)`,
`|s_c| < q`, tail differences `|F_c| < B` that vanish when only axis `c` moves,
`∑_c (e_c q B + s_c B + F_c)² ≥ B² q² c(q)²`. -/
theorem sep_core (q B : ℤ) (hq : 4 ≤ q) (hB : 0 < B)
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
    B ^ 2 * minC q ≤ (e0 * q * B + s0 * B + F0) ^ 2 + (e1 * q * B + s1 * B + F1) ^ 2
      + (e2 * q * B + s2 * B + F2) ^ 2 := by
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have m1 := minC_le1 q
  have m2 := minC_le2 q
  have m3 := minC_le3 q
  have p0 := sq_nonneg (e0 * q * B + s0 * B + F0)
  have p1 := sq_nonneg (e1 * q * B + s1 * B + F1)
  have p2 := sq_nonneg (e2 * q * B + s2 * B + F2)
  by_cases hw : (e0 ≠ 0 ∧ e1 ≠ 0) ∨ (e1 ≠ 0 ∧ e2 ≠ 0) ∨ (e0 ≠ 0 ∧ e2 ≠ 0)
  · have hC := signLemma e0 (mem3 he0) e1 (mem3 he1) e2 (mem3 he2) κ0 (mem2 hκ0)
      κ1 (mem2 hκ1) κ2 (mem2 hκ2) hw
    -- generic per-coordinate bounds
    have b0 : ∀ j : ℤ, bw e0 (sg e0 e1 e2 κ2) → |sg e0 e1 e2 κ2| ≤ j → j ≤ 3 →
        B ^ 2 * (q - 1 - j) ^ 2 ≤ (e0 * q * B + s0 * B + F0) ^ 2 := fun j hb hj hj3 =>
      coord_bound_j q B e0 _ s0 F0 j hq hB hb (pm1 he0 hb.1) hj hj3 hs0 hd0 hF0
    have b1 : ∀ j : ℤ, bw e1 (sg e1 e2 e0 κ0) → |sg e1 e2 e0 κ0| ≤ j → j ≤ 3 →
        B ^ 2 * (q - 1 - j) ^ 2 ≤ (e1 * q * B + s1 * B + F1) ^ 2 := fun j hb hj hj3 =>
      coord_bound_j q B e1 _ s1 F1 j hq hB hb (pm1 he1 hb.1) hj hj3 hs1 hd1 hF1
    have b2 : ∀ j : ℤ, bw e2 (sg e2 e0 e1 κ1) → |sg e2 e0 e1 κ1| ≤ j → j ≤ 3 →
        B ^ 2 * (q - 1 - j) ^ 2 ≤ (e2 * q * B + s2 * B + F2) ^ 2 := fun j hb hj hj3 =>
      coord_bound_j q B e2 _ s2 F2 j hq hB hb (pm1 he2 hb.1) hj hj3 hs2 hd2 hF2
    have two : ∀ a b c : ℤ, B ^ 2 * (q - 1 - 1) ^ 2 ≤ a → B ^ 2 * (q - 1 - 3) ^ 2 ≤ b →
        0 ≤ c → B ^ 2 * minC q ≤ a + b + c := by
      intro a b c ha hb hc
      have : B ^ 2 * minC q ≤ B ^ 2 * ((q - 2) ^ 2 + (q - 4) ^ 2) :=
        mul_le_mul_of_nonneg_left m2 hB2
      nlinarith
    rcases hC with ⟨ha, ha1, (⟨hb, hb3⟩ | ⟨hb, hb3⟩)⟩ | ⟨ha, ha1, (⟨hb, hb3⟩ | ⟨hb, hb3⟩)⟩ |
        ⟨ha, ha1, (⟨hb, hb3⟩ | ⟨hb, hb3⟩)⟩ | ⟨ha, ha2, hb, hb2, hc, hc2⟩
    · have := two _ _ _ (b0 1 ha ha1 (by norm_num)) (b1 3 hb hb3 le_rfl) p2; linarith
    · have := two _ _ _ (b0 1 ha ha1 (by norm_num)) (b2 3 hb hb3 le_rfl) p1; linarith
    · have := two _ _ _ (b1 1 ha ha1 (by norm_num)) (b0 3 hb hb3 le_rfl) p2; linarith
    · have := two _ _ _ (b1 1 ha ha1 (by norm_num)) (b2 3 hb hb3 le_rfl) p0; linarith
    · have := two _ _ _ (b2 1 ha ha1 (by norm_num)) (b0 3 hb hb3 le_rfl) p1; linarith
    · have := two _ _ _ (b2 1 ha ha1 (by norm_num)) (b1 3 hb hb3 le_rfl) p0; linarith
    · have x0 := b0 2 ha ha2 (by norm_num)
      have x1 := b1 2 hb hb2 (by norm_num)
      have x2 := b2 2 hc hc2 (by norm_num)
      have : B ^ 2 * minC q ≤ B ^ 2 * (3 * (q - 3) ^ 2) := mul_le_mul_of_nonneg_left m3 hB2
      nlinarith
  · -- exactly one axis moves
    push Not at hw
    have one : ∀ a : ℤ, B ^ 2 * (q - 1) ^ 2 ≤ a → B ^ 2 * minC q ≤ a := by
      intro a ha
      have : B ^ 2 * minC q ≤ B ^ 2 * (q - 1) ^ 2 := mul_le_mul_of_nonneg_left m1 hB2
      linarith
    rcases hne with h | h | h
    · have h1 : e1 = 0 := hw.1 h
      have h2 : e2 = 0 := hw.2.2 h
      have hF := hj0 h1 h2
      subst hF h1 h2
      have hd : q ∣ s0 - -e0 := by simpa [sg] using hd0
      have := coord_bound_still q B e0 s0 hq hB (pm1 he0 h) hs0 hd
      have := one _ (by nlinarith : B ^ 2 * (q - 1) ^ 2 ≤ (e0 * q * B + s0 * B + 0) ^ 2)
      linarith
    · have h0 : e0 = 0 := by by_contra h'; exact h (hw.1 h')
      have h2 : e2 = 0 := hw.2.1 h
      have hF := hj1 h2 h0
      subst hF h0 h2
      have hd : q ∣ s1 - -e1 := by simpa [sg] using hd1
      have := coord_bound_still q B e1 s1 hq hB (pm1 he1 h) hs1 hd
      have := one _ (by nlinarith : B ^ 2 * (q - 1) ^ 2 ≤ (e1 * q * B + s1 * B + 0) ^ 2)
      linarith
    · have h0 : e0 = 0 := by by_contra h'; exact h (hw.2.2 h')
      have h1 : e1 = 0 := by by_contra h'; exact h (hw.2.1 h')
      have hF := hj2 h0 h1
      subst hF h0 h1
      have hd : q ∣ s2 - -e2 := by simpa [sg] using hd2
      have := coord_bound_still q B e2 s2 hq hB (pm1 he2 h) hs2 hd
      have := one _ (by nlinarith : B ^ 2 * (q - 1) ^ 2 ≤ (e2 * q * B + s2 * B + 0) ^ 2)
      linarith

/-- The toroidal residue is `|u - z N|` for a suitable `z`. -/
theorem cres_eq_abs (N : ℕ) (hN : 0 < N) (u : ℤ) :
    ∃ z : ℤ, ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) = |u - z * N| := by
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
  have hdm := Int.emod_add_mul_ediv u (N : ℤ)
  have hρ : ((u % (N : ℤ)).toNat : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg h0
  rcases le_total (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) with h | h
  · refine ⟨u / N, ?_⟩
    rw [min_eq_left h, hρ, abs_of_nonneg (by linarith [mul_comm (u / (N : ℤ)) (N : ℤ)])]
    linarith [mul_comm (u / (N : ℤ)) (N : ℤ)]
  · refine ⟨u / N + 1, ?_⟩
    rw [min_eq_right h]
    have hle : (u % (N : ℤ)).toNat ≤ N := by omega
    push_cast [hle]
    rw [hρ, abs_of_nonpos (by nlinarith)]
    nlinarith

/-- **Carries.** If `n = N q + ℓ`, `n' = N' q + ℓ'` (`0 ≤ ℓ, ℓ' < q`) and
`n' = n + E + z · Q q` with `q ∣ Q` and `E ∈ {-1,0,1}`, then `ℓ' ≡ ℓ + E` and
`N' ≡ N + κ E (mod q)` for a carry `κ ∈ {0,1}`. -/
theorem carry (q Q N ℓ N' ℓ' E z : ℤ) (hq : 0 < q) (hQ : q ∣ Q)
    (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < q) (hℓ0' : 0 ≤ ℓ') (hℓ1' : ℓ' < q)
    (hE : E = -1 ∨ E = 0 ∨ E = 1)
    (h : N' * q + ℓ' = N * q + ℓ + E + z * (Q * q)) :
    ∃ κ : ℤ, (κ = 0 ∨ κ = 1) ∧ q ∣ ℓ' - (ℓ + E) ∧ q ∣ N' - (N + κ * E) := by
  obtain ⟨Q', rfl⟩ := hQ
  set t := N' - N - z * (q * Q') with ht
  have htq : t * q = ℓ + E - ℓ' := by rw [ht]; linarith
  have hu : t ≤ 1 := by
    by_contra hc; push Not at hc
    have : 2 * q ≤ t * q := by nlinarith
    omega
  have hl : -1 ≤ t := by
    by_contra hc; push Not at hc
    have : t * q ≤ -2 * q := by nlinarith
    omega
  have hdl : ∀ κ : ℤ, t = κ * E → q ∣ N' - (N + κ * E) := by
    intro κ hκ
    exact ⟨z * Q', by rw [← hκ]; linarith⟩
  have hdl' : q ∣ ℓ' - (ℓ + E) := ⟨-t, by linarith⟩
  interval_cases t
  · -- t = -1
    rcases hE with rfl | rfl | rfl
    · exact ⟨1, Or.inr rfl, hdl', hdl 1 (by ring)⟩
    · omega
    · omega
  · exact ⟨0, Or.inl rfl, hdl', hdl 0 (by ring)⟩
  · rcases hE with rfl | rfl | rfl
    · omega
    · omega
    · exact ⟨1, Or.inr rfl, hdl', hdl 1 (by ring)⟩

end Z3Net.Sep
