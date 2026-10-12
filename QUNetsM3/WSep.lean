/-
`prop:wnet` (2): the separation of `𝒲_p` for any third rows, and its persistence under the digital
shifts of `rem:shiftshared` with `a ≡ 2b` or `a ≡ 2b + 1` (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WNet
public import QUNetsM3.WCore
public import QUNetsM3.NetBasic

@[expose] public section

/-!
# `prop:wnet` (2)

`w_freeJitter_gen`: one point per cell `n ∈ [0,p)³` at `p²n + p g(n) + f(n)` (integer scale `p³`), with
second digits `g_z(n) ≡ (h − r)(n_x + n_y) + ρn_z + b`, `g_x = g_y = (2g_z + c₀) mod p` (`c₀ ∈ {0,1}`) and
arbitrary third digits `f(n) ∈ [0,p)³`. The wraps of `g_x` obey `wrap_nec` (`lem:wwrap`, necessary part;
for `c₀ = 1` the shifted digit of `rem:shiftshared`), `2D + ρQ ≡ 0 (mod p)` as `2(h − r) ≡ −ρ`, and the
integer core `w_core` gives `256|pE + Δg|² ≥ 281p² − 690p`; the triangle inequality (`sq_tri_lower`) absorbs the
jitter `|Δf| ≤ √3(p − 1)`. `c₀ = 0`, `b = 0` is `prop:wnet` (2) (`w_freeJitter`, `w_sep`); general `b` and
`c₀ ∈ {0, 1}` are the shifted nets of `rem:shiftshared` (`w_shift`).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-- A digit `a < p` with `a ≡ 2z + c₀ (mod p)` equals `(2z + c₀) mod p`. -/
theorem digit_eq_mod {a z c₀ : ℕ} (ha : a < p) (h : (a : ZMod p) = 2 * (z : ZMod p) + c₀) :
    a = (2 * z + c₀) % p := by
  have : ((a : ℕ) : ZMod p) = ((2 * z + c₀ : ℕ) : ZMod p) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rwa [Nat.mod_eq_of_lt ha] at this

/-- `2(h − r) = −ρ` in `𝔽_p`. -/
theorem two_hr (hodd : p % 2 = 1) (r : ℕ) :
    2 * ((hW p : ZMod p) - r) = -rhoZ p r := by
  have := two_hW (p := p) hodd
  unfold rhoZ; push_cast
  linear_combination this

/-- The second rows: `x` reads twice the digit of `z` (`ρ(−1,−1,2) ≡ 2(h − r, h − r, ρ)`). -/
theorem genWr_x1_eq (hodd : p % 2 = 1) (r : ℕ) (s : Fin 3 → ZMod p) :
    (genWr p r 0 *ᵥ s) 1 = 2 * (genWr p r 2 *ᵥ s) 1 := by
  rw [genWr_x1, genWr_z1]
  linear_combination (-(s 0 + s 1)) * two_hr (p := p) hodd r

/-- **`prop:wnet` (2), general form** (any `b`, `c₀ ∈ {0,1}`; arbitrary third digits). -/
theorem w_freeJitter_gen (hp : p.Prime) (hp53 : 53 ≤ p) {c₀ : ℕ} (hc₀ : c₀ ≤ 1) (b : ZMod p)
    (g f : (Fin 3 → ℕ) → Fin 3 → ℕ)
    (hg : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, g n c < p)
    (hgx : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 0 = (2 * g n 2 + c₀) % p)
    (hgy : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 1 = g n 0)
    (hgz : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ((g n 2 : ℕ) : ZMod p) =
      ((hW p : ZMod p) - rW p) * ((n 0 : ZMod p) + (n 1 : ZMod p)) + rhoZ p (rW p) * (n 2 : ZMod p) + b)
    (hf : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, f n c < p)
    (n n' : Fin 3 → ℕ) (hn : ∀ c, n c < p) (hn' : ∀ c, n' c < p) (hne : n ≠ n')
    (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤
      ∑ c : Fin 3, ((((p : ℤ) ^ 2 * ((n' c : ℤ) - n c) + p * ((g n' c : ℤ) - g n c)
        + ((f n' c : ℤ) - f n c) + (p : ℤ) ^ 3 * t c : ℤ)) : ℝ) ^ 2 := by
  have hodd := odd_of_prime5 hp (by omega)
  obtain ⟨κ, hκeq, hκ0⟩ := wrap_nec hodd hc₀ (hg n hn 2) (hg n' hn' 2)
  set E : Fin 3 → ℤ := fun c => ((n' c : ℤ) - n c) + (p : ℤ) * t c with hEdef
  set D : ℤ := (g n' 2 : ℤ) - g n 2 with hDdef
  set J : Fin 3 → ℤ := fun c => (f n' c : ℤ) - f n c with hJ
  have hκ : (κ = 0 ∧ 2 * D ≤ p - 1 ∧ -(2 * D) ≤ p - 1) ∨ (κ = 1 ∧ 0 < D) ∨ (κ = -1 ∧ D < 0) := by
    rcases hκ0 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, by omega⟩)
  have hgx' : (g n' 0 : ℤ) - g n 0 = 2 * D - p * κ := by
    rw [hgx n' hn', hgx n hn, hκeq]
  have hgy' : (g n' 1 : ℤ) - g n 1 = 2 * D - p * κ := by
    rw [hgy n' hn', hgy n hn, hgx']
  -- the congruence `2D + ρQ ≡ 0`
  have hdiv : (p : ℤ) ∣ 2 * D + (2 * (rW p : ℤ) + 1) * (E 0 + E 1 - 2 * E 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 := hgz n' hn'
    have h2 := hgz n hn
    have h2h := two_hW (p := p) hodd
    simp only [hEdef, hDdef]
    unfold rhoZ at h1 h2
    push_cast at h1 h2 ⊢
    simp only [ZMod.natCast_self, zero_mul, add_zero]
    linear_combination 2 * h1 - 2 * h2 +
      (((n' 0 : ZMod p) - n 0) + ((n' 1 : ZMod p) - n 1)) * h2h
  have hE0 : ∀ c, E c = 0 → n' c = n c := by
    intro c hc
    have h1 := hn c
    have h2 := hn' c
    simp only [hEdef] at hc
    rcases lt_trichotomy (t c) 0 with ht | ht | ht
    · have : (p : ℤ) * t c ≤ -(p : ℤ) := by nlinarith
      omega
    · rw [ht] at hc; omega
    · have : (p : ℤ) ≤ (p : ℤ) * t c := by nlinarith
      omega
  have hE : E 0 ≠ 0 ∨ E 1 ≠ 0 ∨ E 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    funext c
    fin_cases c
    · exact (hE0 0 hcon.1).symm
    · exact (hE0 1 hcon.2.1).symm
    · exact (hE0 2 hcon.2.2).symm
  have hb0 := hg n hn 0; have hb0' := hg n' hn' 0
  have hb2 := hg n hn 2; have hb2' := hg n' hn' 2
  have core := w_core (p : ℤ) (rW p) ((p % 48 : ℕ) : ℤ) (E 0) (E 1) (E 2) D κ
    (by exact_mod_cast hp53) (by unfold rW; omega) (by omega) (by omega) (by omega) hdiv
    (by omega) (by omega) (by rw [← hgx']; omega) (by rw [← hgx']; omega) hκ hE
  have hJb : ∀ c, |J c| ≤ p - 1 := by
    intro c
    have := hf n hn c; have := hf n' hn' c
    simp only [hJ]
    rw [abs_le]; constructor <;> omega
  -- real form
  set W0 : ℤ := (p : ℤ) * E 0 + 2 * D - p * κ
  set W1 : ℤ := (p : ℤ) * E 1 + 2 * D - p * κ
  set W2 : ℤ := (p : ℤ) * E 2 + D
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp53
  have hp0 : (0 : ℝ) < p := by linarith
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have harg : 0 ≤ 281 / 256 - 345 / (128 * (p : ℝ)) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set a := Real.sqrt (281 / 256 - 345 / (128 * (p : ℝ))) with ha
  have ha2 : a ^ 2 = 281 / 256 - 345 / (128 * (p : ℝ)) := Real.sq_sqrt harg
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hpa : (p : ℝ) ^ 4 * a ^ 2 = (p : ℝ) ^ 2 * (281 * (p : ℝ) ^ 2 - 690 * p) / 256 := by
    rw [ha2]; field_simp; ring
  have coreR : (281 * (p : ℝ) ^ 2 - 690 * p) ≤
      256 * ((W0 : ℝ) ^ 2 + (W1 : ℝ) ^ 2 + (W2 : ℝ) ^ 2) := by exact_mod_cast core
  have hβα : Real.sqrt 3 * p ≤ (p : ℝ) ^ 2 * a := by
    have h1 : (Real.sqrt 3 * p) ^ 2 ≤ ((p : ℝ) ^ 2 * a) ^ 2 := by
      rw [mul_pow, hs3, mul_pow, show ((p : ℝ) ^ 2) ^ 2 = (p : ℝ) ^ 4 by ring, hpa]
      have h96 : 0 ≤ 281 * (p : ℝ) ^ 2 - 690 * p - 768 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) h96]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  have htri := sq_tri_lower ((p : ℝ) * W0) ((p : ℝ) * W1) ((p : ℝ) * W2)
    (J 0 : ℝ) (J 1 : ℝ) (J 2 : ℝ) ((p : ℝ) ^ 2 * a) (Real.sqrt 3 * p) (by positivity) hβα
    (by
      have : ((p : ℝ) ^ 2 * a) ^ 2 = (p : ℝ) ^ 4 * a ^ 2 := by ring
      rw [this, hpa]
      have hp2 : 0 ≤ (p : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left coreR hp2])
    (by
      have hb : ∀ c, ((J c : ℤ) : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
        intro c
        have h := hJb c
        have h' : (J c) ^ 2 ≤ ((p : ℤ) - 1) ^ 2 := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
        have h'' : ((J c : ℤ) : ℝ) ^ 2 ≤ (((p : ℤ) - 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast h'
        push_cast at h''
        nlinarith
      rw [mul_pow, hs3]
      linarith [hb 0, hb 1, hb 2])
  have hgoal : ((p : ℝ) ^ 2 * cW p) = (p : ℝ) ^ 2 * a - Real.sqrt 3 * p := by
    unfold cW; rw [← ha]; field_simp
  rw [hgoal]
  refine le_of_le_of_eq htri ?_
  rw [Fin.sum_univ_three]
  have e0 : ((p : ℤ) ^ 2 * ((n' 0 : ℤ) - n 0) + p * ((g n' 0 : ℤ) - g n 0) + ((f n' 0 : ℤ) - f n 0) +
      (p : ℤ) ^ 3 * t 0) = p * W0 + J 0 := by
    rw [hgx']; simp only [W0, hEdef, hJ]; ring
  have e1 : ((p : ℤ) ^ 2 * ((n' 1 : ℤ) - n 1) + p * ((g n' 1 : ℤ) - g n 1) + ((f n' 1 : ℤ) - f n 1) +
      (p : ℤ) ^ 3 * t 1) = p * W1 + J 1 := by
    rw [hgy']; simp only [W1, hEdef, hJ]; ring
  have e2 : ((p : ℤ) ^ 2 * ((n' 2 : ℤ) - n 2) + p * ((g n' 2 : ℤ) - g n 2) + ((f n' 2 : ℤ) - f n 2) +
      (p : ℤ) ^ 3 * t 2) = p * W2 + J 2 := by
    simp only [W2, hEdef, hDdef, hJ]; ring
  rw [e0, e1, e2]
  push_cast
  ring

/-- **`prop:wnet` (2), free jitter** (proof of `W_freeJitter`). -/
theorem w_freeJitter (hp : p.Prime) (hp53 : 53 ≤ p) (g f : (Fin 3 → ℕ) → Fin 3 → ℕ)
    (hg : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, g n c < p)
    (hgx : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ((g n 0 : ℕ) : ZMod p) =
      rhoZ p (rW p) * (-(n 0 : ZMod p) - (n 1 : ZMod p) + 2 * (n 2 : ZMod p)))
    (hgy : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 1 = g n 0)
    (hgz : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ((g n 2 : ℕ) : ZMod p) =
      ((hW p : ZMod p) - rW p) * ((n 0 : ZMod p) + (n 1 : ZMod p)) + rhoZ p (rW p) * (n 2 : ZMod p))
    (hf : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, f n c < p)
    (n n' : Fin 3 → ℕ) (hn : ∀ c, n c < p) (hn' : ∀ c, n' c < p) (hne : n ≠ n')
    (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤
      ∑ c : Fin 3, ((((p : ℤ) ^ 2 * ((n' c : ℤ) - n c) + p * ((g n' c : ℤ) - g n c)
        + ((f n' c : ℤ) - f n c) + (p : ℤ) ^ 3 * t c : ℤ)) : ℝ) ^ 2 := by
  have hodd := odd_of_prime5 hp (by omega)
  have h2 := two_hr (p := p) hodd (rW p)
  refine w_freeJitter_gen hp hp53 (c₀ := 0) (by norm_num) 0 g f hg ?_ hgy
    (fun n hn => by rw [hgz n hn, add_zero]) hf n n' hn hn' hne t
  intro n hn
  refine digit_eq_mod (hg n hn 0) ?_
  rw [hgx n hn, hgz n hn]
  push_cast
  linear_combination (-(((n 0 : ZMod p) + (n 1 : ZMod p)))) * h2

/-! ## The net `𝒲_p` -/

/-- The second and third digits of the cell `n` of the digital point set `C`. -/
def g2G (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (n : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun c => ((C c *ᵥ (fun i => (n i : ZMod p))) 1).val

def g3G (p : ℕ) (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (n : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun c => ((C c *ᵥ (fun i => (n i : ZMod p))) 2).val

/-- The point of index `x` of a digital point set whose first rows are `e_x, e_y, e_z`. -/
theorem digitalPt_row0 [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC : ∀ c s, (C c *ᵥ s) 0 = s c) (x : ℕ) (c : Fin 3) :
    digitalPt p C x c = cellDigits p x c * p ^ 2 + g2G p C (cellDigits p x) c * p + g3G p C (cellDigits p x) c := by
  have hd : (fun i => ((cellDigits p x i : ℕ) : ZMod p)) = digits p x := by
    funext i; simp [cellDigits]
  rw [digitalPt_eq, coord_def]
  simp only [g2G, g3G, hd, hC]
  rfl

/-- `sepSqG` in cell form. -/
theorem sepSqG_row0 [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC : ∀ c s, (C c *ᵥ s) 0 = s c) (x x' : ℕ) (t : Fin 3 → ℤ) :
    sepSqG p C x x' t = ∑ c' : Fin 3,
      ((p : ℤ) ^ 2 * ((cellDigits p x' c' : ℤ) - cellDigits p x c') +
        p * ((g2G p C (cellDigits p x') c' : ℤ) - g2G p C (cellDigits p x) c') +
        ((g3G p C (cellDigits p x') c' : ℤ) - g3G p C (cellDigits p x) c') + (p : ℤ) ^ 3 * t c') ^ 2 := by
  unfold sepSqG
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [digitalPt_row0 C hC, digitalPt_row0 C hC]
  push_cast
  ring

/-- Distinct indices `< p³` have distinct cells. -/
theorem cellE1_ne [NeZero p] {x x' : ℕ} (hx : x < p ^ 3) (hx' : x' < p ^ 3) (hne : x ≠ x') :
    cellDigits p x ≠ cellDigits p x' := by
  intro heq
  apply hne
  have hd : digits p x = digits p x' := by
    funext c
    exact ZMod.val_injective p (congrFun heq c)
  rw [← coord_digits hx, ← coord_digits hx', hd]

/-- **Separation of `𝒲_p`** (proof of `W_sep`). -/
theorem w_sep (hp : p.Prime) (hp53 : 53 ≤ p) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤ (sepSqG p (genW p) x x' t : ℝ) := by
  have := Fact.mk hp
  have hC : ∀ c s, (genW p c *ᵥ s) 0 = s c := fun c s => genWr_row0 _ s c
  have fj := w_freeJitter hp hp53 (g2G p (genW p)) (g3G p (genW p)) (fun n _ c => ZMod.val_lt _)
    (by intro n _; simp only [g2G, ZMod.natCast_zmod_val, genW, genWr_x1])
    (by intro n _; simp only [g2G, genW, genWr_x1, genWr_y1])
    (by intro n _; simp only [g2G, ZMod.natCast_zmod_val, genW, genWr_z1])
    (fun n _ c => ZMod.val_lt _) (cellDigits p x) (cellDigits p x') (fun c => ZMod.val_lt _)
    (fun c => ZMod.val_lt _) (cellE1_ne hx hx' hne) t
  rw [sepSqG_row0 _ hC]
  push_cast at fj ⊢
  exact fj

/-- `cW p > 0` for `p ≥ 53`. -/
theorem cW_pos (hp53 : 53 ≤ p) : 0 < cW p := by
  unfold cW
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp53
  have hp0 : (0 : ℝ) < p := by linarith
  have hs3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h1 : Real.sqrt 3 / p < 1 / 20 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num)]; nlinarith
  have h2 : (1 / 20 : ℝ) < Real.sqrt (281 / 256 - 345 / (128 * (p : ℝ))) := by
    rw [Real.lt_sqrt (by norm_num)]
    have : 345 / (128 * (p : ℝ)) ≤ 345 / (128 * 53) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  linarith

/-- **Normalized separation of `𝒲_p`** (proof of `W_sep_real`). -/
theorem w_sep_real (hp : p.Prime) (hp53 : 53 ≤ p) :
    0 < cW p ∧ ∀ x x' : ℕ, x < p ^ 3 → x' < p ^ 3 → x ≠ x' → ∀ t : Fin 3 → ℤ,
      cW p ≤ Real.sqrt (sepSqG p (genW p) x x' t : ℝ) / (p : ℝ) ^ 3 *
        ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hc := cW_pos hp53
  refine ⟨hc, ?_⟩
  intro x x' hx hx' hne t
  have hroot : ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = p := by
    rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hpR.le (by norm_num)
  rw [hroot]
  have hS := w_sep hp hp53 x x' hx hx' hne t
  have hsq : (p : ℝ) ^ 2 * cW p ≤ Real.sqrt (sepSqG p (genW p) x x' t : ℝ) :=
    Real.le_sqrt_of_sq_le hS
  rw [show Real.sqrt (sepSqG p (genW p) x x' t : ℝ) / (p : ℝ) ^ 3 * p =
      Real.sqrt (sepSqG p (genW p) x x' t : ℝ) / (p : ℝ) ^ 2 by field_simp]
  rw [le_div_iff₀ hp2]
  linarith

/-! ## Digital shifts (`rem:shiftshared`) -/

/-- The point of index `x` of the shifted point set, in cell form: the cell is `digits(x) + τ_{·,0}`. -/
theorem digitalPtS_row0 [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC : ∀ c s, (C c *ᵥ s) 0 = s c) (τ : Fin 3 → Fin 3 → ZMod p) (x : ℕ) (c : Fin 3) :
    digitalPtS p C τ x c = (digits p x c + τ c 0).val * p ^ 2 +
      ((C c *ᵥ digits p x) 1 + τ c 1).val * p + ((C c *ᵥ digits p x) 2 + τ c 2).val := by
  unfold digitalPtS
  rw [coord_def]
  simp only [Pi.add_apply, hC]

/-- **The shifted nets of `rem:shiftshared`** (proof of `W_shift`): if the second shift digits are
`τ_{x,2} = τ_{y,2} = a`, `τ_{z,2} = b` with `a ≡ 2b` or `a ≡ 2b + 1`, the bound of `prop:wnet` (2) holds for every
pair of distinct points (any first and third shift digits). -/
theorem w_shift (hp : p.Prime) (hp53 : 53 ≤ p) (τ : Fin 3 → Fin 3 → ZMod p) (hxy : τ 0 1 = τ 1 1)
    (hab : τ 0 1 = 2 * τ 2 1 ∨ τ 0 1 = 2 * τ 2 1 + 1) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤ (sepSqGS p (genW p) τ x x' t : ℝ) := by
  have := Fact.mk hp
  have hodd := odd_of_prime5 hp (by omega)
  have h2 := two_hr (p := p) hodd (rW p)
  -- the cell of an index, and the digits as functions of the cell `m = d + τ_{·,0}`
  let cellS : ℕ → Fin 3 → ℕ := fun y c => (digits p y c + τ c 0).val
  let gS : (Fin 3 → ℕ) → Fin 3 → ℕ := fun m c =>
    ((genW p c *ᵥ (fun i => (m i : ZMod p) - τ i 0)) 1 + τ c 1).val
  let fS : (Fin 3 → ℕ) → Fin 3 → ℕ := fun m c =>
    ((genW p c *ᵥ (fun i => (m i : ZMod p) - τ i 0)) 2 + τ c 2).val
  obtain ⟨bS, hbS⟩ : ∃ bS : ZMod p, bS = τ 2 1 - (((hW p : ZMod p) - rW p) * (τ 0 0 + τ 1 0) +
      rhoZ p (rW p) * τ 2 0) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀, hab'⟩ : ∃ c₀ : ℕ, c₀ ≤ 1 ∧ τ 0 1 = 2 * τ 2 1 + c₀ := by
    rcases hab with h | h
    · exact ⟨0, by norm_num, by rw [h]; simp⟩
    · exact ⟨1, le_rfl, by rw [h]; simp⟩
  have hzS : ∀ m : Fin 3 → ℕ, ((gS m 2 : ℕ) : ZMod p) =
      ((hW p : ZMod p) - rW p) * ((m 0 : ZMod p) + (m 1 : ZMod p)) + rhoZ p (rW p) * (m 2 : ZMod p) +
        bS := by
    intro m
    simp only [gS, ZMod.natCast_zmod_val, genW, genWr_z1]
    rw [hbS]
    ring
  have hxS : ∀ m : Fin 3 → ℕ, ((gS m 0 : ℕ) : ZMod p) = 2 * ((gS m 2 : ℕ) : ZMod p) + c₀ := by
    intro m
    simp only [gS, ZMod.natCast_zmod_val, genW]
    rw [genWr_x1_eq hodd, hab']
    ring
  have fj := w_freeJitter_gen hp hp53 hc₀ bS gS fS (fun n _ c => ZMod.val_lt _)
    (fun m _ => digit_eq_mod (ZMod.val_lt _) (hxS m))
    (by intro m _; simp only [gS, genW, genWr_x1, genWr_y1, hxy])
    (fun m _ => hzS m) (fun n _ c => ZMod.val_lt _) (cellS x) (cellS x')
    (fun c => ZMod.val_lt _) (fun c => ZMod.val_lt _)
    (by
      intro heq
      apply hne
      have hd : digits p x = digits p x' := by
        funext c
        have := ZMod.val_injective p (congrFun heq c)
        exact add_right_cancel this
      rw [← coord_digits hx, ← coord_digits hx', hd]) t
  have hcell : ∀ y, (fun i => ((cellS y i : ℕ) : ZMod p) - τ i 0) = digits p y := by
    intro y; funext i; simp [cellS]
  have hS : sepSqGS p (genW p) τ x x' t = ∑ c' : Fin 3,
      ((p : ℤ) ^ 2 * ((cellS x' c' : ℤ) - cellS x c') +
        p * ((gS (cellS x') c' : ℤ) - gS (cellS x) c') +
        ((fS (cellS x') c' : ℤ) - fS (cellS x) c') + (p : ℤ) ^ 3 * t c') ^ 2 := by
    unfold sepSqGS
    refine Finset.sum_congr rfl fun c' _ => ?_
    have hC : ∀ c s, (genW p c *ᵥ s) 0 = s c := fun c s => genWr_row0 _ s c
    rw [digitalPtS_row0 _ hC, digitalPtS_row0 _ hC]
    simp only [gS, fS, hcell]
    push_cast
    ring
  rw [hS]
  push_cast at fj ⊢
  exact fj

/-! ## The bound `c_W(p)` -/

theorem cW_mono {p p' : ℕ} (hp : 53 ≤ p) (hle : p ≤ p') : cW p ≤ cW p' := by
  unfold cW
  have hpR : (53 : ℝ) ≤ p := by exact_mod_cast hp
  have hle' : (p : ℝ) ≤ p' := by exact_mod_cast hle
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : Real.sqrt (281 / 256 - 345 / (128 * (p : ℝ))) ≤
      Real.sqrt (281 / 256 - 345 / (128 * (p' : ℝ))) := by
    apply Real.sqrt_le_sqrt
    have : 345 / (128 * (p' : ℝ)) ≤ 345 / (128 * (p : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith
  have h2 : Real.sqrt 3 / p' ≤ Real.sqrt 3 / p :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg 3) h0 hle'
  linarith

theorem sqrt3_lt_W : Real.sqrt 3 < 1.7320509 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt3_gt_W : 1.7320508 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt66_lt_W : Real.sqrt 66 / 8 < 1.0155049 := by
  rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt66_gt_W : 1.0155048 < Real.sqrt 66 / 8 := by
  rw [lt_div_iff₀ (by norm_num), Real.lt_sqrt (by norm_num)]; norm_num

/-- `cW` at the primes named in the proof: `1.0024 < c(67) < 1.0025`, `c(61) < 1`, `1.0164 < c(97) < 1.0165`,
`c(89) < √66/8`. -/
theorem cW_values : 1.0024 < cW 67 ∧ cW 67 < 1.0025 ∧ cW 61 < 1 ∧ 1.0164 < cW 97 ∧ cW 97 < 1.0165 ∧
    cW 89 < Real.sqrt 66 / 8 := by
  have h3l := sqrt3_gt_W
  have h3u := sqrt3_lt_W
  have h66 := sqrt66_gt_W
  unfold cW
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1.0024 + Real.sqrt 3 / 67 < Real.sqrt (281 / 256 - 345 / (128 * 67)) := by
      rw [Real.lt_sqrt (by positivity)]; nlinarith
    linarith
  · have : Real.sqrt (281 / 256 - 345 / (128 * 67)) < 1.0025 + Real.sqrt 3 / 67 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    linarith
  · have : Real.sqrt (281 / 256 - 345 / (128 * 61)) < 1 + Real.sqrt 3 / 61 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    linarith
  · have : 1.0164 + Real.sqrt 3 / 97 < Real.sqrt (281 / 256 - 345 / (128 * 97)) := by
      rw [Real.lt_sqrt (by positivity)]; nlinarith
    linarith
  · have : Real.sqrt (281 / 256 - 345 / (128 * 97)) < 1.0165 + Real.sqrt 3 / 97 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    linarith
  · have : Real.sqrt (281 / 256 - 345 / (128 * 89)) < 1.0155048 + Real.sqrt 3 / 89 := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    linarith

theorem cW_gt1 (hp : 67 ≤ p) : 1 < cW p := by
  have := cW_mono (p := 67) (by norm_num) hp
  have := cW_values.1
  linarith

theorem cW_gt66 (hp : 97 ≤ p) : Real.sqrt 66 / 8 < cW p := by
  have := cW_mono (p := 97) (by norm_num) hp
  have := cW_values.2.2.2.1
  have := sqrt66_lt_W
  linarith

end QUNetsM3
