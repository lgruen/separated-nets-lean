/-
Entry TwoCoset: `prop:twocoset` (2), free jitter and the separation of `𝒯_p`
(`paper/core.tex`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.TCNet
public import QUNetsM3.TCCore
public import QUNetsM3.NetBasic

@[expose] public section

/-!
# `prop:twocoset` (2): separation for arbitrary jitter

`tc_freeJitter_gen` (`tc_freeJitter'` for `b_x = b_y = 0`): one point per cell `n ∈ [0,p)³` at `p²n + p·g(n) + f(n)` (integer scale `p³`)
with geometric digits `g(n) ∈ [0,p)³`, `g_x ≡ h(n_y + n_z) + b_x`, `g_y ≡ r n_x − n_y + n_z + b_y`,
`g_z = g_y` (the shared wrap) and arbitrary third digits `f(n) ∈ [0,p)³`.  The integer core
`tc_core` gives `32|pE + Δg|² ≥ 33p² − 82p`, and the triangle inequality (`sq_tri_lower`) absorbs the
jitter `|Δf| ≤ √3 (p − 1)`.
-/

namespace QUNetsM3

open Matrix Filter Topology

variable {p : ℕ}

theorem thetaTC_cases (hodd : p % 2 = 1) :
    thetaTC p = -3 ∨ thetaTC p = -1 ∨ thetaTC p = 1 ∨ thetaTC p = 3 := by
  unfold thetaTC rTC; omega

theorem eight_rTC (p : ℕ) : 8 * (rTC p : ZMod p) = (thetaTC p : ZMod p) := by
  unfold thetaTC; push_cast; simp

/-- **`prop:twocoset` (2), free jitter, affine second digits**: the bound holds when the second digits are
`g_x ≡ h(n_y + n_z) + b_x`, `g_y ≡ r n_x − n_y + n_z + b_y` for any constants `b_x, b_y` (the digital shifts of
`rem:wshift`, `tc_shift`); `b_x = b_y = 0` is `tc_freeJitter'`. -/
theorem tc_freeJitter_gen (hp : p.Prime) (hp41 : 41 ≤ p) (bx bY : ZMod p) (g f : (Fin 3 → ℕ) → Fin 3 → ℕ)
    (hg : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, g n c < p)
    (hgx : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) →
      ((g n 0 : ℕ) : ZMod p) = hTC p * ((n 1 : ZMod p) + (n 2 : ZMod p)) + bx)
    (hgy : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) →
      ((g n 1 : ℕ) : ZMod p) = (rTC p : ZMod p) * (n 0 : ZMod p) - (n 1 : ZMod p) + (n 2 : ZMod p) + bY)
    (hgz : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 2 = g n 1)
    (hf : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, f n c < p)
    (n n' : Fin 3 → ℕ) (hn : ∀ c, n c < p) (hn' : ∀ c, n' c < p) (hne : n ≠ n')
    (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * (Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p)) ^ 2 ≤
      ∑ c : Fin 3, ((((p : ℤ) ^ 2 * ((n' c : ℤ) - n c) + p * ((g n' c : ℤ) - g n c)
        + ((f n' c : ℤ) - f n c) + (p : ℤ) ^ 3 * t c : ℤ)) : ℝ) ^ 2 := by
  have hodd := odd_of_prime5 hp (by omega)
  set E : Fin 3 → ℤ := fun c => ((n' c : ℤ) - n c) + (p : ℤ) * t c with hEdef
  set ξ : ℤ := (g n' 0 : ℤ) - g n 0 with hξdef
  set η : ℤ := (g n' 1 : ℤ) - g n 1 with hηdef
  set J : Fin 3 → ℤ := fun c => (f n' c : ℤ) - f n c with hJ
  have hη2 : (g n' 2 : ℤ) - g n 2 = η := by rw [hgz n' hn', hgz n hn]
  -- the congruences
  have hcj : (p : ℤ) ∣ 2 * ξ + (E 1 + E 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 := hgx n' hn'
    have h2 := hgx n hn
    have h2h := two_hTC hodd
    simp only [hEdef, hξdef]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, add_zero]
    linear_combination 2 * h1 - 2 * h2 +
      (((n' 1 : ZMod p) + n' 2) - ((n 1 : ZMod p) + n 2)) * h2h
  have hci : (p : ℤ) ∣ 8 * η - (thetaTC p * E 0 - 8 * (E 1 - E 2)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 := hgy n' hn'
    have h2 := hgy n hn
    have h8 := eight_rTC p
    simp only [hEdef, hηdef]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, add_zero]
    linear_combination 8 * h1 - 8 * h2 + ((n' 0 : ZMod p) - n 0) * h8
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
  have hξb : |ξ| ≤ p - 1 := by
    have := hg n hn 0; have := hg n' hn' 0
    rw [abs_le]; constructor <;> omega
  have hηb : |η| ≤ p - 1 := by
    have := hg n hn 1; have := hg n' hn' 1
    rw [abs_le]; constructor <;> omega
  have hJb : ∀ c, |J c| ≤ p - 1 := by
    intro c
    have := hf n hn c; have := hf n' hn' c
    simp only [hJ]
    rw [abs_le]; constructor <;> omega
  have core := tc_core (p : ℤ) (rTC p) (thetaTC p) (E 0) (E 1) (E 2) ξ η
    (by exact_mod_cast hp41) (thetaTC_cases hodd) (by unfold thetaTC; ring) hξb hηb hcj hci hE
  -- real form
  set W0 : ℤ := (p : ℤ) * E 0 + ξ
  set W1 : ℤ := (p : ℤ) * E 1 + η
  set W2 : ℤ := (p : ℤ) * E 2 + η
  have hpR : (41 : ℝ) ≤ p := by exact_mod_cast hp41
  have hp0 : (0 : ℝ) < p := by linarith
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have harg : 0 ≤ 33 / 32 - 41 / (16 * (p : ℝ)) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set a := Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) with ha
  have ha2 : a ^ 2 = 33 / 32 - 41 / (16 * (p : ℝ)) := Real.sq_sqrt harg
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hpa : (p : ℝ) ^ 4 * a ^ 2 = (p : ℝ) ^ 2 * (33 * (p : ℝ) ^ 2 - 82 * p) / 32 := by
    rw [ha2]; field_simp; ring
  have coreR : (33 * (p : ℝ) ^ 2 - 82 * p) ≤
      32 * ((W0 : ℝ) ^ 2 + (W1 : ℝ) ^ 2 + (W2 : ℝ) ^ 2) := by exact_mod_cast core
  have hβα : Real.sqrt 3 * p ≤ (p : ℝ) ^ 2 * a := by
    have h1 : (Real.sqrt 3 * p) ^ 2 ≤ ((p : ℝ) ^ 2 * a) ^ 2 := by
      rw [mul_pow, hs3, mul_pow, show ((p : ℝ) ^ 2) ^ 2 = (p : ℝ) ^ 4 by ring, hpa]
      have h96 : 0 ≤ 33 * (p : ℝ) ^ 2 - 82 * p - 96 := by nlinarith
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
  have hgoal : ((p : ℝ) ^ 2 * (a - Real.sqrt 3 / p)) = (p : ℝ) ^ 2 * a - Real.sqrt 3 * p := by
    field_simp
  rw [hgoal]
  refine le_of_le_of_eq htri ?_
  rw [Fin.sum_univ_three]
  simp only [W0, W1, W2, hEdef, hJ, hξdef, hηdef]
  rw [hgz n' hn', hgz n hn]
  push_cast
  ring

/-- **`prop:twocoset` (2), free jitter** (proof of `TC_freeJitter`). -/
theorem tc_freeJitter' (hp : p.Prime) (hp41 : 41 ≤ p) (g f : (Fin 3 → ℕ) → Fin 3 → ℕ)
    (hg : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, g n c < p)
    (hgx : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) →
      ((g n 0 : ℕ) : ZMod p) = hTC p * ((n 1 : ZMod p) + (n 2 : ZMod p)))
    (hgy : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) →
      ((g n 1 : ℕ) : ZMod p) = (rTC p : ZMod p) * (n 0 : ZMod p) - (n 1 : ZMod p) + (n 2 : ZMod p))
    (hgz : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 2 = g n 1)
    (hf : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, f n c < p)
    (n n' : Fin 3 → ℕ) (hn : ∀ c, n c < p) (hn' : ∀ c, n' c < p) (hne : n ≠ n')
    (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * (Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p)) ^ 2 ≤
      ∑ c : Fin 3, ((((p : ℤ) ^ 2 * ((n' c : ℤ) - n c) + p * ((g n' c : ℤ) - g n c)
        + ((f n' c : ℤ) - f n c) + (p : ℤ) ^ 3 * t c : ℤ)) : ℝ) ^ 2 :=
  tc_freeJitter_gen hp hp41 0 0 g f hg (fun n hn => by rw [hgx n hn, add_zero])
    (fun n hn => by rw [hgy n hn, add_zero]) hgz hf n n' hn hn' hne t

/-- The geometric and third digits of the cell `n` of `𝒯_p`. -/
def gTC (p : ℕ) (n : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun c => ((genTC p c *ᵥ (fun i => (n i : ZMod p))) 1).val

def fTC (p : ℕ) (n : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun c => ((genTC p c *ᵥ (fun i => (n i : ZMod p))) 2).val

theorem digitalPt_genTC [NeZero p] (x : ℕ) (c : Fin 3) :
    digitalPt p (genTC p) x c = cellDigits p x c * p ^ 2 + gTC p (cellDigits p x) c * p +
      fTC p (cellDigits p x) c := by
  have hd : (fun i => ((cellDigits p x i : ℕ) : ZMod p)) = digits p x := by
    funext i; simp [cellDigits, ZMod.natCast_zmod_val]
  rw [digitalPt_eq, coord_def]
  simp only [gTC, fTC, hd]
  congr 2
  fin_cases c
  · simp [genTC_x0, cellDigits]
  · simp [genTC_y0, cellDigits]
  · simp [genTC_z0, cellDigits]

/-- **Separation of `𝒯_p`** (proof of `TC_sep`). -/
theorem tc_sep' (hp : p.Prime) (hp41 : 41 ≤ p) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * (Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p)) ^ 2 ≤
      (sepSqG p (genTC p) x x' t : ℝ) := by
  have := Fact.mk hp
  have hcell : ∀ y, ∀ c, cellDigits p y c < p := fun y c => ZMod.val_lt _
  have fj := tc_freeJitter' hp hp41 (gTC p) (fTC p) (fun n _ c => ZMod.val_lt _)
    (by intro n _; simp only [gTC, ZMod.natCast_zmod_val, genTC_x1])
    (by intro n _; simp only [gTC, ZMod.natCast_zmod_val, genTC_y1])
    (by intro n _; simp only [gTC, genTC_y1, genTC_z1])
    (fun n _ c => ZMod.val_lt _) (cellDigits p x) (cellDigits p x') (hcell x) (hcell x')
    (by
      intro heq
      apply hne
      have hd : digits p x = digits p x' := by
        funext c
        exact ZMod.val_injective p (congrFun heq c)
      rw [← coord_digits hx, ← coord_digits hx', hd])
    t
  have hS : sepSqG p (genTC p) x x' t = ∑ c' : Fin 3,
      ((p : ℤ) ^ 2 * ((cellDigits p x' c' : ℤ) - cellDigits p x c') +
        p * ((gTC p (cellDigits p x') c' : ℤ) - gTC p (cellDigits p x) c') +
        ((fTC p (cellDigits p x') c' : ℤ) - fTC p (cellDigits p x) c') + (p : ℤ) ^ 3 * t c') ^ 2 := by
    unfold sepSqG
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [digitalPt_genTC, digitalPt_genTC]
    push_cast
    ring
  rw [hS]
  push_cast at fj ⊢
  exact fj

/-- `cTC p > 0` for `p ≥ 41`. -/
theorem cTC_pos (hp41 : 41 ≤ p) : 0 < cTC p := by
  unfold cTC
  have hpR : (41 : ℝ) ≤ p := by exact_mod_cast hp41
  have hp0 : (0 : ℝ) < p := by linarith
  have hs3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h1 : Real.sqrt 3 / p < 1 / 20 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num)]; nlinarith
  have h2 : (1 / 20 : ℝ) < Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) := by
    rw [Real.lt_sqrt (by norm_num)]
    have : 41 / (16 * (p : ℝ)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  linarith

/-- **Normalized separation** (proof of `TC_sep_real`). -/
theorem tc_sep_real' (hp : p.Prime) (hp41 : 41 ≤ p) :
    0 < cTC p ∧ ∀ x x' : ℕ, x < p ^ 3 → x' < p ^ 3 → x ≠ x' → ∀ t : Fin 3 → ℤ,
      cTC p ≤ Real.sqrt (sepSqG p (genTC p) x x' t : ℝ) / (p : ℝ) ^ 3 *
        ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hc := cTC_pos hp41
  refine ⟨hc, ?_⟩
  intro x x' hx hx' hne t
  have hroot : ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = p := by
    rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hpR.le (by norm_num)
  rw [hroot]
  have hS := tc_sep' hp hp41 x x' hx hx' hne t
  have hsq : (p : ℝ) ^ 2 * cTC p ≤ Real.sqrt (sepSqG p (genTC p) x x' t : ℝ) :=
    Real.le_sqrt_of_sq_le hS
  rw [show Real.sqrt (sepSqG p (genTC p) x x' t : ℝ) / (p : ℝ) ^ 3 * p =
      Real.sqrt (sepSqG p (genTC p) x x' t : ℝ) / (p : ℝ) ^ 2 by field_simp]
  rw [le_div_iff₀ hp2]
  linarith

end QUNetsM3
