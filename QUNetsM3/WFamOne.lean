/-
`prop:wfamily` (1) and the net part of (3): `F_p(u) = F(u/p)`, `|δN^{1/3} − √F_p(u)| < √3/p`,
`F_p(u) < μ*²`, `δN^{1/3} < μ* + √3/p` (`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WFamThree
public import QUNetsM3.WExactCore

@[expose] public section

/-!
# `prop:wfamily` (1)

As printed. Every pair of distinct points of the net without third digits (`genWfam p u 0`) is an option of
`τ = u/p` (`w_reduce`: `δ = Δζ/p`, the wrap rules of `lem:wwrap`), so `F_p(u) ≥ F(u/p)`; conversely every option
of `u/p` with `|V|² ≤ 4` (hence `|E_c| ≤ 2`, `E ≢ 0 (mod p)`) is realized by a pair (`lem:wwrap`, existence part),
and the option of the step `e_z` has `|V|² ≤ 3`, so `F_p(u) ≤ F(u/p)`. The third digits move each pair by at most
`√3(p − 1) < √3 p` at integer scale `p³`. Lean needs neither `u ≠ 0` nor the net property for (1).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

section rows
variable (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) (s : Fin 3 → ZMod p)

theorem genWfam_row0 (c : Fin 3) : (genWfam p u T c *ᵥ s) 0 = s c := by
  simp [genWfam, Matrix.mulVec]

theorem genWfam_row1 (c : Fin 3) :
    (genWfam p u T c *ᵥ s) 1 = (![2, 2, 1] : Fin 3 → ZMod p) c * (u ⬝ᵥ s) := by
  simp [genWfam, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem genWfam_row2 (c : Fin 3) : (genWfam p u T c *ᵥ s) 2 = T c ⬝ᵥ s := by
  simp [genWfam, Matrix.mulVec]

end rows

/-- The set of values of `F_p(u)`. -/
def fpSet (p : ℕ) (u : Fin 3 → ZMod p) : Set ℝ :=
  {v : ℝ | ∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < p ^ 3 ∧ x' < p ^ 3 ∧ x ≠ x' ∧
    v = (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 4}

theorem FpW_def (u : Fin 3 → ZMod p) : FpW p u = sInf (fpSet p u) := rfl

theorem fpSet_bdd (u : Fin 3 → ZMod p) : BddBelow (fpSet p u) := by
  refine ⟨0, ?_⟩
  rintro v ⟨x, x', t, -, -, -, rfl⟩
  apply div_nonneg _ (by positivity)
  unfold sepSqG; push_cast; positivity

theorem fpSet_nonempty (hp : 2 ≤ p) (u : Fin 3 → ZMod p) : (fpSet p u).Nonempty :=
  ⟨_, 0, 1, 0, by positivity, Nat.one_lt_pow (by norm_num) (by omega), by norm_num, rfl⟩

/-- An integer `X` with `p ∣ X` and `|X| ≤ p − 1` is `0`. -/
theorem eq_zero_of_small {X : ℤ} (h : ((X : ℤ) : ZMod p) = 0) (h1 : X ≤ p - 1)
    (h2 : -X ≤ p - 1) : X = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)

/-- **Every pair is an option** (`F_p(u) ≥ F(u/p)`). -/
theorem fp_mem (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) {v : ℝ} (hv : v ∈ fpSet p u) :
    v ∈ optSet (tauOf p u) := by
  have := Fact.mk hp
  obtain ⟨x, x', t, hx, hx', hne, rfl⟩ := hv
  obtain ⟨E, D, κ, F, hE, -, hD, hD1, hD2, hκ, -, -, hF, hval⟩ :=
    w_reduce hp hp5 (genWfam p u 0) (fun c s => genWfam_row0 u 0 s c)
      (fun s => by rw [genWfam_row1, genWfam_row1]; rfl)
      (fun s => by rw [genWfam_row1, genWfam_row1]; simp) x x' hx hx' hne t
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hF0 : ∀ c, F c = 0 := by
    intro c
    refine eq_zero_of_small ?_ (hF c).2.1 (hF c).2.2
    rw [(hF c).1, genWfam_row2]; simp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- the option `δ = D/p`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, D = ∑ c, ((u c).val : ℤ) * E c + p * m := by
    have h1 : ((D - ∑ c, ((u c).val : ℤ) * E c : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hD, genWfam_row1]
      simp [dotProduct]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    obtain ⟨m, hm⟩ := h1
    exact ⟨m, by linarith⟩
  refine ⟨E, hE, (D : ℝ) / p, κ, ⟨?_, ?_, ⟨m, ?_⟩, ?_⟩, ?_⟩
  · rw [lt_div_iff₀ hpR]; have : (-(D : ℝ)) ≤ p - 1 := by exact_mod_cast hD2
    linarith
  · rw [div_lt_iff₀ hpR]; have : (D : ℝ) ≤ p - 1 := by exact_mod_cast hD1
    linarith
  · rw [hm]; simp only [tauOf]; push_cast
    rw [add_div, mul_div_cancel_left₀ _ hpR.ne', Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by ring
  · rcases hκ with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩
    · right; refine ⟨rfl, ?_⟩
      rw [abs_lt]
      have h1' : 2 * (D : ℝ) ≤ p - 1 := by exact_mod_cast h1
      have h2' : -(2 * (D : ℝ)) ≤ p - 1 := by exact_mod_cast h2
      constructor
      · rw [lt_div_iff₀ hpR]; linarith
      · rw [div_lt_iff₀ hpR]; linarith
    · left; rw [sgnR_pos (div_pos (by exact_mod_cast h1) hpR)]
    · left; rw [sgnR_neg (div_neg_of_neg_of_pos (by exact_mod_cast h1) hpR)]
  · rw [hval, hF0 0, hF0 1, hF0 2, optValW_eval]
    field_simp
    push_cast
    ring

/-- `(2z) mod p = 2z − p[2z ≥ p]` for `z < p`. -/
theorem two_mod {z : ℕ} (hz : z < p) : (((2 * z) % p : ℕ) : ℤ) = 2 * z - p * wrapW p z := by
  unfold wrapW
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; push_cast [Nat.cast_sub h]; ring
  · rw [Nat.mod_eq_of_lt (by omega)]; push_cast; ring

/-- **An option with `|V|² ≤ 4` is realized by a pair** (`F_p(u) ≤ F(u/p)`; `lem:wwrap`, existence part). -/
theorem fp_real (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) {v : ℝ} (hv : v ∈ optSet (tauOf p u))
    (hv4 : v ≤ 4) : v ∈ fpSet p u := by
  have := Fact.mk hp
  have hodd := odd_of_prime5 hp hp5
  obtain ⟨E, hE, δ, κ, hopt, rfl⟩ := hv
  have hsmall : |E 0| < 3 ∧ |E 1| < 3 ∧ |E 2| < 3 := by
    by_contra hc
    have : 3 ≤ |E 0| ∨ 3 ≤ |E 1| ∨ 3 ≤ |E 2| := by
      by_contra hc'; push Not at hc'; exact hc hc'
    have := opt_long hopt this; linarith
  have hkap := opt_kappa hopt
  obtain ⟨hd1, hd2, ⟨k, hk⟩, -⟩ := hopt
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- `d = pδ`
  set d : ℤ := ∑ c, ((u c).val : ℤ) * E c + p * k with hd
  have hδ : δ = (d : ℝ) / p := by
    rw [hk, hd]; simp only [tauOf]; push_cast
    rw [add_div, mul_div_cancel_left₀ _ hpR.ne', Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by ring
  have hdlo : -(p : ℤ) < d := by
    have : -1 < (d : ℝ) / p := hδ ▸ hd1
    rw [lt_div_iff₀ hpR] at this; exact_mod_cast (by linarith : (-(p : ℝ)) < d)
  have hdhi : d < p := by
    have : (d : ℝ) / p < 1 := hδ ▸ hd2
    rw [div_lt_iff₀ hpR] at this; exact_mod_cast (by linarith : (d : ℝ) < p)
  have hdcast : (d : ZMod p) = u ⬝ᵥ fun c => (E c : ZMod p) := by
    rw [hd]; push_cast; simp [dotProduct]
  set σ := sigmaW p u E with hσ
  have hσlt : σ < p := ZMod.val_lt _
  have hdσ : d ∈ [((σ : ℕ) : ℤ) % (p : ℤ), ((σ : ℕ) : ℤ) % (p : ℤ) - p] := by
    refine mem_two_res hp0 ?_ (by omega) (by omega)
    rw [hdcast, hσ, sigmaW]; push_cast; simp
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hσlt)] at hdσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdσ
  -- the wrap rules
  have hallow : WrapAllowed p σ d κ := by
    unfold WrapAllowed
    by_cases hs0 : σ = 0
    · left
      have hd0 : d = 0 := by rw [hs0] at hdσ; push_cast at hdσ; omega
      refine ⟨hs0, hd0, ?_⟩
      rw [hδ, hd0] at hkap; push_cast at hkap
      rcases hkap with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · simp at h
      · simp at h
      · exact h
    · right
      refine ⟨hs0, hdσ, ?_⟩
      rw [hδ] at hkap
      rcases hkap with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩
      · left
        have : (0 : ℝ) < d := by rwa [div_pos_iff_of_pos_right hpR] at h
        rw [Int.sign_eq_one_of_pos (by exact_mod_cast this)]
      · left
        have : (d : ℝ) < 0 := by
          by_contra hc; push Not at hc; have := div_nonneg hc hpR.le; linarith
        rw [Int.sign_eq_neg_one_of_neg (by exact_mod_cast this)]
      · right; refine ⟨rfl, ?_⟩
        rw [lt_div_iff₀ hpR] at h1; rw [div_lt_iff₀ hpR] at h2
        have a1 : 2 * d < p := by exact_mod_cast (by linarith : (2 * (d : ℝ)) < p)
        have a2 : -(2 * d) < p := by exact_mod_cast (by linarith : (-(2 * (d : ℝ))) < p)
        rw [abs_le]; unfold hW; constructor <;> omega
  obtain ⟨n, hn1, hn2⟩ := (wwrap hp hp5 u E d κ).2 hallow
  -- the pair
  set Ec : Fin 3 → ZMod p := fun c => (E c : ZMod p)
  set n' := n + Ec
  have hdiv : ∀ c, (p : ℤ) ∣ E c - ((n' c).val - (n c).val) := by
    intro c
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; simp only [n', Ec, Pi.add_apply, ZMod.natCast_zmod_val]; ring
  choose tt htt using hdiv
  refine ⟨coord p n, coord p n', tt, coord_lt _, coord_lt _, ?_, ?_⟩
  · intro h
    have h' : n = n' := by rw [← digits_coord n, h, digits_coord]
    apply hE
    funext c
    have hc : Ec c = 0 := by
      have := congrFun h' c
      simp only [n', Pi.add_apply] at this
      linear_combination -this
    have hall : ∀ c, |E c| < 3 := fun c => by
      fin_cases c
      exacts [hsmall.1, hsmall.2.1, hsmall.2.2]
    have h3 := hall c
    rw [abs_lt] at h3
    exact eq_zero_of_small hc (by omega) (by omega)
  · have hcell : ∀ w : Fin 3 → ZMod p, (fun i => ((cellDigits p (coord p w) i : ℕ) : ZMod p)) = w := by
      intro w; funext i; simp [cellDigits, digits_coord]
    have hc1 : ∀ w : Fin 3 → ZMod p, ∀ c, ((cellDigits p (coord p w) c : ℕ) : ℤ) = (w c).val := by
      intro w c; simp [cellDigits, digits_coord]
    have hg2 : ∀ (w : Fin 3 → ZMod p) (c : Fin 3), g2G p (genWfam p u 0) (cellDigits p (coord p w)) c =
        ((![2, 2, 1] : Fin 3 → ZMod p) c * (u ⬝ᵥ w)).val := by
      intro w c; simp only [g2G, hcell, genWfam_row1]
    have hg3 : ∀ (w : Fin 3 → ZMod p) (c : Fin 3), g3G p (genWfam p u 0) (cellDigits p (coord p w)) c = 0 := by
      intro w c; simp only [g3G, hcell, genWfam_row2, Pi.zero_apply, zero_dotProduct, ZMod.val_zero]
    have h2v : (2 : ZMod p).val = 2 := by
      have := ZMod.val_natCast (n := p) 2; rw [Nat.mod_eq_of_lt (by omega)] at this; exact_mod_cast this
    have hx : ∀ y : Fin 3 → ZMod p, ((((2 : ZMod p) * (u ⬝ᵥ y)).val : ℕ) : ℤ) =
        2 * (u ⬝ᵥ y).val - p * wrapW p (u ⬝ᵥ y).val := by
      intro y; rw [ZMod.val_mul, h2v]; exact two_mod (ZMod.val_lt _)
    have hz : (((u ⬝ᵥ n').val : ℕ) : ℤ) - ((u ⬝ᵥ n).val : ℕ) = d := by rw [← hn1]; rfl
    have hκ : wrapW p (u ⬝ᵥ n').val - wrapW p (u ⬝ᵥ n).val = κ := by rw [← hn2]; rfl
    have hgx : ∀ c : Fin 3, (![2, 2, 1] : Fin 3 → ZMod p) c = 2 → ((g2G p (genWfam p u 0) (cellDigits p (coord p n')) c : ℕ) : ℤ) -
        g2G p (genWfam p u 0) (cellDigits p (coord p n)) c = 2 * d - p * κ := by
      intro c hc
      rw [hg2, hg2, hc, hx, hx, ← hz, ← hκ]; ring
    have hgz : ((g2G p (genWfam p u 0) (cellDigits p (coord p n')) 2 : ℕ) : ℤ) -
        g2G p (genWfam p u 0) (cellDigits p (coord p n)) 2 = d := by
      rw [hg2, hg2, show (![2, 2, 1] : Fin 3 → ZMod p) 2 = 1 from rfl, one_mul, one_mul, ← hz]
    have hsum : ∀ c : Fin 3, ∀ G : ℤ, ((g2G p (genWfam p u 0) (cellDigits p (coord p n')) c : ℕ) : ℤ) -
        g2G p (genWfam p u 0) (cellDigits p (coord p n)) c = G →
        (p : ℤ) ^ 2 * ((cellDigits p (coord p n') c : ℤ) - cellDigits p (coord p n) c) +
          p * ((g2G p (genWfam p u 0) (cellDigits p (coord p n')) c : ℤ) -
            g2G p (genWfam p u 0) (cellDigits p (coord p n)) c) +
          ((g3G p (genWfam p u 0) (cellDigits p (coord p n')) c : ℤ) -
            g3G p (genWfam p u 0) (cellDigits p (coord p n)) c) + (p : ℤ) ^ 3 * tt c =
        (p : ℤ) ^ 2 * E c + p * G := by
      intro c G hG
      rw [hG, hg3, hg3, hc1, hc1]
      have := htt c
      push_cast
      linear_combination (-(p : ℤ) ^ 2) * this
    have hint : sepSqG p (genWfam p u 0) (coord p n) (coord p n') tt =
        ((p : ℤ) ^ 2 * E 0 + p * (2 * d - p * κ)) ^ 2 + ((p : ℤ) ^ 2 * E 1 + p * (2 * d - p * κ)) ^ 2 +
          ((p : ℤ) ^ 2 * E 2 + p * d) ^ 2 := by
      rw [sepSqG_row0 _ (fun c s => genWfam_row0 u 0 s c), Fin.sum_univ_three,
        hsum 0 _ (hgx 0 rfl), hsum 1 _ (hgx 1 rfl), hsum 2 _ hgz]
    rw [hint, optValW_eval, hδ]
    push_cast
    field_simp
    ring

/-- The option of the step `e_z` has `|V|² ≤ 3`. -/
theorem optSet_le3 (u : Fin 3 → ZMod p) (hp : 0 < p) : ∃ v ∈ optSet (tauOf p u), v ≤ 3 := by
  have : NeZero p := ⟨by omega⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set f := ((u 2).val : ℝ) / p with hf
  have hf0 : 0 ≤ f := by positivity
  have hf1 : f < 1 := by rw [hf, div_lt_one hpR]; exact_mod_cast ZMod.val_lt _
  have hsum : ∑ c, tauOf p u c * (((![0, 0, 1] : Fin 3 → ℤ) c : ℤ) : ℝ) = f := by
    rw [sum3]; simp [tauOf, hf]
  rcases hf0.lt_or_eq with h | h
  · refine ⟨optValW ![0, 0, 1] (f - 1) (-1), ⟨![0, 0, 1], by decide, f - 1, -1,
      ⟨by linarith, by linarith, ⟨-1, by rw [hsum]; push_cast; ring⟩,
        Or.inl (by rw [sgnR_neg (by linarith)])⟩, rfl⟩, ?_⟩
    rw [optValW3]; push_cast; nlinarith
  · refine ⟨optValW ![0, 0, 1] 0 0, ⟨![0, 0, 1], by decide, 0, 0,
      ⟨by norm_num, by norm_num, ⟨0, by rw [hsum, ← h]; simp⟩, Or.inl (by simp [sgnR])⟩, rfl⟩, ?_⟩
    rw [optValW3]; norm_num

/-- **`prop:wfamily` (1)**, first part (proof of `Wfam_one`): `F_p(u) = F(u/p)`. -/
theorem wfam_FpW (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) : FpW p u = Ffam (tauOf p u) := by
  rw [FpW_def, Ffam_def]
  obtain ⟨v0, hv0, hv03⟩ := optSet_le3 u hp.pos
  apply le_antisymm
  · apply le_csInf ⟨v0, hv0⟩
    intro v hv
    rcases le_or_gt v 4 with h | h
    · exact csInf_le (fpSet_bdd u) (fp_real hp hp5 u hv h)
    · exact le_trans (csInf_le (fpSet_bdd u) (fp_real hp hp5 u hv0 (by linarith))) (by linarith)
  · apply le_csInf (fpSet_nonempty (by omega) u)
    intro v hv
    exact csInf_le (optSet_bdd _) (fp_mem hp hp5 u hv)

/-! ## The third digits: `|δN^{1/3} − √F_p(u)| < √3/p` -/

/-- `|√(Σ(a+b)²) − √(Σa²)| ≤ √(Σb²)` in `ℝ³`. -/
theorem sqrt_tri3 (a0 a1 a2 b0 b1 b2 : ℝ) :
    |Real.sqrt ((a0 + b0) ^ 2 + (a1 + b1) ^ 2 + (a2 + b2) ^ 2) - Real.sqrt (a0 ^ 2 + a1 ^ 2 + a2 ^ 2)| ≤
      Real.sqrt (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) := by
  set A := a0 ^ 2 + a1 ^ 2 + a2 ^ 2
  set B := b0 ^ 2 + b1 ^ 2 + b2 ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  set S := Real.sqrt A
  set T := Real.sqrt B
  have hS2 : S ^ 2 = A := Real.sq_sqrt hA
  have hT2 : T ^ 2 = B := Real.sq_sqrt hB
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hcs : (a0 * b0 + a1 * b1 + a2 * b2) ^ 2 ≤ A * B := by
    nlinarith [sq_nonneg (a0 * b1 - a1 * b0), sq_nonneg (a0 * b2 - a2 * b0), sq_nonneg (a1 * b2 - a2 * b1)]
  have hdot : |a0 * b0 + a1 * b1 + a2 * b2| ≤ S * T := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  rw [abs_le] at hdot
  have hU : (a0 + b0) ^ 2 + (a1 + b1) ^ 2 + (a2 + b2) ^ 2 = A + 2 * (a0 * b0 + a1 * b1 + a2 * b2) + B := by ring
  rw [abs_le, hU]
  constructor
  · -- `U ≥ S − T`
    rcases le_or_gt S T with h | h
    · have := Real.sqrt_nonneg (A + 2 * (a0 * b0 + a1 * b1 + a2 * b2) + B); linarith
    · have : (S - T) ^ 2 ≤ A + 2 * (a0 * b0 + a1 * b1 + a2 * b2) + B := by nlinarith
      have := Real.le_sqrt_of_sq_le this
      linarith
  · have : A + 2 * (a0 * b0 + a1 * b1 + a2 * b2) + B ≤ (S + T) ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt this
    rw [Real.sqrt_sq (by positivity)] at this
    linarith

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at this

/-- An integer jitter `|j_c| ≤ p − 1` moves `√(Σ a_c²)` by at most `√3(p − 1)`. -/
theorem jitter3 (hp : 1 ≤ p) (a j : Fin 3 → ℤ) (hj : ∀ c, |j c| ≤ (p : ℤ) - 1) :
    |Real.sqrt ((∑ c, (a c + j c) ^ 2 : ℤ) : ℝ) - Real.sqrt ((∑ c, a c ^ 2 : ℤ) : ℝ)| ≤ Real.sqrt 3 * (p - 1) := by
  have hJ : ∀ c, ((j c : ℤ) : ℝ) ^ 2 ≤ ((p : ℝ) - 1) ^ 2 := by
    intro c
    have : |(j c : ℝ)| ≤ (p : ℝ) - 1 := by exact_mod_cast hj c
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpm : (0 : ℝ) ≤ p - 1 := by linarith
  have key := sqrt_tri3 (a 0 : ℝ) (a 1 : ℝ) (a 2 : ℝ) (j 0 : ℝ) (j 1 : ℝ) (j 2 : ℝ)
  have e3 : Real.sqrt 3 * ((p : ℝ) - 1) = Real.sqrt (3 * ((p : ℝ) - 1) ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hpm]
  have hJs : Real.sqrt ((j 0 : ℝ) ^ 2 + (j 1 : ℝ) ^ 2 + (j 2 : ℝ) ^ 2) ≤ Real.sqrt 3 * (p - 1) := by
    rw [e3]; apply Real.sqrt_le_sqrt; linarith [hJ 0, hJ 1, hJ 2]
  simp only [Fin.sum_univ_three]; push_cast
  exact le_trans key hJs

/-- With third rows `T`, every pair moves by at most `√3(p − 1)` at integer scale `p³`. -/
theorem sep_T_close (hp : 2 ≤ p) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) (x x' : ℕ)
    (t : Fin 3 → ℤ) :
    |Real.sqrt (sepSqG p (genWfam p u T) x x' t : ℝ) - Real.sqrt (sepSqG p (genWfam p u 0) x x' t : ℝ)| ≤
      Real.sqrt 3 * (p - 1) := by
  have : NeZero p := ⟨by omega⟩
  have hC : ∀ T' : Fin 3 → Fin 3 → ZMod p, ∀ c s, (genWfam p u T' c *ᵥ s) 0 = s c :=
    fun T' c s => genWfam_row0 u T' s c
  have hg2 : ∀ m c, g2G p (genWfam p u T) m c = g2G p (genWfam p u 0) m c := by
    intro m c; simp only [g2G, genWfam_row1]
  have hg3 : ∀ m c, g3G p (genWfam p u 0) m c = 0 := by
    intro m c; simp only [g3G, genWfam_row2, Pi.zero_apply, zero_dotProduct, ZMod.val_zero]
  set a : Fin 3 → ℤ := fun c => (p : ℤ) ^ 2 * ((cellDigits p x' c : ℤ) - cellDigits p x c) +
    p * ((g2G p (genWfam p u 0) (cellDigits p x') c : ℤ) - g2G p (genWfam p u 0) (cellDigits p x) c) + (p : ℤ) ^ 3 * t c
  set j : Fin 3 → ℤ := fun c => (g3G p (genWfam p u T) (cellDigits p x') c : ℤ) - g3G p (genWfam p u T) (cellDigits p x) c
  have hT : sepSqG p (genWfam p u T) x x' t = ∑ c, (a c + j c) ^ 2 := by
    rw [sepSqG_row0 _ (hC T)]
    exact Finset.sum_congr rfl fun c _ => by simp only [a, j, hg2]; ring
  have h0 : sepSqG p (genWfam p u 0) x x' t = ∑ c, a c ^ 2 := by
    rw [sepSqG_row0 _ (hC 0)]
    exact Finset.sum_congr rfl fun c _ => by simp only [a, hg3]; push_cast; ring
  rw [hT, h0]
  refine jitter3 (by omega) a j fun c => ?_
  have h1 : g3G p (genWfam p u T) (cellDigits p x') c < p := ZMod.val_lt _
  have h2 : g3G p (genWfam p u T) (cellDigits p x) c < p := ZMod.val_lt _
  simp only [j]; rw [abs_le]; constructor <;> omega

/-- **`prop:wfamily` (1)**, second part (proof of `Wfam_one`): `|δN^{1/3} − √F_p(u)| < √3/p` for any third rows. -/
theorem wfam_delta (hp : p.Prime) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) :
    |deltaG p (genWfam p u T) - Real.sqrt (FpW p u)| < Real.sqrt 3 / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by positivity
  have hp2' : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  set F := FpW p u
  -- every pair of the net without third digits is `≥ √F`
  have hpair : ∀ x x' t, x < p ^ 3 → x' < p ^ 3 → x ≠ x' →
      Real.sqrt F ≤ Real.sqrt (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 2 := by
    intro x x' t hx hx' hne
    have h1 : F ≤ (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 4 :=
      csInf_le (fpSet_bdd u) ⟨x, x', t, hx, hx', hne, rfl⟩
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_div' _ hp4.le, show (p : ℝ) ^ 4 = ((p : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq hp2'.le] at this
  have hgap : Real.sqrt 3 * (p - 1) / (p : ℝ) ^ 2 + Real.sqrt 3 / (p : ℝ) ^ 2 = Real.sqrt 3 / p := by
    field_simp; ring
  have hpos : 0 < Real.sqrt 3 / (p : ℝ) ^ 2 := by positivity
  rw [abs_lt]
  constructor
  · -- lower bound
    have hlow : Real.sqrt F - Real.sqrt 3 * (p - 1) / (p : ℝ) ^ 2 ≤ deltaG p (genWfam p u T) := by
      unfold deltaG
      apply le_csInf
      · exact ⟨_, 0, 1, 0, by positivity, Nat.one_lt_pow (by norm_num) (by omega), by norm_num, rfl⟩
      · rintro e ⟨x, x', t, hx, hx', hne, rfl⟩
        have h1 := hpair x x' t hx hx' hne
        have h2 := sep_T_close hp2 u T x x' t
        rw [abs_le] at h2
        rw [sub_div' (by positivity), div_le_div_iff_of_pos_right hp2']
        rw [le_div_iff₀ hp2'] at h1
        linarith
    linarith
  · -- upper bound: a pair within `3/p⁴` of `F`
    have hne : (fpSet p u).Nonempty := fpSet_nonempty hp2 u
    obtain ⟨v, ⟨x, x', t, hx, hx', hxx, rfl⟩, hv⟩ :=
      exists_lt_of_csInf_lt hne (show sInf (fpSet p u) < F + 3 / (p : ℝ) ^ 4 by
        rw [← FpW_def]; have : (0 : ℝ) < 3 / (p : ℝ) ^ 4 := by positivity
        linarith)
    have hF0 : 0 ≤ F := le_csInf hne (fun w hw => by
      obtain ⟨y, y', s, -, -, -, rfl⟩ := hw
      apply div_nonneg _ hp4.le
      unfold sepSqG; push_cast; positivity)
    have h1 : Real.sqrt (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 2 <
        Real.sqrt F + Real.sqrt 3 / (p : ℝ) ^ 2 := by
      have := Real.sqrt_lt_sqrt (by apply div_nonneg _ hp4.le; unfold sepSqG; push_cast; positivity) hv
      rw [Real.sqrt_div' _ hp4.le, show (p : ℝ) ^ 4 = ((p : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq hp2'.le] at this
      refine lt_of_lt_of_le this ?_
      calc Real.sqrt (F + 3 / ((p : ℝ) ^ 2) ^ 2) ≤ Real.sqrt F + Real.sqrt (3 / ((p : ℝ) ^ 2) ^ 2) :=
            sqrt_add_le' hF0 (by positivity)
        _ = Real.sqrt F + Real.sqrt 3 / (p : ℝ) ^ 2 := by
            rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp2'.le]
    have h2 := sep_T_close hp2 u T x x' t
    rw [abs_le] at h2
    have h3 : deltaG p (genWfam p u T) ≤ Real.sqrt (sepSqG p (genWfam p u T) x x' t : ℝ) / (p : ℝ) ^ 2 := by
      unfold deltaG
      apply csInf_le
      · exact ⟨0, by rintro e ⟨y, y', s, -, -, -, rfl⟩; positivity⟩
      · exact ⟨x, x', t, hx, hx', hxx, rfl⟩
    have h4 : Real.sqrt (sepSqG p (genWfam p u T) x x' t : ℝ) / (p : ℝ) ^ 2 ≤
        Real.sqrt (sepSqG p (genWfam p u 0) x x' t : ℝ) / (p : ℝ) ^ 2 + Real.sqrt 3 * (p - 1) / (p : ℝ) ^ 2 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hp2'.le
    linarith

/-- `F_p(u) ≥ 0`. -/
theorem FpW_nonneg (hp : 2 ≤ p) (u : Fin 3 → ZMod p) : 0 ≤ FpW p u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by positivity
  refine le_csInf (fpSet_nonempty hp u) (fun w hw => ?_)
  obtain ⟨y, y', s, -, -, -, rfl⟩ := hw
  apply div_nonneg _ hp4.le
  unfold sepSqG; push_cast; positivity

/-- **`prop:wfamily` (3), the nets** (proof of `Wfam_three`): `F_p(u) < μ*²` and `δN^{1/3} < μ* + √3/p`, for every
prime `p ≥ 5`, every `u` and any third rows. -/
theorem wfam_three_net (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) :
    FpW p u < muStarSq ∧ deltaG p (genWfam p u T) < muStar + Real.sqrt 3 / p := by
  have hF : FpW p u < muStarSq := by
    rw [wfam_FpW hp hp5]
    obtain ⟨hle, hiff⟩ := wfam_three_tau (tauOf p u)
    refine lt_of_le_of_ne hle fun heq => ?_
    obtain ⟨k, hk⟩ := hiff.1 heq
    exact tauOf_ne_star p u k hk
  refine ⟨hF, ?_⟩
  have h1 := wfam_delta hp u T
  rw [abs_lt] at h1
  have h2 : Real.sqrt (FpW p u) < muStar := Real.sqrt_lt_sqrt (FpW_nonneg hp.two_le u) hF
  linarith

end QUNetsM3
