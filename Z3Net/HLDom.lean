module
public import Mathlib
public import Z3Net.HLRelax

@[expose] public section

/-!
# Entry HL, part 7: Prop H_k(b), the dominance limit (symbolic in `s`)

For a half-integer design (`2F_0` odd including the diagonal, `2F_x` even with zero diagonal for
`x ≥ 1`) with dominant diagonal (`2a_c = -2F_0[c][c] ≥ 2A_c`) and a relaxation configuration
`(E, J, Δ)` of `HL_relax`:

* parity: `sig2_c ≡ ∑_d E_d (mod 2)` for every `c`;
* `|sig2_c| ≤ e (2a_c + 2A_c)` with `e = max |E_d|`, and every coordinate with `|E_c| = e` is
  backward: `E_c · sig2_c ≤ 0`;
* `∑ E` odd: every coordinate gives `2 max(0, |qE_c + Δ_c| - 1) ≥ q - 2B - 2`;
* `∑ E` even: a backward coordinate gives `max(0, |qE_c + Δ_c| - 1) ≥ q |E_c| - B - 1`; with
  `e = 1` there are two moving coordinates, with `e = 2` one coordinate gives `2q - B - 1`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

section dom

variable {s : ℕ} (F2 : ℕ → Fin s → Fin s → ℤ)

/-- `max_{j ≤ s-2} |2M^(j)[c][d]|`. -/
def mx (c d : Fin s) : ℕ := (range (s - 1)).sup fun j => (M2 F2 j c d).natAbs

lemma A2_eq (c : Fin s) : (A2 s F2 c : ℤ) = ∑ d ∈ univ.erase c, (mx F2 c d : ℤ) := by
  simp [A2, mx]

lemma M2_le_mx (j : ℕ) (hj : j < s - 1) (c d : Fin s) : |M2 F2 j c d| ≤ (mx F2 c d : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup (f := fun j => (M2 F2 j c d).natAbs) (mem_range.mpr hj)

lemma M2_eq (j : ℕ) (c d : Fin s) : M2 F2 j c d = F2 0 c d + ∑ x ∈ Icc 1 j, F2 x c d := by
  unfold M2
  rw [Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  have : Icc 1 j = Finset.map ⟨(· + 1), add_left_injective 1⟩ (range j) := by
    ext t; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨t - 1, by omega, by omega⟩
    · rintro ⟨a, h1, rfl⟩; omega
  rw [this, Finset.sum_map]
  rfl

/-- One axis' contribution to `sig2_c`. -/
def contrib (E : ℤ) (J : ℕ) (c d : Fin s) : ℤ := E * F2 0 c d + E.sign * ∑ x ∈ Icc 1 J, F2 x c d

lemma contrib_bound (E : ℤ) (hE : |E| ≤ 2) (J : ℕ) (hJ : J < s - 1) (c d : Fin s) :
    |contrib F2 E J c d| ≤ |E| * (mx F2 c d : ℤ) := by
  have h0 := M2_le_mx F2 0 (by omega) c d
  have hJm := M2_le_mx F2 J hJ c d
  have e0 : M2 F2 0 c d = F2 0 c d := by simp [M2]
  rw [e0] at h0
  have eJ := M2_eq F2 J c d
  unfold contrib
  by_cases hE0 : E = 0
  · subst hE0; simp
  have hsE : E = E.sign * |E| := (Int.sign_mul_abs E).symm
  have hsg : |E.sign| = 1 := by
    rcases lt_or_gt_of_ne hE0 with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; rfl
    · rw [Int.sign_eq_one_of_pos h]; rfl
  have e : E * F2 0 c d + E.sign * ∑ x ∈ Icc 1 J, F2 x c d =
      E.sign * ((|E| - 1) * F2 0 c d + M2 F2 J c d) := by
    rw [eJ, show E * F2 0 c d = E.sign * |E| * F2 0 c d by rw [Int.sign_mul_abs]]
    ring
  rw [e, abs_mul, hsg, one_mul]
  have hE1 : 1 ≤ |E| := Int.one_le_abs hE0
  have := abs_add_le ((|E| - 1) * F2 0 c d) (M2 F2 J c d)
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ |E| - 1)] at this
  nlinarith

lemma sig2_split (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s) :
    sig2 F2 E J c = E c * F2 0 c c + ∑ d ∈ univ.erase c, contrib F2 (E d) (J d) c d := by
  unfold sig2
  rw [← Finset.add_sum_erase _ _ (mem_univ c)]
  congr 1
  rw [Finset.sum_eq_zero (fun x hx => hdiag x c (mem_Icc.mp hx).1)]
  ring

/-- `|sig2_c| ≤ e (2a_c + 2A_c)`, and coordinates with `|E_c| = e` are backward. -/
lemma sig2_bound (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (e : ℤ) (he2 : e ≤ 2) (he : ∀ d, |E d| ≤ e) (hJ : ∀ d, J d < s - 1) (c : Fin s)
    (hdom : (A2 s F2 c : ℤ) ≤ -F2 0 c c) :
    |sig2 F2 E J c| ≤ e * (-F2 0 c c + A2 s F2 c) ∧ (|E c| = e → E c * sig2 F2 E J c ≤ 0) := by
  have hR : |∑ d ∈ univ.erase c, contrib F2 (E d) (J d) c d| ≤ e * A2 s F2 c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [A2_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have := contrib_bound F2 (E d) ((he d).trans he2) (J d) (hJ d) c d
    have hm : (0 : ℤ) ≤ mx F2 c d := by positivity
    nlinarith [he d]
  rw [sig2_split F2 hdiag]
  set R := ∑ d ∈ univ.erase c, contrib F2 (E d) (J d) c d
  have hA0 : (0 : ℤ) ≤ A2 s F2 c := by positivity
  have hEc := he c
  rw [abs_le] at hR
  constructor
  · rw [abs_le]
    have h1 : |E c * F2 0 c c| ≤ e * (-F2 0 c c) := by
      rw [abs_mul, abs_of_nonpos (by linarith : F2 0 c c ≤ 0)]
      exact mul_le_mul_of_nonneg_right hEc (by linarith)
    rw [abs_le] at h1
    constructor <;> nlinarith
  · intro hce
    have hsq : E c * E c = e * e := by
      have := sq_abs (E c); rw [hce] at this; nlinarith
    have hER : E c * R ≤ e * (e * A2 s F2 c) := by
      have h2 : |E c * R| ≤ e * (e * A2 s F2 c) := by
        rw [abs_mul, hce]
        have : |R| ≤ e * A2 s F2 c := abs_le.mpr hR
        have he0 : 0 ≤ e := hce ▸ abs_nonneg _
        exact mul_le_mul_of_nonneg_left this he0
      exact (le_abs_self _).trans h2
    have : E c * (E c * F2 0 c c + R) = (E c * E c) * F2 0 c c + E c * R := by ring
    rw [this, hsq]
    have he0 : 0 ≤ e := hce ▸ abs_nonneg _
    nlinarith

/-- Parity: `sig2_c ≡ ∑ E (mod 2)`. -/
lemma sig2_parity (hodd : ∀ c d, Odd (F2 0 c d)) (heven : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s) : Even (sig2 F2 E J c - ∑ d, E d) := by
  unfold sig2
  rw [← Finset.sum_sub_distrib]
  apply Finset.even_sum
  intro d _
  have h1 : Even (F2 0 c d - 1) := by
    obtain ⟨t, ht⟩ := hodd c d; exact ⟨t, by omega⟩
  have h2 : Even (∑ x ∈ Icc 1 (J d), F2 x c d) :=
    Finset.even_sum _ fun x hx => heven x c d (mem_Icc.mp hx).1
  have : E d * F2 0 c d + (E d).sign * ∑ x ∈ Icc 1 (J d), F2 x c d - E d =
      E d * (F2 0 c d - 1) + (E d).sign * ∑ x ∈ Icc 1 (J d), F2 x c d := by ring
  rw [this]
  exact (h1.mul_left _).add (h2.mul_left _)

/-! ## One coordinate -/

lemma odd_coord (q : ℤ) (hq : 0 < q) (hqodd : Odd q) (E Δ S : ℤ) (hS : Odd S)
    (hdvd : q ∣ 2 * Δ - S) (hΔ : |Δ| < q) (hSq : |S| < q) :
    q - |S| - 2 ≤ 2 * max 0 (|q * E + Δ| - 1) := by
  obtain ⟨t, ht⟩ := hdvd
  have htodd : Odd t := by
    by_contra h
    rw [Int.not_odd_iff_even] at h
    obtain ⟨r, hr⟩ := h
    obtain ⟨w, hw⟩ := hS
    have : 2 * Δ - S = 2 * (q * r) := by rw [ht, hr]; ring
    omega
  have ht1 : t = 1 ∨ t = -1 := by
    rw [abs_lt] at hΔ hSq
    have h3 : -3 < t := by
      by_contra h; push_neg at h; nlinarith
    have h4 : t < 3 := by
      by_contra h; push_neg at h; nlinarith
    obtain ⟨w, hw⟩ := htodd
    omega
  have key : q - |S| ≤ |2 * (q * E + Δ)| := by
    have e : 2 * (q * E + Δ) = q * (2 * E + t) + S := by linarith
    rw [e]
    have h1 : 1 ≤ |2 * E + t| := by
      rcases ht1 with h | h <;> subst h <;> exact Int.one_le_abs (by omega)
    have h2 : q ≤ |q * (2 * E + t)| := by
      rw [abs_mul, abs_of_pos hq]; nlinarith
    have := abs_add_le (q * (2 * E + t) + S) (-S)
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  rw [abs_mul, abs_two] at key
  have := le_max_right 0 (|q * E + Δ| - 1)
  linarith

lemma even_coord (q : ℤ) (hq : 0 < q) (hqodd : Odd q) (E Δ σ : ℤ)
    (hdvd : q ∣ 2 * Δ - 2 * σ) (hΔ : |Δ| < q) (hσq : 2 * |σ| < q) (hE : E ≠ 0)
    (hback : E * σ ≤ 0) :
    q * |E| - |σ| - 1 ≤ max 0 (|q * E + Δ| - 1) := by
  obtain ⟨t, ht⟩ := hdvd
  have hteven : Even t := by
    by_contra h
    rw [Int.not_even_iff_odd] at h
    have hprod : Odd (q * t) := hqodd.mul h
    rw [← ht] at hprod
    obtain ⟨w, hw⟩ := hprod
    omega
  obtain ⟨κ, hκ⟩ := hteven
  have hΔe : Δ = σ + κ * q := by
    have h2 : 2 * Δ - 2 * σ = 2 * (κ * q) := by rw [ht, hκ]; ring
    omega
  have hκ1 : κ = -1 ∨ κ = 0 ∨ κ = 1 := by
    have h1 : |κ * q| < 2 * q := by
      have e : κ * q = Δ - σ := by linarith
      rw [e]
      have := abs_sub Δ σ
      linarith [abs_nonneg σ]
    rw [abs_mul, abs_of_pos hq] at h1
    have h2 : |κ| < 2 := by nlinarith
    rw [abs_lt] at h2
    omega
  have key : q * |E| - |σ| ≤ |q * E + Δ| := by
    rw [hΔe]
    rcases hκ1 with h | h | h <;> subst h
    · -- `κ = -1`: only possible for `E < 0`
      rcases lt_or_gt_of_ne hE with hneg | hpos
      · have e : q * E + (σ + -1 * q) = q * (E - 1) + σ := by ring
        rw [e, abs_of_neg hneg]
        have h1 : |q * (E - 1)| = q * (1 - E) := by
          rw [abs_mul, abs_of_pos hq, abs_of_neg (by omega)]; ring
        have := abs_add_le (q * (E - 1) + σ) (-σ)
        rw [add_neg_cancel_right, abs_neg, h1] at this
        linarith
      · exfalso
        have : 0 ≤ σ ∨ σ < 0 := le_or_gt 0 σ
        rcases this with h0 | h0
        · rw [abs_lt] at hΔ; rw [hΔe] at hΔ
          have : E * σ ≤ 0 := hback
          have hσ0 : σ = 0 := by nlinarith
          subst hσ0; linarith [hΔ.1]
        · rw [abs_lt] at hΔ; rw [hΔe] at hΔ
          have : E * σ ≤ 0 := hback
          nlinarith
    · have e : q * E + (σ + 0 * q) = q * E + σ := by ring
      rw [e]
      have h1 : |q * E| = q * |E| := by rw [abs_mul, abs_of_pos hq]
      have := abs_add_le (q * E + σ) (-σ)
      rw [add_neg_cancel_right, abs_neg, h1] at this
      linarith
    · rcases lt_or_gt_of_ne hE with hneg | hpos
      · exfalso
        rw [abs_lt] at hΔ; rw [hΔe] at hΔ
        have : E * σ ≤ 0 := hback
        rcases le_or_gt σ 0 with h0 | h0
        · have hσ0 : σ = 0 := by nlinarith
          subst hσ0; linarith [hΔ.2]
        · linarith [hΔ.2]
      · have e : q * E + (σ + 1 * q) = q * (E + 1) + σ := by ring
        rw [e, abs_of_pos hpos]
        have h1 : |q * (E + 1)| = q * (E + 1) := by
          rw [abs_mul, abs_of_pos hq, abs_of_pos (by omega)]
        have := abs_add_le (q * (E + 1) + σ) (-σ)
        rw [add_neg_cancel_right, abs_neg, h1] at this
        linarith
  have := le_max_right 0 (|q * E + Δ| - 1)
  linarith

/-! ## The dominance bound for one configuration -/

lemma Bdom_ge (c : Fin s) (hdom : (A2 s F2 c : ℤ) ≤ -F2 0 c c) :
    -F2 0 c c + A2 s F2 c ≤ (Bdom s F2 : ℤ) := by
  have h := Finset.le_sup (f := fun c : Fin s => (-F2 0 c c).toNat + A2 s F2 c) (mem_univ c)
  have h0 : (0 : ℤ) ≤ -F2 0 c c := le_trans (by positivity) hdom
  have : (((-F2 0 c c).toNat + A2 s F2 c : ℕ) : ℤ) = -F2 0 c c + A2 s F2 c := by
    push_cast; rw [Int.toNat_of_nonneg h0]
  rw [← this]
  exact_mod_cast h

theorem dom_arith (hs : 2 ≤ s) (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (q : ℤ) (hqodd : Odd q) (hqB : 2 * (Bdom s F2 : ℤ) + 2 ≤ q)
    (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ) (hE : ∀ c, |E c| ≤ 2) (hne : ∃ c, E c ≠ 0)
    (hJ : ∀ c, J c < s - 1) (hdvd : ∀ c, q ∣ 2 * Δ c - sig2 F2 E J c) (hΔ : ∀ c, |Δ c| < q) :
    min ((s : ℤ) * (q - 2 * Bdom s F2 - 2) ^ 2) (8 * (q - Bdom s F2 - 1) ^ 2) ≤
      4 * ∑ c, (max 0 (|q * E c + Δ c| - 1)) ^ 2 := by
  set B : ℤ := (Bdom s F2 : ℤ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hq0 : 0 < q := by linarith
  have hBc : ∀ c, -F2 0 c c + A2 s F2 c ≤ B := fun c => Bdom_ge F2 c (hdom c)
  have hnn : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤ (max 0 (|q * E c + Δ c| - 1)) ^ 2 :=
    fun c _ => sq_nonneg _
  have hS2 : ∀ c, |sig2 F2 E J c| ≤ 2 * B := by
    intro c
    have := (sig2_bound F2 hdiag E J 2 le_rfl hE hJ c (hdom c)).1
    nlinarith [hBc c]
  by_cases hpar : Odd (∑ d, E d)
  · -- odd case: every coordinate is half a cell off
    have hc : ∀ c, (q - 2 * B - 2) ^ 2 ≤ 4 * (max 0 (|q * E c + Δ c| - 1)) ^ 2 := by
      intro c
      have hSodd : Odd (sig2 F2 E J c) := by
        have h := sig2_parity F2 hhalf0 hhalf E J c
        have : sig2 F2 E J c = (sig2 F2 E J c - ∑ d, E d) + ∑ d, E d := by ring
        rw [this]; exact h.add_odd hpar
      have h1 := odd_coord q hq0 hqodd (E c) (Δ c) (sig2 F2 E J c) hSodd (hdvd c) (hΔ c)
        (by linarith [hS2 c])
      have h2 : q - 2 * B - 2 ≤ 2 * max 0 (|q * E c + Δ c| - 1) := by linarith [hS2 c]
      have h3 : 0 ≤ q - 2 * B - 2 := by linarith
      nlinarith
    calc min ((s : ℤ) * (q - 2 * B - 2) ^ 2) (8 * (q - B - 1) ^ 2) ≤ (s : ℤ) * (q - 2 * B - 2) ^ 2 :=
          min_le_left _ _
      _ = ∑ _c : Fin s, (q - 2 * B - 2) ^ 2 := by simp
      _ ≤ ∑ c, 4 * (max 0 (|q * E c + Δ c| - 1)) ^ 2 := Finset.sum_le_sum fun c _ => hc c
      _ = _ := by rw [Finset.mul_sum]
  · -- even case: backward coordinates
    rw [Int.not_odd_iff_even] at hpar
    have hSeven : ∀ c, Even (sig2 F2 E J c) := by
      intro c
      have h := sig2_parity F2 hhalf0 hhalf E J c
      have : sig2 F2 E J c = (sig2 F2 E J c - ∑ d, E d) + ∑ d, E d := by ring
      rw [this]; exact h.add hpar
    have hback : ∀ (e : ℤ), e ≤ 2 → (∀ d, |E d| ≤ e) → ∀ c, |E c| = e → E c ≠ 0 →
        q * e - e * B / 2 - 1 ≤ max 0 (|q * E c + Δ c| - 1) ∧ |sig2 F2 E J c| ≤ e * B := by
      intro e he2 he c hce hc0
      obtain ⟨hb, hbk⟩ := sig2_bound F2 hdiag E J e he2 he hJ c (hdom c)
      have he0 : 0 ≤ e := hce ▸ abs_nonneg _
      have hb' : |sig2 F2 E J c| ≤ e * B := le_trans hb (by nlinarith [hBc c])
      obtain ⟨σ, hσ⟩ := hSeven c
      have hS : sig2 F2 E J c = 2 * σ := by rw [hσ]; ring
      have hσb : 2 * |σ| ≤ e * B := by
        have : |sig2 F2 E J c| = 2 * |σ| := by rw [hS, abs_mul]; norm_num
        linarith
      have hσq : 2 * |σ| < q := by nlinarith
      have hbk' : E c * σ ≤ 0 := by
        have := hbk hce; rw [hS] at this; nlinarith
      have h1 := even_coord q hq0 hqodd (E c) (Δ c) σ (by rw [← hS]; exact hdvd c) (hΔ c) hσq hc0 hbk'
      refine ⟨?_, hb'⟩
      rw [hce] at h1
      have : e * B / 2 ≥ |σ| := by
        rw [ge_iff_le, Int.le_ediv_iff_mul_le (by norm_num)]; linarith
      linarith
    by_cases h2 : ∃ c, |E c| = 2
    · obtain ⟨c, hc⟩ := h2
      have hc0 : E c ≠ 0 := by intro h; rw [h] at hc; simp at hc
      obtain ⟨h1, _⟩ := hback 2 le_rfl hE c hc hc0
      have hB2 : 2 * B / 2 = B := by omega
      rw [hB2] at h1
      have hpos : 0 ≤ q * 2 - B - 1 := by linarith
      have hsq : (q * 2 - B - 1) ^ 2 ≤ (max 0 (|q * E c + Δ c| - 1)) ^ 2 :=
        pow_le_pow_left₀ hpos h1 2
      have hsingle := Finset.single_le_sum hnn (mem_univ c)
      calc min ((s : ℤ) * (q - 2 * B - 2) ^ 2) (8 * (q - B - 1) ^ 2) ≤ 8 * (q - B - 1) ^ 2 :=
            min_le_right _ _
        _ ≤ 4 * (q * 2 - B - 1) ^ 2 := by nlinarith
        _ ≤ _ := by nlinarith
    · push_neg at h2
      have hE1 : ∀ d, |E d| ≤ 1 := by
        intro d; have := hE d; have := h2 d; omega
      obtain ⟨c0, hc0⟩ := hne
      have hc0a : |E c0| = 1 := by have := hE1 c0; have := Int.one_le_abs hc0; omega
      have hc1 : ∃ c1, c1 ≠ c0 ∧ E c1 ≠ 0 := by
        by_contra hall
        push_neg at hall
        have : ∑ d, E d = E c0 := by
          rw [← Finset.add_sum_erase _ _ (mem_univ c0), Finset.sum_eq_zero (fun d hd =>
            hall d (Finset.ne_of_mem_erase hd)), add_zero]
        rw [this] at hpar
        obtain ⟨w, hw⟩ := hpar
        rw [abs_eq (by norm_num)] at hc0a
        omega
      obtain ⟨c1, hc10, hc1⟩ := hc1
      have hc1a : |E c1| = 1 := by have := hE1 c1; have := Int.one_le_abs hc1; omega
      obtain ⟨h0, _⟩ := hback 1 (by norm_num) hE1 c0 hc0a hc0
      obtain ⟨h1, _⟩ := hback 1 (by norm_num) hE1 c1 hc1a hc1
      have hBh : 1 * B / 2 ≤ B := by omega
      have hpos : 0 ≤ q - B - 1 := by linarith
      have h0' : q - B - 1 ≤ max 0 (|q * E c0 + Δ c0| - 1) := by linarith
      have h1' : q - B - 1 ≤ max 0 (|q * E c1 + Δ c1| - 1) := by linarith
      have hpair : (max 0 (|q * E c0 + Δ c0| - 1)) ^ 2 + (max 0 (|q * E c1 + Δ c1| - 1)) ^ 2 ≤
          ∑ c, (max 0 (|q * E c + Δ c| - 1)) ^ 2 := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c => (max 0 (|q * E c + Δ c| - 1)) ^ 2)
          (subset_univ ({c0, c1} : Finset (Fin s))) (fun c _ _ => sq_nonneg _)
        rwa [Finset.sum_pair (Ne.symm hc10)] at this
      calc min ((s : ℤ) * (q - 2 * B - 2) ^ 2) (8 * (q - B - 1) ^ 2) ≤ 8 * (q - B - 1) ^ 2 :=
            min_le_right _ _
        _ ≤ 4 * ((max 0 (|q * E c0 + Δ c0| - 1)) ^ 2 + (max 0 (|q * E c1 + Δ c1| - 1)) ^ 2) := by
            nlinarith [pow_le_pow_left₀ hpos h0' 2, pow_le_pow_left₀ hpos h1' 2]
        _ ≤ _ := by linarith

end dom

end

end Z3NetHL.Proofs
