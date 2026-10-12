module
public import Mathlib
public import Z3Net.S1Cells
public import Z3Net.S1Real

@[expose] public section

/-!
# Entry S1, part 8: Theorem `thm:S1`(1) limit and (3) covering, mesh ratio, limits

* `digits_exist`, `low_sum_bound`: signed base-`ρ` digits in prescribed windows `[0, ρ-1]` or
  `[-(ρ-1), 0]`, and `|∑_{i<n} e_i ρ^i| ≤ ρ^n - 1`.
* `cover_int`: for every fine cell `Q ∈ [0, p^(k+1))^s` there is `a ∈ Λ` in the same range with
  `‖a - Q‖∞ ≤ μ` (the proof of `thm:S1`(3)); with `S1_cells` every such `a` is an occupied cell.
* `S1_cover`, `S1_mesh`, `S1_mu`; `S1_const_tendsto`, `S1_mesh_tendsto`.
-/

namespace Z3NetS1.Proofs

open Finset Filter Topology Z3NetKN.Geom

/-! ## Signed digits -/

lemma digits_exist (ρ : ℤ) (hρ : 1 ≤ ρ) : ∀ (n : ℕ) (t : ℤ) (τ : ℕ → Bool),
    ∃ e : ℕ → ℤ, ∃ q : ℤ,
      (∀ i < n, (τ i = true → 0 ≤ e i ∧ e i ≤ ρ - 1) ∧ (τ i = false → -(ρ - 1) ≤ e i ∧ e i ≤ 0)) ∧
      t = ∑ i ∈ range n, e i * ρ ^ i + q * ρ ^ n
  | 0, t, _ => ⟨fun _ => 0, t, by simp, by simp⟩
  | n + 1, t, τ => by
    have hρ0 : 0 < ρ := by omega
    obtain ⟨e0, t1, he0, ht⟩ : ∃ e0 t1 : ℤ,
        ((τ 0 = true → 0 ≤ e0 ∧ e0 ≤ ρ - 1) ∧ (τ 0 = false → -(ρ - 1) ≤ e0 ∧ e0 ≤ 0)) ∧
          t = e0 + ρ * t1 := by
      cases h0 : τ 0
      · refine ⟨-((-t) % ρ), -((-t) / ρ), ⟨fun h => by simp at h, fun _ => ?_⟩, ?_⟩
        · have := Int.emod_nonneg (-t) hρ0.ne'
          have := Int.emod_lt_of_pos (-t) hρ0
          constructor <;> omega
        · have := Int.mul_ediv_add_emod (-t) ρ
          linarith
      · refine ⟨t % ρ, t / ρ, ⟨fun _ => ?_, fun h => by simp at h⟩, ?_⟩
        · have := Int.emod_nonneg t hρ0.ne'
          have := Int.emod_lt_of_pos t hρ0
          constructor <;> omega
        · have := Int.mul_ediv_add_emod t ρ
          linarith
    obtain ⟨e', q, he', ht1⟩ := digits_exist ρ hρ n t1 (fun i => τ (i + 1))
    refine ⟨fun i => if i = 0 then e0 else e' (i - 1), q, ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · simpa using he0
      · simpa using he' i (by omega)
    · rw [sum_range_succ']
      simp only [pow_zero, mul_one, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, ite_true,
        if_true]
      rw [ht, ht1, mul_add, mul_sum]
      have : ∀ i ∈ range n, ρ * (e' i * ρ ^ i) = e' i * ρ ^ (i + 1) := fun i _ => by ring
      rw [sum_congr rfl this, pow_succ]
      ring

lemma low_sum_bound (ρ : ℤ) (hρ : 1 ≤ ρ) (e : ℕ → ℤ) : ∀ n : ℕ, (∀ i < n, |e i| ≤ ρ - 1) →
    |∑ i ∈ range n, e i * ρ ^ i| ≤ ρ ^ n - 1
  | 0, _ => by simp
  | n + 1, h => by
    rw [sum_range_succ]
    have h1 := low_sum_bound ρ hρ e n (fun i hi => h i (by omega))
    have hρ0 : (0 : ℤ) ≤ ρ ^ n := pow_nonneg (by omega) n
    have h2 : |e n * ρ ^ n| ≤ (ρ - 1) * ρ ^ n := by
      rw [abs_mul, abs_of_nonneg hρ0]
      exact mul_le_mul_of_nonneg_right (h n (by omega)) hρ0
    calc |∑ i ∈ range n, e i * ρ ^ i + e n * ρ ^ n|
        ≤ |∑ i ∈ range n, e i * ρ ^ i| + |e n * ρ ^ n| := abs_add_le _ _
      _ ≤ (ρ ^ n - 1) + (ρ - 1) * ρ ^ n := add_le_add h1 h2
      _ = ρ ^ (n + 1) - 1 := by ring

/-! ## The integer covering lemma -/

theorem cover_int (s p k ρ μ : ℕ) (hs : 2 ≤ s) (hρ : 1 ≤ ρ) (hp : 0 < p) (hμρ : ρ - 1 ≤ μ)
    (hμp : p ≤ μ * ρ ^ (s - 1)) (hP : 2 * μ + 1 ≤ p ^ (k + 1)) (Q : Fin s → ℕ)
    (hQ : ∀ c, Q c < p ^ (k + 1)) :
    ∃ a : Fin s → ℕ, (∀ c, a c < p ^ (k + 1)) ∧ (fun c => (a c : ℤ)) ∈ S1lat s p ρ ∧
      ∀ c, |(a c : ℤ) - Q c| ≤ μ := by
  set P : ℤ := ((p ^ (k + 1) : ℕ) : ℤ) with hPdef
  set n := s - 1 with hn
  have hn1 : 1 ≤ n := by omega
  set Qn : ℕ → ℤ := fun i => if h : i < s then (Q ⟨i, h⟩ : ℤ) else 0 with hQn
  have hρz : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  set R : ℤ := (ρ : ℤ) ^ n with hR
  have hR1 : 1 ≤ R := one_le_pow₀ hρz
  -- the target residue
  set T : ℤ := Qn (s - 1) - ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * Qn d with hT
  set up : Bool := decide (2 * Qn (s - 2) < P) with hup
  set T' : ℤ := if up then T % p else T % p - p with hT'
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hTm := Int.emod_nonneg T hp'.ne'
  have hTl := Int.emod_lt_of_pos T hp'
  set τ : ℕ → Bool := fun i => if i = 0 then decide ¬(2 * Qn (s - 1) < P) else decide (2 * Qn (i - 1) < P)
    with hτ
  obtain ⟨e, q, he, hTe⟩ := digits_exist (ρ : ℤ) hρz n T' τ
  have heb : ∀ i < n, |e i| ≤ (ρ : ℤ) - 1 := by
    intro i hi
    rcases (he i hi) with ⟨h1, h2⟩
    cases hτi : τ i
    · obtain ⟨a1, a2⟩ := h2 hτi; rw [abs_le]; constructor <;> linarith
    · obtain ⟨a1, a2⟩ := h1 hτi; rw [abs_le]; constructor <;> linarith
  have hL := low_sum_bound (ρ : ℤ) hρz e n heb
  rw [← hR] at hL
  set L := ∑ i ∈ range n, e i * (ρ : ℤ) ^ i with hLdef
  have hμ' : (p : ℤ) ≤ (μ : ℤ) * R := by rw [hR]; exact_mod_cast hμp
  -- the top digit
  have hqR : q * R = T' - L := by rw [hR]; linarith
  have hT'abs : |T'| ≤ p := by
    rw [hT']; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hq : |q| ≤ μ := by
    have h1 : |q| * R ≤ p + R - 1 := by
      have ea : |q| * R = |q * R| := by rw [abs_mul, abs_of_pos (show (0 : ℤ) < R by omega)]
      rw [ea, hqR]
      calc |T' - L| ≤ |T'| + |L| := abs_sub _ _
        _ ≤ p + (R - 1) := add_le_add hT'abs hL
        _ = p + R - 1 := by ring
    have h2 : |q| * R < ((μ : ℤ) + 1) * R := by nlinarith
    have := lt_of_mul_lt_mul_right h2 (by omega)
    omega
  have hqsign : (up = true → 0 ≤ q) ∧ (up = false → q ≤ 0) := by
    have hLa := abs_le.1 hL
    constructor
    · intro hu
      have : 0 ≤ T' := by rw [hT', if_pos hu]; exact hTm
      have h3 : -R < q * R := by rw [hqR]; linarith
      by_contra hneg
      have : q * R ≤ -R := by nlinarith
      linarith
    · intro hu
      have : T' ≤ -1 := by rw [hT', if_neg (by simp [hu])]; linarith
      have h3 : q * R < R := by rw [hqR]; linarith
      by_contra hpos
      have : R ≤ q * R := by nlinarith
      linarith
  -- the extended digits and the step `d`
  set E : ℕ → ℤ := fun i => if i < n then e i else q with hE
  set D : ℕ → ℤ := fun c => if c = s - 1 then E 0 else -E (c + 1) with hD
  have hDabs : ∀ c < s, |D c| ≤ μ := by
    intro c hc
    have hEb : ∀ i ≤ n, |E i| ≤ μ := by
      intro i hi
      simp only [hE]
      split_ifs with h
      · have := heb i h; omega
      · exact hq
    simp only [hD]
    split_ifs with h
    · exact hEb 0 (by omega)
    · rw [abs_neg]; exact hEb (c + 1) (by omega)
  have hDsign : ∀ c < s, (2 * Qn c < P → D c ≤ 0) ∧ (¬ 2 * Qn c < P → 0 ≤ D c) := by
    intro c hc
    by_cases hz : c = s - 1
    · subst hz
      have hE0 : E 0 = e 0 := by simp only [hE]; rw [if_pos (by omega)]
      have hτ0 : τ 0 = decide ¬(2 * Qn (s - 1) < P) := by simp [hτ]
      simp only [hD, if_pos rfl, hE0]
      obtain ⟨h1, h2⟩ := he 0 (by omega)
      constructor
      · intro hlt; exact (h2 (by rw [hτ0]; simp [hlt])).2
      · intro hlt; exact (h1 (by rw [hτ0]; simp [hlt])).1
    · simp only [hD, if_neg hz]
      by_cases hcn : c + 1 < n
      · have hEc : E (c + 1) = e (c + 1) := by simp only [hE]; rw [if_pos hcn]
        have hτc : τ (c + 1) = decide (2 * Qn c < P) := by simp [hτ]
        rw [hEc]
        obtain ⟨h1, h2⟩ := he (c + 1) hcn
        constructor
        · intro hlt; have := (h1 (by rw [hτc]; simp [hlt])).1; linarith
        · intro hlt; have := (h2 (by rw [hτc]; simp [hlt])).2; linarith
      · have hcs : c = s - 2 := by omega
        have hEc : E (c + 1) = q := by simp only [hE]; rw [if_neg hcn]
        rw [hEc]
        constructor
        · intro hlt
          have hu : up = true := by rw [hup, ← hcs]; simp [hlt]
          have := hqsign.1 hu; linarith
        · intro hlt
          have hu : up = false := by rw [hup, ← hcs]; simp [hlt]
          have := hqsign.2 hu; linarith
  -- the cell `a = Q - D`
  have hPμ : 2 * (μ : ℤ) + 1 ≤ P := by rw [hPdef]; exact_mod_cast hP
  have hrange : ∀ c < s, 0 ≤ Qn c - D c ∧ Qn c - D c < P := by
    intro c hc
    have hQc : 0 ≤ Qn c ∧ Qn c < P := by
      simp only [hQn, dif_pos hc]
      exact ⟨by positivity, by rw [hPdef]; exact_mod_cast hQ ⟨c, hc⟩⟩
    have hd := abs_le.1 (hDabs c hc)
    obtain ⟨hs1, hs2⟩ := hDsign c hc
    by_cases hlt : 2 * Qn c < P
    · have := hs1 hlt; constructor <;> linarith
    · have := hs2 hlt; constructor <;> linarith
  refine ⟨fun c => (Qn c - D c).toNat, ?_, ?_, ?_⟩
  · intro c
    have := hrange c c.isLt
    have h2 : ((Qn c - D c).toNat : ℤ) < P := by rw [Int.toNat_of_nonneg this.1]; exact this.2
    rw [hPdef] at h2; exact_mod_cast h2
  · rw [mem_S1lat, sum_chk s ρ (by omega)]
    have hcast : ∀ d, d < s → (if h : d < s then (((fun c : Fin s => (Qn c - D c).toNat) ⟨d, h⟩ : ℕ) : ℤ)
        else 0) = Qn d - D d := by
      intro d hd
      rw [dif_pos hd]
      exact Int.toNat_of_nonneg (hrange d hd).1
    rw [hcast (s - 1) (by omega)]
    rw [sum_congr rfl fun d hd => by simp only [mem_range] at hd; rw [hcast d (by omega)]]
    -- `∑ ρ^(d+1) (Q_d - D_d) - (Q_z - D_z) = T' - T`
    have hDsum : D (s - 1) - ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * D d = T' := by
      rw [hTe]
      simp only [hD, if_pos rfl]
      have hEsum : ∑ i ∈ range (n + 1), E i * (ρ : ℤ) ^ i = L + q * R := by
        rw [sum_range_succ, hLdef, hR]
        simp only [hE, if_neg (lt_irrefl n)]
        congr 1
        exact sum_congr rfl fun i hi => by simp only [mem_range] at hi; rw [if_pos hi]
      rw [← hEsum, sum_range_succ', ← hn]
      have : ∀ d ∈ range n, (ρ : ℤ) ^ (d + 1) * (if d = s - 1 then E 0 else -E (d + 1)) =
          -(E (d + 1) * (ρ : ℤ) ^ (d + 1)) := by
        intro d hd; simp only [mem_range] at hd
        rw [if_neg (by omega)]; ring
      rw [sum_congr rfl this, sum_neg_distrib, sub_neg_eq_add]
      ring
    have hdvd : (p : ℤ) ∣ T' - T := by
      rw [hT']
      split_ifs
      · rw [Int.emod_def]; exact ⟨-(T / p), by ring⟩
      · rw [Int.emod_def]; exact ⟨-(T / p) - 1, by ring⟩
    have e2 : ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * (Qn d - D d) - (Qn (s - 1) - D (s - 1)) =
        T' - T := by
      rw [← hDsum, hT]
      simp only [mul_sub, sum_sub_distrib]
      ring
    rw [e2]; exact hdvd
  · intro c
    have h1 := hrange c c.isLt
    rw [Int.toNat_of_nonneg h1.1]
    have hQc : Qn c = (Q c : ℤ) := by simp only [hQn, dif_pos c.isLt]
    rw [hQc, show (Q c : ℤ) - D c - Q c = -D c by ring, abs_neg]
    exact hDabs c c.isLt

/-! ## `ρ_s(p)`, `μ` -/

lemma rhoS_bounds (s p : ℕ) (hs : 1 ≤ s) (hp : 1 ≤ p) :
    rhoS s p ^ s < p ∧ p ≤ (rhoS s p + 1) ^ s := by
  have hspec : rhoS s p ^ s < p := Nat.findGreatest_spec (P := fun ρ => ρ ^ s < p) (Nat.zero_le p)
    (by simp only [zero_pow (show s ≠ 0 by omega)]; omega)
  refine ⟨hspec, ?_⟩
  have hρlt : rhoS s p < p := lt_of_le_of_lt (Nat.le_self_pow (by omega) _) hspec
  have := Nat.findGreatest_is_greatest (P := fun ρ => ρ ^ s < p) (n := p)
    (k := rhoS s p + 1) (by unfold rhoS; omega) (by omega)
  simpa using this

lemma rhoS_ge (s p M : ℕ) (hs : 1 ≤ s) (hM : M ^ s + M < p) : M ≤ rhoS s p :=
  Nat.le_findGreatest (by omega) (by omega)

lemma rhoS_tendsto (s : ℕ) (hs : 1 ≤ s) : Tendsto (fun p => rhoS s p) atTop atTop :=
  tendsto_atTop_atTop.2 fun M => ⟨M ^ s + M + 1, fun p hp => rhoS_ge s p M hs (by omega)⟩

lemma muS_spec (s p ρ : ℕ) (hρ : 1 ≤ ρ) :
    p ≤ muS s p ρ * ρ ^ (s - 1) ∧ muS s p ρ * ρ ^ (s - 1) ≤ p + ρ ^ (s - 1) - 1 := by
  have hR : 0 < ρ ^ (s - 1) := Nat.pos_of_ne_zero (by positivity)
  unfold muS
  have h1 := Nat.div_mul_le_self (p + ρ ^ (s - 1) - 1) (ρ ^ (s - 1))
  have h2 := Nat.lt_div_mul_add (a := p + ρ ^ (s - 1) - 1) hR
  generalize (p + ρ ^ (s - 1) - 1) / ρ ^ (s - 1) * ρ ^ (s - 1) = y at h1 h2 ⊢
  omega

/-- `ρ - 1 ≤ μ` whenever `ρ^s < p` (`ρ ≥ 1`, `s ≥ 1`). -/
lemma muS_ge (s p ρ : ℕ) (hs : 1 ≤ s) (hρ : 1 ≤ ρ) (hρp : ρ ^ s < p) : ρ - 1 ≤ muS s p ρ := by
  obtain ⟨h1, -⟩ := muS_spec s p ρ hρ
  have hR : 0 < ρ ^ (s - 1) := Nat.pos_of_ne_zero (by positivity)
  have e : ρ ^ s = ρ * ρ ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (ρ - 1) * ρ ^ (s - 1) < muS s p ρ * ρ ^ (s - 1) := by
    calc (ρ - 1) * ρ ^ (s - 1) ≤ ρ * ρ ^ (s - 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = ρ ^ s := e.symm
      _ < p := hρp
      _ ≤ _ := h1
  exact le_of_lt (lt_of_mul_lt_mul_right this (Nat.zero_le _))

/-- `2 μ + 1 ≤ p` for `s ≥ 3`, `ρ ≥ 2`, `p ≥ 5`. -/
lemma muS_small (s p ρ : ℕ) (hs : 3 ≤ s) (hρ : 2 ≤ ρ) (hp : 5 ≤ p) : 2 * muS s p ρ + 1 ≤ p := by
  obtain ⟨-, h2⟩ := muS_spec s p ρ (by omega)
  have hR : 4 ≤ ρ ^ (s - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ρ ^ (s - 1) := Nat.pow_le_pow_left hρ _
  -- `μ R ≤ p + R - 1` with `R ≥ 4` gives `4 (μ - 1) ≤ p - 1`
  have : (muS s p ρ - 1) * ρ ^ (s - 1) ≤ p - 1 := by
    rw [Nat.sub_mul, one_mul]; omega
  have h4 : (muS s p ρ - 1) * 4 ≤ p - 1 := le_trans (Nat.mul_le_mul_left _ hR) this
  omega

/-! ## Real forms -/

lemma hrp_eq (s p k : ℕ) (hs : 1 ≤ s) (hp : 0 < p) :
    (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) =
      1 / (p : ℝ) ^ (k + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hm1 : (s * k + (s - 1)) + 1 = s * (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [← Real.mul_rpow hp0.le (by positivity), ← pow_succ', hm1, ← Real.rpow_natCast,
    ← Real.rpow_mul hp0.le, show ((s * (k + 1) : ℕ) : ℝ) * (-(1 / (s : ℝ))) = -((k + 1 : ℕ) : ℝ) by
      push_cast; field_simp, Real.rpow_neg hp0.le, Real.rpow_natCast, one_div]

theorem S1_cover (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k (rhoS s p) C) (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, Real.sqrt (∑ c, (y c - (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2)
      < Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) *
          ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hρ2, hρs, -, -⟩ := S1_const s p (by omega) hp hps
  set ρ := rhoS s p with hρdef
  set μ := muS s p ρ with hμdef
  have hp0 := hp.pos
  have h8 : 8 ≤ 2 ^ s := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  set P := p ^ (k + 1) with hPdef
  have hpP : p ≤ P := Nat.le_self_pow (by omega) p
  have hP0 : 0 < P := by positivity
  set Q : Fin s → ℕ := fun c => ⌊y c * (P : ℝ)⌋₊ with hQdef
  have hQ : ∀ c, Q c < P := by
    intro c
    have hyc := hy c
    have : y c * (P : ℝ) < (P : ℕ) := by
      have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
      nlinarith
    exact (Nat.floor_lt (mul_nonneg (hy c).1 (by positivity))).2 this
  obtain ⟨a, ha, hmem, hdist⟩ := cover_int s p k ρ μ (by omega) (by omega) hp0
    (muS_ge s p ρ (by omega) (by omega) hρs) (muS_spec s p ρ (by omega)).1
    (le_trans (muS_small s p ρ hs hρ2 (by omega)) hpP) Q hQ
  obtain ⟨v, hv, -⟩ := S1_cells s p k ρ (by omega) hp C hC |>.2 a ha hmem
  refine ⟨v, ?_⟩
  -- each coordinate is within `(μ + 1)/P`
  have hkm : k + 1 ≤ (s * k + (s - 1)) := kle (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f = p ^ ((s * k + (s - 1)) - (k + 1)) := ⟨_, rfl⟩
  have hN : (p : ℝ) ^ (s * k + (s - 1)) = (P : ℝ) * (f : ℝ) := by
    rw [hPdef, hf]; push_cast; rw [← pow_add]; congr 1; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
  have hfr : (0 : ℝ) < f := by rw [hf]; push_cast; positivity
  have hcoord : ∀ c, (a c : ℝ) * f ≤ (digPoint p (s * k + (s - 1)) C v c : ℝ) ∧
      (digPoint p (s * k + (s - 1)) C v c : ℝ) < ((a c : ℝ) + 1) * f := by
    intro c
    have hsplit := coord_split (C c) v (k + 1) hkm
    have hlow := low_lt (C c) v (k + 1)
    rw [← hf] at hsplit hlow
    have hPf : Pf k (C c) v = a c := by rw [← finePos_eq (by omega), hv c]
    unfold Pf at hPf
    have e : (digPoint p (s * k + (s - 1)) C v c : ℝ) = (a c : ℝ) * f + (low (C c) v (k + 1) : ℝ) := by
      unfold digPoint; rw [coord_eq, hsplit, hPf]; push_cast; ring
    have hl : (low (C c) v (k + 1) : ℝ) < f := by exact_mod_cast hlow
    rw [e]; constructor
    · have : (0 : ℝ) ≤ low (C c) v (k + 1) := by positivity
      linarith
    · linarith
  have hbound : ∀ c, (y c - (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 <
      (((μ : ℝ) + 1) / P) ^ 2 := by
    intro c
    obtain ⟨hc1, hc2⟩ := hcoord c
    have hQ1 : (Q c : ℝ) ≤ y c * P := Nat.floor_le (by have := (hy c).1; positivity)
    have hQ2 : y c * P < (Q c : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd := abs_le.1 (hdist c)
    have hd1 : ((a c : ℤ) : ℝ) - (Q c : ℤ) ≤ μ := by exact_mod_cast hd.2
    have hd2 : -(μ : ℝ) ≤ ((a c : ℤ) : ℝ) - (Q c : ℤ) := by exact_mod_cast hd.1
    push_cast at hd1 hd2
    have hx1 : (a c : ℝ) / P ≤ (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1)) := by
      rw [hN, div_le_div_iff₀ hPr (by positivity)]; nlinarith
    have hx2 : (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1)) < ((a c : ℝ) + 1) / P := by
      rw [hN, div_lt_div_iff₀ (by positivity) hPr]; nlinarith
    have hy1 : (Q c : ℝ) / P ≤ y c := by rw [div_le_iff₀ hPr]; linarith
    have hy2 : y c < ((Q c : ℝ) + 1) / P := by rw [lt_div_iff₀ hPr]; linarith
    have hA : ((a c : ℝ) + 1) / P - (Q c : ℝ) / P ≤ ((μ : ℝ) + 1) / P := by
      rw [← sub_div, div_le_div_iff_of_pos_right hPr]; linarith
    have hB : ((Q c : ℝ) + 1) / P - (a c : ℝ) / P ≤ ((μ : ℝ) + 1) / P := by
      rw [← sub_div, div_le_div_iff_of_pos_right hPr]; linarith
    exact sq_lt_sq' (by linarith) (by linarith)
  have hsum : ∑ c, (y c - (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 <
      ∑ _c : Fin s, (((μ : ℝ) + 1) / P) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩) fun c _ => hbound c
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrhs : Real.sqrt s * ((μ : ℝ) + 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) *
      ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) = Real.sqrt ((s : ℝ) * (((μ : ℝ) + 1) / P) ^ 2) := by
    rw [mul_assoc (Real.sqrt s * ((μ : ℝ) + 1)), hrp_eq s p k (by omega) hp0,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hPdef]
    push_cast; ring
  rw [hrhs]
  exact Real.sqrt_lt_sqrt (by positivity) hsum

theorem S1_mesh (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k (rhoS s p) C) (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, ∀ w w' : Fin (s * k + (s - 1)) → ZMod p, w ≠ w' →
      ((rhoS s p : ℝ) - 1) *
          Real.sqrt (∑ c, (y c - (digPoint p (s * k + (s - 1)) C v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2)
        ≤ Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) *
          Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
            ((digPoint p (s * k + (s - 1)) C w c : ℤ) - (digPoint p (s * k + (s - 1)) C w' c : ℤ)) : ℝ)
            / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  obtain ⟨hρ2, hρs, -, -⟩ := S1_const s p (by omega) hp hps
  obtain ⟨v, hv⟩ := S1_cover s p k hs hp hps C hC y hy
  refine ⟨v, fun w w' hww' => ?_⟩
  have hsep := S1_sep_real s p k (rhoS s p) hs hp hρ2 hρs C hC w w' hww'
  have hρ1 : (0 : ℝ) ≤ (rhoS s p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ rhoS s p := by exact_mod_cast hρ2
    linarith
  have hK : (0 : ℝ) ≤ Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) := by positivity
  calc ((rhoS s p : ℝ) - 1) * Real.sqrt _
      ≤ ((rhoS s p : ℝ) - 1) * (Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) *
          (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))) :=
        mul_le_mul_of_nonneg_left hv.le hρ1
    _ = Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) * (((rhoS s p : ℝ) - 1) *
          (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsep hK

/-! ## `μ` bounds -/

/-- Real facts: `ρ^s < p ≤ (ρ+1)^s`, `p ≤ μ ρ^(s-1) ≤ p + ρ^(s-1) - 1`. -/
lemma mu_real (s p ρ : ℕ) (hs : 1 ≤ s) (hρ : 1 ≤ ρ) :
    (p : ℝ) ≤ (muS s p ρ : ℝ) * (ρ : ℝ) ^ (s - 1) ∧
      (muS s p ρ : ℝ) * (ρ : ℝ) ^ (s - 1) ≤ p + (ρ : ℝ) ^ (s - 1) - 1 := by
  obtain ⟨h1, h2⟩ := muS_spec s p ρ hρ
  have hR : 1 ≤ ρ ^ (s - 1) := Nat.one_le_pow _ _ (by omega)
  constructor
  · exact_mod_cast h1
  · have : ((muS s p ρ * ρ ^ (s - 1) : ℕ) : ℝ) ≤ ((p + ρ ^ (s - 1) - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast [Nat.cast_sub (show 1 ≤ p + ρ ^ (s - 1) by omega)] at this
    exact this

/-- `(μ + 1) ≤ (ρ + 1)^s / ρ^(s-1) + 2`, as `(μ + 1) ρ^(s-1) < (ρ+1)^s + 2 ρ^(s-1)`. -/
lemma mu_upper (s p ρ : ℕ) (hs : 1 ≤ s) (hρ : 1 ≤ ρ) (hp : p ≤ (ρ + 1) ^ s) :
    ((muS s p ρ : ℝ) + 1) * (ρ : ℝ) ^ (s - 1) < ((ρ : ℝ) + 1) ^ s + 2 * (ρ : ℝ) ^ (s - 1) := by
  obtain ⟨-, h2⟩ := mu_real s p ρ hs hρ
  have hpr : (p : ℝ) ≤ ((ρ : ℝ) + 1) ^ s := by exact_mod_cast hp
  nlinarith

theorem S1_mu (s p : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p) :
    rhoS s p - 1 ≤ muS s p (rhoS s p) ∧
      (muS s p (rhoS s p) : ℝ) < (rhoS s p : ℝ) * (1 + 1 / (rhoS s p : ℝ)) ^ s + 1 ∧
      ((muS s p (rhoS s p) : ℝ) + 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) ≤ (3 / 2 : ℝ) ^ s + 1 ∧
      ((muS s p (rhoS s p) : ℝ) + 1) / ((rhoS s p : ℝ) - 1) ≤ 2 * (3 / 2 : ℝ) ^ s + 2 := by
  obtain ⟨hρ2, hρs, hlt, -⟩ := S1_const s p (by omega) hp hps
  set ρ := rhoS s p
  set μ := muS s p ρ
  have hr2 : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ2
  have hr0 : (0 : ℝ) < ρ := by linarith
  set R : ℝ := (ρ : ℝ) ^ (s - 1) with hR
  have hR0 : 0 < R := by positivity
  have hs1 : (ρ : ℝ) ^ s = ρ * R := by rw [hR, ← pow_succ']; congr 1; omega
  have hpR : (p : ℝ) < ((ρ : ℝ) + 1) ^ s := by exact_mod_cast hlt
  have hρsR : ((ρ : ℝ)) ^ s < p := by exact_mod_cast hρs
  obtain ⟨hm1, hm2⟩ := mu_real s p ρ (by omega) (by omega)
  -- `(1 + 1/ρ)^s ρ^s = (ρ+1)^s`
  have hpow : (1 + 1 / (ρ : ℝ)) ^ s * (ρ : ℝ) ^ s = ((ρ : ℝ) + 1) ^ s := by
    rw [← mul_pow]; congr 1; field_simp
  have h32 : (1 + 1 / (ρ : ℝ)) ^ s ≤ (3 / 2 : ℝ) ^ s := by
    apply pow_le_pow_left₀ (by positivity)
    have : 1 / (ρ : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hr0 (by norm_num)]; linarith
    linarith
  -- `μ < p / R + 1 < ρ (1 + 1/ρ)^s + 1`
  have hμlt : (μ : ℝ) * R < ((ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s) * R + R := by
    have : (ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s * R = ((ρ : ℝ) + 1) ^ s := by
      rw [← hpow, hs1]; ring
    rw [this]; linarith
  have hμ1 : (μ : ℝ) < (ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s + 1 := by
    have : (μ : ℝ) * R < ((ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s + 1) * R := by linarith
    exact lt_of_mul_lt_mul_right this hR0.le
  refine ⟨muS_ge s p ρ (by omega) (by omega) hρs, hμ1, ?_, ?_⟩
  · -- `p^(-1/s) ≤ 1/ρ`
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hroot : (ρ : ℝ) ≤ (p : ℝ) ^ (1 / (s : ℝ)) := by
      have h2 := Real.rpow_le_rpow (by positivity) hρsR.le (by positivity : (0 : ℝ) ≤ 1 / (s : ℝ))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((s : ℕ) : ℝ) * (1 / (s : ℝ)) = 1 by field_simp, Real.rpow_one] at h2
    have hpinv : (p : ℝ) ^ (-(1 / (s : ℝ))) ≤ 1 / (ρ : ℝ) := by
      rw [Real.rpow_neg hp0.le, ← one_div]
      exact one_div_le_one_div_of_le hr0 hroot
    have hμ0 : (0 : ℝ) ≤ (μ : ℝ) + 1 := by positivity
    calc ((μ : ℝ) + 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) ≤ ((μ : ℝ) + 1) * (1 / (ρ : ℝ)) :=
          mul_le_mul_of_nonneg_left hpinv hμ0
      _ ≤ (1 + 1 / (ρ : ℝ)) ^ s + 2 / (ρ : ℝ) := by
          have : ((μ : ℝ) + 1) < (ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s + 2 := by linarith
          rw [mul_one_div, div_le_iff₀ hr0]
          have e : ((1 + 1 / (ρ : ℝ)) ^ s + 2 / (ρ : ℝ)) * ρ = (ρ : ℝ) * (1 + 1 / (ρ : ℝ)) ^ s + 2 := by
            field_simp
          rw [e]; linarith
      _ ≤ (3 / 2 : ℝ) ^ s + 1 := by
          have : 2 / (ρ : ℝ) ≤ 1 := by rw [div_le_iff₀ hr0]; linarith
          linarith
  · have hρ1 : (0 : ℝ) < (ρ : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hρ1]
    have hA : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ s := by positivity
    have : (μ : ℝ) + 1 < (ρ : ℝ) * (3 / 2 : ℝ) ^ s + 2 := by
      have := mul_le_mul_of_nonneg_left h32 hr0.le
      linarith
    nlinarith

/-! ## Limits -/

theorem S1_const_tendsto (s : ℕ) (hs : 2 ≤ s) :
    Tendsto (fun p : ℕ => ((rhoS s p : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ)))) atTop (𝓝 1) := by
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) - 2 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop
      (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have hlow := hg.comp (rhoS_tendsto s (by omega))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with p hp
    obtain ⟨h1, h2⟩ := rhoS_bounds s p (by omega) hp
    simp only [Function.comp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hr0 : (0 : ℝ) < (rhoS s p : ℝ) + 1 := by positivity
    have hroot : (p : ℝ) ^ (1 / (s : ℝ)) ≤ (rhoS s p : ℝ) + 1 := by
      have h1' : (p : ℝ) ≤ ((rhoS s p : ℝ) + 1) ^ s := by exact_mod_cast h2
      have h3 := Real.rpow_le_rpow hp0.le h1' (by positivity : (0 : ℝ) ≤ 1 / (s : ℝ))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((s : ℕ) : ℝ) * (1 / (s : ℝ)) = 1 by field_simp, Real.rpow_one] at h3
    have hpos : (0 : ℝ) < (p : ℝ) ^ (1 / (s : ℝ)) := by positivity
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    rcases Nat.lt_or_ge (rhoS s p) 1 with h0 | h0
    · have : rhoS s p = 0 := by omega
      rw [this]; push_cast
      have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / (s : ℝ)) := Real.one_le_rpow (by exact_mod_cast hp) (by positivity)
      have h2 : (-1 : ℝ) ≤ (0 - 1) / (p : ℝ) ^ (1 / (s : ℝ)) := by rw [le_div_iff₀ hpos]; linarith
      have h3 : (1 : ℝ) - 2 / (0 + 1) = -1 := by norm_num
      linarith
    · have hr1 : (0 : ℝ) ≤ (rhoS s p : ℝ) - 1 := by
        have : (1 : ℝ) ≤ rhoS s p := by exact_mod_cast h0
        linarith
      have e : (1 : ℝ) - 2 / ((rhoS s p : ℝ) + 1) = ((rhoS s p : ℝ) - 1) / ((rhoS s p : ℝ) + 1) := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left hr1 hpos hroot
  · filter_upwards [eventually_ge_atTop 1] with p hp
    obtain ⟨h1, -⟩ := rhoS_bounds s p (by omega) hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hroot : (rhoS s p : ℝ) < (p : ℝ) ^ (1 / (s : ℝ)) := by
      have h1' : ((rhoS s p : ℝ)) ^ s < p := by exact_mod_cast h1
      have h3 := Real.rpow_lt_rpow (by positivity) h1' (by positivity : (0 : ℝ) < 1 / (s : ℝ))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((s : ℕ) : ℝ) * (1 / (s : ℝ)) = 1 by field_simp, Real.rpow_one] at h3
    have hpos : (0 : ℝ) < (p : ℝ) ^ (1 / (s : ℝ)) := by positivity
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv, div_le_one hpos]
    linarith

theorem S1_mesh_tendsto (s : ℕ) (hs : 2 ≤ s) :
    Tendsto (fun p : ℕ => Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) / ((rhoS s p : ℝ) - 1))
      atTop (𝓝 (Real.sqrt s)) := by
  -- `φ(t) = ((1 + t)^s + 2 t) / (1 - t)`, continuous at `0` with `φ 0 = 1`
  set φ : ℝ → ℝ := fun t => ((1 + t) ^ s + 2 * t) / (1 - t) with hφ
  have hφc : ContinuousAt φ 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
  have hφ0 : φ 0 = 1 := by simp [hφ]
  have h1n : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hup : Tendsto (fun p : ℕ => Real.sqrt s * φ (1 / (rhoS s p : ℝ))) atTop (𝓝 (Real.sqrt s)) := by
    have := (hφc.tendsto.comp (h1n.comp (rhoS_tendsto s (by omega))))
    rw [hφ0] at this
    simpa using (tendsto_const_nhds (x := Real.sqrt s)).mul this
  have hev : ∀ᶠ p : ℕ in atTop, 2 ≤ rhoS s p := (rhoS_tendsto s (by omega)).eventually_ge_atTop 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hev, eventually_ge_atTop 1] with p hρ hp
    obtain ⟨h1, -⟩ := rhoS_bounds s p (by omega) hp
    have hμ := muS_ge s p (rhoS s p) (by omega) (by omega) h1
    have hr : (1 : ℝ) < rhoS s p := by exact_mod_cast (show 1 < rhoS s p by omega)
    have hμr : (rhoS s p : ℝ) - 1 ≤ muS s p (rhoS s p) := by
      have : ((rhoS s p - 1 : ℕ) : ℝ) ≤ muS s p (rhoS s p) := by exact_mod_cast hμ
      push_cast [Nat.cast_sub (show 1 ≤ rhoS s p by omega)] at this
      exact this
    rw [mul_div_assoc]
    have hs0 : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg _
    have : (1 : ℝ) ≤ ((muS s p (rhoS s p) : ℝ) + 1) / ((rhoS s p : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  · filter_upwards [hev, eventually_ge_atTop 1] with p hρ hp
    obtain ⟨-, h2⟩ := rhoS_bounds s p (by omega) hp
    have hmu := mu_upper s p (rhoS s p) (by omega) (by omega) h2
    set r : ℝ := ((rhoS s p : ℕ) : ℝ) with hr
    have hr2 : (2 : ℝ) ≤ r := by rw [hr]; exact_mod_cast hρ
    have hR0 : (0 : ℝ) < r ^ (s - 1) := by positivity
    have hs1 : r ^ s = r * r ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    -- `φ(1/r) = ((r+1)^s / r^(s-1) + 2) / (r - 1)`
    have e : φ (1 / r) = (((r + 1) ^ s + 2 * r ^ (s - 1)) / r ^ (s - 1)) / (r - 1) := by
      simp only [hφ]
      have hr0 : r ≠ 0 := by linarith
      have hr1 : r - 1 ≠ 0 := by linarith
      have e1 : (1 + 1 / r) ^ s = (r + 1) ^ s / r ^ s := by rw [← div_pow]; congr 1; field_simp
      rw [e1, hs1]
      field_simp
    rw [e, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [le_div_iff₀ hR0]; linarith

end Z3NetS1.Proofs
