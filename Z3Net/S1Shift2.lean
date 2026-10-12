/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.S1Shift

@[expose] public section

/-!
# V14 stage S10′: `thm:S1`(2), (3) under digital shifts (`prop:shift`)

The fine position of coordinate `c` of the shifted point is the digital shift of the unshifted fine
position by the first `k + 1` digits of `τ_c` (`fineS_eq`, `Z3NetF.Proofs.dshiftCoord_prefix`); only its
last digit enters the lattice condition, and there the shift adds the constant `τ_c(k)`
(`fineS_cast`). So the occupied fine cells form the COSET `g + Λ` (`g` the fine position of the index
`0`), each cell exactly once (`S1_cells_shift_core`; the bijection is the inverse digital shift,
`dshiftCoord_neg`). The covering argument of `thm:S1`(3) needs only that the occupied cells are a
translate of `Λ`: `cover_int_coset` is `cover_int` with the target residue moved by `g`, and
`S1_cover_shift_core`, `S1_mesh_shift_core` follow as before.
-/

namespace Z3NetS1.Proofs

open Finset Matrix Filter Topology Z3NetKN.Geom

/-! ## Fine positions of a shifted net -/

section cells

variable {s p k ρ : ℕ} {C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p)}

/-- The fine position of a shifted point is the shift of the unshifted fine position by the first
`k + 1` digits of `τ_c`. -/
lemma fineS_eq [NeZero p] (hs : 2 ≤ s) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p)
    (v : Fin (s * k + (s - 1)) → ZMod p) (c : Fin s) :
    Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c / p ^ (s * k + (s - 1) - (k + 1)) =
      Z3NetF.dshiftCoord p (k + 1) (fun j => τ c ⟨j, lt_of_lt_of_le j.isLt (kle hs)⟩)
        (finePos s p k C v c) := by
  rw [Z3NetF.Proofs.digPointShift_eq_dshiftPt]
  unfold Z3NetF.dshiftPt
  rw [Z3NetF.Proofs.dshiftCoord_prefix _ _ _ _ (kle hs)]
  rfl

lemma dsh_cast [NeZero p] (t : Fin (k + 1) → ZMod p) (x : ℕ) :
    ((Z3NetF.dshiftCoord p (k + 1) t x : ℕ) : ZMod p) = ((x : ℕ) : ZMod p) + t ⟨k, by omega⟩ := by
  have h := Z3NetF.Proofs.dshiftCoord_digit (k + 1) t x ⟨k, by omega⟩
  simp only [show k + 1 - 1 - k = 0 by omega, pow_zero, Nat.div_one] at h
  rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val, ZMod.natCast_mod]

lemma finePos_lt [NeZero p] (hs : 2 ≤ s) (v : Fin (s * k + (s - 1)) → ZMod p) (c : Fin s) :
    finePos s p k C v c < p ^ (k + 1) := by
  rw [finePos_eq hs]; exact Pf_lt _ _

lemma mem_S1lat_cast (s p ρ : ℕ) (a : Fin s → ℤ) :
    a ∈ S1lat s p ρ ↔ ∑ c, ((chk s ρ c : ℤ) : ZMod p) * ((a c : ℤ) : ZMod p) = 0 := by
  rw [mem_S1lat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast; rfl

end cells

/-- **`prop:shift`, `thm:S1`(2) under digital shifts**: the occupied fine cells of every digitally
shifted net with the S1 skeleton row form a coset `g + Λ` of the lattice `Λ`, each cell of the coset
in `[0, p^(k+1))^s` occupied by exactly one point. -/
theorem S1_cells_shift_core (s p k ρ : ℕ) (hs : 2 ≤ s) (hp : p.Prime)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    ∃ g : Fin s → ℤ,
      (∀ v, (fun c => ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c /
          p ^ (s * k + (s - 1) - (k + 1)) : ℕ) : ℤ) - g c) ∈ S1lat s p ρ) ∧
      ∀ a : Fin s → ℕ, (∀ c, a c < p ^ (k + 1)) → (fun c => (a c : ℤ) - g c) ∈ S1lat s p ρ →
        ∃! v, ∀ c, Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c /
          p ^ (s * k + (s - 1) - (k + 1)) = a c := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hkm := kle (k := k) hs
  set tr : Fin s → Fin (k + 1) → ZMod p := fun c j => τ c ⟨j, lt_of_lt_of_le j.isLt hkm⟩ with htr
  set fS : (Fin (s * k + (s - 1)) → ZMod p) → Fin s → ℕ := fun v c =>
    Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c / p ^ (s * k + (s - 1) - (k + 1)) with hfS
  have hfS_eq : ∀ v c, fS v c = Z3NetF.dshiftCoord p (k + 1) (tr c) (finePos s p k C v c) :=
    fun v c => fineS_eq hs τ v c
  set T0 : ZMod p := ∑ c, ((chk s ρ c : ℤ) : ZMod p) * tr c ⟨k, by omega⟩ with hT0
  have hsum : ∀ v, ∑ c, ((chk s ρ c : ℤ) : ZMod p) * (((fS v c : ℕ) : ℤ) : ZMod p) = T0 := by
    intro v
    have h0 := (mem_S1lat_cast s p ρ _).1 (finePos_mem hs hp hC v)
    simp only [Int.cast_natCast] at h0 ⊢
    rw [hT0, ← zero_add (∑ c, ((chk s ρ c : ℤ) : ZMod p) * tr c ⟨k, by omega⟩), ← h0, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [hfS_eq, dsh_cast]; ring
  refine ⟨fun c => (fS 0 c : ℤ), fun v => ?_, fun a ha hmem => ?_⟩
  · rw [mem_S1lat_cast]
    calc ∑ c, ((chk s ρ c : ℤ) : ZMod p) * ((((fS v c : ℕ) : ℤ) - (fS 0 c : ℤ) : ℤ) : ZMod p)
        = ∑ c, ((chk s ρ c : ℤ) : ZMod p) * (((fS v c : ℕ) : ℤ) : ZMod p) -
          ∑ c, ((chk s ρ c : ℤ) : ZMod p) * (((fS 0 c : ℕ) : ℤ) : ZMod p) := by
          rw [← sum_sub_distrib]; refine sum_congr rfl fun c _ => ?_; push_cast; ring
      _ = 0 := by rw [hsum, hsum, sub_self]
  · -- the unshifted cell
    set a' : Fin s → ℕ := fun c => Z3NetF.dshiftCoord p (k + 1) (-(tr c)) (a c) with ha'
    have ha'lt : ∀ c, a' c < p ^ (k + 1) := fun c => Z3NetF.Proofs.dshiftCoord_lt _ _ _
    have hmem' : (fun c => (a' c : ℤ)) ∈ S1lat s p ρ := by
      have h1 := (mem_S1lat_cast s p ρ _).1 hmem
      push_cast at h1
      simp only [mul_sub, sum_sub_distrib] at h1
      have e2 := hsum 0
      push_cast at e2
      rw [e2, sub_eq_zero] at h1
      rw [mem_S1lat_cast]
      push_cast
      have : ∀ c, ((a' c : ℕ) : ZMod p) = ((a c : ℕ) : ZMod p) - tr c ⟨k, by omega⟩ := by
        intro c
        rw [ha']; simp only
        rw [dsh_cast, Pi.neg_apply, sub_eq_add_neg]
      simp only [this, mul_sub, sum_sub_distrib]
      rw [h1, hT0, sub_self]
    obtain ⟨v, hv, huniq⟩ := (S1_cells s p k ρ hs hp C hC).2 a' ha'lt hmem'
    have hback : ∀ c, Z3NetF.dshiftCoord p (k + 1) (tr c) (a' c) = a c := by
      intro c
      have := Z3NetF.Proofs.dshiftCoord_neg (k + 1) (-(tr c)) (a c) (ha c)
      rwa [neg_neg] at this
    refine ⟨v, fun c => ?_, fun w hw => huniq w fun c => ?_⟩
    · show fS v c = a c
      rw [hfS_eq, hv c, hback]
    · have hw' : fS w c = a c := hw c
      rw [hfS_eq] at hw'
      rw [ha']; simp only
      rw [← hw', Z3NetF.Proofs.dshiftCoord_neg _ _ _ (finePos_lt hs w c)]

/-! ## Covering -/

theorem cover_int_coset (s p k ρ μ : ℕ) (hs : 2 ≤ s) (hρ : 1 ≤ ρ) (hp : 0 < p) (hμρ : ρ - 1 ≤ μ)
    (hμp : p ≤ μ * ρ ^ (s - 1)) (hP : 2 * μ + 1 ≤ p ^ (k + 1)) (Q : Fin s → ℕ)
    (hQ : ∀ c, Q c < p ^ (k + 1)) (g : Fin s → ℤ) :
    ∃ a : Fin s → ℕ, (∀ c, a c < p ^ (k + 1)) ∧ (fun c => (a c : ℤ) - g c) ∈ S1lat s p ρ ∧
      ∀ c, |(a c : ℤ) - Q c| ≤ μ := by
  set P : ℤ := ((p ^ (k + 1) : ℕ) : ℤ) with hPdef
  set n := s - 1 with hn
  have hn1 : 1 ≤ n := by omega
  set Qn : ℕ → ℤ := fun i => if h : i < s then (Q ⟨i, h⟩ : ℤ) else 0 with hQn
  set gn : ℕ → ℤ := fun i => if h : i < s then g ⟨i, h⟩ else 0 with hgn
  have hρz : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  set R : ℤ := (ρ : ℤ) ^ n with hR
  have hR1 : 1 ≤ R := one_le_pow₀ hρz
  -- the target residue
  set T : ℤ := (Qn (s - 1) - gn (s - 1)) - ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * (Qn d - gn d)
    with hT
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
  · have key : ∀ x : Fin s → ℤ, (∀ c : Fin s, x c = Qn c - D c - gn c) → x ∈ S1lat s p ρ := by
      intro x hx
      rw [mem_S1lat, sum_chk s ρ (by omega)]
      have hcast : ∀ d, d < s → (if h : d < s then x ⟨d, h⟩ else 0) = Qn d - D d - gn d := by
        intro d hd
        rw [dif_pos hd, hx]
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
      have e2 : ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * (Qn d - D d - gn d) -
          (Qn (s - 1) - D (s - 1) - gn (s - 1)) = T' - T := by
        rw [← hDsum, hT]
        simp only [mul_sub, sum_sub_distrib]
        ring
      rw [e2]; exact hdvd
    refine key _ fun c => ?_
    have h1 := hrange c c.isLt
    simp only
    rw [Int.toNat_of_nonneg h1.1]
    have hgc : gn c = g c := by simp only [hgn, dif_pos c.isLt]
    rw [hgc]
  · intro c
    have h1 := hrange c c.isLt
    rw [Int.toNat_of_nonneg h1.1]
    have hQc : Qn c = (Q c : ℤ) := by simp only [hQn, dif_pos c.isLt]
    rw [hQc, show (Q c : ℤ) - D c - Q c = -D c by ring, abs_neg]
    exact hDabs c c.isLt


theorem S1_cover_shift_core (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k (rhoS s p) C)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, Real.sqrt (∑ c, (y c - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2)
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
  obtain ⟨g, -, hcells⟩ := S1_cells_shift_core s p k ρ (by omega) hp C hC τ
  obtain ⟨a, ha, hmem, hdist⟩ := cover_int_coset s p k ρ μ (by omega) (by omega) hp0
    (muS_ge s p ρ (by omega) (by omega) hρs) (muS_spec s p ρ (by omega)).1
    (le_trans (muS_small s p ρ hs hρ2 (by omega)) hpP) Q hQ g
  obtain ⟨v, hv, -⟩ := hcells a ha hmem
  refine ⟨v, ?_⟩
  -- each coordinate is within `(μ + 1)/P`
  have hkm : k + 1 ≤ (s * k + (s - 1)) := kle (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f = p ^ ((s * k + (s - 1)) - (k + 1)) := ⟨_, rfl⟩
  have hN : (p : ℝ) ^ (s * k + (s - 1)) = (P : ℝ) * (f : ℝ) := by
    rw [hPdef, hf]; push_cast; rw [← pow_add]; congr 1; omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
  have hfr : (0 : ℝ) < f := by rw [hf]; push_cast; positivity
  have hcoord : ∀ c, (a c : ℝ) * f ≤ (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) ∧
      (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) < ((a c : ℝ) + 1) * f := by
    intro c
    have hvc := hv c
    rw [← hf] at hvc
    have hf0 : 0 < f := by rw [hf]; positivity
    have hlo : a c * f ≤ Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c := by
      rw [← hvc]; exact Nat.div_mul_le_self _ _
    have hhi : Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c < (a c + 1) * f := by
      have h1 := Nat.div_add_mod (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c) f
      have h2 := Nat.mod_lt (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c) hf0
      rw [hvc] at h1
      nlinarith
    constructor
    · exact_mod_cast hlo
    · have : ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℕ) : ℝ) < (((a c + 1) * f : ℕ) : ℝ) := by
        exact_mod_cast hhi
      push_cast at this; exact this
  have hbound : ∀ c, (y c - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 <
      (((μ : ℝ) + 1) / P) ^ 2 := by
    intro c
    obtain ⟨hc1, hc2⟩ := hcoord c
    have hQ1 : (Q c : ℝ) ≤ y c * P := Nat.floor_le (by have := (hy c).1; positivity)
    have hQ2 : y c * P < (Q c : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd := abs_le.1 (hdist c)
    have hd1 : ((a c : ℤ) : ℝ) - (Q c : ℤ) ≤ μ := by exact_mod_cast hd.2
    have hd2 : -(μ : ℝ) ≤ ((a c : ℤ) : ℝ) - (Q c : ℤ) := by exact_mod_cast hd.1
    push_cast at hd1 hd2
    have hx1 : (a c : ℝ) / P ≤ (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1)) := by
      rw [hN, div_le_div_iff₀ hPr (by positivity)]; nlinarith
    have hx2 : (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1)) < ((a c : ℝ) + 1) / P := by
      rw [hN, div_lt_div_iff₀ (by positivity) hPr]; nlinarith
    have hy1 : (Q c : ℝ) / P ≤ y c := by rw [div_le_iff₀ hPr]; linarith
    have hy2 : y c < ((Q c : ℝ) + 1) / P := by rw [lt_div_iff₀ hPr]; linarith
    have hA : ((a c : ℝ) + 1) / P - (Q c : ℝ) / P ≤ ((μ : ℝ) + 1) / P := by
      rw [← sub_div, div_le_div_iff_of_pos_right hPr]; linarith
    have hB : ((Q c : ℝ) + 1) / P - (a c : ℝ) / P ≤ ((μ : ℝ) + 1) / P := by
      rw [← sub_div, div_le_div_iff_of_pos_right hPr]; linarith
    exact sq_lt_sq' (by linarith) (by linarith)
  have hsum : ∑ c, (y c - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 <
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

theorem S1_mesh_shift_core (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k (rhoS s p) C)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, ∀ w w' : Fin (s * k + (s - 1)) → ZMod p, w ≠ w' →
      ((rhoS s p : ℝ) - 1) *
          Real.sqrt (∑ c, (y c - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) / (p : ℝ) ^ (s * k + (s - 1))) ^ 2)
        ≤ Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) *
          Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
            ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w' c : ℤ)) : ℝ)
            / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  obtain ⟨hρ2, hρs, -, -⟩ := S1_const s p (by omega) hp hps
  obtain ⟨v, hv⟩ := S1_cover_shift_core s p k hs hp hps C hC τ y hy
  refine ⟨v, fun w w' hww' => ?_⟩
  have hsep := S1_sep_shift_real_core s p k (rhoS s p) hs hp hρ2 hρs C hC τ w w' hww'
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

end Z3NetS1.Proofs
