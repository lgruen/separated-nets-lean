/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Link
public import Z3Net.B23CertNetA
public import Z3Net.B23CertNetB1
public import Z3Net.B23CertNetB2
public import Z3Net.B23CertC1A1
public import Z3Net.B23CertC1A2
public import Z3Net.B23CertC1B1
public import Z3Net.B23CertC1B2
public import Z3Net.B23CertWit
public import Z3Net.B23CertC2_20
public import Z3Net.B23CertC2_21
public import Z3Net.B23CertC2_22
public import Z3Net.B23CertC2_30
public import Z3Net.B23CertC2_31
public import Z3Net.B23CertC2_32

@[expose] public section

/-!
# V14 stage S14′: assembly of `thm:base23`

* `b23_net`: every net of the theorem (`IsB23Gen`) is a `(0,m,3)`-net, with any digital shift.
* `b23_exists`: for every `m ≥ 1` there is one (witness, chain level, or a continuation built with `lem:lift`(B)).
* `b23_sep` (`thm:base23`(3)): for every digital shift, `δ N^{1/3} ≥ b23C b (m mod 3)`.
* the numeric checks `numChk`, `witNum` (kernel `decide`), and the conversions to real numbers.
-/

namespace Z3NetB23

/-- The numeric conditions at the certificate level (`g_L` and the proviso) and the chain levels, for the constant
`b23Cnum b r / 10⁴`. -/
def numChk (b r : ℕ) : Bool :=
  decide (b23Cnum b r ^ 6 * b ^ (4 * b23Lev b r (b23NL b r)) ≤
    (b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2)) ^ 6 * b23V b r ^ 3 * 10000 ^ 6) &&
  decide (b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) ≤ b ^ b23Lev b r (b23NL b r)) &&
  decide (b23Cnum b r ^ 3 * b ^ (2 * b23Lev b r (b23NL b r)) ≤
    (b ^ b23Lev b r (b23NL b r) - b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2)) ^ 3 * 10000 ^ 3) &&
  (List.range (b23NL b r)).all (fun k => decide (b23Cnum b r ^ 6 * b ^ (4 * b23Lev b r k) ≤
    ((b23Mid b r).getD k (0, 0, [], [], [])).2.1 ^ 3 * 10000 ^ 6))

/-- The numeric condition of a witness. -/
def witNum (b m : ℕ) : Bool := decide (b23Cnum b (m % 3) ^ 6 * b ^ (4 * m) ≤ b23WitU b m ^ 3 * 10000 ^ 6)

end Z3NetB23

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

/-! ## Real conversions -/

lemma real_from_U (b m U T p : ℕ) (hb : 1 < b) (h : p ^ 6 * b ^ (4 * m) ≤ U ^ 3 * 10000 ^ 6) (hT : U ≤ T) :
    ((p : ℝ) / 10000) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt T / (b : ℝ) ^ m := by
  set B : ℝ := (b : ℝ) with hB
  have hB0 : 0 < B := by rw [hB]; exact_mod_cast (by omega : 0 < b)
  have hBm : 0 < B ^ m := pow_pos hB0 m
  set u : ℝ := (B ^ m) ^ (-(1 / 3 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hBm _
  have hu3 : u ^ 3 = (B ^ m)⁻¹ := by
    rw [hu, ← Real.rpow_mul_natCast hBm.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hl : 0 ≤ (p : ℝ) / 10000 * u := by positivity
  have hr : 0 ≤ Real.sqrt T / B ^ m := by positivity
  rw [← pow_le_pow_iff_left₀ hl hr (by norm_num : (6 : ℕ) ≠ 0)]
  have e1 : ((p : ℝ) / 10000 * u) ^ 6 = (p : ℝ) ^ 6 / 10000 ^ 6 * (B ^ m)⁻¹ ^ 2 := by
    rw [← hu3]; ring
  have e2 : (Real.sqrt T / B ^ m) ^ 6 = (T : ℝ) ^ 3 / (B ^ m) ^ 6 := by
    rw [div_pow, show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [e1, e2]
  have hc : ((p ^ 6 * b ^ (4 * m) : ℕ) : ℝ) ≤ ((T ^ 3 * 10000 ^ 6 : ℕ) : ℝ) := by
    exact_mod_cast h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hT 3))
  push_cast at hc
  rw [← hB] at hc
  have hB4 : B ^ (4 * m) = (B ^ m) ^ 4 := by ring
  rw [hB4] at hc
  have hX : 0 < B ^ m := hBm
  rw [show (p : ℝ) ^ 6 / 10000 ^ 6 * ((B ^ m)⁻¹) ^ 2 = (p : ℝ) ^ 6 * (B ^ m) ^ 4 / (10000 ^ 6 * (B ^ m) ^ 6) by
    field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ 10000 ^ 6 * (B ^ m) ^ 6 by positivity)
  nlinarith [pow_pos hX 6]

lemma gL_mono (b L : ℕ) {v V : ℕ} (h : v ≤ V) : gL b L v ≤ gL b L V := by
  unfold gL
  have : Real.sqrt v ≤ Real.sqrt V := Real.sqrt_le_sqrt (by exact_mod_cast h)
  have h1 : (0 : ℝ) ≤ (b : ℝ) ^ (L - L / 2) := by positivity
  have h2 : (0 : ℝ) ≤ ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h1) h2

lemma real_from_cert (b L v p : ℕ) (hb : 1 < b)
    (h1 : p ^ 6 * b ^ (4 * L) ≤ (b ^ (L - L / 2)) ^ 6 * v ^ 3 * 10000 ^ 6) (hW : b ^ (L - L / 2) ≤ b ^ L)
    (h2 : p ^ 3 * b ^ (2 * L) ≤ (b ^ L - b ^ (L - L / 2)) ^ 3 * 10000 ^ 3) :
    (p : ℝ) / 10000 ≤ min (gL b L v) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) := by
  set B : ℝ := (b : ℝ) with hB
  have hB0 : 0 < B := by rw [hB]; exact_mod_cast (by omega : 0 < b)
  have hBL : 0 < B ^ L := pow_pos hB0 L
  set u : ℝ := (B ^ L) ^ (-(1 / 3 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hBL _
  have hu3 : u ^ 3 = (B ^ L)⁻¹ := by
    rw [hu, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h13 : (B ^ L) ^ (1 / 3 : ℝ) = u⁻¹ := by rw [hu, Real.rpow_neg hBL.le, inv_inv]
  have h23 : (B ^ L) ^ (-(2 / 3 : ℝ)) = u ^ 2 := by
    rw [hu, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 3) by norm_num]
  set W : ℝ := B ^ (L - L / 2) with hWdef
  have hW0 : 0 < W := pow_pos hB0 _
  have hgL : gL b L v = W * Real.sqrt v * u ^ 2 := by unfold gL; rw [← hB, h23]
  rw [hgL, h13, h23]
  have hp0 : (0 : ℝ) ≤ (p : ℝ) / 10000 := by positivity
  apply le_min
  · -- `c ≤ W √v u²`
    have hr : 0 ≤ W * Real.sqrt v * u ^ 2 := by positivity
    rw [← pow_le_pow_iff_left₀ hp0 hr (by norm_num : (6 : ℕ) ≠ 0)]
    have e : (W * Real.sqrt v * u ^ 2) ^ 6 = W ^ 6 * (v : ℝ) ^ 3 * ((B ^ L)⁻¹) ^ 4 := by
      rw [← hu3, show (6 : ℕ) = 2 * 3 by rfl]
      have : Real.sqrt v ^ 2 = v := Real.sq_sqrt (by positivity)
      calc (W * Real.sqrt v * u ^ 2) ^ (2 * 3) = W ^ 6 * (Real.sqrt v ^ 2) ^ 3 * u ^ 12 := by ring
        _ = _ := by rw [this]; ring
    rw [e]
    have hc : ((p ^ 6 * b ^ (4 * L) : ℕ) : ℝ) ≤ (((b ^ (L - L / 2)) ^ 6 * v ^ 3 * 10000 ^ 6 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at hc
    rw [← hB, ← hWdef, show B ^ (4 * L) = (B ^ L) ^ 4 by ring] at hc
    rw [show ((p : ℝ) / 10000) ^ 6 = (p : ℝ) ^ 6 / 10000 ^ 6 by ring,
      show W ^ 6 * (v : ℝ) ^ 3 * ((B ^ L)⁻¹) ^ 4 = W ^ 6 * (v : ℝ) ^ 3 / (B ^ L) ^ 4 by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hBL 4]
  · -- `c ≤ u⁻¹ − W u²`
    have hWL : W ≤ B ^ L := by rw [hWdef, hB]; exact_mod_cast hW
    have e : u⁻¹ - W * u ^ 2 = (1 - W * (B ^ L)⁻¹) / u := by
      rw [← hu3]; field_simp
    rw [e, le_div_iff₀ hu0]
    have hr : 0 ≤ 1 - W * (B ^ L)⁻¹ := by
      rw [sub_nonneg, mul_inv_le_iff₀ hBL]; linarith
    have hl : 0 ≤ (p : ℝ) / 10000 * u := by positivity
    rw [← pow_le_pow_iff_left₀ hl hr (by norm_num : (3 : ℕ) ≠ 0), mul_pow, hu3]
    have hc : ((p ^ 3 * b ^ (2 * L) : ℕ) : ℝ) ≤ (((b ^ L - b ^ (L - L / 2)) ^ 3 * 10000 ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast [Nat.cast_sub hW] at hc
    rw [← hB, ← hWdef, show B ^ (2 * L) = (B ^ L) ^ 2 by ring] at hc
    have e2 : 1 - W * (B ^ L)⁻¹ = (B ^ L - W) / B ^ L := by field_simp
    rw [e2, show ((p : ℝ) / 10000) ^ 3 * (B ^ L)⁻¹ = (p : ℝ) ^ 3 * (B ^ L) ^ 2 / (10000 ^ 3 * (B ^ L) ^ 3) by
      field_simp, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ (B ^ L) ^ 3 by positivity)
    nlinarith [pow_pos hBL 3]

/-! ## The family -/

section family

variable {b : ℕ} [Fact b.Prime]

lemma seed_facts (hb : b = 2 ∨ b = 3) (r : ℕ) (hr : r < 3) :
    b23SeedM b r % 3 = r ∧ 1 ≤ b23SeedM b r ∧ b23SeedM b r + 3 * b23NL b r = b23L b r ∧
      2 * (b23L b r / 2) = b23L b r ∧ b23SeedM b r ≤ 11 := by
  rcases hb with rfl | rfl <;> interval_cases r <;> decide

/-- The certificates of one base. -/
def B23Certs (b : ℕ) : Prop :=
  (∀ r, r < 3 → netChk b r = true ∧ c1Chk b r = true ∧ numChk b r = true ∧ ∀ k, k < b23NL b r → c2Chk b r k = true) ∧
  ∀ m, 1 ≤ m → m < b23SeedM b (m % 3) → witChk b m (b23Wit b m) (b23WitU b m) = true ∧ witNum b m = true

/-- **The continuations are deep-shift chains from the certificate level** (`D_ℓ = ⌊ℓ/2⌋`). -/
theorem chain_from_L (hb : b = 2 ∨ b = 3) {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    (h : IsB23Gen b m C) : ∀ r, r < 3 → m % 3 = r → b23L b r ≤ m →
      ∃ σ, LiftChain b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) 0 (fun ℓ => ℓ / 2) m C σ := by
  induction h with
  | wit m h1 h2 =>
    intro r hr hmr hL
    obtain ⟨-, -, h3, -, -⟩ := seed_facts hb r hr
    subst hmr
    omega
  | chain r' k hr' hk =>
    intro r hr hmr hL
    obtain ⟨h1, -, h3, -, -⟩ := seed_facts hb r' hr'
    have hrr : r' = r := by unfold b23Lev at hmr; omega
    subst hrr
    obtain rfl : k = b23NL b r' := by unfold b23Lev at hL; omega
    exact ⟨0, LiftChain.refl⟩
  | @cont ℓ C sA sB hC hLℓ hadm hA hB ih =>
    intro r hr hmr hL
    have hℓ : ℓ % 3 = r := by omega
    rw [hℓ] at hLℓ
    obtain ⟨σ, hσ⟩ := ih r hr hℓ hLℓ
    exact ⟨liftShift σ, LiftChain.step sA sB hσ hA hB⟩

/-- **`thm:base23`, the nets**: every net of the theorem is a `(0,m,3)`-net over `F_b`, with any digital shift. -/
theorem b23_net (hb : b = 2 ∨ b = 3) (hc : B23Certs b) {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    (h : IsB23Gen b m C) (σ : Fin 3 → Fin m → ZMod b) : Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m C σ) := by
  induction h with
  | wit m h1 h2 => exact (wit_ok (hc.2 m h1 h2).1).1 σ
  | chain r k hr hk => exact (chain_ok (hc.1 r hr).1 k hk).2 σ
  | @cont ℓ C sA sB hC hLℓ hadm hA hB ih =>
    have := lift_net C 0 sA sB (ih 0) hadm
    rw [net_shift_iff] at this ⊢
    exact this

lemma numChk_spec {r : ℕ} (h : numChk b r = true) :
    b23Cnum b r ^ 6 * b ^ (4 * b23Lev b r (b23NL b r)) ≤
      (b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2)) ^ 6 * b23V b r ^ 3 * 10000 ^ 6 ∧
    b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) ≤ b ^ b23Lev b r (b23NL b r) ∧
    b23Cnum b r ^ 3 * b ^ (2 * b23Lev b r (b23NL b r)) ≤
      (b ^ b23Lev b r (b23NL b r) - b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2)) ^ 3 * 10000 ^ 3 ∧
    ∀ k, k < b23NL b r → b23Cnum b r ^ 6 * b ^ (4 * b23Lev b r k) ≤
      ((b23Mid b r).getD k (0, 0, [], [], [])).2.1 ^ 3 * 10000 ^ 6 := by
  simp only [numChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **`thm:base23`(3) below the certificate level** (witnesses and chain levels). -/
theorem b23_sep_low (hb : b = 2 ∨ b = 3) (hc : B23Certs b) {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    (h : IsB23Gen b m C) (hlow : m < b23L b (m % 3)) (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b)
    (hvw : v ≠ w) :
    b23C b (m % 3) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  have hb1 : 1 < b := (Fact.out : b.Prime).one_lt
  have e := sqrt_torus (b ^ m) (pow_pos (by omega) m) (Z3NetF.digPointShift b m C τ v) (Z3NetF.digPointShift b m C τ w)
  push_cast at e
  rw [e]
  induction h with
  | wit m h1 h2 =>
    obtain ⟨hw, hn⟩ := hc.2 m h1 h2
    simp only [witNum, decide_eq_true_eq] at hn
    exact real_from_U b m _ _ _ hb1 hn ((wit_ok hw).2 τ v w hvw)
  | chain r k hr hk =>
    obtain ⟨h1, -, h3, -, -⟩ := seed_facts hb r hr
    have hmr : b23Lev b r k % 3 = r := by unfold b23Lev; omega
    rw [hmr] at hlow ⊢
    have hk' : k < b23NL b r := by unfold b23Lev at hlow; omega
    obtain ⟨hn, -, hnum, hc2⟩ := hc.1 r hr
    exact real_from_U b _ _ _ _ hb1 ((numChk_spec hnum).2.2.2 k hk') (c2_dist hn hk' (hc2 k hk') τ v w hvw)
  | @cont ℓ C sA sB hC hLℓ hadm hA hB ih =>
    exfalso
    rw [show (ℓ + 3) % 3 = ℓ % 3 by omega] at hlow
    omega

/-- **`thm:base23`(3)**: for every net of the theorem at level `m ≥ 1` and every digital shift `τ` of depth `m`,
`δ(P_m ⊕ τ) N^{1/3} ≥ b23C b (m mod 3)` (toroidal distance). -/
theorem b23_sep (hb : b = 2 ∨ b = 3) (hc : B23Certs b) {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    (h : IsB23Gen b m C) (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    b23C b (m % 3) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  have hb1 : 1 < b := (Fact.out : b.Prime).one_lt
  set r := m % 3 with hrdef
  have hr : r < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hL : b23L b r ≤ m
  · obtain ⟨σ, hσ⟩ := chain_from_L hb h r hr rfl hL
    obtain ⟨h1, h2, h3, h4, -⟩ := seed_facts hb r hr
    obtain ⟨hn, hc1, hnum, -⟩ := hc.1 r hr
    have hLev : b23Lev b r (b23NL b r) = b23L b r := by unfold b23Lev; omega
    have hD : ∀ ℓ, b23Lev b r (b23NL b r) ≤ ℓ →
        b23Lev b r (b23NL b r) / 2 + (ℓ - b23Lev b r (b23NL b r)) / 3 ≤ ℓ / 2 := by intro ℓ _; omega
    have hsc := shiftcert_a hD hσ τ v w hvw
    have hv := c1_vcirc hn hc1 (by rw [hLev]; exact h4) (by rw [hLev]; omega)
    obtain ⟨n1, n2, n3, -⟩ := numChk_spec hnum
    have hcl := real_from_cert b _ _ _ hb1 n1 n2 n3
    refine le_trans ?_ hsc
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact hcl.trans (min_le_min_right _ (gL_mono _ _ hv))
  · exact b23_sep_low hb hc h (by simp only [hrdef] at hL; omega) τ v w hvw

/-- **`thm:base23`, existence**: for every `m ≥ 1` there is a net of the theorem at level `m` (for `m` beyond the
certificate level by `lem:lift`(B), with `D_ℓ = ⌊ℓ/2⌋`). -/
theorem b23_exists (hb : b = 2 ∨ b = 3) (hc : B23Certs b) :
    ∀ m, 1 ≤ m → ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), IsB23Gen b m C := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hr : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    obtain ⟨h1, h2, h3, h4, -⟩ := seed_facts hb (m % 3) hr
    by_cases hs : m < b23SeedM b (m % 3)
    · exact ⟨_, IsB23Gen.wit m hm hs⟩
    by_cases hL : m ≤ b23L b (m % 3)
    · generalize hr' : m % 3 = r at *
      obtain ⟨k, hk⟩ : ∃ k, m = b23Lev b r k := ⟨(m - b23SeedM b r) / 3, by unfold b23Lev; omega⟩
      have hkL : k ≤ b23NL b r := by unfold b23Lev at hk; omega
      subst hk
      exact ⟨_, IsB23Gen.chain r k hr hkL⟩
    · obtain ⟨ℓ, rfl⟩ : ∃ ℓ, m = ℓ + 3 := ⟨m - 3, by omega⟩
      obtain ⟨C, hC⟩ := ih ℓ (by omega) (by omega)
      have hnet := b23_net hb hc hC 0
      obtain ⟨sA, sB, hA, hB, hadm⟩ := lift_exists C 0 hnet (ℓ / 2) (by omega)
      exact ⟨_, IsB23Gen.cont sA sB hC (by rw [show ℓ % 3 = (ℓ + 3) % 3 by omega]; omega) hadm hA hB⟩


end family

/-! ## The certificates of the bases two and three (kernel runs in `Z3Net/B23Cert*.lean`) -/

theorem cert_num_2_0 : numChk 2 0 = true := by decide +kernel

theorem cert_num_2_1 : numChk 2 1 = true := by decide +kernel

theorem cert_num_2_2 : numChk 2 2 = true := by decide +kernel

theorem cert_num_3_0 : numChk 3 0 = true := by decide +kernel

theorem cert_num_3_1 : numChk 3 1 = true := by decide +kernel

theorem cert_num_3_2 : numChk 3 2 = true := by decide +kernel

theorem cert_wnum_2_1 : witNum 2 1 = true := by decide +kernel

theorem cert_wnum_2_2 : witNum 2 2 = true := by decide +kernel

theorem cert_wnum_2_3 : witNum 2 3 = true := by decide +kernel

theorem cert_wnum_2_4 : witNum 2 4 = true := by decide +kernel

theorem cert_wnum_2_5 : witNum 2 5 = true := by decide +kernel

theorem cert_wnum_2_6 : witNum 2 6 = true := by decide +kernel

theorem cert_wnum_2_7 : witNum 2 7 = true := by decide +kernel

theorem cert_wnum_2_8 : witNum 2 8 = true := by decide +kernel

theorem cert_wnum_3_1 : witNum 3 1 = true := by decide +kernel

theorem cert_wnum_3_2 : witNum 3 2 = true := by decide +kernel

theorem cert_wnum_3_3 : witNum 3 3 = true := by decide +kernel

theorem cert_wnum_3_4 : witNum 3 4 = true := by decide +kernel

theorem cert_wnum_3_5 : witNum 3 5 = true := by decide +kernel

theorem b23_certs (b : ℕ) (hb : b = 2 ∨ b = 3) : B23Certs b := by
  rcases hb with rfl | rfl
  · refine ⟨fun r hr => ?_, fun m h1 h2 => ?_⟩
    · interval_cases r
      · have e : b23NL 2 0 = 7 := rfl
        refine ⟨cert_netChk_2_0, cert_c1Chk_2_0, cert_num_2_0, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_2_0_0
        · exact cert_c2Chk_2_0_1
        · exact cert_c2Chk_2_0_2
        · exact cert_c2Chk_2_0_3
        · exact cert_c2Chk_2_0_4
        · exact cert_c2Chk_2_0_5
        · exact cert_c2Chk_2_0_6
      · have e : b23NL 2 1 = 6 := rfl
        refine ⟨cert_netChk_2_1, cert_c1Chk_2_1, cert_num_2_1, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_2_1_0
        · exact cert_c2Chk_2_1_1
        · exact cert_c2Chk_2_1_2
        · exact cert_c2Chk_2_1_3
        · exact cert_c2Chk_2_1_4
        · exact cert_c2Chk_2_1_5
      · have e : b23NL 2 2 = 3 := rfl
        refine ⟨cert_netChk_2_2, cert_c1Chk_2_2, cert_num_2_2, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_2_2_0
        · exact cert_c2Chk_2_2_1
        · exact cert_c2Chk_2_2_2
    · have hm : m ≤ 10 := by
        have := (seed_facts (b := 2) (Or.inl rfl) (m % 3) (Nat.mod_lt _ (by norm_num))).2.2.2.2; omega
      interval_cases m
      · exact ⟨cert_witChk_2_1, cert_wnum_2_1⟩
      · exact ⟨cert_witChk_2_2, cert_wnum_2_2⟩
      · exact ⟨cert_witChk_2_3, cert_wnum_2_3⟩
      · exact ⟨cert_witChk_2_4, cert_wnum_2_4⟩
      · exact ⟨cert_witChk_2_5, cert_wnum_2_5⟩
      · exact ⟨cert_witChk_2_6, cert_wnum_2_6⟩
      · exact ⟨cert_witChk_2_7, cert_wnum_2_7⟩
      · exact ⟨cert_witChk_2_8, cert_wnum_2_8⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  · refine ⟨fun r hr => ?_, fun m h1 h2 => ?_⟩
    · interval_cases r
      · have e : b23NL 3 0 = 4 := rfl
        refine ⟨cert_netChk_3_0, cert_c1Chk_3_0, cert_num_3_0, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_3_0_0
        · exact cert_c2Chk_3_0_1
        · exact cert_c2Chk_3_0_2
        · exact cert_c2Chk_3_0_3
      · have e : b23NL 3 1 = 5 := rfl
        refine ⟨cert_netChk_3_1, cert_c1Chk_3_1, cert_num_3_1, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_3_1_0
        · exact cert_c2Chk_3_1_1
        · exact cert_c2Chk_3_1_2
        · exact cert_c2Chk_3_1_3
        · exact cert_c2Chk_3_1_4
      · have e : b23NL 3 2 = 4 := rfl
        refine ⟨cert_netChk_3_2, cert_c1Chk_3_2, cert_num_3_2, fun k hk => ?_⟩
        rw [e] at hk
        interval_cases k
        · exact cert_c2Chk_3_2_0
        · exact cert_c2Chk_3_2_1
        · exact cert_c2Chk_3_2_2
        · exact cert_c2Chk_3_2_3
    · have hm : m ≤ 10 := by
        have := (seed_facts (b := 3) (Or.inr rfl) (m % 3) (Nat.mod_lt _ (by norm_num))).2.2.2.2; omega
      interval_cases m
      · exact ⟨cert_witChk_3_1, cert_wnum_3_1⟩
      · exact ⟨cert_witChk_3_2, cert_wnum_3_2⟩
      · exact ⟨cert_witChk_3_3, cert_wnum_3_3⟩
      · exact ⟨cert_witChk_3_4, cert_wnum_3_4⟩
      · exact ⟨cert_witChk_3_5, cert_wnum_3_5⟩
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)

/-! ## The statements of `thm:base23` -/

theorem base23_net_core (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} (h : IsB23Gen b m C) (σ : Fin 3 → Fin m → ZMod b) :
    Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m C σ) := b23_net hb (b23_certs b hb) h σ

theorem base23_exists_core (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), IsB23Gen b m C := b23_exists hb (b23_certs b hb) m hm

theorem base23_everyshift_core (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} (h : IsB23Gen b m C) (τ : Fin 3 → Fin m → ZMod b)
    (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    b23C b (m % 3) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) :=
  b23_sep hb (b23_certs b hb) h τ v w hvw

lemma b23C_ge (b r : ℕ) (hb : b = 2 ∨ b = 3) (hr : r < 3) :
    (if b = 2 then (0.1718 : ℝ) else 0.0770) ≤ b23C b r := by
  unfold b23C
  rcases hb with rfl | rfl <;> interval_cases r <;> norm_num [b23Cnum]

theorem base23_base_core (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} (h : IsB23Gen b m C) (τ : Fin 3 → Fin m → ZMod b)
    (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    (if b = 2 then (0.1718 : ℝ) else 0.0770) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) :=
  le_trans (mul_le_mul_of_nonneg_right (b23C_ge b (m % 3) hb (Nat.mod_lt _ (by norm_num))) (by positivity))
    (base23_everyshift_core b hb h τ v w hvw)

theorem b23_vcirc_core (b r : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) :
    b23V b r ≤ vcirc b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := seed_facts hb r hr
  obtain ⟨hn, hc1, -, -⟩ := (b23_certs b hb).1 r hr
  have hLev : b23Lev b r (b23NL b r) = b23L b r := by unfold b23Lev; omega
  exact c1_vcirc hn hc1 (by rw [hLev]; exact h4) (by rw [hLev]; omega)

theorem b23_lift_core (b r k : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) (hk : k < b23NL b r) :
    b23Gen b r (k + 1) = liftGen (b23Gen b r k) (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).1)
      (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).2) ∧
    Admissible (b23Gen b r k) (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).1)
      (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).2) := by
  obtain ⟨hn, -, -, -⟩ := (b23_certs b hb).1 r hr
  exact ⟨b23Gen_succ hn k hk, liftChk_sound (chain_ok hn k (by omega)).1 (netChk_lift hn k hk)⟩

theorem b23_seed_core (b r : ℕ) (hb : b = 2 ∨ b = 3) :
    b23Gen b r 0 = ![1, rowMat b (b23SeedM b r) (b23RowsY b r), rowMat b (b23SeedM b r) (b23RowsZ b r)] :=
  colMat_seedCols (by rcases hb with rfl | rfl <;> norm_num) _ _ _

/-- The current witnesses `b = 2`, `m = 6, 7`: nets with every-shift constants `.2165`, `.3100`. -/
theorem b23_witcur_core (m : ℕ) (hm : m = 6 ∨ m = 7) :
    (∀ σ, Z3NetF.IsNet0 3 2 m (Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) σ)) ∧
    ∀ (τ : Fin 3 → Fin m → ZMod 2) (v w : Fin m → ZMod 2), v ≠ w →
      (if m = 6 then (0.2165 : ℝ) else 0.3100) * ((2 : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
        Real.sqrt (∑ c, ((Z3NetF.cres (2 ^ m) ((Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ v c : ℤ) -
          Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ w c) : ℝ) / (2 : ℝ) ^ m) ^ 2) := by
  have hw : witChk 2 m (b23WitCur m) (b23WitCurU m) = true := by
    rcases hm with rfl | rfl
    · exact cert_witChk_2_6_cur
    · exact cert_witChk_2_7_cur
  obtain ⟨hnet, hd⟩ := wit_ok hw
  refine ⟨hnet, fun τ v w hvw => ?_⟩
  have e := sqrt_torus (2 ^ m) (pow_pos (by norm_num) m) (Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ v)
    (Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ w)
  push_cast at e
  rw [e]
  have hnum : (if m = 6 then 2165 else 3100) ^ 6 * 2 ^ (4 * m) ≤ b23WitCurU m ^ 3 * 10000 ^ 6 := by
    rcases hm with rfl | rfl <;> decide
  have := real_from_U 2 m _ _ _ (by norm_num) hnum (hd τ v w hvw)
  push_cast at this
  convert this using 2
  rcases hm with rfl | rfl <;> norm_num

/-- **`thm:base23`(1) for the continuations, given the certificate** `v*_L(P_L ⊕ σ_L) ≥ v₁` (a finite check; see
the statement-review notes (research repository) for its cost): along every deep-shift chain from the certificate level with its explicit
shift and `D_ℓ = ⌊ℓ/2⌋`, `δ N^{1/3} ≥ min(g_L(v₁), b^{L/3} − W b^{-2L/3})`. -/
theorem base23_shifted_core (b r : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) (v₁ : ℕ)
    (hcert : ∀ n n' : Fin (b23Lev b r (b23NL b r)) → ZMod b, n ≠ n' →
      v₁ ≤ ∑ c : Fin 3, hW (Z3NetF.cres (b ^ (b23Lev b r (b23NL b r) / 2))
        (((Z3NetF.digPointShift b _ (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r)) n c /
            b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) : ℕ) : ℤ) -
          ((Z3NetF.digPointShift b _ (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r)) n' c /
            b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) : ℕ) : ℤ))))
    {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r))
      (fun ℓ => ℓ / 2) m C σ) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b (b23Lev b r (b23NL b r)) v₁) (((b : ℝ) ^ b23Lev b r (b23NL b r)) ^ (1 / 3 : ℝ) -
        (b : ℝ) ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) *
          ((b : ℝ) ^ b23Lev b r (b23NL b r)) ^ (-(2 / 3 : ℝ))) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C σ v c : ℤ) -
        Z3NetF.digPointShift b m C σ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  have hD : ∀ ℓ, b23Lev b r (b23NL b r) ≤ ℓ →
      b23Lev b r (b23NL b r) / 2 + (ℓ - b23Lev b r (b23NL b r)) / 3 ≤ ℓ / 2 := by intro ℓ _; omega
  have hls := liftsep hD h v w hvw
  refine le_trans (mul_le_mul_of_nonneg_right (min_le_min_right _ (gL_mono _ _ ?_)) (by positivity)) hls
  obtain ⟨h1, h2, h3, -, -⟩ := seed_facts hb r hr
  have hL : 0 < b23Lev b r (b23NL b r) := by unfold b23Lev; omega
  haveI : Nonempty {p : (Fin (b23Lev b r (b23NL b r)) → ZMod b) × (Fin (b23Lev b r (b23NL b r)) → ZMod b) //
      p.1 ≠ p.2} := ⟨⟨(0, Pi.single ⟨0, hL⟩ 1), fun e => by have := congrFun e ⟨0, hL⟩; simp at this⟩⟩
  exact le_ciInf fun p => hcert p.1.1 p.1.2 p.2

end Z3NetB23.Proofs
