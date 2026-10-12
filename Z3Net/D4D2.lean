/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.D4D2Cert
public import Z3Net.FDeficit
public import Z3Net.ThmASharp

@[expose] public section

/-!
# V14 stage S8: `prop:4D2` (dimension four, deficit two)

The design `F4D2` of `app:designs` on the places `∞, 0, 1, 2` with `λ' ≡ 1`, over `ℤ[1/2] = RS 4`.

* (1) `residual_core`: the residual problem is solved over `ℤ[1/2]` by `U' = UrW` (exact
  interpolation; the identities are checked in `ℚ` through the injective map `ι : ℤ[1/2] → ℚ`), so
  `cor:tsk` gives the net property for every odd `q` (`net_core`), with box minors that are units
  of `ℤ[1/2]`, i.e. `±2^i` (`boxMinor_core`), and the covering radius `h ≤ 2 N^(-1/4)`.
* (2) `sep_core`: `lem:Ss` with `B = (q-2)²`: for `q ≥ 23 = Q_D(2, 7)` by `prop:Dprime` with the kernel
  certificates `K(F) = 2`, `S(F) = 7` (`D4D2Cert`); for `q = 17, 19, 21` by the exact relaxation
  `Bmin q F 3 3 = (q-2)²` (`D4D2Cert`), which bounds the truncations `L = min(k, 3) < 3` (capped
  carry classes).
* (3) `ceil_core`: `cor:ceils`(i) along `a = ∞` (column `(-2, 1, 1, 1)` of `F_0`), through the counting
  step `USharp.sharp_core` (as for Theorem A, `A_sharp_core`); it holds for every `k ≥ 2`.
-/

namespace Z3NetF.Proofs.D4D2

open Finset Z3NetF Z3NetA Z3NetA.Proofs

set_option linter.unusedSectionVars false

noncomputable section

/-! ## (1) The residual problem over `ℤ[1/2]` -/

/-- The numerators of `2 U'_d` (rows `n'`, columns `n`, upper triangular), from exact interpolation. -/
def UrT : Fin 4 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![2, 0, 0; 0, -2, -1; 0, 0, 1], !![-4, 6, -4; 0, -4, 12; 0, 0, -8],
    !![-2, 2, -2; 0, -2, 2; 0, 0, 2], !![-4, 2, 0; 0, -4, -16; 0, 0, -16]]

/-- `2 U'_d[n', n]` for `n', n < 3`, `0` otherwise. -/
def UrN (d : Fin 4) (n' n : ℕ) : ℤ := if h : n' < 3 ∧ n < 3 then UrT d ⟨n', h.1⟩ ⟨n, h.2⟩ else 0

/-- The solution `U'` of the residual problem: `U'_d[n', n] = UrN_d[n', n] / 2`. -/
def UrW : Fin 4 → ℕ → ℕ → RS 4 := fun d n' n => (UrN d n' n : RS 4) * Ring.inverse 2

lemma unit2 : IsUnit (2 : RS 4) := by
  have := unit_int 4 2 (by norm_num) (by norm_num)
  simpa using this

lemma ι_half : ι 4 (Ring.inverse 2) = 1 / 2 := by
  rw [ι_inv 4 _ unit2, map_ofNat, one_div]

lemma ι_UrW (d : Fin 4) (n' n : ℕ) : ι 4 (UrW d n' n) = (UrN d n' n : ℚ) / 2 := by
  rw [UrW, map_mul, map_intCast, ι_half]; ring

theorem residual_core : Residual (0 : Fin 4) placeA F4D2R 1 UrW := by
  refine ⟨fun c => isUnit_one, ?_, ?_, ?_⟩
  · intro d n' n hn hn'
    have : UrN d n' n = 0 := by
      simp only [UrN]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        fin_cases d <;> interval_cases n' <;> interval_cases n <;> simp_all [UrT]
      · rfl
    simp [UrW, this]
  · intro d n hn
    simp only [UrW]
    refine IsUnit.mul ?_ unit2.ringInverse
    have h2 := unit2
    have h4 : IsUnit (4 : RS 4) := by rw [show (4 : RS 4) = 2 * 2 by norm_num]; exact h2.mul h2
    have h8 : IsUnit (8 : RS 4) := by rw [show (8 : RS 4) = 4 * 2 by norm_num]; exact h4.mul h2
    have h16 : IsUnit (16 : RS 4) := by rw [show (16 : RS 4) = 4 * 4 by norm_num]; exact h4.mul h4
    fin_cases d <;> interval_cases n <;> simp [UrN, UrT] <;>
      first | assumption | exact h2.neg | exact h4.neg | exact h8.neg | exact h16.neg
  · intro c d hcd n hn
    apply ι_inj 4
    simp only [F4D2R, Pi.one_apply, one_mul, map_intCast, map_sum, map_mul, map_pow, ι_UrW,
      ι_wN (by norm_num : 2 ≤ 4) c d hcd, ι_yN (by norm_num : 2 ≤ 4) c d hcd]
    fin_cases c <;> fin_cases d <;> (first | exact absurd rfl hcd | skip) <;>
      interval_cases n <;>
      norm_num [wQ, yQ, wN, yN, placeA, F4D2, UrN, UrT, Finset.sum_range_succ]

/-- The data `U'`, `β` of the net exist (`prop:Gs`). -/
theorem data_core : Residual (0 : Fin 4) placeA F4D2R 1 Ur4D2 ∧
    BetaRel (0 : Fin 4) placeA F4D2R 1 beta4D2 := by
  have hres : Residual (0 : Fin 4) placeA F4D2R 1 Ur4D2 :=
    Classical.epsilon_spec ⟨UrW, residual_core⟩
  refine ⟨hres, Classical.epsilon_spec ?_⟩
  have hb := fun d n => (Z3NetF.Proofs.Gs_beta_core (0 : Fin 4) (placeA : Fin 4 → RS 4) (by norm_num)
    (placesOK (by norm_num)) F4D2R 1 Ur4D2 hres d n).exists
  choose b hb using hb
  refine ⟨fun d n i => if h : i < 4 - 1 then b d n ⟨i, h⟩ else 0, fun d n _ c hc => ?_⟩
  rw [hb d n c hc, Finset.sum_range]
  refine sum_congr rfl fun i _ => ?_
  dsimp only
  rw [dite_eq_left i.isLt]

/-! ## The reduction `ℤ[1/2] → ℤ/qℤ` for odd `q` -/

lemma adm_of_odd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) : AdmBase 4 q := by
  refine ⟨by omega, fun p hp hpq => ?_⟩
  have h2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hpq)
  have := hp.two_le
  omega

lemma odd_of_hom {q : ℕ} [NeZero q] (ψ : RS 4 →+* ZMod q) : Odd q := by
  have h := unit2.map ψ
  rw [map_ofNat] at h
  have hc : Nat.Coprime 2 q := (ZMod.isUnit_iff_coprime 2 q).1 (by exact_mod_cast h)
  exact (Nat.coprime_two_left.1 hc)

lemma P4D2_eq {q : ℕ} (k : ℕ) (ψ : RS 4 →+* ZMod q) :
    P4D2 q k = digPoint q (4 * k) (fun c =>
      (PGen k (0 : Fin 4) placeA F4D2R 1 Ur4D2 beta4D2 c).map ψ) := by
  funext v
  unfold P4D2
  rw [dite_eq_left ⟨ψ⟩]
  dsimp only
  rw [hom_unique (Classical.choice _) ψ]

/-! ## (1) The net, the box minors, the covering radius -/

theorem net_core (q k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) : IsNet0 4 q (4 * k) (P4D2 q k) := by
  have : NeZero q := ⟨by omega⟩
  obtain ⟨ψ⟩ := (A_hom_core (s := 4) (by norm_num) (adm_of_odd hq h3)).1
  rw [P4D2_eq k ψ]
  exact Z3NetF.Proofs.tsk_net_core (k := k) (inf := (0 : Fin 4)) (x := placeA) ψ
    (placesOK (by norm_num)) F4D2R 1 Ur4D2 beta4D2 data_core.1

/-- The units of `ℤ[1/2]` are `±2^i`, `i ∈ ℤ`. -/
lemma unit_pow2 (x : RS 4) (hx : IsUnit x) :
    ∃ (i : ℕ) (ε : RS 4), (ε = 1 ∨ ε = -1) ∧ (x = ε * 2 ^ i ∨ x * 2 ^ i = ε) := by
  have hx1 : InRS 4 (ι 4 x) := (inRS_iff 4 _).2 ⟨x, rfl⟩
  have hy1 : InRS 4 (ι 4 (Ring.inverse x)) := (inRS_iff 4 _).2 ⟨_, rfl⟩
  obtain ⟨z, e, hz⟩ := hx1
  obtain ⟨z', e', hz'⟩ := hy1
  have hf : (((4 - 2).factorial : ℕ) : ℚ) = 2 := by norm_num [Nat.factorial]
  rw [hf] at hz hz'
  have hprod : ι 4 x * ι 4 (Ring.inverse x) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hx, map_one]
  rw [hz, hz'] at hprod
  have hzz : (z : ℚ) * z' = 2 ^ (e + e') := by
    field_simp at hprod
    rw [pow_add]; linarith
  have hzz' : z * z' = 2 ^ (e + e') := by exact_mod_cast hzz
  have hdvd : z.natAbs ∣ 2 ^ (e + e') := by
    have : (z.natAbs : ℤ) ∣ 2 ^ (e + e') := by
      rw [← hzz']; exact (Int.natAbs_dvd.mpr (dvd_mul_right z z'))
    exact_mod_cast this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hzpm : (z : ℚ) = 2 ^ i ∨ (z : ℚ) = -2 ^ i := by
    rcases Int.natAbs_eq z with h | h
    · left; rw [h, hi]; push_cast; ring
    · right; rw [h, hi]; push_cast; ring
  have key : ∀ ε : RS 4, (ι 4 ε = 1 ∨ ι 4 ε = -1) → (ε = 1 ∨ ε = -1) := by
    intro ε hε
    rcases hε with h | h
    · left; apply ι_inj 4; rw [h, map_one]
    · right; apply ι_inj 4; rw [h, map_neg, map_one]
  by_cases hie : e ≤ i
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hie
    rcases hzpm with h | h
    · refine ⟨t, 1, Or.inl rfl, Or.inl (ι_inj 4 ?_)⟩
      rw [hz, h, map_mul, map_one, map_pow, map_ofNat, pow_add]; field_simp
    · refine ⟨t, -1, Or.inr rfl, Or.inl (ι_inj 4 ?_)⟩
      rw [hz, h, map_mul, map_neg, map_one, map_pow, map_ofNat, pow_add]; field_simp
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt (not_le.mp hie)
    rcases hzpm with h | h
    · refine ⟨t + 1, 1, Or.inl rfl, Or.inr (ι_inj 4 ?_)⟩
      rw [map_mul, hz, h, map_one, map_pow, map_ofNat, ht, pow_add, pow_add]; field_simp; ring
    · refine ⟨t + 1, -1, Or.inr rfl, Or.inr (ι_inj 4 ?_)⟩
      rw [map_mul, hz, h, map_neg, map_one, map_pow, map_ofNat, ht, pow_add, pow_add]; field_simp; ring

theorem boxMinor_core (k : ℕ) (d : Fin 4 → ℕ) (hd : ∑ c, d c = 4 * k) :
    ∃ (i : ℕ) (ε : RS 4), (ε = 1 ∨ ε = -1) ∧
      ((boxMatrix (PGen k (0 : Fin 4) placeA F4D2R 1 Ur4D2 beta4D2) d).det = ε * 2 ^ i ∨
        (boxMatrix (PGen k (0 : Fin 4) placeA F4D2R 1 Ur4D2 beta4D2) d).det * 2 ^ i = ε) :=
  unit_pow2 _ (Z3NetF.Proofs.tsk_unit_core k (0 : Fin 4) placeA (placesOK (by norm_num)) F4D2R 1
    Ur4D2 beta4D2 data_core.1 d hd)

theorem covering_core (q k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (P4D2 q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 4 / ((q : ℝ) ^ k) ^ 2 := by
  have := covering_of_net_core (s := 4) (by norm_num) (by omega) _ (net_core q k hq h3) x hx
  simpa using this

/-! ## (2) The separation bound -/

lemma sqrt2_bounds : (7 : ℝ) / 5 < Real.sqrt 2 ∧ Real.sqrt 2 < 10 / 7 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `Q_D(2, 7) = 23` (`prop:Dprime`). -/
theorem QD_eq : QD 2 7 = 23 := by
  obtain ⟨h1, h2⟩ := sqrt2_bounds
  unfold QD
  have hpos : (0 : ℝ) < Real.sqrt 2 - 1 := by linarith
  have hc : ⌈(Real.sqrt 2 * (((7 : ℕ) : ℝ) + 1) - ((2 : ℕ) : ℝ)) / (Real.sqrt 2 - 1)⌉₊ = 23 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    push_cast
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_le_iff₀ hpos]; nlinarith
  rw [hc]; rfl

set_option maxRecDepth 100000 in
/-- The exact relaxation at `q = 17, 19, 21` (kernel certificates) bounds every configuration of
`lem:Ss` with `L' ≤ 3` levels (capped carry classes) by `(q - 2)²`. -/
lemma bound_small (q : ℕ) (hq : q = 17 ∨ q = 19 ∨ q = 21) {k L' : ℕ} (hL' : 1 ≤ L')
    (hL'3 : L' ≤ 3) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (hc : IsConfig k e j) :
    ((q : ℤ) - 2) ^ 2 ≤ ∑ i, bval q F4D2 L' e j i ^ 2 := by
  have hB : ((q : ℤ) - 2) ^ 2 ≤ Bmin q F4D2 3 3 := by
    rcases hq with rfl | rfl | rfl
    · rw [B17]; norm_num
    · rw [B19]; norm_num
    · rw [B21]; norm_num
  have hall : ∀ ej ∈ cfgs 4 3, ((q : ℤ) - 2) ^ 2 ≤ ∑ i, bval q F4D2 3 ej.1 ej.2 i ^ 2 :=
    ((Finset.le_fold_min _).1 hB).2
  have hmem : (e, Z3NetF.Proofs.Deficit.cap L' j) ∈ cfgs 4 3 := by
    rw [Z3NetF.Proofs.RemK.mem_cfgs]
    exact ⟨hc.1, hc.2.1, fun d => by simp only [Z3NetF.Proofs.Deficit.cap]; omega⟩
  have h : ((q : ℤ) - 2) ^ 2 ≤ ∑ i, bval q F4D2 3 e (Z3NetF.Proofs.Deficit.cap L' j) i ^ 2 :=
    hall (e, Z3NetF.Proofs.Deficit.cap L' j) hmem
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Z3NetF.Proofs.Deficit.bval_congr q F4D2 F4D2 L' 3 e j _ i
    (Z3NetF.Proofs.Deficit.sigma_cap F4D2 hL'3 e j i)]

theorem sep_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (4 * k - k)) * ((q : ℤ) - 2) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (4 * k)) (P4D2 q k v) (P4D2 q k w) : ℤ) := by
  have : NeZero q := ⟨by omega⟩
  obtain ⟨ψ⟩ := (A_hom_core (s := 4) (by norm_num) (adm_of_odd hq (by omega))).1
  rw [P4D2_eq k ψ]
  obtain ⟨hres, hβ⟩ := data_core
  by_cases h23 : 23 ≤ q
  · have hQ : QD 2 (Sdef F4D2 (4 - 1)) ≤ q := by
      have hS : Sdef F4D2 (4 - 1) = 7 := S_eq
      rw [hS, QD_eq]; exact h23
    exact Z3NetF.Proofs.Deficit.Dprime_sep_core (s := 4) (K := 2) (by norm_num) ψ k hk (0 : Fin 4)
      placeA (placesOK (by norm_num)) F4D2 1 Ur4D2 beta4D2 hres hβ K_eq hQ (by omega) v w hvw
  · have hqs : q = 17 ∨ q = 19 ∨ q = 21 := by
      obtain ⟨r, hr⟩ := hq; omega
    rw [Z3NetF.Proofs.PGen_map_eq]
    obtain ⟨h1, h2⟩ := Z3NetF.Proofs.PGen_H1H2 ψ k (0 : Fin 4) placeA (placesOK (by norm_num))
      F4D2 1 Ur4D2 beta4D2 hres hβ
    have hL : 1 ≤ min k (4 - 1) := by omega
    exact Z3NetF.Proofs.Ss_sep_core 4 q k _ F4D2 _ (by norm_num) (by omega) hk hL
      (min_le_left _ _) h1 h2 _ (by nlinarith)
      (fun e j hc => bound_small q hqs hL (by omega) e j hc) v w hvw

/-- The toroidal form: `(1 - 2/q) N^(-1/4) ≤ ‖P v - P w‖_torus`. -/
theorem sep_real_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) := by
  have hZ := sep_core q k hq hq17 hk v w hvw
  unfold torusDist2 at hZ
  have hR : (q : ℝ) ^ (2 * (4 * k - k)) * ((q : ℝ) - ((2 : ℕ) : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 *
      ∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this ⊢
    exact this
  have hsum : ∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (4 * k)) ^ 2 = (∑ c, ((cres (q ^ (4 * k))
        ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)) ^ 2) / ((q : ℝ) ^ (4 * k)) ^ 2 := by
    rw [Finset.sum_div]; exact sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  have := sep_real_of_int (s := 4) (a := 2) (by norm_num) (by omega) _ hR
  simpa using this

/-- The Euclidean form: `(1 - 2/q) N^(-1/4) ≤ ‖P v - P w‖`. -/
theorem sep_eucl_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) := by
  refine (sep_real_core q k hq hq17 hk v w hvw).trans (Real.sqrt_le_sqrt ?_)
  refine Finset.sum_le_sum fun c _ => ?_
  have hq0 : 0 < q := by omega
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set X := P4D2 q k
  have hc := Z3NetF.Proofs.Deficit.cres_le_abs (q ^ (4 * k)) (pow_pos hq0 _)
    ((X v c : ℤ) - (X w c : ℤ))
  have hc0 : (0 : ℤ) ≤ (cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) := by positivity
  have hsq : ((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ)) ^ 2 ≤
      ((X v c : ℤ) - (X w c : ℤ)) ^ 2 := by
    rw [← sq_abs ((X v c : ℤ) - _)]; exact pow_le_pow_left₀ hc0 hc 2
  have : (((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ)) ^ 2 ≤
      ((X v c : ℝ) - (X w c : ℝ)) ^ 2 := by exact_mod_cast hsq
  exact this

/-- `LB ≥ 1 - 2/q` for every odd `q ≥ 17` and every `k ≥ 1` (`L = min(k, 3)` levels). -/
theorem LB_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k) :
    1 - (2 : ℝ) / q ≤ LBval q F4D2 (min k 3) k := by
  by_cases h23 : 23 ≤ q
  · have hQ : QD 2 (Sdef F4D2 3) ≤ q := by rw [S_eq, QD_eq]; exact h23
    have := Z3NetF.Proofs.Deficit.Dprime_core (q := q) (L := 3) (L' := min k 3) (k := k) (K := 2)
      F4D2 (by omega) (min_le_right _ _)
      K_eq hQ
    simpa using this
  · have hqs : q = 17 ∨ q = 19 ∨ q = 21 := by
      obtain ⟨r, hr⟩ := hq; omega
    have hq0 : (0 : ℤ) ≤ (q : ℤ) - 2 := by omega
    have := Z3NetF.Proofs.Deficit.LBval_ge (q := q) (K := 2) (k := k) (L := min k 3) F4D2 (by omega) (by omega)
      ⟨by push_cast; nlinarith, fun e j hc => by
        push_cast; exact bound_small q hqs (by omega) (min_le_right _ _) e j hc⟩
    simpa using this

/-- The exact relaxation `LB = (q-2)/q` at `q = 17, 19, 21` (`L = 3`, three cell levels). -/
theorem LB_small (q : ℕ) (hq : q = 17 ∨ q = 19 ∨ q = 21) :
    LBval q F4D2 3 3 = 1 - (2 : ℝ) / q := by
  have hB : Bmin q F4D2 3 3 = ((q : ℤ) - 2) ^ 2 := by
    rcases hq with rfl | rfl | rfl
    · rw [B17]; norm_num
    · rw [B19]; norm_num
    · rw [B21]; norm_num
  have hq2 : (2 : ℝ) ≤ q := by rcases hq with rfl | rfl | rfl <;> norm_num
  unfold LBval
  rw [hB]
  push_cast
  rw [Real.sqrt_sq (by linarith)]
  have : (0 : ℝ) < q := by linarith
  field_simp

/-! ## (3) The ceiling (`cor:ceils`(i) along `a = ∞`) -/

lemma F0_col (u : Fin 4) (hu : u ≠ 0) : F4D2 0 u 0 = 1 := by
  fin_cases u <;> simp_all [F4D2]

/-- `cor:ceils`(i) for the net of `prop:4D2` along the coordinate `∞` (column `(-2, 1, 1, 1)` of
`F_0`), for every odd `q ≥ 17` and every `k ≥ 2`: two distinct points at squared Euclidean and
toroidal distance, in cell units, `< (1 - 2/q)² + 12/q²`. -/
theorem ceil_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (4 * k))
          ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 := by
  classical
  have : NeZero q := ⟨by omega⟩
  obtain ⟨ψ⟩ := (A_hom_core (s := 4) (by norm_num) (adm_of_odd hq (by omega))).1
  obtain ⟨hres, hβ⟩ := data_core
  set Φ : Fin 4 → Fin 4 → Matrix (Fin (4 * k - k)) (Fin k) (ZMod q) :=
    fun c d => (PPhi k (0 : Fin 4) placeA F4D2R 1 Ur4D2 beta4D2 c d).map ψ with hΦ
  have hpt : P4D2 q k = gfPoint q k Φ := by
    rw [P4D2_eq k ψ]
    unfold gfPoint
    rw [Z3NetF.Proofs.PGen_map_eq]
  obtain ⟨hH1, hH2'⟩ := Z3NetF.Proofs.PGen_H1H2 ψ k (0 : Fin 4) placeA (placesOK (by norm_num))
    F4D2 1 Ur4D2 beta4D2 hres hβ
  have hsk : 0 < 4 * k - k := by omega
  have hent0 : ∀ c d, ent (Φ c d) 0 (k - 1) = ((F4D2 0 c d : ℤ) : ZMod q) := by
    intro c d
    unfold ent
    rw [dif_pos ⟨hsk, by omega⟩]
    have := hH1 c d ⟨0, hsk⟩ rfl ⟨k - 1, by omega⟩
    simp only at this
    rw [Nat.sub_self, if_pos (by omega)] at this
    exact this
  have hH2 : ∀ r, 1 ≤ r → ent (Φ 0 0) r (k - 1) = 0 := by
    intro r hr
    unfold ent
    split_ifs with h
    · exact hH2' 0 ⟨r, h.1⟩ (by simp; omega) ⟨k - 1, h.2⟩
    · rfl
  have hMt : ∀ u, u ≠ 0 → Mt Φ u 0 = F4D2 0 u 0 := by
    intro u hu
    unfold Mt
    rw [hent0]
    apply Z3NetU.Proofs.USharp.valMinAbs_eq
    rw [F0_col u hu]
    have : (17 : ℤ) ≤ q := by exact_mod_cast hq17
    norm_num; omega
  have hcol0 : ∑ u ∈ univ.erase (0 : Fin 4), |F4D2 0 u 0| = 3 := by decide
  have hcolMt : ∑ u ∈ univ.erase (0 : Fin 4), |Mt Φ u 0| < q := by
    rw [Finset.sum_congr rfl fun u hu => by rw [hMt u (mem_erase.mp hu).1], hcol0]
    have : (17 : ℤ) ≤ q := by exact_mod_cast hq17
    omega
  have hμval : (ent (Φ 0 0) 0 (k - 1)).val = q - 2 := by
    rw [hent0, show F4D2 0 0 0 = -((2 : ℕ) : ℤ) by decide, Int.cast_neg, Int.cast_natCast,
      ZMod.neg_val, if_neg, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hμ : 1 ≤ (ent (Φ 0 0) 0 (k - 1)).val := by rw [hμval]; omega
  have hnet : IsNet0 4 q (4 * k) (gfPoint q k Φ) := by
    rw [← hpt]; exact net_core q k hq (by omega)
  obtain ⟨v, w, hvw, hXa, hXu⟩ :=
    Z3NetF.Proofs.USharp.sharp_core (by norm_num) (by omega) hk Φ hnet 0 hcolMt hμ hH2
  rw [← hpt, hμval] at hXa
  refine ⟨v, w, hvw, ?_⟩
  set X := P4D2 q k with hX
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set G : ℝ := (q : ℝ) ^ (4 * k - k - 1) with hG
  have hGpos : 0 < G := by positivity
  have hQ : (q : ℝ) ^ (4 * k) = G * q * (q : ℝ) ^ k := by
    rw [hG, mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
  have hk2 : ((q : ℝ) ^ k) ^ 2 = (q : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
  have key : ∀ c, (q : ℝ) ^ (2 * k) * (((X v c : ℝ) - X w c) / (q : ℝ) ^ (4 * k)) ^ 2 =
      (((X v c : ℝ) - X w c) / (G * q)) ^ 2 := by
    intro c
    rw [hQ, ← hk2]
    field_simp
  have hA : (((X v 0 : ℝ) - X w 0) / (G * q)) ^ 2 = (1 - (2 : ℝ) / q) ^ 2 := by
    have : ((X v 0 : ℝ) - X w 0) = -(G * ((q : ℝ) - 2)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXa
      push_cast [Nat.cast_sub (show 2 ≤ q by omega)] at this
      rw [hG]; linarith
    rw [this]
    field_simp
  have hU : ∀ u, u ≠ 0 → (((X v u : ℝ) - X w u) / (G * q)) ^ 2 < ((2 : ℝ) / q) ^ 2 := by
    intro u hu
    obtain ⟨Δ, hΔ, hXΔ⟩ := hXu u hu
    rw [← hpt] at hXΔ
    apply sq_lt_of_abs' hGpos hq0 (by positivity)
    have e1 : ((X v u : ℝ) - X w u) = -(G * (Mt Φ u 0 : ℝ) + Δ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXΔ
      push_cast at this
      rw [hG]; linarith
    rw [e1, abs_neg]
    have hF : |(Mt Φ u 0 : ℝ)| = 1 := by
      rw [hMt u hu, F0_col u hu]; norm_num
    have hΔ' : |(Δ : ℝ)| < G := by rw [hG]; exact_mod_cast hΔ
    calc |G * (Mt Φ u 0 : ℝ) + Δ| ≤ G * |(Mt Φ u 0 : ℝ)| + |(Δ : ℝ)| := by
          rw [← abs_of_pos hGpos, ← abs_mul, abs_of_pos hGpos]; exact abs_add_le _ _
      _ < G * 1 + G := by rw [hF]; linarith
      _ = G * 2 := by ring
  have hsum : (q : ℝ) ^ (2 * k) * ∑ c, (((X v c : ℝ) - X w c) / (q : ℝ) ^ (4 * k)) ^ 2 <
      (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => key c,
      ← Finset.add_sum_erase _ _ (mem_univ (0 : Fin 4)), hA]
    have hne : (univ.erase (0 : Fin 4)).Nonempty := ⟨1, by decide⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun u hu => hU u (mem_erase.mp hu).1
    have hc : ∑ _u ∈ univ.erase (0 : Fin 4), ((2 : ℝ) / q) ^ 2 = 12 / (q : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
        Fintype.card_fin, div_pow]
      norm_num
      ring
    linarith
  refine ⟨hsum, lt_of_le_of_lt ?_ hsum⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun c _ => ?_
  rw [div_pow, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := Z3NetF.Proofs.Deficit.cres_le_abs (q ^ (4 * k)) (pow_pos (Nat.pos_of_neZero q) _)
    ((X v c : ℤ) - (X w c : ℤ))
  have h0' : (0 : ℝ) ≤ ((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) := by positivity
  have h1' : ((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤ |((X v c : ℝ) - X w c)| := by
    have : ((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤
        (((|(X v c : ℤ) - (X w c : ℤ)|) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    exact this
  calc ((cres (q ^ (4 * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) ^ 2
      ≤ |((X v c : ℝ) - X w c)| ^ 2 := by
        apply pow_le_pow_left₀ h0'
        exact_mod_cast h1'
    _ = ((X v c : ℝ) - X w c) ^ 2 := sq_abs _

/-- The real form: `δ N^(1/4) < 1 - 2/q + 8/q²` (toroidal and Euclidean), odd `q ≥ 17`, `k ≥ 2`. -/
theorem ceil_real_core (q k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) ∧
      Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) := by
  obtain ⟨v, w, hvw, hE, hT⟩ := ceil_core q k hq hq17 hk
  refine ⟨v, w, hvw, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrp := rpow_N 4 q k (by norm_num) (by omega)
  push_cast at hrp
  rw [hrp]
  set α : ℝ := 1 - (2 : ℝ) / q
  have hα : (15 : ℝ) / 17 ≤ α := by
    have : (17 : ℝ) ≤ q := by exact_mod_cast hq17
    have : (2 : ℝ) / q ≤ 2 / 17 := by
      rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
    simp only [α]; linarith
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hk2 : (q : ℝ) ^ (2 * k) = ((q : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hsq : α ^ 2 + 12 / (q : ℝ) ^ 2 ≤ (α + 8 / (q : ℝ) ^ 2) ^ 2 := by
    have h8 : 0 ≤ 8 / (q : ℝ) ^ 2 := by positivity
    have : 12 / (q : ℝ) ^ 2 ≤ 2 * α * (8 / (q : ℝ) ^ 2) := by
      rw [show 2 * α * (8 / (q : ℝ) ^ 2) = (16 * α) / (q : ℝ) ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ hq2.le
      linarith
    nlinarith
  have key : ∀ S : ℝ, 0 ≤ S → (q : ℝ) ^ (2 * k) * S < α ^ 2 + 12 / (q : ℝ) ^ 2 →
      Real.sqrt S < (α + 8 / (q : ℝ) ^ 2) * (1 / (q : ℝ) ^ k) := by
    intro S hS0 h
    have h1 : (q : ℝ) ^ (2 * k) * S < (α + 8 / (q : ℝ) ^ 2) ^ 2 := by linarith
    rw [hk2] at h1
    have hpos : 0 < α + 8 / (q : ℝ) ^ 2 := by positivity
    rw [Real.sqrt_lt' (by positivity), mul_one_div, div_pow, lt_div_iff₀ (by positivity)]
    linarith
  exact ⟨key _ (by positivity) hT, key _ (by positivity) hE⟩

end

end Z3NetF.Proofs.D4D2
