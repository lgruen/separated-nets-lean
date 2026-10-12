module
public import Mathlib
public import Z3Net.HLGFUp
public import Z3Net.HLMainH

@[expose] public section

/-!
# Entry HL, stage 1, part 4: the split-frame nets as graph forms; Theorem HL completed

* `HL_rowDesign_core` — (H1) in the form `RowDesign` (only the design levels `< min(k, s-1)`
  need to be half-integral), and `HLpoint = GFpoint … (HLPhi …)`.
* `HL_upper_core` — the upper bound of Theorem HL for `H_s` (via `GF_upper_core`; the constant
  `C2max` of the doubled level-0 layer of `H_s` is at most `CH2 = max_c 2a_c`).
* `HL_limit_core` — `δ N^(1/s) → min(√s/2, √2)` uniformly in `k`.
* `HL_Bbound_core` — `B_s ≤ 6(s-1)(2s-1)^((s-1)²) + 2 ≤ (2s)^(s²)`: the partial sums of the
  doubled design telescope to `2M^(j) = Q e^(s-2) + 2Q e^(s-2-j)` (`j ≥ 1`), so
  `|2M^(j)| ≤ 3|Λ_c|` with `|Λ_c| ≤ (2s-1)^((s-1)²)`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## (H1) as `RowDesign` -/

theorem HL_rowDesign_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k) :
    RowDesign s q k (HLPhi s q k u v lam gco dg) F2 ∧
      ∀ x, HLpoint s q k u v lam gco dg x = GFpoint s q k (HLPhi s q k u v lam gco dg) x := by
  refine ⟨fun c d r hr j => ?_, fun x => rfl⟩
  rw [HL_row0 s q k u v lam gco dg hs hq hden hk c d r hr j]
  have hj := j.isLt
  set n := k - 1 - (j : ℕ) with hn
  split_ifs with h
  · have h2 : Good q (2 : ℚ) := by simpa using good_int (q := q) 2
    have := (good_mul h2 (HLdes_good hq hden n c d)).2
    rw [hF2 n c d (lt_min (by omega) h), qr_int] at this
    rw [show (2 : ZMod q) = qr q (2 : ℚ) by
      rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) by simp, qr_int]; simp, ← this]
  · have : HLdes u v lam gco dg n c d = 0 := by simp [HLdes, show s - 1 ≤ n by omega]
    rw [this, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp, qr_int]; simp

theorem HL_domL_real_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q)
    (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) :=
  GF_dom_real_core s q k (HLPhi s q k u v lam gco dg) F2 hs hqodd hk
    (HL_rowDesign_core s q k u v lam gco dg F2 hs hq hden hF2 hk).1 hhalf0 hhalf hdiag hdom hqB x y hxy

/-! ## The level-0 constant of `H_s` -/

variable {s : ℕ}

lemma F2Hf_le_CH2 (hs : 2 ≤ s) (c d : Fin s) : |F2Hf s 0 c d| ≤ (CH2 s : ℤ) := by
  have haC : (aH2 s c : ℤ) ≤ CH2 s := by
    exact_mod_cast Finset.le_sup (f := fun c : Fin s => aH2 s c) (mem_univ c)
  by_cases hcd : c = d
  · subst hcd
    rw [F2Hf_diag0 hs, abs_neg, abs_of_nonneg (by positivity)]
    exact haC
  · have h1 := M2_le_mx (F2Hf s) 0 (by omega) c d
    have e0 : M2 (F2Hf s) 0 c d = F2Hf s 0 c d := by simp [M2]
    rw [e0] at h1
    have h2 : (mx (F2Hf s) c d : ℤ) ≤ A2 s (F2Hf s) c := by
      rw [A2_eq]
      exact Finset.single_le_sum (f := fun d => (mx (F2Hf s) c d : ℤ)) (fun d _ => by positivity)
        (mem_erase.mpr ⟨Ne.symm hcd, mem_univ d⟩)
    have h3 : (A2 s (F2Hf s) c : ℤ) ≤ aH2 s c := by
      rw [A2_H]; unfold aH2; split_ifs <;> push_cast <;> omega
    linarith

lemma C2max_H_le (hs : 2 ≤ s) : C2max s (F2Hf s) ≤ CH2 s := by
  unfold C2max
  refine Finset.sup_le fun c _ => Finset.sup_le fun d _ => ?_
  have := F2Hf_le_CH2 hs c d
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

theorem HL_upper_core (s q k : ℕ) (hs : 3 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqC : 2 * s * CH2 s + 2 < q) (hk : 1 ≤ k) :
    ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
      Real.sqrt (∑ c, (((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℝ) -
          (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
        ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + Real.sqrt s * ((CH2 s : ℝ) + 1) / q) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  have hs2 : 2 ≤ s := by omega
  have hadm := adm_H hs2 q hq hqs
  have hq2 : q ≠ 2 := by omega
  have hden := den_H (s := s) q hq hq2
  obtain ⟨hrow, _⟩ := HL_rowDesign_core s q k uH vH (lamH s) gcoH (dgH s) (F2Hf s) hs2 hadm hden
    (fun x c d _ => hF2_H x c d) hk
  have hCle := C2max_H_le (s := s) hs2
  have hqC' : 2 * s * C2max s (F2Hf s) + 2 < q := by
    have : 2 * s * C2max s (F2Hf s) ≤ 2 * s * CH2 s := Nat.mul_le_mul_left _ hCle
    omega
  obtain ⟨x, y, hxy, h⟩ := GF_upper_core s q k (HLPhi s q k uH vH (lamH s) gcoH (dgH s)) (F2Hf s)
    hs hq hk hrow (F2Hf_half0 hs2) hqC'
  refine ⟨x, y, hxy, h.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have : (C2max s (F2Hf s) : ℝ) ≤ CH2 s := by exact_mod_cast hCle
  have : Real.sqrt s * ((C2max s (F2Hf s) : ℝ) + 1) / q ≤ Real.sqrt s * ((CH2 s : ℝ) + 1) / q := by
    apply div_le_div_of_nonneg_right _ hq0.le
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
  linarith

/-! ## The limit -/

theorem HL_limit_core (s : ℕ) (hs : 3 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ q k : ℕ, q.Prime → P ≤ q → 1 ≤ k →
      (∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (min (Real.sqrt s / 2) (Real.sqrt 2) - ε) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
              ((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℤ) -
                (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2)) ∧
      ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
        Real.sqrt (∑ c, (((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℝ) -
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
          ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + ε) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  set K : ℝ := Real.sqrt s * (((BH s) : ℝ) + (CH2 s) + 2) / ε
  refine ⟨⌈K⌉₊ + 2 * s + 2 * (BH s) + 2 * s * (CH2 s) + 3, fun q k hq hP hk => ?_⟩
  have hs2 : 2 ≤ s := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hKq : K ≤ q := by
    have := Nat.le_ceil K
    have : (⌈K⌉₊ : ℝ) ≤ q := by exact_mod_cast (show ⌈K⌉₊ ≤ q by omega)
    linarith
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hKe : Real.sqrt s * (((BH s) : ℝ) + (CH2 s) + 2) ≤ ε * q := by
    have := mul_le_mul_of_nonneg_left hKq hε.le
    simp only [K] at this
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hB0 : (0 : ℝ) ≤ (BH s) := by positivity
  have hC0 : (0 : ℝ) ≤ (CH2 s) := by positivity
  have hNp : (0 : ℝ) < ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by positivity
  have h22 : Real.sqrt 2 ≤ Real.sqrt s := Real.sqrt_le_sqrt (by exact_mod_cast hs2)
  constructor
  · intro x y hxy
    have h := HL_main_real s q k hs2 hq (by omega) (by omega) hk x y hxy
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hNp.le) h
    have hη : Real.sqrt s * ((((BH s) : ℝ) + 1) / q) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hq0]
      nlinarith
    have hη0 : 0 ≤ (((BH s) : ℝ) + 1) / q := by positivity
    have h2η : Real.sqrt 2 * ((((BH s) : ℝ) + 1) / q) ≤ Real.sqrt s * ((((BH s) : ℝ) + 1) / q) :=
      mul_le_mul_of_nonneg_right h22 hη0
    apply le_min
    · have := min_le_left (Real.sqrt s / 2) (Real.sqrt 2)
      nlinarith
    · have := min_le_right (Real.sqrt s / 2) (Real.sqrt 2)
      nlinarith
  · obtain ⟨x, y, hxy, h⟩ := HL_upper_core s q k hs hq (by omega) (by omega) hk
    refine ⟨x, y, hxy, h.trans (mul_le_mul_of_nonneg_right ?_ hNp.le)⟩
    have : Real.sqrt s * (((CH2 s) : ℝ) + 1) / q ≤ ε := by
      rw [div_le_iff₀ hq0]; nlinarith
    linarith

/-! ## Growth of `B_s` -/

lemma gcoHZ_sum_F2Hf (x : ℕ) (c d : Fin s) (hcd : c ≠ d) (hx : x < s - 1) :
    F2Hf s x c d = ∑ n' ∈ range (x + 1), gcoHZ x n' * (QH s c d * (uH c - vH d) ^ (s - 2 - n')) := by
  simp [F2Hf, show ¬ s - 1 ≤ x by omega, hcd]

/-- The terms `T_n = Q e^(s-2-n)`. -/
def TH (s : ℕ) (c d : Fin s) (n : ℕ) : ℤ := QH s c d * (uH c - vH d) ^ (s - 2 - n)

lemma F2Hf_val (x : ℕ) (c d : Fin s) (hcd : c ≠ d) (hx : x < s - 1) :
    F2Hf s x c d = if x = 0 then TH s c d 0 else if x = 1 then 2 * TH s c d 1
      else 2 * TH s c d x - 2 * TH s c d (x - 1) := by
  rw [gcoHZ_sum_F2Hf x c d hcd hx]
  rcases Nat.lt_or_ge x 2 with h | h
  · interval_cases x
    · simp [gcoHZ, TH]
    · simp [Finset.sum_range_succ, gcoHZ, TH]
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
    rw [if_neg (by omega), if_neg (by omega), Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun n hn => by
      have := mem_range.mp hn
      simp [gcoHZ, show n ≠ y + 2 by omega, show n ≠ y + 1 by omega])]
    simp [gcoHZ, TH, show y + 2 - 1 = y + 1 by omega]
    ring

lemma M2_H_val (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j < s - 1) :
    M2 (F2Hf s) j c d = TH s c d 0 + (if j = 0 then 0 else 2 * TH s c d j) := by
  induction j with
  | zero => simp [M2, F2Hf_val 0 c d hcd (by omega)]
  | succ j ih =>
    rw [show M2 (F2Hf s) (j + 1) c d = M2 (F2Hf s) j c d + F2Hf s (j + 1) c d by
      simp [M2, Finset.sum_range_succ], ih (by omega), F2Hf_val (j + 1) c d hcd hj]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show j + 1 - 1 = j by omega]
      ring

lemma eH_one_le (c d : Fin s) : 1 ≤ |uH c - vH d| := Int.one_le_abs (eH_ne c d)

lemma TH_abs_le (c d : Fin s) (n : ℕ) : |TH s c d n| ≤ |QH s c d| * |uH c - vH d| ^ (s - 2) := by
  unfold TH
  rw [abs_mul, abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ (eH_one_le c d) (by omega)

/-- `|Λ_c| ≤ (2s-1)^((s-1)²)`. -/
lemma LamH_abs_le (c : Fin s) : |LamH s c| ≤ (((2 * s - 1) ^ ((s - 1) ^ 2) : ℕ) : ℤ) := by
  unfold LamH
  rw [Finset.abs_prod]
  have hcard : (univ.erase c).card = s - 1 := by simp
  have hs1 : 1 ≤ s := by have := c.isLt; omega
  calc ∏ d ∈ univ.erase c, |(uH c - vH d) ^ (s - 1)|
      ≤ ∏ _d ∈ univ.erase c, (((2 * s - 1 : ℕ) : ℤ)) ^ (s - 1) := by
        gcongr with d hd
        rw [abs_pow]
        apply pow_le_pow_left₀ (abs_nonneg _)
        have := eH_abs c d
        push_cast [hs1]; omega
    _ = (((2 * s - 1) ^ ((s - 1) ^ 2) : ℕ) : ℤ) := by
        rw [prod_const, hcard, ← pow_mul, sq]; push_cast; rfl

lemma M2_H_le (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j < s - 1) :
    (M2 (F2Hf s) j c d).natAbs ≤ 3 * (2 * s - 1) ^ ((s - 1) ^ 2) := by
  have hT := fun n => TH_abs_le (s := s) c d n
  have hQe : |QH s c d| * |uH c - vH d| ^ (s - 2) ≤ |LamH s c| := by
    rw [LamH_split c d hcd, abs_mul, abs_pow, mul_comm (|uH c - vH d| ^ (s - 1))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (eH_one_le c d) (by omega)) (abs_nonneg _)
  have hL : (|LamH s c| : ℤ) ≤ ((2 * s - 1) ^ ((s - 1) ^ 2) : ℕ) := LamH_abs_le c
  have hM : |M2 (F2Hf s) j c d| ≤ 3 * ((2 * s - 1) ^ ((s - 1) ^ 2) : ℕ) := by
    rw [M2_H_val c d hcd j hj]
    have h0 := hT 0; have hj' := hT j
    split_ifs
    · rw [add_zero]; linarith
    · have := abs_add_le (TH s c d 0) (2 * TH s c d j)
      rw [abs_mul, abs_two] at this
      linarith
  rw [Int.abs_eq_natAbs] at hM
  exact_mod_cast hM

theorem HL_Bbound_core (s : ℕ) (hs : 2 ≤ s) :
    BH s ≤ 6 * (s - 1) * (2 * s - 1) ^ ((s - 1) ^ 2) + 2 ∧ BH s ≤ (2 * s) ^ (s ^ 2) := by
  set X := (2 * s - 1) ^ ((s - 1) ^ 2) with hX
  have hmx : ∀ c d : Fin s, c ≠ d → mx (F2Hf s) c d ≤ 3 * X := by
    intro c d hcd
    exact Finset.sup_le fun j hj => M2_H_le c d hcd j (mem_range.mp hj)
  have hA : ∀ c : Fin s, A2 s (F2H0 s) c ≤ (s - 1) * (3 * X) := by
    intro c
    rw [← A2_H]
    have := A2_eq (F2Hf s) c
    have h : A2 s (F2Hf s) c = ∑ d ∈ univ.erase c, mx (F2Hf s) c d := by
      unfold A2 mx; rfl
    rw [h]
    calc ∑ d ∈ univ.erase c, mx (F2Hf s) c d ≤ ∑ _d ∈ univ.erase c, 3 * X :=
          Finset.sum_le_sum fun d hd => hmx c d (Ne.symm (ne_of_mem_erase hd))
      _ = (s - 1) * (3 * X) := by simp
  have hB : BH s ≤ 6 * (s - 1) * X + 1 := by
    unfold BH
    refine Finset.sup_le fun c _ => ?_
    have := hA c
    unfold aH2
    split_ifs <;> nlinarith
  refine ⟨by omega, ?_⟩
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hXle : X ≤ (2 * s) ^ ((s - 1) ^ 2) := Nat.pow_le_pow_left (by omega) _
  have h6 : 6 * s ≤ (2 * s) ^ (2 * s - 1) := by
    calc 6 * s ≤ 8 * s := by omega
      _ ≤ 8 * s * (s * s) := Nat.le_mul_of_pos_right _ (by positivity)
      _ = (2 * s) ^ 3 := by ring
      _ ≤ (2 * s) ^ (2 * s - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hexp : (2 * s) ^ (s ^ 2) = (2 * s) ^ (2 * s - 1) * (2 * s) ^ ((s - 1) ^ 2) := by
    rw [← pow_add]; congr 1
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring_nf; omega
  calc BH s ≤ 6 * (s - 1) * X + 1 := hB
    _ ≤ 6 * s * X := by
        have : 6 * (s - 1) * X + 6 * X = 6 * s * X := by
          rw [← add_mul, ← mul_add_one]; congr 2; omega
        omega
    _ ≤ (2 * s) ^ (2 * s - 1) * (2 * s) ^ ((s - 1) ^ 2) := Nat.mul_le_mul h6 hXle
    _ = (2 * s) ^ (s ^ 2) := hexp.symm

end

end Z3NetHL.Proofs
