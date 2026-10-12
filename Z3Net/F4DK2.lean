module
public import Z3Net.FDsep
public import Z3Net.FTsk
public import Z3Net.FRemK

@[expose] public section

/-!
# Entry F, stage 6: `prop:4DK2`, the design `A♯` in dimension four

* `As_residual_core`: the places `(0, -1, ∞, 1)` are admissible over `ℤ[1/10]` and `(λ', U')` of
  `app:designs` solves the residual problem of `A♯`; the identities are checked in `ℚ` through
  the injective map `ℤ[1/10] → ℚ`;
* `As_unit_core`, `As_net_core`: `cor:tsk`;
* `As_sep_core`: `lem:Ss` with the bound `BAs q`; for `7 ≤ q ≤ 21` (`gcd(q, 10) = 1`) every
  step is checked in the kernel, for `q ≥ 23` the backward coordinates of every step give a
  quadratic in `q - 23` with nonnegative coefficients (checked in the kernel).
-/

namespace Z3NetF.Proofs.As

open Finset Z3NetF

abbrev R10 := Localization.Away (10 : ℤ)

noncomputable def ι : R10 →+* ℚ :=
  IsLocalization.Away.lift (10 : ℤ) (g := Int.castRingHom ℚ) (by norm_num)

lemma ι_inj : Function.Injective ι := by
  unfold ι
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    have := IsLocalization.injective (M := Submonoid.powers (10 : ℤ)) R10
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : ℤ) ≠ 0)) h
    simp [this]
  · intro h
    have hx : (x : ℚ) = y := by simpa using h
    have : x = y := by exact_mod_cast hx
    rw [this]

lemma unit10 : IsUnit (10 : R10) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := R10) (10 : ℤ)
  simpa using h

lemma unit2 : IsUnit (2 : R10) := by
  have h := unit10
  rw [show (10 : R10) = 2 * 5 by norm_num] at h
  exact isUnit_of_mul_isUnit_left h

lemma unit5 : IsUnit (5 : R10) := by
  have h := unit10
  rw [show (10 : R10) = 2 * 5 by norm_num] at h
  exact isUnit_of_mul_isUnit_right h

/-- `±2^i 5^j` are units. -/
lemma unit_int (a : ℤ) (h : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 8 ∨ a = -10) :
    IsUnit (a : R10) := by
  have h2 := unit2; have h5 := unit5
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · rw [show ((-1 : ℤ) : R10) = -1 by norm_num]; exact (isUnit_one (M := R10)).neg
  · rw [show ((2 : ℤ) : R10) = 2 by norm_num]; exact h2
  · rw [show ((-2 : ℤ) : R10) = -2 by norm_num]; exact h2.neg
  · have : ((8 : ℤ) : R10) = 2 * 2 * 2 := by norm_num
    rw [this]; exact (h2.mul h2).mul h2
  · have : ((-10 : ℤ) : R10) = -(2 * 5) := by norm_num
    rw [this]; exact (h2.mul h5).neg

lemma ι_inv (a : ℤ) (h : IsUnit (a : R10)) : ι (Ring.inverse (a : R10)) = (a : ℚ)⁻¹ := by
  have h1 : Ring.inverse (a : R10) * (a : R10) = 1 := Ring.inverse_mul_cancel _ h
  have h2 := congrArg ι h1
  rw [map_mul, map_one, map_intCast] at h2
  exact eq_inv_of_mul_eq_one_left h2

def xR : Fin 4 → R10 := fun c => (xAs c : R10)

lemma xR_sub (c d : Fin 4) : xR c - xR d = ((xAs c - xAs d : ℤ) : R10) := by
  simp [xR]

lemma diff_unit (c d : Fin 4) (hc : c ≠ 2) (hd : d ≠ 2) (hcd : c ≠ d) :
    xAs c - xAs d = 1 ∨ xAs c - xAs d = -1 ∨ xAs c - xAs d = 2 ∨ xAs c - xAs d = -2 ∨
      xAs c - xAs d = 8 ∨ xAs c - xAs d = -10 := by
  fin_cases c <;> fin_cases d <;> simp_all [xAs]

lemma places : PlacesOK (2 : Fin 4) xR := by
  intro c d hc hd hcd
  rw [xR_sub]
  exact unit_int _ (diff_unit c d hc hd hcd)

/-- `w_cd` in `ℚ`. -/
def wQ (c d : Fin 4) : ℚ := if c = 2 ∨ d = 2 then 1 else ((xAs c - xAs d : ℤ) : ℚ)⁻¹

/-- `y_cd` in `ℚ`. -/
def yQ (c d : Fin 4) : ℚ :=
  if c = 2 then 0 else if d = 2 then (xAs c : ℚ) else ((xAs c - xAs d : ℤ) : ℚ)⁻¹

lemma ι_wN (c d : Fin 4) (hcd : c ≠ d) : ι (wN (2 : Fin 4) xR c d) = wQ c d := by
  unfold wN wQ
  split_ifs with h
  · simp
  · push Not at h
    rw [xR_sub, ι_inv _ (unit_int _ (diff_unit c d h.1 h.2 hcd))]

lemma ι_yN (c d : Fin 4) (hcd : c ≠ d) : ι (yN (2 : Fin 4) xR c d) = yQ c d := by
  unfold yN yQ
  split_ifs with h1 h2
  · simp
  · simp [xR]
  · rw [xR_sub, ι_inv _ (unit_int _ (diff_unit c d h1 h2 hcd))]

theorem As_residual_core :
    PlacesOK (2 : Fin 4) (fun c => (xAs c : R10)) ∧
      Residual (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
        (fun c => (lamAs c : R10)) (fun d n' n => (UrAs d n' n : R10)) := by
  refine ⟨places, ?_, ?_, ?_, ?_⟩
  · intro c
    exact unit_int _ (by fin_cases c <;> simp [lamAs])
  · intro d n' n hn hn'
    have : UrAs d n' n = 0 := by
      fin_cases d <;> interval_cases n' <;> interval_cases n <;> simp_all [UrAs, UAs]
    simp [this]
  · intro d n hn
    exact unit_int _ (by fin_cases d <;> interval_cases n <;> simp [UrAs, UAs])
  · intro c d hcd n hn
    apply ι_inj
    rw [map_intCast, map_mul, map_intCast, map_sum]
    simp only [map_mul, map_pow, map_intCast]
    have hw : ι (wN (2 : Fin 4) (fun c => (xAs c : R10)) c d) = wQ c d := ι_wN c d hcd
    have hy : ι (yN (2 : Fin 4) (fun c => (xAs c : R10)) c d) = yQ c d := ι_yN c d hcd
    rw [hw, hy]
    fin_cases c <;> fin_cases d <;> (first | exact absurd rfl hcd | skip) <;>
      interval_cases n <;>
      norm_num [wQ, yQ, FAs, lamAs, UrAs, UAs, xAs, Finset.sum_range_succ]

theorem As_unit_core (k : ℕ) (β : Fin 4 → ℕ → ℕ → R10) (d : Fin 4 → ℕ)
    (hd : ∑ c, d c = 4 * k) : IsUnit (boxMatrix (PAs k β) d).det :=
  tsk_unit_core (k := k) (inf := (2 : Fin 4)) (x := fun c => (xAs c : R10)) As_residual_core.1
    (fun n c d => (FAs n c d : R10)) (fun c => (lamAs c : R10))
    (fun d n' n => (UrAs d n' n : R10)) β As_residual_core.2 d hd

theorem As_net_core {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) (k : ℕ) (β : Fin 4 → ℕ → ℕ → R10) :
    IsNet0 4 q (4 * k) (digPoint q (4 * k) fun c => (PAs k β c).map ψ) :=
  tsk_net_core (k := k) (inf := (2 : Fin 4)) (x := fun c => (xAs c : R10)) ψ As_residual_core.1
    (fun n c d => (FAs n c d : R10)) (fun c => (lamAs c : R10))
    (fun d n' n => (UrAs d n' n : R10)) β As_residual_core.2

/-! ## The relaxation of `A♯` -/

/-- Steps coded by `Fin 3` digits (`e_d = code - 1`). -/
def eC (e0 e1 e2 e3 : Fin 3) : Fin 4 → ℤ := ![(e0 : ℤ) - 1, (e1 : ℤ) - 1, (e2 : ℤ) - 1, (e3 : ℤ) - 1]
def jC (j0 j1 j2 j3 : Fin 3) : Fin 4 → ℕ := ![(j0 : ℕ), j1, j2, j3]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_7 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 7 ≤ ∑ i, bval 7 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_7 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 7 ≤ ∑ i, bval 7 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_9 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 9 ≤ ∑ i, bval 9 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_9 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 9 ≤ ∑ i, bval 9 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_11 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 11 ≤ ∑ i, bval 11 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_11 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 11 ≤ ∑ i, bval 11 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_13 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 13 ≤ ∑ i, bval 13 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_13 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 13 ≤ ∑ i, bval 13 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_17 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 17 ≤ ∑ i, bval 17 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_17 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 17 ≤ ∑ i, bval 17 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_19 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 19 ≤ ∑ i, bval 19 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_19 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 19 ≤ ∑ i, bval 19 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small3_21 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 21 ≤ ∑ i, bval 21 FAs 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) i ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma small2_21 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    BAs 21 ≤ ∑ i, bval 21 FAs 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] i ^ 2 := by
  decide +kernel

/-! ### `q ≥ 23`: the backward coordinates -/

/-- The jitter `jit_i` of `lem:Ss`. -/
def jitA (e : Fin 4 → ℤ) (i : Fin 4) : ℤ := if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1

/-- The cost `|σ_i| + jit_i` of a backward coordinate. -/
def costA (L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (i : Fin 4) : ℤ := |sigma FAs L e j i| + jitA e i

/-- The `q`-independent tail criterion of a step: `|σ_i| ≤ 8`, some backward coordinate, a single
one costs `≤ 2`, two or more give `∑ (q - c_i)² - (q-2)²` with nonnegative coefficients in
`t = q - 23`. -/
def Crit (L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) : Prop :=
  (∀ i, |sigma FAs L e j i| ≤ 8) ∧ (bwd FAs L e j).Nonempty ∧
    ((bwd FAs L e j).card = 1 → ∀ i ∈ bwd FAs L e j, costA L e j i ≤ 2) ∧
    (2 ≤ (bwd FAs L e j).card → 0 ≤ 2 * ∑ i ∈ bwd FAs L e j, (23 - costA L e j i) - 42 ∧
      0 ≤ ∑ i ∈ bwd FAs L e j, (23 - costA L e j i) ^ 2 - 441)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma crit3 : ∀ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    Crit 3 (eC e0 e1 e2 e3) (jC j0 j1 j2 j3) := by
  unfold Crit costA jitA
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
lemma crit2 : ∀ e0 e1 e2 e3 : Fin 3, ∀ j0 j1 j2 j3 : Fin 2, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
    (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) →
    Crit 2 (eC e0 e1 e2 e3) ![(j0 : ℕ), j1, j2, j3] := by
  unfold Crit costA jitA
  decide +kernel

lemma tail_bound (L : ℕ) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hc : Crit L e j) (q : ℕ) (hq : 23 ≤ q) :
    ((q : ℤ) - 2) ^ 2 ≤ ∑ i, bval q FAs L e j i ^ 2 := by
  obtain ⟨h8, hne, h1, h2⟩ := hc
  have hb : ∀ i ∈ bwd FAs L e j, bval q FAs L e j i = q - costA L e j i := by
    intro i hi
    have hi' := (Z3NetF.Proofs.RemK.mem_bwd FAs L e j i).1 hi
    rw [Z3NetF.Proofs.RemK.bv_back q FAs L e j i (he i) (by have := h8 i; omega) hi', costA, jitA]
    ring
  have hsub : ∑ i ∈ bwd FAs L e j, bval q FAs L e j i ^ 2 ≤ ∑ i, bval q FAs L e j i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine le_trans ?_ hsub
  rw [Finset.sum_congr rfl (fun i hi => by rw [hb i hi])]
  have hcost : ∀ i, 0 ≤ costA L e j i := fun i => by
    unfold costA jitA; split_ifs <;> positivity
  by_cases hc1 : (bwd FAs L e j).card = 1
  · obtain ⟨b, hb1⟩ := Finset.card_eq_one.1 hc1
    have hcb := h1 hc1 b (by rw [hb1]; exact mem_singleton_self b)
    rw [hb1, sum_singleton]
    have := hcost b
    exact pow_le_pow_left₀ (by omega) (by linarith) 2
  · have hc2 : 2 ≤ (bwd FAs L e j).card := by
      have := Finset.card_pos.2 hne; omega
    obtain ⟨ha1, ha0⟩ := h2 hc2
    set t : ℤ := (q : ℤ) - 23 with ht
    have ht0 : 0 ≤ t := by omega
    have hexp : ∑ i ∈ bwd FAs L e j, ((q : ℤ) - costA L e j i) ^ 2 =
        ((bwd FAs L e j).card : ℤ) * t ^ 2 + 2 * t * ∑ i ∈ bwd FAs L e j, (23 - costA L e j i) +
          ∑ i ∈ bwd FAs L e j, (23 - costA L e j i) ^ 2 := by
      rw [Finset.mul_sum]
      rw [show ((bwd FAs L e j).card : ℤ) * t ^ 2 = ∑ _i ∈ bwd FAs L e j, t ^ 2 by
        rw [Finset.sum_const, nsmul_eq_mul]]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ht]; ring
    rw [hexp]
    have hcard : (2 : ℤ) ≤ ((bwd FAs L e j).card : ℤ) := by exact_mod_cast hc2
    have hq' : ((q : ℤ) - 2) = t + 21 := by rw [ht]; ring
    rw [hq']
    nlinarith [mul_nonneg ha1 ht0, mul_nonneg (by linarith : (0 : ℤ) ≤ ((bwd FAs L e j).card : ℤ) - 1)
      (sq_nonneg t)]

/-! ### All `q` -/

lemma sigma_canon (L : ℕ) (e : Fin 4 → ℤ) (j j' : Fin 4 → ℕ)
    (hj : ∀ d, e d ≠ 0 → min (j' d) (L - 1) = min (j d) (L - 1)) (i : Fin 4) :
    sigma FAs L e j' i = sigma FAs L e j i := by
  unfold sigma
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : e d = 0
  · rw [h, zero_mul, zero_mul]
  · rw [hj d h]

lemma bval_canon (q L : ℕ) (e : Fin 4 → ℤ) (j j' : Fin 4 → ℕ)
    (hj : ∀ d, e d ≠ 0 → min (j' d) (L - 1) = min (j d) (L - 1)) (i : Fin 4) :
    bval q FAs L e j' i = bval q FAs L e j i := by
  unfold bval; rw [sigma_canon L e j j' hj]

/-- Every step is a coded step (`e = eC …`, carries reduced and `0` on still axes). -/
lemma coded (q L : ℕ) (hL : 2 ≤ L) (hL3 : L ≤ 3) (e : Fin 4 → ℤ) (j : Fin 4 → ℕ)
    (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1) (hne : ∃ d, e d ≠ 0) :
    ∃ e0 e1 e2 e3 j0 j1 j2 j3 : Fin 3, ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
      (e0 ≠ 1 ∨ j0 = 0) ∧ (e1 ≠ 1 ∨ j1 = 0) ∧ (e2 ≠ 1 ∨ j2 = 0) ∧ (e3 ≠ 1 ∨ j3 = 0)) ∧
      (j0 : ℕ) < L ∧ (j1 : ℕ) < L ∧ (j2 : ℕ) < L ∧ (j3 : ℕ) < L ∧
      e = eC e0 e1 e2 e3 ∧ ∀ i, bval q FAs L e (jC j0 j1 j2 j3) i = bval q FAs L e j i := by
  have hc : ∀ d, ((e d + 1).toNat) < 3 := fun d => by have := he d; omega
  have hjc : ∀ d, (if e d = 0 then 0 else min (j d) (L - 1)) < 3 := fun d => by
    split_ifs <;> omega
  set ce : Fin 4 → Fin 3 := fun d => ⟨_, hc d⟩ with hce
  set cj : Fin 4 → Fin 3 := fun d => ⟨_, hjc d⟩ with hcj
  have hce1 : ∀ d, ce d = 1 ↔ e d = 0 := fun d => by
    rw [Fin.ext_iff]; simp only [hce, Fin.val_one]; have := he d; omega
  have hcj0 : ∀ d, e d = 0 → cj d = 0 := fun d h => by
    rw [Fin.ext_iff]; simp [hcj, h]
  have hcjL : ∀ d, (cj d : ℕ) < L := fun d => by
    simp only [hcj]; split_ifs <;> omega
  have hcjm : ∀ d, e d ≠ 0 → min (cj d : ℕ) (L - 1) = min (j d) (L - 1) := fun d h => by
    simp only [hcj, if_neg h]; omega
  have hdisj : ∀ d, ce d ≠ 1 ∨ cj d = 0 := fun d => by
    by_cases h : e d = 0
    · exact Or.inr (hcj0 d h)
    · exact Or.inl (fun h' => h ((hce1 d).1 h'))
  have heq : e = eC (ce 0) (ce 1) (ce 2) (ce 3) := by
    funext d
    have : ∀ d, ((ce d : ℕ) : ℤ) - 1 = e d := fun d => by
      simp only [hce]; have := he d; omega
    fin_cases d <;> simp [eC, this]
  refine ⟨ce 0, ce 1, ce 2, ce 3, cj 0, cj 1, cj 2, cj 3, ⟨?_, hdisj 0, hdisj 1, hdisj 2, hdisj 3⟩,
    hcjL 0, hcjL 1, hcjL 2, hcjL 3, heq, fun i => bval_canon q L e j _ ?_ i⟩
  · obtain ⟨d, hd⟩ := hne
    have hd' : ce d ≠ 1 := fun h => hd ((hce1 d).1 h)
    fin_cases d
    · exact Or.inl hd'
    · exact Or.inr (Or.inl hd')
    · exact Or.inr (Or.inr (Or.inl hd'))
    · exact Or.inr (Or.inr (Or.inr hd'))
  · intro d hd
    have := hcjm d hd
    fin_cases d <;> simpa [jC] using this

lemma hB_all (q L : ℕ) (hq : 7 ≤ q) (hcop : Nat.Coprime 10 q) (hL : L = 2 ∨ L = 3) (k : ℕ)
    (e : Fin 4 → ℤ) (j : Fin 4 → ℕ) (hc : IsConfig k e j) :
    BAs q ≤ ∑ i, bval q FAs L e j i ^ 2 := by
  obtain ⟨he, hne, -⟩ := hc
  obtain ⟨e0, e1, e2, e3, j0, j1, j2, j3, hpre, hj0, hj1, hj2, hj3, heq, hbv⟩ :=
    coded q L (by omega) (by omega) e j he hne
  rw [show (∑ i, bval q FAs L e j i ^ 2) = ∑ i, bval q FAs L e (jC j0 j1 j2 j3) i ^ 2 from
    Finset.sum_congr rfl (fun i _ => by rw [hbv i])]
  subst heq
  by_cases hq23 : 23 ≤ q
  · have hBq : BAs q ≤ ((q : ℤ) - 2) ^ 2 := by
      unfold BAs; rw [if_neg (by omega)]; exact min_le_left _ _
    refine hBq.trans (tail_bound L _ _ he ?_ q hq23)
    rcases hL with rfl | rfl
    · have := crit2 e0 e1 e2 e3 ⟨j0, hj0⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩ (by
        obtain ⟨h0, h1, h2, h3, h4⟩ := hpre
        refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff, Fin.val_zero] at * <;> omega)
      exact this
    · exact crit3 e0 e1 e2 e3 j0 j1 j2 j3 hpre
  · have hcases : q = 7 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 21 := by
      have h2 : ¬ 2 ∣ q := fun h => by
        have := Nat.Coprime.coprime_dvd_right h hcop; norm_num at this
      have h5 : ¬ 5 ∣ q := fun h => by
        have := Nat.Coprime.coprime_dvd_right h hcop; norm_num at this
      omega
    rcases hL with rfl | rfl
    · have hpre2 : ((e0 ≠ 1 ∨ e1 ≠ 1 ∨ e2 ≠ 1 ∨ e3 ≠ 1) ∧
          (e0 ≠ 1 ∨ (⟨j0, hj0⟩ : Fin 2) = 0) ∧ (e1 ≠ 1 ∨ (⟨j1, hj1⟩ : Fin 2) = 0) ∧
          (e2 ≠ 1 ∨ (⟨j2, hj2⟩ : Fin 2) = 0) ∧ (e3 ≠ 1 ∨ (⟨j3, hj3⟩ : Fin 2) = 0)) := by
        obtain ⟨h0, h1, h2, h3, h4⟩ := hpre
        refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff, Fin.val_zero] at * <;> omega
      have hjj : jC j0 j1 j2 j3 = ![(((⟨j0, hj0⟩ : Fin 2) : ℕ)), ((⟨j1, hj1⟩ : Fin 2) : ℕ),
          ((⟨j2, hj2⟩ : Fin 2) : ℕ), ((⟨j3, hj3⟩ : Fin 2) : ℕ)] := rfl
      rw [hjj]
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact small2_7 _ _ _ _ _ _ _ _ hpre2
      · exact small2_9 _ _ _ _ _ _ _ _ hpre2
      · exact small2_11 _ _ _ _ _ _ _ _ hpre2
      · exact small2_13 _ _ _ _ _ _ _ _ hpre2
      · exact small2_17 _ _ _ _ _ _ _ _ hpre2
      · exact small2_19 _ _ _ _ _ _ _ _ hpre2
      · exact small2_21 _ _ _ _ _ _ _ _ hpre2
    · rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact small3_7 _ _ _ _ _ _ _ _ hpre
      · exact small3_9 _ _ _ _ _ _ _ _ hpre
      · exact small3_11 _ _ _ _ _ _ _ _ hpre
      · exact small3_13 _ _ _ _ _ _ _ _ hpre
      · exact small3_17 _ _ _ _ _ _ _ _ hpre
      · exact small3_19 _ _ _ _ _ _ _ _ hpre
      · exact small3_21 _ _ _ _ _ _ _ _ hpre

lemma coprime_of_hom {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) : Nat.Coprime 10 q := by
  have h := unit10.map ψ
  rw [map_ofNat] at h
  exact (ZMod.isUnit_iff_coprime 10 q).1 (by exact_mod_cast h)

theorem As_sep_core {q : ℕ} [NeZero q] (ψ : R10 →+* ZMod q) (hq : 7 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) (β : Fin 4 → ℕ → ℕ → R10)
    (hβ : BetaRel (2 : Fin 4) (fun c => (xAs c : R10)) (fun n c d => (FAs n c d : R10))
      (fun c => (lamAs c : R10)) β)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (4 * k - k)) * BAs q ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (4 * k)) (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) v)
        (digPoint q (4 * k) (fun c => (PAs k β c).map ψ) w) : ℤ) := by
  obtain ⟨hx, hres⟩ := As_residual_core
  set xx : Fin 4 → R10 := fun c => (xAs c : R10)
  set FR : ℕ → Fin 4 → Fin 4 → R10 := fun n c d => (FAs n c d : R10)
  set lam : Fin 4 → R10 := fun c => (lamAs c : R10)
  set Ur : Fin 4 → ℕ → ℕ → R10 := fun d n' n => (UrAs d n' n : R10)
  set Φ : Fin 4 → Fin 4 → Matrix (Fin (4 * k - k)) (Fin k) (ZMod q) :=
    fun c d => (PPhi k (2 : Fin 4) xx FR lam Ur β c d).map ψ with hΦ
  have hgen : (fun c => (PAs k β c).map ψ) = graphGenK (m := 4 * k) (fun _ => k) Φ := by
    funext c
    exact graphGenK_map ψ (m := 4 * k) (fun _ => k) _ c
  rw [hgen]
  set L := min k 3 with hLdef
  have hL : 1 ≤ L := by omega
  have hLk : L ≤ k := min_le_left _ _
  have hcond : ∀ j : Fin k, (k - 1 - (j : ℕ) < 4 - 1 ↔ k - 1 - (j : ℕ) < L) := by
    intro j; have := j.isLt; omega
  have h1 : H1 FAs L Φ := by
    intro c d r hr j
    simp only [hΦ, Matrix.map_apply]
    by_cases hcd : c = d
    · subst hcd
      have e1 : PPhi k (2 : Fin 4) xx FR lam Ur β c c r j =
          if (r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < 4 - 1 then FR (k - 1 - (j : ℕ)) c c else 0 := by
        simp [PPhi]
      rw [e1]
      by_cases hj : k - 1 - (j : ℕ) < 4 - 1
      · rw [if_pos ⟨hr, hj⟩, if_pos ((hcond j).mp hj), map_intCast]
      · rw [if_neg (fun h => hj h.2), if_neg (fun h => hj ((hcond j).mpr h)), map_zero]
    · have e1 : PPhi k (2 : Fin 4) xx FR lam Ur β c d =
          Lmat k (2 : Fin 4) xx lam c * frameGraph R10 k (2 : Fin 4) xx c d *
            Ugauge k (2 : Fin 4) xx Ur β d := by
        simp [PPhi, hcd]
      rw [e1, Gs_row0_core k (2 : Fin 4) xx FR lam Ur β hx hres hβ c d hcd r hr j]
      by_cases hj : k - 1 - (j : ℕ) < 4 - 1
      · rw [if_pos hj, if_pos ((hcond j).mp hj), map_intCast]
      · rw [if_neg hj, if_neg (fun h => hj ((hcond j).mpr h)), map_zero]
  have h2 : H2 Φ := by
    intro c r hr j
    have e1 : PPhi k (2 : Fin 4) xx FR lam Ur β c c r j =
        if (r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < 4 - 1 then FR (k - 1 - (j : ℕ)) c c else 0 := by
      simp [PPhi]
    simp only [hΦ, Matrix.map_apply]
    rw [e1, if_neg (fun h => hr h.1), map_zero]
  have hBq : BAs q ≤ (q : ℤ) ^ 2 := by
    unfold BAs
    split_ifs with h7
    · subst h7; norm_num
    · exact (min_le_left _ _).trans (by nlinarith)
  exact Ss_sep_core 4 q k Φ FAs L (by norm_num) (by omega) (by omega) hL hLk h1 h2 _ hBq
    (fun e j hc => hB_all q L hq (coprime_of_hom ψ) (by omega) k e j hc) v w hvw

end Z3NetF.Proofs.As
