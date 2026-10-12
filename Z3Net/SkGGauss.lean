module
public import Mathlib
public import Z3Net.S2Defs
public import Z3Net.SkGBase

@[expose] public section

/-!
# Entry S2, `lem:skellat`(G): the Gaussian lattice

With `|u|_∞ ≤ B` the relations `z ≡ A x (mod p)` are exact, so `Z = z_1 + i z_2 =
∑_d x_d col_d` (`col_d = Ω_{d+1}`, resp. `i Ω_{r-1}`) is divisible by `ω_1 = Ω_1`, and
`N(Z) ≤ 2B² < N(ω_1)` forces `Z = 0`. Inductively, `ω_{t+1} ∣ x_t` (`Ω_{t+2}` divides every later
column), and a rational integer is divisible by `c + i` only if it is divisible by `c² + 1 > B`,
so `x_t = 0`; finally `(x_{r-1} + i x_r) Ω_{r-1} = 0`.
-/

namespace Z3NetF.Proofs

open Finset

namespace SkG

lemma re_sum' (S : Finset ℕ) (f : ℕ → GaussianInt) : (∑ n ∈ S, f n).re = ∑ n ∈ S, (f n).re := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, Zsqrtd.re_add, ih]

lemma im_sum' (S : Finset ℕ) (f : ℕ → GaussianInt) : (∑ n ∈ S, f n).im = ∑ n ∈ S, (f n).im := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, Zsqrtd.im_add, ih]

lemma gaussOmega_ne_zero (c : ℕ → ℤ) (l : ℕ) : gaussOmega c l ≠ 0 := by
  rw [gaussOmega, prod_ne_zero_iff]
  intro j _ h
  have := congrArg Zsqrtd.im h
  simp at this

lemma gaussOmega_dvd (c : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) : gaussOmega c a ∣ gaussOmega c b :=
  prod_dvd_prod_of_subset _ _ _ (range_subset_range.mpr hab)

lemma gcol_dvd (r : ℕ) (c : ℕ → ℤ) (t n : ℕ) (h1 : t ≤ n + 1) (h2 : t ≤ r - 1) :
    gaussOmega c t ∣ gcol r c n := by
  unfold gcol
  split_ifs with h
  · exact gaussOmega_dvd c h1
  · exact Dvd.dvd.mul_left (gaussOmega_dvd c h2) _

/-- A rational integer divisible by `a + i` is divisible by `a² + 1`. -/
lemma dvd_of_mk_dvd (a n : ℤ) (h : (⟨a, 1⟩ : GaussianInt) ∣ (n : GaussianInt)) : a ^ 2 + 1 ∣ n := by
  obtain ⟨w, hw⟩ := h
  have hre := congrArg Zsqrtd.re hw
  have him := congrArg Zsqrtd.im hw
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  refine ⟨-w.im, ?_⟩
  have : w.re = -(a * w.im) := by linarith
  rw [hre, this]; ring

lemma eq_of_dvd_of_abs_lt' {p a b : ℤ} (h : p ∣ a - b) (hab : |a - b| < p) : a = b :=
  sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd h hab)

end SkG

theorem skellat_G (r p B : ℕ) (hr : 3 ≤ r) (hB : 1 ≤ B) (c : ℕ → ℤ)
    (hc1 : Real.sqrt 2 * (B : ℝ) < (c 0 : ℝ)) (hc : ∀ l, 1 ≤ l → l + 2 ≤ r → (B : ℤ) < c l ^ 2 + 1)
    (hp : ∀ i : Fin 2, (B : ℤ) * (1 + ∑ d ∈ range r, |gaussA r c i d|) < p)
    (x : Fin r → ℤ) (z : Fin 2 → ℤ)
    (hz : ∀ i, (p : ℤ) ∣ z i - ∑ d : Fin r, gaussA r c i (d : ℕ) * x d) (hne : ¬(x = 0 ∧ z = 0)) :
    (B : ℤ) + 1 ≤ |z 0| ∨ (B : ℤ) + 1 ≤ |z 1| ∨ ∃ d, (B : ℤ) + 1 ≤ |x d| := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hz0, hz1, hx⟩ := hcon
  set X : ℕ → ℤ := fun n => if h : n < r then x ⟨n, h⟩ else 0 with hX
  have hXb : ∀ n, |X n| ≤ B := by
    intro n; simp only [hX]; split_ifs with h
    · have := hx ⟨n, h⟩; omega
    · simp
  have hsum : ∀ i : Fin 2, ∑ d : Fin r, gaussA r c i (d : ℕ) * x d =
      ∑ n ∈ range r, gaussA r c i n * X n := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun d _ => ?_
    simp [hX, d.isLt]
  have hzb : ∀ i : Fin 2, |z i| ≤ B := by
    intro i; fin_cases i
    · simp; omega
    · simp; omega
  -- exactness
  have hexact : ∀ i : Fin 2, z i = ∑ n ∈ range r, gaussA r c i n * X n := by
    intro i
    have hd := hz i
    rw [hsum i] at hd
    apply SkG.eq_of_dvd_of_abs_lt' hd
    have h1 : |∑ n ∈ range r, gaussA r c i n * X n| ≤ ∑ n ∈ range r, |gaussA r c i n| * B := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb n) (abs_nonneg _)
    rw [← sum_mul] at h1
    have h2 := abs_sub (z i) (∑ n ∈ range r, gaussA r c i n * X n)
    have h3 := hp i
    nlinarith [hzb i]
  -- the Gaussian integer `Z`
  set Z : GaussianInt := ⟨z 0, z 1⟩ with hZ
  have hZsum : Z = ∑ n ∈ range r, (X n : GaussianInt) * SkG.gcol r c n := by
    apply Zsqrtd.ext
    · rw [SkG.re_sum', hZ]; simp only
      rw [hexact 0]
      refine sum_congr rfl fun n _ => ?_
      rw [Zsqrtd.re_smul, SkG.gaussA_zero]; ring
    · rw [SkG.im_sum', hZ]; simp only
      rw [hexact 1]
      refine sum_congr rfl fun n _ => ?_
      rw [Zsqrtd.im_smul, SkG.gaussA_one]; ring
  -- step 1: `Z = 0`
  have hZ0 : Z = 0 := by
    have hdvd : gaussOmega c 1 ∣ Z := by
      rw [hZsum]
      exact dvd_sum fun n _ => Dvd.dvd.mul_left (SkG.gcol_dvd r c 1 n (by omega) (by omega)) _
    obtain ⟨W, hW⟩ := hdvd
    have hN := congrArg Zsqrtd.norm hW
    rw [Zsqrtd.norm_mul, SkG.norm_gaussOmega] at hN
    simp only [range_one, prod_singleton] at hN
    have hNZ : Z.norm ≤ 2 * (B : ℤ) ^ 2 := by
      rw [SkG.norm_eq, hZ]
      simp only
      have := sq_abs (z 0); have := sq_abs (z 1)
      have h0 := hzb 0; have h1 := hzb 1
      nlinarith [abs_nonneg (z 0), abs_nonneg (z 1)]
    have hc0 : 2 * (B : ℤ) ^ 2 < c 0 ^ 2 := by
      have hs : (0 : ℝ) ≤ Real.sqrt 2 * B := by positivity
      have : (Real.sqrt 2 * B) ^ 2 < (c 0 : ℝ) ^ 2 := by
        exact pow_lt_pow_left₀ hc1 hs (by norm_num)
      rw [mul_pow, Real.sq_sqrt (by norm_num)] at this
      exact_mod_cast this
    by_contra hZne
    have hWne : W ≠ 0 := by rintro rfl; simp at hW; exact hZne hW
    have hWn : 1 ≤ W.norm := GaussianInt.norm_pos.mpr hWne
    nlinarith
  -- step 2: `X t = 0` for `t < r - 2`
  have hlow : ∀ t, t < r - 2 → X t = 0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have h0 : (0 : GaussianInt) = (X t : GaussianInt) * gaussOmega c (t + 1) +
          ∑ n ∈ (range r).erase t, (X n : GaussianInt) * SkG.gcol r c n := by
        rw [← hZ0, hZsum, ← add_sum_erase _ _ (mem_range.mpr (show t < r by omega))]
        congr 2
        unfold SkG.gcol; rw [if_pos (by omega)]
      have hrest : gaussOmega c (t + 2) ∣
          ∑ n ∈ (range r).erase t, (X n : GaussianInt) * SkG.gcol r c n := by
        refine dvd_sum fun n hn => ?_
        rcases lt_or_gt_of_ne (ne_of_mem_erase hn) with h | h
        · rw [ih n h (by omega)]; simp
        · exact Dvd.dvd.mul_left (SkG.gcol_dvd r c (t + 2) n (by omega) (by omega)) _
      have hmain : gaussOmega c (t + 1) * ⟨c (t + 1), 1⟩ ∣
          gaussOmega c (t + 1) * (X t : GaussianInt) := by
        rw [← SkG.gaussOmega_succ, mul_comm (gaussOmega c (t + 1))]
        have : (X t : GaussianInt) * gaussOmega c (t + 1) =
            -∑ n ∈ (range r).erase t, (X n : GaussianInt) * SkG.gcol r c n := by
          linear_combination -h0
        rw [this]; exact (dvd_neg).mpr hrest
      have hd := (mul_dvd_mul_iff_left (SkG.gaussOmega_ne_zero c (t + 1))).mp hmain
      have hd' := SkG.dvd_of_mk_dvd _ _ hd
      have hct := hc (t + 1) (by omega) (by omega)
      exact Int.eq_zero_of_abs_lt_dvd hd' (by have := hXb t; nlinarith [sq_nonneg (c (t + 1))])
  -- step 3: the last two coordinates
  have htop : X (r - 2) = 0 ∧ X (r - 1) = 0 := by
    have h0 := hZsum
    rw [hZ0] at h0
    obtain ⟨n, hn⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
    rw [hn, sum_range_succ, sum_range_succ,
      sum_eq_zero (fun t ht => by rw [hlow t (by simp at ht; omega)]; simp), zero_add] at h0
    have e1 : SkG.gcol (n + 2) c n = gaussOmega c (n + 1) := by
      unfold SkG.gcol; rw [if_pos (by omega)]
    have e2 : SkG.gcol (n + 2) c (n + 1) = ⟨0, 1⟩ * gaussOmega c (n + 1) := by
      unfold SkG.gcol; rw [if_neg (by omega), show n + 2 - 1 = n + 1 by omega]
    rw [e1, e2] at h0
    have h1 : ((X n : GaussianInt) + ⟨0, 1⟩ * (X (n + 1) : GaussianInt)) * gaussOmega c (n + 1) = 0 := by
      rw [h0]; ring
    rcases mul_eq_zero.mp h1 with h | h
    · have hre := congrArg Zsqrtd.re h
      have him := congrArg Zsqrtd.im h
      simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
      subst hn
      refine ⟨?_, ?_⟩
      · simpa using hre
      · simpa using him
    · exact absurd h (SkG.gaussOmega_ne_zero c _)
  apply hne
  constructor
  · funext d
    have : X d = 0 := by
      rcases lt_or_ge (d : ℕ) (r - 2) with h | h
      · exact hlow d h
      · rcases (show (d : ℕ) = r - 2 ∨ (d : ℕ) = r - 1 by omega) with h' | h'
        · rw [h']; exact htop.1
        · rw [h']; exact htop.2
    simpa [hX, d.isLt] using this
  · funext i
    have hre := congrArg Zsqrtd.re hZ0
    have him := congrArg Zsqrtd.im hZ0
    simp [hZ] at hre him
    fin_cases i
    · simpa using hre
    · simpa using him

end Z3NetF.Proofs
