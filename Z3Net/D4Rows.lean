module
public import Mathlib
public import Z3Net.D4Net

@[expose] public section

/-!
# 4D entry, part 5: the first offset row is design A, for every `k` (hypothesis (H1))

* `Qinv_Psi`: Lemma R / Proposition N in the `E`-basis: `Q_c^(-k) Ψ_cd[0, j] = w_cd y_cd^(k-1-j)`
  (Cauchy kernel: `w = y = 1/(a_c - a_d)` for finite `c, d`, `y = 0` for `c = ∞`, `w = 1`,
  `y = a_c` for `d = ∞`), proved by evaluating the cofactor of `(t - a_c)^k` in `E_{d,j}` at `a_c`.
* `sum_Ux_lt`, `sum_Ux_ge`: the gauge `U'^(k)` acts on the last three levels by `U'_d` and kills
  the levels `n ≥ 3` (`v_n - α_n v_1 - β_n v_2 = 0`, Proposition G).
* `row0`: `Φ'_cd[0, j] = F_{k-1-j}[c][d]` for all `c, d`, `k ≥ 2`.
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## The Cauchy layer -/

/-- `w_cd` of Proposition N (with `h = 1/2`). -/
def wtab (h : R) (c d : Fin 4) : R :=
  if c = 0 ∧ d = 3 then -1 else if c = 1 ∧ d = 0 then -1 else if c = 1 ∧ d = 3 then -h
  else if c = 3 ∧ d = 1 then h else 1

/-- `y_cd` of Proposition N (with `h = 1/2`). -/
def ytab (h : R) (c d : Fin 4) : R :=
  if c = 2 then 0 else if d = 2 then ((place c : ℤ) : R)
  else if c = 0 ∧ d = 1 then 1 else if c = 0 ∧ d = 3 then -1 else if c = 1 ∧ d = 0 then -1
  else if c = 1 ∧ d = 3 then -h else if c = 3 ∧ d = 0 then 1 else h

lemma Psi_row0_fin (k : ℕ) (c d : Fin 4) (hc : c ≠ 2) (hcd : c ≠ d) (j : Fin k) :
    (Psi k c d ⟨0, by have := j.isLt; omega⟩ j : R) =
      (Gfac R k c d j).eval ((place c : ℤ) : R) := by
  rw [← Fr_E_off k c d j ⟨0, _⟩, Fr_E_fin k c d j j.isLt hc]
  simp only [Nat.add_zero]
  rw [taylor_E_ne k c d j hc hcd j.isLt, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]

lemma Psi_row0_inf (k : ℕ) (d : Fin 4) (hd : d ≠ 2) (j : Fin k) :
    (Psi k 2 d ⟨0, by have := j.isLt; omega⟩ j : R) = if (j : ℕ) + 1 = k then 1 else 0 := by
  have hj := j.isLt
  rw [← Fr_E_off k 2 d j ⟨0, _⟩, Fr_E_inf k d j hj]
  simp only [Nat.add_zero]
  split_ifs with h1
  · rw [show 4 * k - 1 - k = exT k d j + exP k d j + exM k d j by rw [exSum_ne_two k d j hd]; omega,
      coeff_EPoly_top]
  · exact coeff_EPoly_gt k d j _ (by rw [exSum_ne_two k d j hd]; omega)

lemma two_pow_mul_pow (h : R) (hh : 2 * h = 1) (a : ℕ) : (2 : R) ^ a * h ^ a = 1 := by
  rw [← mul_pow, hh, one_pow]

/-- **Proposition N** in the `E`-basis. -/
theorem Qinv_Psi (h : R) (hh : 2 * h = 1) (k : ℕ) (c d : Fin 4) (hcd : c ≠ d) (j : Fin k) :
    Qinv h k c * (Psi k c d ⟨0, by have := j.isLt; omega⟩ j : R) =
      wtab h c d * ytab h c d ^ (k - 1 - (j : ℕ)) := by
  have hj := j.isLt
  obtain ⟨n, hn⟩ : ∃ n, k = (j : ℕ) + n + 1 := ⟨k - 1 - j, by omega⟩
  have hkj : k - 1 - (j : ℕ) = n := by omega
  rw [hkj]
  by_cases hc : c = 2
  · subst hc
    rw [Psi_row0_inf k d (Ne.symm hcd) j]
    simp only [Qinv, wtab, ytab]
    simp
    rcases n with _ | n
    · simp [show (j : ℕ) + 1 = k by omega]
    · simp [show ¬ ((j : ℕ) + 1 = k) by omega]
  rw [Psi_row0_fin k c d hc hcd j]
  have e2 := two_pow_mul_pow h hh
  have m1 : ∀ a : ℕ, (-1 : R) ^ a * (-1) ^ a = 1 := fun a => by rw [← mul_pow]; norm_num
  have odd1 : ∀ a b : ℕ, (-1 : R) ^ (2 * a + b + 1) = -(-1) ^ b := fun a b => by
    rw [pow_succ, pow_add, pow_mul]; norm_num
  have ev1 : ∀ a b : ℕ, (-1 : R) ^ (2 * a + b) = (-1) ^ b := fun a b => by
    rw [pow_add, pow_mul]; norm_num
  have t2 : (-1 - 1 : R) = (-1) * 2 := by ring
  have t2' : (1 + 1 : R) = 2 := by norm_num
  fin_cases c <;> fin_cases d <;> simp at hc hcd <;>
    simp [Gfac, exT, exP, exM, Qinv, wtab, ytab, place, hn]
  -- (0,1)
  · exact m1 _
  -- (0,2)
  · rw [show 2 * ((j : ℕ) + n + 1) - 1 - j - (j + n + 1) = n by omega, mul_left_comm, m1, mul_one]
  -- (0,3)
  · rw [← pow_add, show (j : ℕ) + n + 1 + j = 2 * j + n + 1 by ring, odd1]
  -- (1,0)
  · rw [t2, mul_pow]
    calc _ = (-1) ^ (j : ℕ) * (-1) ^ ((j : ℕ) + n + 1) * (2 ^ ((j : ℕ) + n + 1) * h ^ ((j : ℕ) + n + 1)) := by ring
      _ = _ := by rw [e2, mul_one, ← pow_add, show (j : ℕ) + (j + n + 1) = 2 * j + n + 1 by ring, odd1]
  -- (1,2)
  · rw [t2, mul_pow, show 2 * ((j : ℕ) + n + 1) - 1 - j = j + 2 * n + 1 by omega]
    calc _ = (-1) ^ ((j : ℕ) + 2 * n + 1) * (-1) ^ ((j : ℕ) + n + 1) *
          (2 ^ ((j : ℕ) + n + 1) * h ^ ((j : ℕ) + n + 1)) := by ring
      _ = _ := by
        rw [e2, mul_one, ← pow_add, show (j : ℕ) + 2 * n + 1 + (j + n + 1) = 2 * (j + n + 1) + n by ring,
          ev1]
  -- (1,3)
  · rw [t2, mul_pow, neg_pow h n]
    calc _ = (-1) ^ ((j : ℕ) + n + 1) * (-1) ^ (j : ℕ) * (2 ^ (j : ℕ) * h ^ (j : ℕ)) * (h * h ^ n) := by ring
      _ = _ := by
        rw [e2, mul_one, ← pow_add, show (j : ℕ) + n + 1 + j = 2 * j + n + 1 by ring, odd1]; ring
  -- (3,0)
  · rw [t2', mul_comm, e2]
  -- (3,1)
  · rw [t2']
    calc _ = (2 ^ (j : ℕ) * h ^ (j : ℕ)) * (h * h ^ n) := by ring
      _ = _ := by rw [e2, one_mul]
  -- (3,2)
  · rw [t2', mul_comm, e2]

/-! ## The gauge `U'^(k)` on the first row -/

lemma sum_reflect (h : R) (k : ℕ) (d : Fin 4) (f : ℕ → R) (j : Fin k) :
    ∑ j' : Fin k, f (k - 1 - (j' : ℕ)) * Uk h k d j' j =
      ∑ n' ∈ range k, f n' * Ux h d n' (k - 1 - (j : ℕ)) := by
  simp only [Uk]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (k - 1 - i) * Ux h d (k - 1 - i) (k - 1 - (j : ℕ))) k]
  exact Finset.sum_range_reflect (fun n' => f n' * Ux h d n' (k - 1 - (j : ℕ))) k

lemma sum_Ux_split (h : R) (d : Fin 4) (f : ℕ → R) (n k : ℕ) (hnk : n < k) :
    ∑ n' ∈ range k, f n' * Ux h d n' n = ∑ n' ∈ range (n + 1), f n' * Ux h d n' n := by
  rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ k by omega)]
  rw [Finset.sum_eq_zero (s := Ico (n + 1) k), add_zero]
  intro n' hn'
  simp only [mem_Ico] at hn'
  rw [Ux_upper h d n' n (by omega), mul_zero]

lemma Ux_small (h : R) (d : Fin 4) (n' n : ℕ) (h1 : n' < 3) (h2 : n < 3) :
    Ux h d n' n = Ures h d ⟨n', h1⟩ ⟨n, h2⟩ := by
  unfold Ux; rw [dif_pos ⟨h1, h2⟩]

lemma sum_Ux_0 (h : R) (d : Fin 4) (f : ℕ → R) (k : ℕ) (hk : 0 < k) :
    ∑ n' ∈ range k, f n' * Ux h d n' 0 = f 0 * Ures h d 0 0 := by
  rw [sum_Ux_split h d f 0 k hk]; simp [Ux_small h d 0 0 (by norm_num) (by norm_num)]

lemma sum_Ux_1 (h : R) (d : Fin 4) (f : ℕ → R) (k : ℕ) (hk : 1 < k) :
    ∑ n' ∈ range k, f n' * Ux h d n' 1 = f 0 * Ures h d 0 1 + f 1 * Ures h d 1 1 := by
  rw [sum_Ux_split h d f 1 k hk, sum_range_succ, sum_range_one,
    Ux_small h d 0 1 (by norm_num) (by norm_num), Ux_small h d 1 1 (by norm_num) (by norm_num)]
  rfl

lemma sum_Ux_2 (h : R) (d : Fin 4) (f : ℕ → R) (k : ℕ) (hk : 2 < k) :
    ∑ n' ∈ range k, f n' * Ux h d n' 2 =
      f 0 * Ures h d 0 2 + f 1 * Ures h d 1 2 + f 2 * Ures h d 2 2 := by
  rw [sum_Ux_split h d f 2 k hk, sum_range_succ, sum_range_succ, sum_range_one,
    Ux_small h d 0 2 (by norm_num) (by norm_num), Ux_small h d 1 2 (by norm_num) (by norm_num),
    Ux_small h d 2 2 (by norm_num) (by norm_num)]
  rfl

lemma sum_Ux_ge (h : R) (d : Fin 4) (f : ℕ → R) (n k : ℕ) (hn : 3 ≤ n) (hnk : n < k) :
    ∑ n' ∈ range k, f n' * Ux h d n' n = f n - alpha h d n * f 1 - beta h d n * f 2 := by
  have e : ∀ n', f n' * Ux h d n' n =
      (if n' = n then f n else 0) + (if n' = 1 then -(alpha h d n * f 1) else 0) +
        (if n' = 2 then -(beta h d n * f 2) else 0) := by
    intro n'
    unfold Ux
    rw [dif_neg (by omega), if_pos hn]
    by_cases h1 : n' = n
    · subst h1; simp [show n' ≠ 1 by omega, show n' ≠ 2 by omega]
    · by_cases h2 : n' = 1
      · subst h2; simp [h1]; ring
      · by_cases h3 : n' = 2
        · subst h3; simp [h1]; ring
        · simp [h1, h2, h3]
  simp only [e, sum_add_distrib, Finset.sum_ite_eq', mem_range, if_pos hnk,
    if_pos (show 1 < k by omega), if_pos (show 2 < k by omega)]
  ring

/-! ## Design A: the residual identities -/

lemma resid0 (h : R) (hh : 2 * h = 1) (c d : Fin 4) (hcd : c ≠ d) :
    (lamRes c : R) * (wtab h c d * ytab h c d ^ 0 * Ures h d 0 0) = (Fdes 0 c d : R) := by
  fin_cases c <;> fin_cases d <;> simp at hcd <;> simp [wtab, ytab, Ures, Fdes, lamRes, place] <;>
    first | ring1 | linear_combination hh | linear_combination (2 * h + 1) * hh | linear_combination (1 - 2 * h) * hh | linear_combination (-4 * h ^ 2 + 2 * h + 1) * hh | linear_combination (-2 * h - 1) * hh | linear_combination (2 * h ^ 2 - 4 * h) * hh | linear_combination (-2 : R) * hh | linear_combination (4 * h ^ 2 - 2 * h - 1) * hh | linear_combination (-1 : R) * hh | linear_combination (2 * h - 1) * hh

lemma resid1 (h : R) (hh : 2 * h = 1) (c d : Fin 4) (hcd : c ≠ d) :
    (lamRes c : R) * (wtab h c d * ytab h c d ^ 0 * Ures h d 0 1 +
      wtab h c d * ytab h c d ^ 1 * Ures h d 1 1) = (Fdes 1 c d : R) := by
  fin_cases c <;> fin_cases d <;> simp at hcd <;> simp [wtab, ytab, Ures, Fdes, lamRes, place] <;>
    first | ring1 | linear_combination hh | linear_combination (2 * h + 1) * hh | linear_combination (1 - 2 * h) * hh | linear_combination (-4 * h ^ 2 + 2 * h + 1) * hh | linear_combination (-2 * h - 1) * hh | linear_combination (2 * h ^ 2 - 4 * h) * hh | linear_combination (-2 : R) * hh | linear_combination (4 * h ^ 2 - 2 * h - 1) * hh | linear_combination (-1 : R) * hh | linear_combination (2 * h - 1) * hh

lemma resid2 (h : R) (hh : 2 * h = 1) (c d : Fin 4) (hcd : c ≠ d) :
    (lamRes c : R) * (wtab h c d * ytab h c d ^ 0 * Ures h d 0 2 +
      wtab h c d * ytab h c d ^ 1 * Ures h d 1 2 + wtab h c d * ytab h c d ^ 2 * Ures h d 2 2) =
      (Fdes 2 c d : R) := by
  fin_cases c <;> fin_cases d <;> simp at hcd <;> simp [wtab, ytab, Ures, Fdes, lamRes, place] <;>
    first | ring1 | linear_combination hh | linear_combination (2 * h + 1) * hh | linear_combination (1 - 2 * h) * hh | linear_combination (-4 * h ^ 2 + 2 * h + 1) * hh | linear_combination (-2 * h - 1) * hh | linear_combination (2 * h ^ 2 - 4 * h) * hh | linear_combination (-2 : R) * hh | linear_combination (4 * h ^ 2 - 2 * h - 1) * hh | linear_combination (-1 : R) * hh | linear_combination (2 * h - 1) * hh

/-- Proposition G: the levels `n ≥ 3` of the first row vanish. -/
lemma resid_ge (h : R) (hh : 2 * h = 1) (c d : Fin 4) (hcd : c ≠ d) (n : ℕ) (hn : 3 ≤ n) :
    wtab h c d * ytab h c d ^ n - alpha h d n * (wtab h c d * ytab h c d ^ 1) -
      beta h d n * (wtab h c d * ytab h c d ^ 2) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hm : m + 3 - 2 = m + 1 := by omega
  have z : (0 : R) ^ (m + 3) = 0 := zero_pow (by omega)
  rcases Nat.even_or_odd (m + 3) with hp | hp
  · have e1 : (m + 3) % 2 = 0 := Nat.even_iff.mp hp
    have e2 : (-1 : R) ^ (m + 3) = 1 := hp.neg_one_pow
    fin_cases c <;> fin_cases d <;> simp at hcd <;>
      simp only [wtab, ytab, alpha, beta, place, hm, e1, e2, Fin.isValue] <;>
      simp <;> (try simp only [e2, neg_pow h, one_mul, neg_one_mul]) <;>
      first | ring1 | linear_combination (h ^ (m + 3) - h ^ 2) * hh |
        linear_combination (-(h ^ (m + 3) - h ^ 2)) * hh
  · have e1 : (m + 3) % 2 = 1 := Nat.odd_iff.mp hp
    have e2 : (-1 : R) ^ (m + 3) = -1 := hp.neg_one_pow
    fin_cases c <;> fin_cases d <;> simp at hcd <;>
      simp only [wtab, ytab, alpha, beta, place, hm, e1, e2, Fin.isValue] <;>
      simp <;> (try simp only [e2, neg_pow h, one_mul, neg_one_mul]) <;>
      first | ring1 | linear_combination (h ^ (m + 3) - h ^ 2) * hh |
        linear_combination (-(h ^ (m + 3) - h ^ 2)) * hh

/-! ## (H1): the first offset row of every block -/

/-- **(H1).** Row `0` of every block `Φ'_cd` is design A on the last three levels and `0` above,
for every `k ≥ 2` (Propositions N and G). -/
theorem row0 (h : R) (hh : 2 * h = 1) (k : ℕ) (hk : 2 ≤ k) (c d : Fin 4) (j : Fin k) :
    D4Phi R h k c d ⟨0, by omega⟩ j = (Fdes (k - 1 - (j : ℕ)) c d : R) := by
  by_cases hcd : c = d
  · subst hcd; simp [D4Phi]
  have hj := j.isLt
  have e : D4Phi R h k c d ⟨0, by omega⟩ j = (lamRes c : R) * ∑ j' : Fin k,
      (wtab h c d * ytab h c d ^ (k - 1 - (j' : ℕ))) * Uk h k d j' j := by
    simp only [D4Phi, if_neg hcd, ↓reduceIte, mul_assoc, Finset.mul_sum]
    refine sum_congr rfl fun j' _ => ?_
    have := Qinv_Psi h hh k c d hcd j'
    calc _ = (lamRes c : R) * ((Qinv h k c * (Psi k c d ⟨0, by omega⟩ j' : R)) * Uk h k d j' j) := by
          ring
      _ = _ := by rw [this]; ring
  rw [e, sum_reflect h k d (fun n' => wtab h c d * ytab h c d ^ n') j]
  have hnk : k - 1 - (j : ℕ) < k := by omega
  rcases (show k - 1 - (j : ℕ) = 0 ∨ k - 1 - (j : ℕ) = 1 ∨ k - 1 - (j : ℕ) = 2 ∨
      3 ≤ k - 1 - (j : ℕ) by omega) with h0 | h1 | h2 | h3
  · rw [h0, sum_Ux_0 h d _ k (by omega), resid0 h hh c d hcd]
  · rw [h1, sum_Ux_1 h d _ k (by omega), resid1 h hh c d hcd]
  · rw [h2, sum_Ux_2 h d _ k (by omega), resid2 h hh c d hcd]
  · rw [sum_Ux_ge h d _ _ k h3 hnk, resid_ge h hh c d hcd _ h3, mul_zero]
    simp [Fdes, show k - 1 - (j : ℕ) ≠ 0 by omega, show k - 1 - (j : ℕ) ≠ 1 by omega,
      show k - 1 - (j : ℕ) ≠ 2 by omega]

/-- **(H2).** The deeper offset rows of the diagonal blocks vanish. -/
lemma diag_deep (h : R) (k : ℕ) (c : Fin 4) (r : Fin (3 * k)) (hr : (r : ℕ) ≠ 0) (j : Fin k) :
    D4Phi R h k c c r j = 0 := by
  simp [D4Phi, hr]

end

end Z3NetD4.Proofs
