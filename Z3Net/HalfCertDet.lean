module
public import Z3Net.HalfBox

@[expose] public section

/-!
# Entry Half: the integer box determinants of the `s = 5` design (`half5_net`)

* `detL`: a kernel-evaluable Laplace expansion along row `0`; `detL_eq`: `detL n A = A.det`.
* `chkDet5 a = true` (`decide +kernel`): for every composition `d = (a, …)` of `5` (`d_c ≤ 5`),
  `|det boxMatrix (halfIntGen M5h D5h) d|` divides `NS = 2⁸·3⁵·5³·7²·11²·13²·17·29·41·47·257`.
* `half5_box_dvd`: hence no prime outside `{2,3,5,7,11,13,17,29,41,47,257}` divides a box
  determinant.
-/

namespace Z3NetHL.Proofs

open Matrix Finset

/-- `∑_{i < n} f i` by recursion (kernel friendly). -/
def sumF : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => f 0 + sumF n (fun i => f i.succ)

lemma sumF_eq : ∀ (n : ℕ) (f : Fin n → ℤ), sumF n f = ∑ i, f i
  | 0, f => by simp [sumF]
  | n + 1, f => by rw [sumF, sumF_eq n, Fin.sum_univ_succ]

/-- Laplace expansion along row `0` (kernel friendly). -/
def detL : (n : ℕ) → (Fin n → Fin n → ℤ) → ℤ
  | 0, _ => 1
  | n + 1, A => sumF (n + 1) fun j =>
      (if (j : ℕ) % 2 = 0 then A 0 j else -A 0 j) * detL n (fun i k => A i.succ (j.succAbove k))

lemma detL_eq : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), detL n A = A.det
  | 0, A => by simp [detL]
  | n + 1, A => by
    show sumF (n + 1) _ = _
    rw [sumF_eq, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd := detL_eq n (A.submatrix Fin.succ j.succAbove)
    have hs : (if (j : ℕ) % 2 = 0 then A 0 j else -A 0 j) = (-1) ^ (j : ℕ) * A 0 j := by
      split_ifs with h
      · rw [Even.neg_one_pow (Nat.even_iff.mpr h), one_mul]
      · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), neg_one_mul]
    rw [hs, ← hd]
    rfl

/-- `2⁸·3⁵·5³·7²·11²·13²·17·29·41·47·257`. -/
def NS : ℕ := 2 ^ 8 * 3 ^ 5 * 5 ^ 3 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2 * 17 ^ 1 * 29 ^ 1 * 41 ^ 1 *
  47 ^ 1 * 257 ^ 1

def okDet5 (d : Fin 5 → ℕ) : Bool :=
  decide ((detL 5 (boxMatrix (halfIntGen M5h D5h) d)).natAbs ∣ NS)

/-- All compositions `(a, b, c, d, e)` of `5`, split by `a`. -/
def chkDet5 (a : ℕ) : Bool :=
  (List.range 6).all fun b => (List.range 6).all fun c => (List.range 6).all fun d =>
    (List.range 6).all fun e => decide (a + b + c + d + e ≠ 5) || okDet5 ![a, b, c, d, e]

lemma prime_dvd_pow_eq {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q ^ k) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)

lemma prime_dvd_NS {p : ℕ} (hp : p.Prime) (h : p ∣ NS) :
    p ∈ ({2, 3, 5, 7, 11, 13, 17, 29, 41, 47, 257} : Finset ℕ) := by
  unfold NS at h
  simp only [hp.dvd_mul] at h
  rcases h with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
    (rw [prime_dvd_pow_eq hp (by norm_num) h]; decide)

lemma chkDet5_sound (hchk : ∀ a ∈ List.range 6, chkDet5 a = true) (d : Fin 5 → ℕ)
    (hd : ∑ c, d c = 5) : (boxMatrix (halfIntGen M5h D5h) d).det.natAbs ∣ NS := by
  rw [Fin.sum_univ_five] at hd
  have m : ∀ c, d c ∈ List.range 6 := fun c => by
    rw [List.mem_range]
    fin_cases c <;> simp <;> omega
  have h := hchk (d 0) (m 0)
  simp only [chkDet5, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [hd, ne_eq, not_true_eq_false, decide_false, Bool.false_or, okDet5,
    decide_eq_true_eq] at h'
  have e : ![d 0, d 1, d 2, d 3, d 4] = d := by
    funext c; fin_cases c <;> rfl
  rw [e, detL_eq] at h'
  exact h'

end Z3NetHL.Proofs
