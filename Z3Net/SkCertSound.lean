/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(draft; LaTeX source `paper/core.tex`). Results are cited by their `\label` names, never by numbers.
Entry S1E: kernel certificates for the values of `tab:S1E` (`prop:S1E`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S1EDefs

@[expose] public section

/-!
# Entry S1E: a kernel-checkable certificate format for `λ_jit(κ)²` and its soundness

`λ_jit(κ)² = lamJit2 s p κ` is the minimum of `jitNorm2 a = ∑_c ((|a_c| - 1)₊)²` over
`0 ≠ a ∈ Λ_κ = {a ∈ ℤ^s : a_z ≡ ∑_d κ_d a_{x_d} (mod p)}`. A certificate consists of

* a basis `B = (b_0, …, b_{s-1})` (rows, typically LLL-reduced) and an integer matrix `W` with
  `W B = E`, where `E` is the standard basis `e_d + κ_d e_z` (`d < s - 1`), `p e_z` of `Λ_κ`
  (`WOK`); hence every `a ∈ Λ_κ` is an integer combination `a = ∑_i y_i b_i`;
* for every level `k` a scale `d_k` and integer vectors `P_{k,j}` (`j ≥ k`, a scaled projection of
  `b_j` orthogonal to `b_0, …, b_{k-1}`) with `⟨P_{k,j'}, b_i⟩ = 0` (`i < k`) and
  `d_k ⟨P_{k,j'}, b_j⟩ = ⟨P_{k,j'}, P_{k,j}⟩` (`levOK`); then
  `‖∑_{j ≥ k} y_j P_{k,j}‖² ≤ d_k² ‖a‖²` (`proj_le`);
* the radius `R² = (J - 1) + 2 r₀ + s` with `s (J - 1) < (r₀ + 1)²`: `jitNorm2 a < J` forces
  `‖a‖² ≤ R²` (`norm_le_of_jit_lt`, Cauchy–Schwarz).

`chk` runs a Fincke–Pohst enumeration of all `y` with `‖∑_{j≥k} y_j P_{k,j}‖² ≤ d_k² R²` at every
level (the interval of `y_k` is computed exactly from an integer square root, which is itself
re-checked) and tests every leaf: `a = 0` or `J ≤ jitNorm2 a`. `certOK_sound`: a successful run
proves `J ≤ jitNorm2 a` for every `0 ≠ a ∈ Λ_κ`; with a witness (`witOK`), `lamJit2 = J`
(`lamJit2_of_cert`). `trunc_le` turns `c^(2s) p² ≤ J^s` into `c ≤ √J p^(-1/s)`.
-/

namespace Z3NetF.Proofs.SkCert

open Finset

/-! ## Kernel-friendly primitives -/

/-- `∑_{t < n} f t`. -/
def sumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- `∑_{t < n} f t` in `ℕ`. -/
def sumToN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumToN f n + f n

/-- `∀ i < n, f i`. -/
def natAll (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => natAll f n && f n

/-- Entry `t` of an integer list (`0` beyond its end). -/
def lget : List ℤ → ℕ → ℤ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => lget xs n

/-- Entry `t` of a natural list (`0` beyond its end). -/
def nget : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nget xs n

/-- Row `i` of a list of rows (`[]` beyond its end). -/
def lrow : List (List ℤ) → ℕ → List ℤ
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, n + 1 => lrow xs n

/-- `[f st, f (st+1), …, f (st+n-1)]`. -/
def vgen (f : ℕ → ℤ) : ℕ → ℕ → List ℤ
  | _, 0 => []
  | st, n + 1 => f st :: vgen f (st + 1) n

/-- Dot product of the first `s` entries. -/
def ldot (s : ℕ) (u v : List ℤ) : ℤ := sumTo (fun t => lget u t * lget v t) s

/-- `y v + w` (first `s` entries). -/
def vaxpy (s : ℕ) (y : ℤ) (v w : List ℤ) : List ℤ := vgen (fun t => y * lget v t + lget w t) 0 s

/-- `∑_j ys_j vs_j`. -/
def lcomb (s : ℕ) : List ℤ → List (List ℤ) → List ℤ
  | y :: ys, v :: vs => vaxpy s y v (lcomb s ys vs)
  | _, _ => []

/-- Newton iteration for the integer square root (any result is re-checked by its caller). -/
def isqrtIter (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if (x + n / x) / 2 < x then isqrtIter n f ((x + n / x) / 2) else x

/-- Integer square root (Newton from `n`). -/
def isqrt (n : ℕ) : ℕ := isqrtIter n 1024 n

/-- `∀ y ∈ [lo, lo + n), f y`. -/
def rangeAll (f : ℤ → Bool) : ℤ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => f lo && rangeAll f (lo + 1) n

/-- The interval `[lo, lo + n)` of all `y` with `‖y v + w‖² ≤ d² R²`, via
`A ‖y v + w‖² = (A y + B)² + A ‖w‖² - B²` (`A = ‖v‖²`, `B = ⟨v, w⟩`); `none` if the integer
square root fails its check or `A ≤ 0`. -/
def levRangeAux (A Bc D : ℤ) (r : ℤ) : Option (ℤ × ℕ) :=
  if D < 0 then some (0, 0)
  else if A ≤ 0 then none
  else if D < (r + 1) ^ 2 then some (-((r + Bc) / A), ((r - Bc) / A + (r + Bc) / A + 1).toNat)
  else none

/-- See `levRangeAux`. -/
def levRange (s : ℕ) (R2 d : ℤ) (v w : List ℤ) : Option (ℤ × ℕ) :=
  levRangeAux (ldot s v v) (ldot s v w)
    (ldot s v v * (d * d * R2 - ldot s w w) + ldot s v w * ldot s v w)
    (isqrt (ldot s v v * (d * d * R2 - ldot s w w) + ldot s v w * ldot s v w).toNat)

/-- The enumeration. The list of levels is `[(d_{s-1}, P_{s-1}), …, (d_0, P_0)]` with
`P_k = [P_{k,k}, …, P_{k,s-1}]`; `ys = [y_{k+1}, …, y_{s-1}]` are the coefficients chosen so far. -/
def chk (s : ℕ) (R2 : ℤ) (leaf : List ℤ → Bool) : List (ℤ × List (List ℤ)) → List ℤ → Bool
  | [], ys => leaf ys
  | (_, []) :: _, _ => false
  | (d, v :: Pt) :: rest, ys =>
    match levRange s R2 d v (lcomb s ys Pt) with
    | none => false
    | some (lo, n) => rangeAll (fun y => chk s R2 leaf rest (y :: ys)) lo n

/-- `a = 0` (first `s` entries). -/
def allZero (s : ℕ) (a : List ℤ) : Bool := sumToN (fun t => (lget a t).natAbs) s == 0

/-- The jitter norm of the first `s` entries. -/
def jitL (s : ℕ) (a : List ℤ) : ℕ := sumToN (fun t => ((lget a t).natAbs - 1) ^ 2) s

/-- Leaf test: `a = ∑ y_i b_i` is `0` or has jitter norm at least `J`. -/
def leafOK (s J : ℕ) (B : List (List ℤ)) (ys : List ℤ) : Bool :=
  allZero s (lcomb s ys B) || decide (J ≤ jitL s (lcomb s ys B))

/-- The orthogonality certificate of level `k`. -/
def levOK (s : ℕ) (B : List (List ℤ)) (k : ℕ) (d : ℤ) (P : List (List ℤ)) : Bool :=
  P.length == s - k &&
  natAll (fun j' =>
    natAll (fun i => ldot s (lrow P j') (lrow B i) == 0) k &&
    natAll (fun j => d * ldot s (lrow P j') (lrow B (k + j)) == ldot s (lrow P j') (lrow P j))
      (s - k)) (s - k)

/-- All levels (level `k` = number of levels after it). -/
def levsOK (s : ℕ) (B : List (List ℤ)) : List (ℤ × List (List ℤ)) → Bool
  | [] => true
  | (d, P) :: rest => levOK s B rest.length d P && levsOK s B rest

/-- Entry `(j, t)` of the standard basis `E` of `Λ_κ`. -/
def Eent (s p : ℕ) (kl : List ℕ) (j t : ℕ) : ℤ :=
  if j + 1 < s then (if t = j then 1 else if t + 1 = s then (nget kl j : ℤ) else 0)
  else if t + 1 = s then (p : ℤ) else 0

/-- `W B = E`. -/
def WOK (s p : ℕ) (kl : List ℕ) (B W : List (List ℤ)) : Bool :=
  natAll (fun j => natAll (fun t =>
    sumTo (fun i => lget (lrow W j) i * lget (lrow B i) t) s == Eent s p kl j t) s) s

/-- The full certificate check for `J ≤ lamJit2 s p (kapL p kl)`. -/
def certOK (s p : ℕ) (kl : List ℕ) (J r0 : ℕ) (B W : List (List ℤ))
    (Ls : List (ℤ × List (List ℤ))) : Bool :=
  decide (s * (J - 1) < (r0 + 1) ^ 2) && B.length == s && WOK s p kl B W && Ls.length == s &&
    levsOK s B Ls && chk s ((J - 1 + 2 * r0 + s : ℕ) : ℤ) (leafOK s J B) Ls []

/-- `∑_{c < s-1} κ_c a_c - a_{s-1}`. -/
def latX (s : ℕ) (kl : List ℕ) (a : List ℤ) : ℤ :=
  sumTo (fun c => if c + 1 < s then (nget kl c : ℤ) * lget a c else -lget a c) s

/-- The witness check: `a ∈ Λ_κ`, `jitNorm2 a = J`, `a ≠ 0`. -/
def witOK (s p : ℕ) (kl : List ℕ) (J : ℕ) (a : List ℤ) : Bool :=
  latX s kl a % (p : ℤ) == 0 && jitL s a == J && !allZero s a

/-! ## Basic lemmas -/

lemma sumTo_eq (f : ℕ → ℤ) (n : ℕ) : sumTo f n = ∑ t ∈ range n, f t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, sum_range_succ]

lemma sumToN_eq (f : ℕ → ℕ) (n : ℕ) : sumToN f n = ∑ t ∈ range n, f t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumToN, ih, sum_range_succ]

lemma natAll_iff (f : ℕ → Bool) (n : ℕ) : natAll f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [natAll]
  | succ n ih =>
    rw [natAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma lget_nil (t : ℕ) : lget [] t = 0 := by cases t <;> rfl

lemma lget_cons_succ (x : ℤ) (xs : List ℤ) (t : ℕ) : lget (x :: xs) (t + 1) = lget xs t := rfl

lemma lrow_cons_succ (x : List ℤ) (xs : List (List ℤ)) (t : ℕ) :
    lrow (x :: xs) (t + 1) = lrow xs t := rfl

lemma nget_eq (L : List ℕ) (d : ℕ) : nget L d = L.getD d 0 := by
  induction L generalizing d with
  | nil => cases d <;> rfl
  | cons x xs ih => cases d with
    | zero => rfl
    | succ d => simp [nget, ih]

lemma lget_vgen (f : ℕ → ℤ) (n st t : ℕ) :
    lget (vgen f st n) t = if t < n then f (st + t) else 0 := by
  induction n generalizing st t with
  | zero => simp [vgen, lget_nil]
  | succ n ih =>
    cases t with
    | zero => simp [vgen, lget]
    | succ t =>
      rw [vgen, lget_cons_succ, ih]
      by_cases h : t < n
      · rw [ite_eq_left h, ite_eq_left (by omega)]; congr 1; omega
      · rw [ite_eq_right h, ite_eq_right (by omega)]

lemma vgen_length (f : ℕ → ℤ) (n st : ℕ) : (vgen f st n).length = n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp [vgen, ih]

lemma lget_vaxpy {s t : ℕ} (ht : t < s) (y : ℤ) (v w : List ℤ) :
    lget (vaxpy s y v w) t = y * lget v t + lget w t := by
  rw [vaxpy, lget_vgen, ite_eq_left ht, zero_add]

lemma lget_lcomb (s : ℕ) {t : ℕ} (ht : t < s) :
    ∀ (ys : List ℤ) (vs : List (List ℤ)),
      lget (lcomb s ys vs) t = ∑ j ∈ range (min ys.length vs.length), lget ys j * lget (lrow vs j) t
  | [], vs => by simp [lcomb, lget_nil]
  | y :: ys, [] => by simp [lcomb, lget_nil]
  | y :: ys, v :: vs => by
    rw [lcomb, lget_vaxpy ht, lget_lcomb s ht ys vs, List.length_cons, List.length_cons,
      Nat.succ_min_succ, sum_range_succ']
    simp only [lget_cons_succ, lrow_cons_succ]
    rw [add_comm]
    rfl

lemma ldot_eq (s : ℕ) (u v : List ℤ) : ldot s u v = ∑ t ∈ range s, lget u t * lget v t := by
  rw [ldot, sumTo_eq]

lemma ldot_self_nonneg (s : ℕ) (v : List ℤ) : 0 ≤ ldot s v v := by
  rw [ldot_eq]; exact sum_nonneg fun t _ => mul_self_nonneg _

lemma ldot_vaxpy (s : ℕ) (y : ℤ) (v w : List ℤ) :
    ldot s (vaxpy s y v w) (vaxpy s y v w) =
      y * y * ldot s v v + 2 * y * ldot s v w + ldot s w w := by
  simp only [ldot_eq]
  rw [sum_congr rfl fun t ht => by rw [lget_vaxpy (mem_range.1 ht)], mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun t _ => by ring

/-! ## The interval of one level -/

lemma rangeAll_sound (f : ℤ → Bool) :
    ∀ (n : ℕ) (lo y : ℤ), rangeAll f lo n = true → lo ≤ y → y < lo + n → f y = true
  | 0, lo, y, _, h1, h2 => by push_cast at h2; omega
  | n + 1, lo, y, h, h1, h2 => by
    rw [rangeAll, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact rangeAll_sound f n (lo + 1) y h.2 (by omega) (by push_cast at h2 ⊢; omega)

lemma levRangeAux_sound {A Bc D r lo : ℤ} {n : ℕ} (y : ℤ) (hr0 : 0 ≤ r)
    (hD : (A * y + Bc) ^ 2 ≤ D) (h : levRangeAux A Bc D r = some (lo, n)) :
    lo ≤ y ∧ y < lo + n := by
  unfold levRangeAux at h
  have hD0 : 0 ≤ D := le_trans (sq_nonneg _) hD
  rw [ite_eq_right (not_lt.2 hD0)] at h
  by_cases hA0 : A ≤ 0
  · rw [ite_eq_left hA0] at h; exact absurd h (by simp)
  rw [ite_eq_right hA0] at h
  have hA' : 0 < A := lt_of_not_ge hA0
  by_cases hr : D < (r + 1) ^ 2
  · rw [ite_eq_left hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt : (A * y + Bc) ^ 2 < (r + 1) ^ 2 := lt_of_le_of_lt hD hr
    have habs := abs_lt_of_sq_lt_sq hlt (by omega)
    rw [abs_lt] at habs
    have h1 : y ≤ (r - Bc) / A := (Int.le_ediv_iff_mul_le hA').2 (by nlinarith [habs.2])
    have h2 : -y ≤ (r + Bc) / A := (Int.le_ediv_iff_mul_le hA').2 (by nlinarith [habs.1])
    have hnn : 0 ≤ (r - Bc) / A + (r + Bc) / A + 1 := by omega
    rw [Int.toNat_of_nonneg hnn]
    omega
  · rw [ite_eq_right hr] at h; exact absurd h (by simp)

lemma levRange_sound {s : ℕ} {R2 d : ℤ} {v w : List ℤ} {lo : ℤ} {n : ℕ} (y : ℤ)
    (h : levRange s R2 d v w = some (lo, n))
    (hy : ldot s (vaxpy s y v w) (vaxpy s y v w) ≤ d * d * R2) : lo ≤ y ∧ y < lo + n := by
  rw [ldot_vaxpy] at hy
  refine levRangeAux_sound y (by positivity) ?_ h
  have hA := ldot_self_nonneg s v
  have e : ldot s v v * (d * d * R2 - ldot s w w) + ldot s v w * ldot s v w -
      (ldot s v v * y + ldot s v w) ^ 2 =
      ldot s v v * (d * d * R2 - (y * y * ldot s v v + 2 * y * ldot s v w + ldot s w w)) := by
    ring
  have := mul_nonneg hA (sub_nonneg.2 hy)
  linarith

/-! ## Completeness of the enumeration -/

/-- The level inequalities along the coefficient vector `y`. -/
def levBound (s : ℕ) (R2 : ℤ) (y : ℕ → ℤ) : List (ℤ × List (List ℤ)) → Prop
  | [] => True
  | (d, P) :: rest =>
    ldot s (lcomb s (vgen y rest.length (s - rest.length)) P)
        (lcomb s (vgen y rest.length (s - rest.length)) P) ≤ d * d * R2 ∧
      levBound s R2 y rest

lemma chk_complete (s : ℕ) (R2 : ℤ) (leaf : List ℤ → Bool) (y : ℕ → ℤ) :
    ∀ Ls : List (ℤ × List (List ℤ)), Ls.length ≤ s → levBound s R2 y Ls →
      chk s R2 leaf Ls (vgen y Ls.length (s - Ls.length)) = true → leaf (vgen y 0 s) = true
  | [], _, _, h => by simpa [chk] using h
  | (d, []) :: rest, _, _, h => by simp [chk] at h
  | (d, v :: Pt) :: rest, hl, hb, h => by
    have hk : rest.length < s := by simp at hl; omega
    have hv : vgen y rest.length (s - rest.length) =
        y rest.length :: vgen y (rest.length + 1) (s - (rest.length + 1)) := by
      have : s - rest.length = (s - (rest.length + 1)) + 1 := by omega
      rw [this, vgen]
    obtain ⟨hb1, hb2⟩ := hb
    rw [hv, lcomb] at hb1
    simp only [List.length_cons] at h
    rw [chk] at h
    split at h
    · exact absurd h (by simp)
    · rename_i lo n hlr
      have hy := levRange_sound (y rest.length) hlr hb1
      have hf := rangeAll_sound _ n lo (y rest.length) h hy.1 hy.2
      rw [← hv] at hf
      exact chk_complete s R2 leaf y rest (by omega) hb2 hf

/-! ## The projection inequality -/

lemma sum_mul_sum_comm (s n : ℕ) (Pt : ℕ → ℤ) (c : ℕ → ℤ) (Q : ℕ → ℕ → ℤ) :
    ∑ t ∈ range s, Pt t * ∑ j ∈ range n, c j * Q j t =
      ∑ j ∈ range n, c j * ∑ t ∈ range s, Pt t * Q j t := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring

lemma proj_le (s k : ℕ) (hk : k ≤ s) (d : ℤ) (y : ℕ → ℤ) (Bf Pf : ℕ → ℕ → ℤ)
    (h1 : ∀ j' < s - k, ∀ i < k, ∑ t ∈ range s, Pf j' t * Bf i t = 0)
    (h2 : ∀ j' < s - k, ∀ j < s - k,
      d * ∑ t ∈ range s, Pf j' t * Bf (k + j) t = ∑ t ∈ range s, Pf j' t * Pf j t) :
    ∑ t ∈ range s, (∑ j ∈ range (s - k), y (k + j) * Pf j t) ^ 2 ≤
      d ^ 2 * ∑ t ∈ range s, (∑ i ∈ range s, y i * Bf i t) ^ 2 := by
  set u : ℕ → ℤ := fun t => ∑ j ∈ range (s - k), y (k + j) * Pf j t with hu
  set a : ℕ → ℤ := fun t => ∑ i ∈ range s, y i * Bf i t with ha
  set r : ℕ → ℤ := fun t => d * a t - u t with hr
  have hr' : ∀ t, r t = ∑ i ∈ range k, (d * y i) * Bf i t +
      ∑ j ∈ range (s - k), y (k + j) * (d * Bf (k + j) t - Pf j t) := by
    intro t
    have hs : s = k + (s - k) := by omega
    simp only [hr, ha, hu]
    rw [hs, sum_range_add, ← hs, mul_add, mul_sum, mul_sum]
    have e1 : ∑ x ∈ range (s - k), y (k + x) * (d * Bf (k + x) t - Pf x t) =
        ∑ x ∈ range (s - k), d * (y (k + x) * Bf (k + x) t) -
          ∑ j ∈ range (s - k), y (k + j) * Pf j t := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun x _ => by ring
    rw [e1]
    have e2 : ∑ x ∈ range k, d * (y x * Bf x t) = ∑ i ∈ range k, d * y i * Bf i t :=
      sum_congr rfl fun x _ => by ring
    rw [e2]; ring
  have horth : ∑ t ∈ range s, u t * r t = 0 := by
    have : ∀ j' < s - k, ∑ t ∈ range s, Pf j' t * r t = 0 := by
      intro j' hj'
      simp only [hr', mul_add, sum_add_distrib]
      rw [sum_mul_sum_comm s k (Pf j') (fun i => d * y i) Bf,
        sum_mul_sum_comm s (s - k) (Pf j') (fun j => y (k + j)) (fun j t => d * Bf (k + j) t - Pf j t)]
      rw [sum_eq_zero (fun i hi => by rw [h1 j' hj' i (mem_range.1 hi), mul_zero]), zero_add]
      refine sum_eq_zero fun j hj => ?_
      have e : ∑ t ∈ range s, Pf j' t * (d * Bf (k + j) t - Pf j t) =
          d * ∑ t ∈ range s, Pf j' t * Bf (k + j) t - ∑ t ∈ range s, Pf j' t * Pf j t := by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun t _ => by ring
      rw [e, h2 j' hj' j (mem_range.1 hj), sub_self, mul_zero]
    calc ∑ t ∈ range s, u t * r t
        = ∑ t ∈ range s, r t * ∑ j ∈ range (s - k), y (k + j) * Pf j t :=
          sum_congr rfl fun t _ => by rw [hu, mul_comm]
      _ = ∑ j ∈ range (s - k), y (k + j) * ∑ t ∈ range s, r t * Pf j t :=
          sum_mul_sum_comm s (s - k) r (fun j => y (k + j)) Pf
      _ = 0 := sum_eq_zero fun j hj => by
          rw [sum_congr rfl fun t _ => mul_comm (r t) (Pf j t), this j (mem_range.1 hj), mul_zero]
  have key : d ^ 2 * ∑ t ∈ range s, a t ^ 2 =
      ∑ t ∈ range s, u t ^ 2 + 2 * ∑ t ∈ range s, u t * r t + ∑ t ∈ range s, r t ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by simp only [hr]; ring
  have hr2 : 0 ≤ ∑ t ∈ range s, r t ^ 2 := sum_nonneg fun t _ => sq_nonneg _
  show ∑ t ∈ range s, u t ^ 2 ≤ d ^ 2 * ∑ t ∈ range s, a t ^ 2
  rw [key, horth]; linarith

lemma levOK_sound {s : ℕ} {B : List (List ℤ)} {k : ℕ} {d : ℤ} {P : List (List ℤ)}
    (h : levOK s B k d P = true) (hk : k ≤ s) (y : ℕ → ℤ) :
    ldot s (lcomb s (vgen y k (s - k)) P) (lcomb s (vgen y k (s - k)) P) ≤
      d ^ 2 * ∑ t ∈ range s, (∑ i ∈ range s, y i * lget (lrow B i) t) ^ 2 := by
  simp only [levOK, Bool.and_eq_true, beq_iff_eq, natAll_iff] at h
  obtain ⟨hlen, h⟩ := h
  have h1 : ∀ j' < s - k, ∀ i < k,
      ∑ t ∈ range s, lget (lrow P j') t * lget (lrow B i) t = 0 := by
    intro j' hj' i hi; rw [← ldot_eq]; exact (h j' hj').1 i hi
  have h2 : ∀ j' < s - k, ∀ j < s - k,
      d * ∑ t ∈ range s, lget (lrow P j') t * lget (lrow B (k + j)) t =
        ∑ t ∈ range s, lget (lrow P j') t * lget (lrow P j) t := by
    intro j' hj' j hj; rw [← ldot_eq, ← ldot_eq]; exact (h j' hj').2 j hj
  have hpl := proj_le s k hk d y (fun i t => lget (lrow B i) t) (fun j t => lget (lrow P j) t) h1 h2
  rw [ldot_eq]
  refine le_trans (le_of_eq ?_) hpl
  refine sum_congr rfl fun t ht => ?_
  rw [← sq, lget_lcomb s (mem_range.1 ht), vgen_length, hlen, min_self]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [lget_vgen, ite_eq_left (mem_range.1 hj)]

lemma levsOK_bound {s : ℕ} {B : List (List ℤ)} (R2 : ℤ) (y : ℕ → ℤ)
    (hR : ∑ t ∈ range s, (∑ i ∈ range s, y i * lget (lrow B i) t) ^ 2 ≤ R2) :
    ∀ Ls : List (ℤ × List (List ℤ)), Ls.length ≤ s → levsOK s B Ls = true →
      levBound s R2 y Ls
  | [], _, _ => trivial
  | (d, P) :: rest, hl, h => by
    simp only [levsOK, Bool.and_eq_true] at h
    have hk : rest.length ≤ s := by simp at hl; omega
    refine ⟨?_, levsOK_bound R2 y hR rest hk h.2⟩
    refine le_trans (levOK_sound h.1 hk y) ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left hR (mul_self_nonneg d)

/-! ## From the lattice to the coefficients -/

/-- The integer form of `InLatK` for `κ = kapL p kl`. -/
lemma inLatK_iff {s p : ℕ} (kl : List ℕ) (a : Fin s → ℤ) :
    InLatK p (kapL p kl) a ↔
      (p : ℤ) ∣ ∑ c ∈ range s, (if c + 1 < s then (nget kl c : ℤ) *
        (if h : c < s then a ⟨c, h⟩ else 0) else -(if h : c < s then a ⟨c, h⟩ else 0)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← Fin.sum_univ_eq_sum_range
    (fun c => if c + 1 < s then (nget kl c : ℤ) * (if h : c < s then a ⟨c, h⟩ else 0)
      else -(if h : c < s then a ⟨c, h⟩ else 0)) s]
  unfold InLatK kapL
  push_cast
  refine Iff.of_eq (congrArg (· = (0 : ZMod p)) (sum_congr rfl fun c _ => ?_))
  simp only [Fin.eta, Fin.is_lt, dite_true, nget_eq]

lemma norm_le_of_jit_lt {s : ℕ} (a : Fin s → ℤ) (J r0 : ℕ) (hr0 : s * (J - 1) < (r0 + 1) ^ 2)
    (hlt : jitNorm2 a < J) :
    ∑ c, (a c) ^ 2 ≤ ((J - 1 + 2 * r0 + s : ℕ) : ℤ) := by
  set j : Fin s → ℕ := fun c => (a c).natAbs - 1 with hj
  have hjit : ∑ c, j c ^ 2 ≤ J - 1 := by
    have : jitNorm2 a = ∑ c, j c ^ 2 := rfl
    omega
  have hcs : (∑ c, j c) ^ 2 ≤ s * ∑ c, j c ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin s))) (f := j)
    simpa using this
  have hsum : ∑ c, j c ≤ r0 := by
    have h3 : (∑ c, j c) ^ 2 < (r0 + 1) ^ 2 :=
      lt_of_le_of_lt (le_trans hcs (Nat.mul_le_mul_left s hjit)) hr0
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h3
    omega
  have hpt : ∀ c, (a c).natAbs ^ 2 ≤ j c ^ 2 + 2 * j c + 1 := by
    intro c
    have : (a c).natAbs ≤ j c + 1 := by simp only [hj]; omega
    calc (a c).natAbs ^ 2 ≤ (j c + 1) ^ 2 := Nat.pow_le_pow_left this 2
      _ = j c ^ 2 + 2 * j c + 1 := by ring
  have hN : ∑ c, (a c).natAbs ^ 2 ≤ J - 1 + 2 * r0 + s := by
    calc ∑ c, (a c).natAbs ^ 2 ≤ ∑ c, (j c ^ 2 + 2 * j c + 1) := sum_le_sum fun c _ => hpt c
      _ = ∑ c, j c ^ 2 + 2 * ∑ c, j c + s := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum]; simp
      _ ≤ J - 1 + 2 * r0 + s := by omega
  have e : ∑ c, (a c) ^ 2 = ((∑ c, (a c).natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast; exact sum_congr rfl fun c _ => (sq_abs _).symm
  rw [e]; exact_mod_cast hN

/-! ## Soundness -/

theorem certOK_sound (s p : ℕ) (kl : List ℕ) (J r0 : ℕ) (B W : List (List ℤ))
    (Ls : List (ℤ × List (List ℤ))) (h : certOK s p kl J r0 B W Ls = true)
    (a : Fin s → ℤ) (ha : InLatK p (kapL p kl) a) (hne : a ≠ 0) : J ≤ jitNorm2 a := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hr0, hBl⟩, hW⟩, hLl⟩, hlev⟩, hchk⟩ := h
  by_contra hlt
  push Not at hlt
  set ah : ℕ → ℤ := fun t => if h : t < s then a ⟨t, h⟩ else 0 with hah
  -- lattice coordinates
  obtain ⟨q, hq⟩ := (inLatK_iff kl a).1 ha
  set cv : ℕ → ℤ := fun j => if j + 1 < s then ah j else -q with hcv
  have hE : ∀ t < s, ∑ j ∈ range s, cv j * Eent s p kl j t = ah t := by
    intro t ht
    have hs : s = (s - 1) + 1 := by omega
    rw [hs, sum_range_succ, ← hs]
    have hlast : cv (s - 1) * Eent s p kl (s - 1) t = if t + 1 = s then -q * p else 0 := by
      simp only [hcv, Eent, show ¬ (s - 1 + 1 < s) by omega, ite_false]
      split_ifs <;> ring
    rw [hlast]
    by_cases htl : t + 1 = s
    · rw [ite_eq_left htl]
      have e1 : ∀ j ∈ range (s - 1), cv j * Eent s p kl j t = (nget kl j : ℤ) * ah j := by
        intro j hj
        have hj' : j + 1 < s := by have := mem_range.1 hj; omega
        simp only [hcv, Eent, ite_eq_left hj', ite_eq_right (show t ≠ j by omega), ite_eq_left htl]
        ring
      rw [sum_congr rfl e1]
      have hsplit : ∀ f : ℕ → ℤ, (range s).sum f = (range (s - 1)).sum f + f (s - 1) := by
        intro f; conv_lhs => rw [hs]
        exact sum_range_succ _ _
      have hq' : ∑ c ∈ range s, (if c + 1 < s then (nget kl c : ℤ) * ah c else -ah c) = p * q := hq
      rw [hsplit] at hq'
      rw [ite_eq_right (by omega)] at hq'
      have e2 : ∑ c ∈ range (s - 1), (if c + 1 < s then (nget kl c : ℤ) * ah c else -ah c) =
          ∑ c ∈ range (s - 1), (nget kl c : ℤ) * ah c :=
        sum_congr rfl fun c hc => ite_eq_left (by have := mem_range.1 hc; omega)
      rw [e2] at hq'
      have : t = s - 1 := by omega
      subst this
      linarith
    · rw [ite_eq_right htl, add_zero]
      have htj : t + 1 < s := by omega
      rw [sum_eq_single t]
      · simp only [hcv, Eent, ite_eq_left htj, ite_true]; ring
      · intro j hj hjt
        have hj' : j + 1 < s := by have := mem_range.1 hj; omega
        simp only [hcv, Eent, ite_eq_left hj', ite_eq_right (Ne.symm hjt), ite_eq_right htl, mul_zero]
      · intro hn; exact absurd (mem_range.2 (by omega)) hn
  -- coefficients in the basis `B`
  set y : ℕ → ℤ := fun i => ∑ j ∈ range s, cv j * lget (lrow W j) i with hy
  have hWB : ∀ j < s, ∀ t < s,
      ∑ i ∈ range s, lget (lrow W j) i * lget (lrow B i) t = Eent s p kl j t := by
    intro j hj t ht
    have := (natAll_iff _ _).1 ((natAll_iff _ _).1 hW j hj) t ht
    rw [beq_iff_eq, sumTo_eq] at this
    exact this
  have hY : ∀ t < s, ∑ i ∈ range s, y i * lget (lrow B i) t = ah t := by
    intro t ht
    rw [← hE t ht]
    simp only [hy, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [← hWB j (mem_range.1 hj) t ht, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  -- the norm bound
  have hN := norm_le_of_jit_lt a J r0 hr0 hlt
  have hfin : ∀ g : ℤ → ℤ, ∑ c, g (a c) = ∑ t ∈ range s, g (ah t) := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun t => g (ah t)) s]
    exact sum_congr rfl fun c _ => by simp [hah]
  have hR : ∑ t ∈ range s, (∑ i ∈ range s, y i * lget (lrow B i) t) ^ 2 ≤
      ((J - 1 + 2 * r0 + s : ℕ) : ℤ) := by
    rw [sum_congr rfl fun t ht => by rw [hY t (mem_range.1 ht)]]
    rw [← hfin (fun x => x ^ 2)]; exact hN
  have hb := levsOK_bound _ y hR Ls (by omega) hlev
  have hleaf := chk_complete s _ (leafOK s J B) y Ls (by omega) hb (by rw [hLl, Nat.sub_self]; exact hchk)
  -- the leaf
  have hA : ∀ t < s, lget (lcomb s (vgen y 0 s) B) t = ah t := by
    intro t ht
    rw [lget_lcomb s ht, vgen_length, hBl, min_self, ← hY t ht]
    refine sum_congr rfl fun i hi => ?_
    rw [lget_vgen, ite_eq_left (mem_range.1 hi), zero_add]
  simp only [leafOK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, allZero, jitL,
    sumToN_eq] at hleaf
  rcases hleaf with h0 | hJ
  · apply hne
    funext c
    have h0' := (sum_eq_zero_iff.1 h0) c (mem_range.2 c.isLt)
    rw [hA c c.isLt] at h0'
    simpa [hah] using h0'
  · rw [sum_congr rfl fun t ht => by rw [hA t (mem_range.1 ht)]] at hJ
    have : jitNorm2 a = ∑ t ∈ range s, ((ah t).natAbs - 1) ^ 2 := by
      unfold jitNorm2
      rw [← Fin.sum_univ_eq_sum_range (fun t => ((ah t).natAbs - 1) ^ 2) s]
      exact sum_congr rfl fun c _ => by simp [hah]
    omega

theorem lamJit2_of_cert (s p : ℕ) (kl : List ℕ) (J r0 : ℕ) (B W : List (List ℤ))
    (Ls : List (ℤ × List (List ℤ))) (wit : List ℤ) (h : certOK s p kl J r0 B W Ls = true)
    (hw : witOK s p kl J wit = true) : lamJit2 s p (kapL p kl) = J := by
  simp only [witOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', allZero, jitL,
    sumToN_eq] at hw
  obtain ⟨⟨hX, hJ⟩, hnz⟩ := hw
  set a : Fin s → ℤ := fun c => lget wit c with ha
  have hfin : ∀ g : ℤ → ℕ, ∑ c, g (a c) = ∑ t ∈ range s, g (lget wit t) := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun t => g (lget wit t)) s]
  have hmem : J ∈ {n | ∃ a : Fin s → ℤ, InLatK p (kapL p kl) a ∧ a ≠ 0 ∧ jitNorm2 a = n} := by
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [inLatK_iff]
      have e : ∑ c ∈ range s, (if c + 1 < s then (nget kl c : ℤ) *
          (if h : c < s then a ⟨c, h⟩ else 0) else -(if h : c < s then a ⟨c, h⟩ else 0)) =
          latX s kl wit := by
        rw [latX, sumTo_eq]
        refine sum_congr rfl fun c hc => ?_
        rw [dite_eq_left (mem_range.1 hc)]
      rw [e]; exact Int.dvd_of_emod_eq_zero hX
    · intro h0
      apply Bool.false_ne_true
      rw [← hnz]
      simp only [beq_iff_eq]
      refine sum_eq_zero fun t ht => ?_
      have := congrFun h0 ⟨t, mem_range.1 ht⟩
      simp only [ha, Pi.zero_apply] at this
      simp [this]
    · unfold jitNorm2
      rw [hfin (fun x => (x.natAbs - 1) ^ 2)]; exact hJ
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨J, hmem⟩ ?_)
  rintro n ⟨b, hb, hb0, rfl⟩
  exact certOK_sound s p kl J r0 B W Ls h b hb hb0

/-! ## Truncated real values -/

theorem trunc_le (J p s : ℕ) (c : ℝ) (hs : 0 < s) (hp : 0 < p) (hc : 0 ≤ c)
    (h : c ^ (2 * s) * (p : ℝ) ^ 2 ≤ (J : ℝ) ^ s) :
    c ≤ Real.sqrt J * (p : ℝ) ^ (-(1 / (s : ℝ))) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ (1 / (s : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp' _
  have hxs : x ^ s = p := by
    rw [hx, one_div]; exact Real.rpow_inv_natCast_pow hp'.le (by omega)
  have hneg : (p : ℝ) ^ (-(1 / (s : ℝ))) = x⁻¹ := by rw [Real.rpow_neg hp'.le]
  rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hx0]
  have hJ : (0 : ℝ) ≤ Real.sqrt J := Real.sqrt_nonneg _
  have h2s : 2 * s ≠ 0 := by omega
  refine (pow_le_pow_iff_left₀ (mul_nonneg hc hx0.le) hJ h2s).1 ?_
  have e1 : (c * x) ^ (2 * s) = c ^ (2 * s) * (x ^ s) ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm s 2]
  have e2 : Real.sqrt J ^ (2 * s) = (J : ℝ) ^ s := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [e1, hxs, e2]; exact h

/-! ## Units -/

/-- `κ_d ≢ 0 (mod p)` for `d < n`. -/
def unitsOK (p : ℕ) (kl : List ℕ) (n : ℕ) : Bool := natAll (fun d => decide (0 < nget kl d % p)) n

theorem units_of_ok (p : ℕ) (kl : List ℕ) (n : ℕ) (h : unitsOK p kl n = true) :
    ∀ d < n, kapL p kl d ≠ 0 := by
  intro d hd h0
  have h1 := (natAll_iff _ _).1 h d hd
  rw [decide_eq_true_eq] at h1
  unfold kapL at h0
  rw [ZMod.natCast_eq_zero_iff, ← nget_eq] at h0
  rw [Nat.mod_eq_zero_of_dvd h0] at h1
  exact absurd h1 (lt_irrefl 0)

end Z3NetF.Proofs.SkCert
