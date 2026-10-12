/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Sep

@[expose] public section

/-!
# V14 stage S14′: kernel checkers for the base-2/3 certificates, part 1 (code arithmetic and `μ`)

Digit vectors are natural numbers (`vecOf b n x`, digit `0` most significant; `dg b x k` is the digit of weight
`b^k`). Digitwise addition `dadd` (`xor` in base `2`), scalar multiples `smul`, matrix–vector products on column codes
`matvec`; their semantics `vecOf_dadd`, `vecOf_smul`, `vecOf_matvec`.

`mulb b n x` is a lower bound for `μ_n` of the digit vector `x` (`lem:shiftcert`): every difference
`int(X ⊕ δ) − int X` is `int δ − ∑_{k ∈ B} b^{k+1}` for a set `B` of positions in the support of `δ` (the carries);
`Fm` bounds `min_B |T − ∑_{k∈B} b^{k+1}|` from below by the recursion over the positions from the top, using that the
lower generators sum to at most `R_k = ∑_{k' < k, δ_{k'} ≠ 0} b^{k'+1} < b^{k+1}`; the toroidal distance is the
minimum over `T = int δ, int δ ∓ b^n`. Soundness: `mulb_le`.
-/

namespace Z3NetB23

/-! ## Code arithmetic (computable, kernel friendly) -/

/-- The digit of weight `b^k` of `x`. -/
def dg (b x k : ℕ) : ℕ := (x / b ^ k) % b

/-- Digitwise addition modulo `b` of the lowest `n` digits (generic). -/
def daddN (b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, y => daddN b n (x / b) (y / b) * b + (x % b + y % b) % b

/-- Digitwise addition modulo `b` of `n`-digit vectors (`xor` in base `2`). -/
def dadd (b n x y : ℕ) : ℕ := if b = 2 then x ^^^ y else daddN b n x y

/-- The digitwise multiple `a · x`. -/
def smul (b n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a + 1, x => dadd b n x (smul b n a x)

/-- `∑_t v_{i+t} · cols[t]` (`v` a `k`-digit vector, `v_i` its digit `i`, digit `0` most significant). -/
def mvAux (b n k : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, i, v => dadd b n (smul b n (dg b v (k - 1 - i)) c) (mvAux b n k cs (i + 1) v)

/-- The matrix–vector product on codes: the `n`-digit code of `M v`, `M` the `n × k` matrix with column codes
`cols`, `v` a `k`-digit code. -/
def matvec (b n k : ℕ) (cols : List ℕ) (v : ℕ) : ℕ := mvAux b n k cols 0 v

/-- The `n × k` matrix with column codes `cols`. -/
def colMatR (b n k : ℕ) (cols : List ℕ) : Matrix (Fin n) (Fin k) (ZMod b) :=
  fun r i => vecOf b n (cols.getD i 0) r

/-! ## `μ` lower bound -/

/-- The support code: digit `k` of the result is `1` iff digit `k` of `x` is nonzero (`n` digits). -/
def suppN (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => suppN b n (x / b) * b + (if x % b = 0 then 0 else 1)

/-- Lower bound for `min_B |T − ∑_{k ∈ B} b^{k+1}|` over the subsets `B` of the support of `x` below `k`
(`sp` the support code of `x`). -/
def Fm (b x sp : ℕ) : ℕ → ℤ → ℕ
  | 0, T => T.natAbs
  | k + 1, T =>
    if dg b x k = 0 then Fm b x sp k T else
      min (if T < 0 then T.natAbs else if T > ((b * (sp % b ^ k) : ℕ) : ℤ) then (T - ((b * (sp % b ^ k) : ℕ) : ℤ)).natAbs
            else Fm b x sp k T)
        (if T - ((b ^ (k + 1) : ℕ) : ℤ) < 0 then (T - ((b ^ (k + 1) : ℕ) : ℤ)).natAbs
          else if T - ((b ^ (k + 1) : ℕ) : ℤ) > ((b * (sp % b ^ k) : ℕ) : ℤ) then
            (T - ((b ^ (k + 1) : ℕ) : ℤ) - ((b * (sp % b ^ k) : ℕ) : ℤ)).natAbs
          else Fm b x sp k (T - ((b ^ (k + 1) : ℕ) : ℤ)))

/-- **Lower bound for `μ_n`** of the `n`-digit vector `x` (`lem:shiftcert`). -/
def mulb (b n x : ℕ) : ℕ :=
  if x = 0 then 0 else
    min (Fm b x (suppN b n x) n x)
      (min (Fm b x (suppN b n x) n ((x : ℤ) - ((b ^ n : ℕ) : ℤ))) (Fm b x (suppN b n x) n ((x : ℤ) + ((b ^ n : ℕ) : ℤ))))

end Z3NetB23

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

variable {b : ℕ}

/-! ## Semantics of the code arithmetic -/

lemma vecOf_apply (n x : ℕ) (j : Fin n) : vecOf b n x j = ((dg b x (n - 1 - j) : ℕ) : ZMod b) := rfl

lemma dg_lt (hb : 0 < b) (x k : ℕ) : dg b x k < b := Nat.mod_lt _ hb

lemma dg_daddN (hb : 0 < b) : ∀ (n x y k : ℕ), k < n → dg b (daddN b n x y) k = (dg b x k + dg b y k) % b := by
  intro n
  induction n with
  | zero => intro x y k hk; omega
  | succ n ih =>
    intro x y k hk
    simp only [daddN]
    have hr : (x % b + y % b) % b < b := Nat.mod_lt _ hb
    cases k with
    | zero =>
      simp only [dg, pow_zero, Nat.div_one]
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_mod]
    | succ k =>
      have := ih (x / b) (y / b) k (by omega)
      simp only [dg] at this ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.mul_comm (daddN b n (x / b) (y / b)) b, Nat.mul_add_div hb, Nat.div_eq_of_lt hr, add_zero, this]

lemma daddN_lt (hb : 0 < b) : ∀ (n x y : ℕ), daddN b n x y < b ^ n := by
  intro n
  induction n with
  | zero => intro x y; simp [daddN]
  | succ n ih =>
    intro x y
    simp only [daddN]
    have h1 := ih (x / b) (y / b)
    have h2 : (x % b + y % b) % b < b := Nat.mod_lt _ hb
    calc daddN b n (x / b) (y / b) * b + (x % b + y % b) % b < daddN b n (x / b) (y / b) * b + b := by omega
      _ = (daddN b n (x / b) (y / b) + 1) * b := by ring
      _ ≤ b ^ n * b := Nat.mul_le_mul_right _ h1
      _ = b ^ (n + 1) := by ring

lemma dg_xor (x y k : ℕ) : dg 2 (x ^^^ y) k = (dg 2 x k + dg 2 y k) % 2 := by
  simp only [dg]
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_xor]
  cases Nat.testBit x k <;> cases Nat.testBit y k <;> rfl

lemma dg_dadd (hb : 0 < b) (n x y k : ℕ) (hk : k < n) : dg b (dadd b n x y) k = (dg b x k + dg b y k) % b := by
  unfold dadd
  split_ifs with h
  · subst h; exact dg_xor x y k
  · exact dg_daddN hb n x y k hk

lemma vecOf_dadd [NeZero b] (n x y : ℕ) : vecOf b n (dadd b n x y) = vecOf b n x + vecOf b n y := by
  funext j
  simp only [vecOf_apply, Pi.add_apply]
  rw [dg_dadd (Nat.pos_of_neZero b) n x y _ (by omega)]
  push_cast
  rw [ZMod.natCast_mod]
  push_cast; ring

lemma vecOf_zero (n : ℕ) : vecOf b n 0 = 0 := by
  funext j; simp [vecOf_apply, dg]

lemma vecOf_smul [NeZero b] (n : ℕ) : ∀ (a x : ℕ), vecOf b n (smul b n a x) = (a : ZMod b) • vecOf b n x := by
  intro a
  induction a with
  | zero => intro x; simp [smul, vecOf_zero]
  | succ a ih =>
    intro x
    simp only [smul]
    rw [vecOf_dadd, ih]
    push_cast
    rw [add_smul, one_smul, add_comm]

lemma vecOf_mvAux [NeZero b] (n k : ℕ) (v : ℕ) :
    ∀ (cs : List ℕ) (i : ℕ) (r : Fin n),
      vecOf b n (mvAux b n k cs i v) r = ∑ t : Fin cs.length, ((dg b v (k - 1 - (i + t)) : ℕ) : ZMod b) *
        vecOf b n (cs.get t) r := by
  intro cs
  induction cs with
  | nil => intro i r; simp [mvAux, vecOf_zero]
  | cons c cs ih =>
    intro i r
    simp only [mvAux]
    rw [vecOf_dadd, Pi.add_apply, vecOf_smul, Pi.smul_apply, smul_eq_mul, ih (i + 1) r]
    show _ = ∑ t : Fin (cs.length + 1), ((dg b v (k - 1 - (i + (t : ℕ))) : ℕ) : ZMod b) *
      vecOf b n ((c :: cs).get t) r
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, Fin.val_zero, add_zero, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 3
    omega

/-- **Matrix–vector products on codes.** -/
lemma vecOf_matvec [NeZero b] (n k : ℕ) (cols : List ℕ) (hlen : cols.length = k) (v : ℕ) :
    vecOf b n (matvec b n k cols v) = colMatR b n k cols *ᵥ vecOf b k v := by
  funext r
  rw [matvec, vecOf_mvAux n k v cols 0 r]
  simp only [mulVec, dotProduct, colMatR, vecOf_apply]
  subst hlen
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [zero_add, List.get_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem t.isLt,
    Option.getD_some]
  ring

/-! ## Digit vectors and their codes -/

lemma dval_vecOf [NeZero b] (n x : ℕ) (hx : x < b ^ n) : dval b (vecOf b n x) = x := by
  rw [dval_eq]
  conv_rhs => rw [← Z3NetF.Proofs.digSum_recon (Nat.pos_of_neZero b) n x hx]
  congr 1
  funext j
  simp only [vecOf_apply, dg, ZMod.val_natCast]
  rw [Nat.mod_mod]

/-- The code of a digit vector. -/
lemma vecOf_dval [NeZero b] {n : ℕ} (x : Fin n → ZMod b) : vecOf b n (dval b x) = x := by
  funext j
  simp only [vecOf_apply, dg, dval_eq]
  rw [Z3NetF.Proofs.digSum_digit (Nat.pos_of_neZero b) n _ (fun _ => ZMod.val_lt _) j, ZMod.natCast_zmod_val]

/-- The top `H` digits of a code. -/
lemma topD_vecOf [NeZero b] (n H x : ℕ) (hH : H ≤ n) :
    topD H hH (vecOf b n x) = vecOf b H (x / b ^ (n - H)) := by
  funext r
  simp only [topD, vecOf_apply, dg, Fin.coe_castLE]
  congr 2
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  omega

/-! ## Soundness of the `μ` lower bound -/

section mu

lemma dg_succ (x k : ℕ) : dg b x (k + 1) = dg b (x / b) k := by
  simp only [dg, pow_succ', Nat.div_div_eq_div_mul]

lemma dval_succ {n : ℕ} (y : Fin (n + 1) → ZMod b) :
    dval b y = b * dval b (fun j : Fin n => y j.castSucc) + (y (Fin.last n)).val := by
  rw [dval_eq, Z3Net.Proofs.digSum_succ]; rfl

lemma vecOf_castSucc (n x : ℕ) (j : Fin n) : vecOf b (n + 1) x j.castSucc = vecOf b n (x / b) j := by
  simp only [vecOf_apply, Fin.val_castSucc]
  rw [show n + 1 - 1 - (j : ℕ) = (n - 1 - j) + 1 by omega, dg_succ]

lemma vecOf_last (n x : ℕ) : vecOf b (n + 1) x (Fin.last n) = ((x % b : ℕ) : ZMod b) := by
  simp [vecOf_apply, dg]

/-- **The carries**: `int(X ⊕ δ) − int X = int δ − ∑_{k ∈ B} b^{k+1}` for a set `B` of positions (weight index)
in the support of `δ`. -/
lemma carry_decomp [NeZero b] : ∀ (n : ℕ) (X : Fin n → ZMod b) (x : ℕ), x < b ^ n →
    ∃ B : Finset ℕ, (∀ k ∈ B, k < n ∧ dg b x k ≠ 0) ∧
      (dval b (X + vecOf b n x) : ℤ) - dval b X = x - ∑ k ∈ B, (b : ℤ) ^ (k + 1) := by
  have hb := Nat.pos_of_neZero b
  intro n
  induction n with
  | zero =>
    intro X x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    refine ⟨∅, by simp, ?_⟩
    simp [dval]
  | succ n ih =>
    intro X x hx
    have hxb : x / b < b ^ n := by
      rw [Nat.div_lt_iff_lt_mul hb]; rw [pow_succ] at hx; exact hx
    obtain ⟨B', hB', hD'⟩ := ih (fun j => X j.castSucc) (x / b) hxb
    have hXl := ZMod.val_lt (X (Fin.last n))
    have hxm := Nat.mod_lt x hb
    have hinj : Set.InjOn (· + 1 : ℕ → ℕ) B' := fun a _ a' _ h => by simpa using h
    refine ⟨B'.image (· + 1) ∪ (if b ≤ (X (Fin.last n)).val + x % b then {0} else ∅), ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_union, Finset.mem_image] at hk
      rcases hk with ⟨k', hk', rfl⟩ | hk
      · obtain ⟨h1, h2⟩ := hB' k' hk'
        exact ⟨by omega, by rw [dg_succ]; exact h2⟩
      · split_ifs at hk with hc
        · rw [Finset.mem_singleton] at hk; subst hk
          refine ⟨by omega, ?_⟩
          simp only [dg, pow_zero, Nat.div_one]; omega
        · simp at hk
    · rw [dval_succ, dval_succ]
      have e1 : (fun j : Fin n => (X + vecOf b (n + 1) x) j.castSucc) = (fun j => X j.castSucc) + vecOf b n (x / b) := by
        funext j; simp only [Pi.add_apply, vecOf_castSucc]
      rw [e1]
      have hlast : ((X + vecOf b (n + 1) x) (Fin.last n)).val = ((X (Fin.last n)).val + x % b) % b := by
        rw [Pi.add_apply, vecOf_last, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hxm]
      rw [hlast]
      have hdisj : Disjoint (B'.image (· + 1)) (if b ≤ (X (Fin.last n)).val + x % b then {0} else ∅) := by
        split_ifs
        · rw [Finset.disjoint_singleton_right, Finset.mem_image]; rintro ⟨k, -, hk⟩; omega
        · exact Finset.disjoint_empty_right _
      rw [Finset.sum_union hdisj, Finset.sum_image hinj]
      have hsum : ∑ k ∈ B', (b : ℤ) ^ (k + 1 + 1) = b * ∑ k ∈ B', (b : ℤ) ^ (k + 1) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsum]
      have hx' : (x : ℤ) = b * ((x / b : ℕ) : ℤ) + ((x % b : ℕ) : ℤ) := by
        have := Nat.div_add_mod x b; exact_mod_cast this.symm
      split_ifs with hc
      · rw [Finset.sum_singleton, zero_add, pow_one]
        have hm : ((X (Fin.last n)).val + x % b) % b = (X (Fin.last n)).val + x % b - b := by
          rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
        rw [hm, hx']
        generalize x / b = y at hD' ⊢
        push_cast [hc]
        linear_combination (b : ℤ) * hD'
      · rw [Finset.sum_empty, add_zero, Nat.mod_eq_of_lt (by omega), hx']
        generalize x / b = y at hD' ⊢
        push_cast
        linear_combination (b : ℤ) * hD'

/-- The support code. -/
lemma suppN_mod (hb : 2 ≤ b) : ∀ (n x k : ℕ), k ≤ n →
    suppN b n x % b ^ k = ∑ k' ∈ Finset.range k, if dg b x k' = 0 then 0 else b ^ k' := by
  intro n
  induction n with
  | zero =>
    intro x k hk
    obtain rfl : k = 0 := by omega
    simp [Nat.mod_one]
  | succ n ih =>
    intro x k hk
    cases k with
    | zero => simp [Nat.mod_one]
    | succ k =>
      simp only [suppN]
      set S := suppN b n (x / b)
      set i := if x % b = 0 then 0 else 1
      have hi : i < b := by simp only [i]; split_ifs <;> omega
      have hlt : (S % b ^ k) * b + i < b ^ (k + 1) := by
        have := Nat.mod_lt S (pow_pos (by omega : 0 < b) k)
        calc (S % b ^ k) * b + i < (S % b ^ k) * b + b := Nat.add_lt_add_left hi _
          _ = (S % b ^ k + 1) * b := by ring
          _ ≤ b ^ k * b := Nat.mul_le_mul_right _ this
          _ = b ^ (k + 1) := by ring
      have e : (S * b + i) % b ^ (k + 1) = (S % b ^ k) * b + i := by
        have h1 := Nat.div_add_mod S (b ^ k)
        calc (S * b + i) % b ^ (k + 1) = ((S % b ^ k) * b + i + b ^ (k + 1) * (S / b ^ k)) % b ^ (k + 1) := by
              congr 1; nth_rewrite 1 [← h1]; ring
          _ = ((S % b ^ k) * b + i) % b ^ (k + 1) := Nat.add_mul_mod_self_left _ _ _
          _ = _ := Nat.mod_eq_of_lt hlt
      rw [e, ih (x / b) k (by omega), Finset.sum_range_succ', Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun k' _ => ?_
        rw [dg_succ]
        split_ifs <;> ring
      · simp [i, dg]

lemma gstep (T' R s' : ℤ) (v : ℕ) (h0 : 0 ≤ s') (hR : s' ≤ R) (hv : (v : ℤ) ≤ |T' - s'|) :
    (((if T' < 0 then T'.natAbs else if T' > R then (T' - R).natAbs else v : ℕ)) : ℤ) ≤ |T' - s'| := by
  split_ifs with h1 h2
  · rw [Int.natCast_natAbs, abs_of_neg h1, abs_of_neg (by linarith)]; linarith
  · rw [Int.natCast_natAbs, abs_of_pos (by linarith : (0:ℤ) < T' - R), abs_of_pos (by linarith)]; linarith
  · exact hv

lemma R_eq (hb : 2 ≤ b) (n x k : ℕ) (hk : k ≤ n) :
    ((b * (suppN b n x % b ^ k) : ℕ) : ℤ) = ∑ k' ∈ Finset.range k, if dg b x k' = 0 then 0 else (b : ℤ) ^ (k' + 1) := by
  rw [suppN_mod hb n x k hk, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k' _ => ?_
  split_ifs <;> push_cast <;> ring

lemma sub_le_R (B : Finset ℕ) (x k : ℕ) (hB : ∀ k' ∈ B, k' < k ∧ dg b x k' ≠ 0) :
    ∑ k' ∈ B, (b : ℤ) ^ (k' + 1) ≤ ∑ k' ∈ Finset.range k, if dg b x k' = 0 then 0 else (b : ℤ) ^ (k' + 1) := by
  have e : ∑ k' ∈ B, (b : ℤ) ^ (k' + 1) = ∑ k' ∈ B, if dg b x k' = 0 then 0 else (b : ℤ) ^ (k' + 1) :=
    Finset.sum_congr rfl fun k' hk' => by rw [if_neg (hB k' hk').2]
  rw [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k' hk'; exact Finset.mem_range.2 (hB k' hk').1
  · intro k' _ _; split_ifs <;> positivity

lemma Fm_le (hb : 2 ≤ b) (n x : ℕ) : ∀ k, k ≤ n → ∀ (T : ℤ) (B : Finset ℕ), (∀ k' ∈ B, k' < k ∧ dg b x k' ≠ 0) →
    (Fm b x (suppN b n x) k T : ℤ) ≤ |T - ∑ k' ∈ B, (b : ℤ) ^ (k' + 1)| := by
  intro k
  induction k with
  | zero =>
    intro _ T B hB
    have : B = ∅ := Finset.eq_empty_of_forall_notMem fun k' hk' => by have := (hB k' hk').1; omega
    subst this
    simp [Fm]
  | succ k ih =>
    intro hk T B hB
    simp only [Fm]
    by_cases hd : dg b x k = 0
    · rw [if_pos hd]
      exact ih (by omega) T B fun k' hk' => ⟨by
        have h1 := hB k' hk'
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1.1 with h | h
        · exact h
        · exact absurd (h ▸ hd) h1.2, (hB k' hk').2⟩
    · rw [if_neg hd]
      have hB' : ∀ k' ∈ B.erase k, k' < k ∧ dg b x k' ≠ 0 := by
        intro k' hk'
        obtain ⟨hne, hk'B⟩ := Finset.mem_erase.1 hk'
        exact ⟨by have := (hB k' hk'B).1; omega, (hB k' hk'B).2⟩
      have hR := R_eq hb n x k (by omega)
      have hs0 : 0 ≤ ∑ k' ∈ B.erase k, (b : ℤ) ^ (k' + 1) := Finset.sum_nonneg fun _ _ => by positivity
      have hsR : ∑ k' ∈ B.erase k, (b : ℤ) ^ (k' + 1) ≤ ((b * (suppN b n x % b ^ k) : ℕ) : ℤ) := by
        rw [hR]; exact sub_le_R _ x k hB'
      push_cast [Nat.cast_min]
      by_cases hkB : k ∈ B
      · rw [← Finset.add_sum_erase B _ hkB]
        refine le_trans (min_le_right _ _) ?_
        have := gstep (T - ((b ^ (k + 1) : ℕ) : ℤ)) (((b * (suppN b n x % b ^ k) : ℕ) : ℤ))
          (∑ k' ∈ B.erase k, (b : ℤ) ^ (k' + 1)) (Fm b x (suppN b n x) k (T - ((b ^ (k + 1) : ℕ) : ℤ)))
          hs0 hsR (ih (by omega) _ _ hB')
        push_cast at this
        convert this using 2; ring
      · have hBe : B.erase k = B := Finset.erase_eq_of_notMem hkB
        rw [hBe] at hB' hs0 hsR
        refine le_trans (min_le_left _ _) ?_
        have := gstep T (((b * (suppN b n x % b ^ k) : ℕ) : ℤ)) (∑ k' ∈ B, (b : ℤ) ^ (k' + 1))
          (Fm b x (suppN b n x) k T) hs0 hsR (ih (by omega) _ _ hB')
        push_cast at this
        exact this

/-- **Soundness of `mulb`**: `mulb b n x ≤ |int(X ⊕ δ) − int X|_{b^n}` for every digit vector `X`, `δ` the digit
vector of `x < b^n`; hence `mulb b n x ≤ μ_n(δ)`. -/
theorem mulb_le (hb : 2 ≤ b) (n x : ℕ) (hx : x < b ^ n) (X : Fin n → ZMod b) :
    have : NeZero b := ⟨by omega⟩
    mulb b n x ≤ Z3NetF.cres (b ^ n) ((dval b (X + vecOf b n x) : ℤ) - dval b X) := by
  have : NeZero b := ⟨by omega⟩
  unfold mulb
  split_ifs with h0
  · exact Nat.zero_le _
  obtain ⟨B, hB, hD⟩ := carry_decomp n X x hx
  set D : ℤ := (dval b (X + vecOf b n x) : ℤ) - dval b X
  set N : ℤ := ((b ^ n : ℕ) : ℤ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast pow_pos (by omega) n
  have hD1 : |D| < N := by
    have a1 := dval_lt (X + vecOf b n x)
    have a2 := dval_lt X
    have b1 : ((dval b (X + vecOf b n x) : ℕ) : ℤ) < N := by simp only [N]; exact_mod_cast a1
    have b2 : ((dval b X : ℕ) : ℤ) < N := by simp only [N]; exact_mod_cast a2
    rw [abs_lt]; constructor <;> simp only [D] <;> omega
  obtain ⟨t, ht⟩ := Z3NetC.Proofs.cres_exists (b ^ n) (pow_pos (by omega) n) D
  have F0 := Fm_le hb n x n le_rfl (x : ℤ) B hB
  have F1 := Fm_le hb n x n le_rfl ((x : ℤ) - N) B hB
  have F2 := Fm_le hb n x n le_rfl ((x : ℤ) + N) B hB
  have e0 : (x : ℤ) - ∑ k ∈ B, (b : ℤ) ^ (k + 1) = D := hD.symm
  rw [e0] at F0
  rw [show (x : ℤ) - N - ∑ k ∈ B, (b : ℤ) ^ (k + 1) = D - N by rw [← e0]; ring] at F1
  rw [show (x : ℤ) + N - ∑ k ∈ B, (b : ℤ) ^ (k + 1) = D + N by rw [← e0]; ring] at F2
  suffices hs : ((min (Fm b x (suppN b n x) n x) (min (Fm b x (suppN b n x) n ((x : ℤ) - N))
      (Fm b x (suppN b n x) n ((x : ℤ) + N))) : ℕ) : ℤ) ≤ Z3NetF.cres (b ^ n) D by exact_mod_cast hs
  rw [ht]
  have hNt : (↑(b ^ n : ℕ) : ℤ) = N := rfl
  rw [hNt]
  push_cast
  rcases lt_trichotomy t 0 with htn | rfl | htp
  · rcases eq_or_lt_of_le (show t ≤ -1 by omega) with rfl | htn2
    · refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
      convert F1 using 2; ring
    · refine le_trans (min_le_left _ _) (F0.trans ?_)
      have : N * 2 ≤ |N * t| := by
        rw [abs_mul, abs_of_pos hN]; have : (2 : ℤ) ≤ |t| := by rw [abs_of_neg htn]; omega
        nlinarith
      have h3 := abs_sub_abs_le_abs_sub (N * t) (-D)
      rw [sub_neg_eq_add, abs_neg, add_comm] at h3
      linarith
  · refine le_trans (min_le_left _ _) ?_
    simpa using F0
  · rcases eq_or_lt_of_le (show 1 ≤ t by omega) with rfl | htp2
    · refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ?_)
      convert F2 using 2; ring
    · refine le_trans (min_le_left _ _) (F0.trans ?_)
      have : N * 2 ≤ |N * t| := by
        rw [abs_mul, abs_of_pos hN, abs_of_pos (by omega : (0:ℤ) < t)]; nlinarith
      have h3 := abs_sub_abs_le_abs_sub (N * t) (-D)
      rw [sub_neg_eq_add, abs_neg, add_comm] at h3
      linarith

end mu

end Z3NetB23.Proofs
