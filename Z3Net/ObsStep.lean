/-
Proof module of entry Obs: steps between neighbouring cells of a graph form with depths
`(k, …, k)` over `ℤ/qℤ` (the geometry of `prop:ceil`, `cor:ceils`, `prop:P2`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsCount
public import Z3Net.FSep

@[expose] public section

/-!
# Entry Obs: steps in a graph form

For the index `w = v + ∑_d e_d n_{d,k-1}` (the last cell level of axis `d` changed by `e_d`), every
offset digit of every coordinate changes by a constant: digit `k + r` of coordinate `c` by
`∑_d e_d (Φ_cd)_{r,k-1}`. The integer coordinate is `X_c = q^(m-k) n_c + q^(m-k-1) r_c + t_c` with the
cell `n_c`, the first offset digit `r_c` and the tail `t_c ∈ [0, q^(m-k-1))` (`X_decompF` of entry F).
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount

noncomputable section

namespace ObsStep

/-! ## Digit arithmetic -/

lemma val_add_int {q : ℕ} [NeZero q] (x : ZMod q) (σ : ℤ) :
    ((x + (σ : ZMod q)).val : ℤ) = ((x.val : ℤ) + σ) % q := by
  have : x + (σ : ZMod q) = (((x.val : ℤ) + σ : ℤ) : ZMod q) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_intCast]

lemma val_m1 {q : ℕ} [NeZero q] : (-1 : ZMod q).val = q - 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by have := Nat.pos_of_neZero q; omega⟩
  rw [ZMod.val_neg_one]; omega

/-- No wrap: adding `σ` to the digit `x` changes its value by exactly `σ`. -/
def NoWrap {q : ℕ} (σ : ℤ) (x : ZMod q) : Prop := ((x + (σ : ZMod q)).val : ℤ) = x.val + σ

instance {q : ℕ} (σ : ℤ) (x : ZMod q) : Decidable (NoWrap σ x) :=
  inferInstanceAs (Decidable (((x + (σ : ZMod q)).val : ℤ) = x.val + σ))

lemma noWrap_iff {q : ℕ} [NeZero q] (σ : ℤ) (x : ZMod q) :
    NoWrap σ x ↔ 0 ≤ (x.val : ℤ) + σ ∧ (x.val : ℤ) + σ < q := by
  unfold NoWrap
  rw [val_add_int]
  have hq : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_neZero q
  constructor
  · intro h
    rw [← h]
    exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
  · rintro ⟨h1, h2⟩
    exact Int.emod_eq_of_lt h1 h2

lemma val_wrap_up {q : ℕ} [NeZero q] (σ : ℤ) (x : ZMod q) (h1 : (q : ℤ) ≤ (x.val : ℤ) + σ)
    (h2 : (x.val : ℤ) + σ < 2 * q) : ((x + (σ : ZMod q)).val : ℤ) = x.val + σ - q := by
  rw [val_add_int]
  have hq : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_neZero q
  calc ((x.val : ℤ) + σ) % q = ((x.val + σ - q) + q) % q := by ring_nf
    _ = (x.val + σ - q) % q := Int.add_emod_right _ _
    _ = x.val + σ - q := Int.emod_eq_of_lt (by linarith) (by linarith)

lemma val_wrap_down {q : ℕ} [NeZero q] (σ : ℤ) (x : ZMod q) (h1 : -(q : ℤ) ≤ (x.val : ℤ) + σ)
    (h2 : (x.val : ℤ) + σ < 0) : ((x + (σ : ZMod q)).val : ℤ) = x.val + σ + q := by
  rw [val_add_int]
  have hq : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_neZero q
  calc ((x.val : ℤ) + σ) % q = ((x.val + σ + q) + q * (-1)) % q := by ring_nf
    _ = (x.val + σ + q) % q := Int.add_mul_emod_self_left _ _ _
    _ = x.val + σ + q := Int.emod_eq_of_lt (by linarith) (by linarith)

/-- At most `|σ|` digits wrap. -/
lemma card_wrap_le {q : ℕ} [NeZero q] (σ : ℤ) :
    (univ.filter fun x : ZMod q => ¬ NoWrap σ x).card ≤ σ.natAbs := by
  classical
  have hq := Nat.pos_of_neZero q
  have hinj : Set.InjOn (fun x : ZMod q => x.val)
      ↑(univ.filter fun x : ZMod q => ¬ NoWrap σ x) := fun x _ y _ h => ZMod.val_injective q h
  rcases le_or_gt 0 σ with h0 | h0
  · refine le_trans (card_le_card_of_injOn (t := Ico (q - σ.natAbs) q) (fun x => x.val) ?_ hinj)
      (by rw [Nat.card_Ico]; omega)
    intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, noWrap_iff, not_and_or,
      not_le, not_lt] at hx
    have hxl := ZMod.val_lt x
    simp only [coe_Ico, Set.mem_Ico]
    omega
  · refine le_trans (card_le_card_of_injOn (t := range σ.natAbs) (fun x => x.val) ?_ hinj)
      (by rw [card_range])
    intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, noWrap_iff, not_and_or,
      not_le, not_lt] at hx
    have hxl := ZMod.val_lt x
    simp only [coe_range, Set.mem_Iio]
    omega

/-! ## Big-endian digit sums `∑_{j ∈ [a, n)} f_j q^(n-1-j)` -/

/-- Digit sum over `[a, n)`. -/
def TS (q : ℕ) (f : ℕ → ℕ) (a n : ℕ) : ℕ := ∑ j ∈ Ico a n, f j * q ^ (n - 1 - j)

lemma TS_succ (q : ℕ) (f : ℕ → ℕ) {a n : ℕ} (h : a < n) :
    TS q f a n = f a * q ^ (n - 1 - a) + TS q f (a + 1) n := by
  unfold TS; rw [Finset.sum_eq_sum_Ico_succ_bot h]

lemma TS_lt {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) (hf : ∀ j, f j < q) :
    ∀ t a n, n = a + t → TS q f a n < q ^ t := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  intro t
  induction t with
  | zero => intro a n h; subst h; simp [TS]
  | succ t ih =>
    intro a n h
    rw [TS_succ (p + 1) f (by omega)]
    have h1 := ih (a + 1) n (by omega)
    have h2 := hf a
    rw [show n - 1 - a = t by omega, pow_succ]
    have : f a * (p + 1) ^ t ≤ p * (p + 1) ^ t := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- A run of digits `q - 1` on `[a, b)` gives `TS ≥ q^(n-a) - q^(n-b)`. -/
lemma TS_ge {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) :
    ∀ t a b n, b = a + t → b ≤ n → (∀ j, a ≤ j → j < b → f j = q - 1) →
      q ^ (n - a) ≤ TS q f a n + q ^ (n - b) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  intro t
  induction t with
  | zero => intro a b n h _ _; subst h; simp
  | succ t ih =>
    intro a b n h hbn hf
    rw [TS_succ (p + 1) f (by omega), hf a le_rfl (by omega)]
    have h1 := ih (a + 1) b n (by omega) hbn (fun j h1 h2 => hf j (by omega) h2)
    have e : (p + 1) ^ (n - a) = (p + 1 - 1) * (p + 1) ^ (n - 1 - a) + (p + 1) ^ (n - (a + 1)) := by
      rw [show n - (a + 1) = n - 1 - a by omega, show n - a = (n - 1 - a) + 1 by omega, pow_succ,
        Nat.add_sub_cancel]
      ring
    omega

/-! ## Graph forms with depths `(k, …, k)` -/

variable {s q k : ℕ} [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))

lemma Cg_eq : Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ = Z3NetU.graphGen s k Φ :=
  graphGenK_const s k Φ

lemma dig_cell (c : Fin s) (v : Fin (s * k) → ZMod q) (i : ℕ) (hi : i < k) :
    dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v i =
      v (Z3NetU.Proofs.ix k c ⟨i, hi⟩) := by
  rw [Cg_eq]
  unfold dig
  rw [dif_pos (lt_of_lt_of_le hi (Z3NetU.Proofs.k_le_sk k c))]
  exact Z3NetU.Proofs.graphGen_cell k Φ c v i hi

lemma dig_off (c : Fin s) (v : Fin (s * k) → ZMod q) (r : ℕ) (hr : r < s * k - k) :
    dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v (k + r) =
      ∑ d : Fin s, ∑ l : Fin k, Φ c d ⟨r, hr⟩ l * v (Z3NetU.Proofs.ix k d l) := by
  rw [Cg_eq]
  unfold dig
  rw [dif_pos (by omega)]
  exact Z3NetU.Proofs.graphGen_off k Φ c v ⟨r, hr⟩

/-- The step vector `∑_d e_d n_{d,k-1}`. -/
def stepVec (hk : 0 < k) (e : Fin s → ZMod q) : Fin (s * k) → ZMod q :=
  ∑ d : Fin s, e d • Pi.single (Z3NetU.Proofs.ix k d ⟨k - 1, by omega⟩) (1 : ZMod q)

lemma stepVec_apply (hk : 0 < k) (e : Fin s → ZMod q) (d : Fin s) (l : Fin k) :
    stepVec hk e (Z3NetU.Proofs.ix k d l) = if (l : ℕ) = k - 1 then e d else 0 := by
  unfold stepVec
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · by_cases hl : (l : ℕ) = k - 1
    · rw [if_pos hl, Pi.single_apply, if_pos (by ext; simp [Z3NetU.Proofs.ix, hl]), mul_one]
    · rw [if_neg hl, Pi.single_apply, if_neg, mul_zero]
      intro h
      have := congrArg (fun x : Fin (s * k) => (x : ℕ) % k) h
      simp only [Z3NetU.Proofs.ix_mod] at this
      exact hl this
  · intro d' _ hd'
    rw [Pi.single_apply, if_neg, mul_zero]
    intro h
    have := congrArg (fun x : Fin (s * k) => (x : ℕ) / k) h
    simp only [Z3NetU.Proofs.ix_div] at this
    exact hd' (Fin.ext this.symm)
  · simp

lemma dig_step_cell (hk : 0 < k) (e : Fin s → ZMod q) (c : Fin s) (i : ℕ) (hi : i < k) :
    dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) (stepVec hk e) i =
      if i = k - 1 then e c else 0 := by
  rw [dig_cell Φ c _ i hi, stepVec_apply]

lemma dig_step_off (hk : 0 < k) (e : Fin s → ZMod q) (c : Fin s) (r : ℕ) (hr : r < s * k - k) :
    dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) (stepVec hk e) (k + r) =
      ∑ d : Fin s, e d * Z3NetF.ent (Φ c d) r (k - 1) := by
  rw [dig_off Φ c _ r hr]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [stepVec_apply, if_pos rfl]
    unfold Z3NetF.ent
    rw [dif_pos ⟨hr, by omega⟩]
    ring
  · intro l _ hl
    rw [stepVec_apply, if_neg (fun h => hl (Fin.ext h)), mul_zero]
  · simp

/-! ## Coordinates: cell, first offset digit, tail -/

/-- The tail `t_c = ∑_{j ∈ [k+1, sk)} d_j q^(sk-1-j)`. -/
def tl (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ :=
  TS q (fun j => (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v j).val) (k + 1) (s * k)

lemma dv_eq (v : Fin (s * k) → ZMod q) (c : Fin s) (j : ℕ) :
    Z3NetU.Proofs.dv s q k (DgF s q k Φ c v) j =
      (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v j).val := by
  unfold Z3NetU.Proofs.dv DgF dig
  rw [Cg_eq]
  split_ifs <;> simp

lemma X_eq (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    (Z3NetF.gfPoint q k Φ v c : ℤ) = (q : ℤ) ^ (s * k - k) * Z3NetU.Proofs.cellN s q k v c +
      ((q : ℤ) ^ (s * k - k - 1) *
        (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k).val + tl Φ v c) := by
  have h := X_decompF s q k Φ hsk v c
  unfold Z3NetF.gfPoint
  rw [h]
  congr 3
  · unfold o0F; rw [dv_eq]
  · unfold tlF tl Z3NetU.Proofs.tail TS
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dv_eq]

lemma tl_lt (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    tl Φ v c < q ^ (s * k - k - 1) :=
  TS_lt (Nat.pos_of_neZero q) _ (fun j => ZMod.val_lt _) _ _ _ (by omega)

lemma cellN_split (hk : 0 < k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    Z3NetU.Proofs.cellN s q k v c =
      (∑ i ∈ range (k - 1), Z3NetU.Proofs.ad s q k v c i * q ^ (k - 1 - i)) +
        (v (Z3NetU.Proofs.ix k c ⟨k - 1, by omega⟩)).val := by
  unfold Z3NetU.Proofs.cellN
  have e : range k = range (k - 1 + 1) := by congr 1; omega
  rw [e, Finset.sum_range_succ]
  congr 1
  · simp only [Z3NetU.Proofs.ad, dif_pos (show k - 1 < k by omega), Nat.sub_self, pow_zero,
      mul_one]

/-- Cell change of an axis under the step: the levels above `k-1` are unchanged. -/
lemma cellN_step (hk : 0 < k) (v : Fin (s * k) → ZMod q) (e : Fin s → ZMod q) (c : Fin s) :
    (Z3NetU.Proofs.cellN s q k (v + stepVec hk e) c : ℤ) - Z3NetU.Proofs.cellN s q k v c =
      ((v (Z3NetU.Proofs.ix k c ⟨k - 1, by omega⟩) + e c).val : ℤ) -
        (v (Z3NetU.Proofs.ix k c ⟨k - 1, by omega⟩)).val := by
  rw [cellN_split hk, cellN_split hk]
  have : ∀ i ∈ range (k - 1), Z3NetU.Proofs.ad s q k (v + stepVec hk e) c i =
      Z3NetU.Proofs.ad s q k v c i := by
    intro i hi
    simp only [mem_range] at hi
    simp only [Z3NetU.Proofs.ad, dif_pos (show i < k by omega), Pi.add_apply, stepVec_apply,
      if_neg (show ¬ i = k - 1 by omega), add_zero]
  rw [Finset.sum_congr rfl fun i hi => by rw [this i hi]]
  simp only [Pi.add_apply, stepVec_apply, if_pos rfl]
  push_cast
  ring

end ObsStep

end

end Z3NetF.Proofs
