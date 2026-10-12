module
public import QUNetsM3.Defs

@[expose] public section

/-!
# Digit packing lemmas

`coord` and `digits` are mutually inverse on `[0, p³)`, and the elementary-box index
`coord w / p ^ (3 - d)` sees exactly the leading `d` digits of `w`.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

theorem digit_lt [NeZero p] (w : Fin 3 → ZMod p) (i : Fin 3) : (w i).val < p := ZMod.val_lt _

/-- The packing of three digits below `p` stays below `p ^ 3`. -/
theorem pack_lt {a b c : ℕ} (ha : a < p) (hb : b < p) (hc : c < p) :
    a * p ^ 2 + b * p + c < p ^ 3 := by
  have h1 : (b + 1) * p ≤ p * p := Nat.mul_le_mul_right _ hb
  have h2 : (a + 1) * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right _ ha
  have e : p ^ 3 = p * p ^ 2 := by ring
  have e2 : p ^ 2 = p * p := by ring
  rw [e]; rw [e2] at h2 ⊢; nlinarith

theorem coord_lt [NeZero p] (w : Fin 3 → ZMod p) : coord p w < p ^ 3 :=
  pack_lt (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)

theorem pack_div_p {a b c : ℕ} (hc : c < p) : (a * p ^ 2 + b * p + c) / p = a * p + b := by
  have hp : 0 < p := by omega
  have e : a * p ^ 2 + b * p + c = c + (a * p + b) * p := by ring
  rw [e, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hc, zero_add]

theorem pack_div_p2 {a b c : ℕ} (hb : b < p) (hc : c < p) :
    (a * p ^ 2 + b * p + c) / p ^ 2 = a := by
  have hp : 0 < p ^ 2 := pow_pos (by omega) 2
  have hlt : b * p + c < p ^ 2 := by
    have h1 : (b + 1) * p ≤ p * p := Nat.mul_le_mul_right _ hb
    nlinarith
  have e : a * p ^ 2 + b * p + c = (b * p + c) + a * p ^ 2 := by ring
  rw [e, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hlt, zero_add]

theorem pack_mod_p {a b c : ℕ} (hc : c < p) : (a * p ^ 2 + b * p + c) % p = c := by
  have e : a * p ^ 2 + b * p + c = c + (a * p + b) * p := by ring
  rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem coord_def (w : Fin 3 → ZMod p) :
    coord p w = (w 0).val * p ^ 2 + (w 1).val * p + (w 2).val := rfl

/-- `digits` inverts `coord`. -/
theorem digits_coord [NeZero p] (w : Fin 3 → ZMod p) : digits p (coord p w) = w := by
  have h0 := ZMod.val_lt (w 0)
  have h1 := ZMod.val_lt (w 1)
  have h2 := ZMod.val_lt (w 2)
  funext i
  fin_cases i
  · simp only [digits, coord_def, Fin.zero_eta, Matrix.cons_val_zero]
    rw [pack_div_p2 h1 h2, ZMod.natCast_zmod_val]
  · simp only [digits, coord_def, Fin.mk_one, Matrix.cons_val_one]
    rw [pack_div_p h2]
    push_cast [ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring
  · simp only [digits, coord_def, Fin.reduceFinMk, Matrix.cons_val]
    push_cast [ZMod.natCast_self, ZMod.natCast_zmod_val]
    ring

theorem digits_val0 (x : ℕ) : (digits p x 0).val = x / p ^ 2 % p := by
  simp [digits, ZMod.val_natCast]

theorem digits_val1 (x : ℕ) : (digits p x 1).val = x / p % p := by
  simp [digits, ZMod.val_natCast]

theorem digits_val2 (x : ℕ) : (digits p x 2).val = x % p := by
  simp [digits, ZMod.val_natCast]

/-- `coord` inverts `digits` on `[0, p³)`. -/
theorem coord_digits [NeZero p] {x : ℕ} (hx : x < p ^ 3) : coord p (digits p x) = x := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [coord_def, digits_val0, digits_val1, digits_val2]
  have hlt : x / p ^ 2 < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp 2)]
    calc x < p ^ 3 := hx
      _ = p * p ^ 2 := by ring
  rw [Nat.mod_eq_of_lt hlt]
  have e1 := Nat.div_add_mod x p
  have e2 := Nat.div_add_mod (x / p) p
  have e3 : x / p / p = x / p ^ 2 := by rw [Nat.div_div_eq_div_mul, sq]
  rw [e3] at e2
  nlinarith [e1, e2]

/-- The elementary-box index of a packed point sees exactly its leading `d` digits. -/
theorem coord_div_eq_iff [NeZero p] (w w' : Fin 3 → ZMod p) {d : ℕ} (hd : d ≤ 3) :
    coord p w / p ^ (3 - d) = coord p w' / p ^ (3 - d) ↔
      ∀ i : Fin 3, (i : ℕ) < d → w i = w' i := by
  have h0 := ZMod.val_lt (w 0); have h1 := ZMod.val_lt (w 1); have h2 := ZMod.val_lt (w 2)
  have h0' := ZMod.val_lt (w' 0); have h1' := ZMod.val_lt (w' 1); have h2' := ZMod.val_lt (w' 2)
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  interval_cases d
  · simp only [Nat.sub_zero, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true]
    rw [Nat.div_eq_of_lt (coord_lt w), Nat.div_eq_of_lt (coord_lt w')]
  · simp only [show 3 - 1 = 2 from rfl, coord_def]
    rw [pack_div_p2 h1 h2, pack_div_p2 h1' h2']
    constructor
    · intro h i hi
      have hi0 : i = 0 := Fin.ext (by omega)
      subst hi0
      exact ZMod.val_injective p h
    · intro h
      exact congrArg ZMod.val (h 0 (by decide))
  · simp only [show 3 - 2 = 1 from rfl, pow_one, coord_def]
    rw [pack_div_p h2, pack_div_p h2']
    constructor
    · intro h i hi
      have hm : (w 1).val = (w' 1).val := by
        have := congrArg (· % p) h
        simpa [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h1'] using this
      have ht : (w 0).val = (w' 0).val := by
        have := congrArg (· / p) h
        rw [show (w 0).val * p + (w 1).val = (w 1).val + (w 0).val * p by ring,
          show (w' 0).val * p + (w' 1).val = (w' 1).val + (w' 0).val * p by ring,
          Nat.add_mul_div_right _ _ hp, Nat.add_mul_div_right _ _ hp,
          Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h1'] at this
        simpa using this
      have : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      rcases this with h' | h'
      · have : i = 0 := Fin.ext h'
        subst this; exact ZMod.val_injective p ht
      · have : i = 1 := Fin.ext h'
        subst this; exact ZMod.val_injective p hm
    · intro h
      rw [h 0 (by decide), h 1 (by decide)]
  · simp only [Nat.sub_self, pow_zero, Nat.div_one]
    constructor
    · intro h i _
      have := congrArg (digits p) h
      rw [digits_coord, digits_coord] at this
      rw [this]
    · intro h
      have : w = w' := funext fun i => h i i.isLt
      rw [this]

theorem div_lt_of_lt_cube {y d : ℕ} (hd : d ≤ 3) (hy : y < p ^ 3) : y / p ^ (3 - d) < p ^ d := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hy
    · exact h
  rw [Nat.div_lt_iff_lt_mul (pow_pos hp _), ← pow_add, Nat.add_sub_cancel' hd]
  exact hy

end QUNetsM3
