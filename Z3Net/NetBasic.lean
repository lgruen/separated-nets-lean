module
public import Z3Net.Defs

@[expose] public section

/-!
# Net property: generic lemmas

* base-`q` digit sums: the integer `∑_j f_j q^(m-1-j)` divided by `q^e` determines the first
  `m - e` digits;
* a Niederreiter-type lemma (`lem:nie`): if every box matrix acts injectively on `(ℤ/qℤ)^m`,
  the digital point set is a `(0,m,3)`-net (counting argument: injective map between finite sets
  of the same cardinality `q^m`);
* box matrices: row description, compatibility with `Matrix.map` and right multiplication;
* lower-triangular matrices with unit diagonal preserve "the first `d` entries vanish".
-/

namespace Z3Net.Proofs

open Matrix Finset

/-! ## Base-`q` digit sums -/

/-- The digit sum `∑_j f_j q^(m-1-j)` (digit `0` most significant). -/
def digSum (q m : ℕ) (f : Fin m → ℕ) : ℕ := ∑ j : Fin m, f j * q ^ (m - 1 - (j : ℕ))

lemma digSum_succ (q m : ℕ) (f : Fin (m + 1) → ℕ) :
    digSum q (m + 1) f = q * digSum q m (fun j => f j.castSucc) + f (Fin.last m) := by
  unfold digSum
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    simp only [Fin.val_castSucc]
    have : m + 1 - 1 - (j : ℕ) = (m - 1 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  · simp

lemma digSum_lt (q : ℕ) : ∀ (m : ℕ) (f : Fin m → ℕ), (∀ j, f j < q) → digSum q m f < q ^ m := by
  intro m
  induction m with
  | zero => intro f _; simp [digSum]
  | succ m ih =>
    intro f hf
    rw [digSum_succ, pow_succ]
    have h1 := ih (fun j => f j.castSucc) (fun j => hf _)
    have h2 := hf (Fin.last m)
    calc q * digSum q m (fun j => f j.castSucc) + f (Fin.last m)
        < q * digSum q m (fun j => f j.castSucc) + q := by omega
      _ = q * (digSum q m (fun j => f j.castSucc) + 1) := by ring
      _ ≤ q * q ^ m := Nat.mul_le_mul_left _ h1
      _ = q ^ m * q := by ring

lemma digSum_div_inj (q : ℕ) (hq : 0 < q) : ∀ (m : ℕ) (f g : Fin m → ℕ), (∀ j, f j < q) →
    (∀ j, g j < q) → ∀ e, digSum q m f / q ^ e = digSum q m g / q ^ e →
    ∀ j : Fin m, (j : ℕ) + e < m → f j = g j := by
  intro m
  induction m with
  | zero => intro f g _ _ e _ j; exact j.elim0
  | succ m ih =>
    intro f g hf hg e he j hj
    rw [digSum_succ, digSum_succ] at he
    set A := digSum q m (fun j => f j.castSucc)
    set B := digSum q m (fun j => g j.castSucc)
    have hr := hf (Fin.last m)
    have hr' := hg (Fin.last m)
    have hdivA : (q * A + f (Fin.last m)) / q = A := by
      rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hr, add_zero]
    have hdivB : (q * B + g (Fin.last m)) / q = B := by
      rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hr', add_zero]
    cases e with
    | zero =>
      simp only [pow_zero, Nat.div_one] at he
      have hAB : A = B := by rw [← hdivA, ← hdivB, he]
      have hrr : f (Fin.last m) = g (Fin.last m) := by
        have h1 : (q * A + f (Fin.last m)) % q = f (Fin.last m) := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
        have h2 : (q * B + g (Fin.last m)) % q = g (Fin.last m) := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr']
        rw [← h1, ← h2, he]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have := ih (fun j => f j.castSucc) (fun j => g j.castSucc) (fun _ => hf _) (fun _ => hg _)
          0 (by simpa using hAB) j' (by simp)
        simpa using this
      · exact hrr
    | succ e =>
      have hAB : A / q ^ e = B / q ^ e := by
        rw [← hdivA, ← hdivB, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ', he]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have := ih (fun j => f j.castSucc) (fun j => g j.castSucc) (fun _ => hf _) (fun _ => hg _)
          e hAB j' (by simp at hj; omega)
        simpa using this
      · simp at hj

/-! ## Box matrices -/

lemma boxMatrix_mulVec {R : Type*} [CommRing R] {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) R)
    (d : Fin 3 → ℕ) (v : Fin m → R) (r : Fin m) :
    (boxMatrix C d *ᵥ v) r =
      if (r : ℕ) < d 0 then (C 0 *ᵥ v) r
      else if (r : ℕ) < d 0 + d 1 then (C 1 *ᵥ v) ⟨(r : ℕ) - d 0, by omega⟩
      else (C 2 *ᵥ v) ⟨(r : ℕ) - d 0 - d 1, by omega⟩ := by
  unfold boxMatrix
  simp only [mulVec, dotProduct]
  split_ifs <;> rfl

/-- The box matrix kills `v` iff the first `d c` digits of every coordinate vanish. -/
lemma boxMatrix_mulVec_eq_zero_iff {R : Type*} [CommRing R] {m : ℕ}
    (C : Fin 3 → Matrix (Fin m) (Fin m) R) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m)
    (v : Fin m → R) :
    boxMatrix C d *ᵥ v = 0 ↔ ∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ v) i = 0 := by
  constructor
  · intro h c i hi
    fin_cases c
    · have hi' : (i : ℕ) < d 0 := hi
      have := congrFun h i
      rw [boxMatrix_mulVec, if_pos hi'] at this
      exact this
    · have hi' : (i : ℕ) < d 1 := hi
      have key : (C 1 *ᵥ v) i = (boxMatrix C d *ᵥ v) ⟨d 0 + i, by omega⟩ := by
        rw [boxMatrix_mulVec, if_neg (by show ¬ (d 0 + (i : ℕ) < d 0); omega),
          if_pos (by show d 0 + (i : ℕ) < d 0 + d 1; omega)]
        congr 1; ext; show (i : ℕ) = d 0 + i - d 0; omega
      show (C 1 *ᵥ v) i = 0
      rw [key]; exact congrFun h _
    · have hi' : (i : ℕ) < d 2 := hi
      have key : (C 2 *ᵥ v) i = (boxMatrix C d *ᵥ v) ⟨d 0 + d 1 + i, by omega⟩ := by
        rw [boxMatrix_mulVec, if_neg (by show ¬ (d 0 + d 1 + (i : ℕ) < d 0); omega),
          if_neg (by show ¬ (d 0 + d 1 + (i : ℕ) < d 0 + d 1); omega)]
        congr 1; ext; show (i : ℕ) = d 0 + d 1 + i - d 0 - d 1; omega
      show (C 2 *ᵥ v) i = 0
      rw [key]; exact congrFun h _
  · intro h
    funext r
    rw [boxMatrix_mulVec]
    split_ifs with h1 h2
    · exact h 0 r h1
    · exact h 1 _ (by simp; omega)
    · exact h 2 _ (by simp; omega)

lemma boxMatrix_mulVec_eq_of {R : Type*} [CommRing R] {m : ℕ}
    (C : Fin 3 → Matrix (Fin m) (Fin m) R) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m)
    (v w : Fin m → R) (h : ∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ v) i = (C c *ᵥ w) i) :
    boxMatrix C d *ᵥ v = boxMatrix C d *ᵥ w := by
  funext r
  rw [boxMatrix_mulVec, boxMatrix_mulVec]
  split_ifs with h1 h2
  · exact h 0 r h1
  · exact h 1 _ (by simp; omega)
  · exact h 2 _ (by simp; omega)

lemma boxMatrix_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S)
    (C : Fin 3 → Matrix (Fin m) (Fin m) R) (d : Fin 3 → ℕ) :
    boxMatrix (fun c => (C c).map f) d = (boxMatrix C d).map f := by
  ext r j
  simp only [boxMatrix, map_apply]
  split_ifs <;> rfl

lemma boxMatrix_mul_right {R : Type*} [CommRing R] {m : ℕ}
    (C : Fin 3 → Matrix (Fin m) (Fin m) R) (M : Matrix (Fin m) (Fin m) R) (d : Fin 3 → ℕ) :
    boxMatrix (fun c => C c * M) d = boxMatrix C d * M := by
  ext r j
  simp only [boxMatrix, mul_apply]
  split_ifs <;> rfl

lemma mulVec_injective_of_isUnit_det {R : Type*} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (h : IsUnit M.det) : Function.Injective M.mulVec := by
  intro v w hvw
  have := congrArg (fun x => M⁻¹ *ᵥ x) hvw
  simp only [mulVec_mulVec, nonsing_inv_mul M h, one_mulVec] at this
  exact this

lemma mulVec_injective_of_ker {R : Type*} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (h : ∀ v, M *ᵥ v = 0 → v = 0) :
    Function.Injective M.mulVec := by
  intro v w hvw
  have := h (v - w) (by rw [mulVec_sub, hvw, sub_self])
  exact sub_eq_zero.mp this

/-! ## The Niederreiter-type lemma -/

/-- **`lem:nie`** (injective form): if every box matrix is injective, the digital point set is a
`(0,m,3)`-net in base `q`. -/
theorem isNet0_of_box_injective (q m : ℕ) [NeZero q]
    (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod q))
    (h : ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 = m → Function.Injective (boxMatrix C d).mulVec) :
    IsNet0 q m (digPoint q m C) := by
  intro d hd a ha
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdle : ∀ c, d c ≤ m := by intro c; fin_cases c <;> simp <;> omega
  have hcoord : ∀ c v, coord q m (C c) v = digSum q m (fun j => ((C c *ᵥ v) j).val) := by
    intro c v; rfl
  have hbound : ∀ c v, digPoint q m C v c / q ^ (m - d c) < q ^ d c := by
    intro c v
    have hlt := digSum_lt q m (fun j => ((C c *ᵥ v) j).val) (fun j => ZMod.val_lt _)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq _), ← pow_add, Nat.add_sub_of_le (hdle c)]
    simpa [digPoint, hcoord] using hlt
  let φ : (Fin m → ZMod q) → ((c : Fin 3) → Fin (q ^ d c)) :=
    fun v c => ⟨digPoint q m C v c / q ^ (m - d c), hbound c v⟩
  have hinj : Function.Injective φ := by
    intro v w hvw
    apply h d hd
    apply boxMatrix_mulVec_eq_of C d hd
    intro c i hi
    have h1 : digPoint q m C v c / q ^ (m - d c) = digPoint q m C w c / q ^ (m - d c) := by
      have := congrFun hvw c
      simpa [φ] using congrArg Fin.val this
    simp only [digPoint, hcoord] at h1
    have := digSum_div_inj q hq m _ _ (fun j => ZMod.val_lt _) (fun j => ZMod.val_lt _) _ h1 i
      (by have := hdle c; omega)
    exact ZMod.val_injective _ this
  have hcard : Fintype.card (Fin m → ZMod q) = Fintype.card ((c : Fin 3) → Fin (q ^ d c)) := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_pi,
      Fin.prod_univ_three]
    rw [← pow_add, ← pow_add, hd]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  obtain ⟨v, hv⟩ := hbij.2 (fun c => ⟨a c, ha c⟩)
  refine ⟨v, fun c => ?_, fun w hw => hinj ?_⟩
  · have := congrArg Fin.val (congrFun hv c)
    simpa [φ] using this
  · rw [hv]
    funext c
    exact Fin.ext (hw c)

/-! ## Lower-triangular matrices -/

/-- A lower-triangular matrix with unit diagonal: if the first `d` entries of `M w` vanish, so do
the first `d` entries of `w`. -/
lemma lowerTri_kill {R : Type*} [CommRing R] {a : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hlow : ∀ i j : Fin a, i < j → M i j = 0) (hdiag : ∀ i, IsUnit (M i i)) (w : Fin a → R)
    (d : ℕ) (h : ∀ r : Fin a, (r : ℕ) < d → (M *ᵥ w) r = 0) :
    ∀ i : Fin a, (i : ℕ) < d → w i = 0 := by
  suffices H : ∀ n, ∀ i : Fin a, (i : ℕ) = n → (i : ℕ) < d → w i = 0 from
    fun i hi => H i i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hin hid
    have hrow := h i hid
    rw [mulVec, dotProduct, Finset.sum_eq_single i] at hrow
    · exact (hdiag i).mul_right_eq_zero.mp hrow
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hj : (j : ℕ) < n := by rw [← hin]; exact hlt
        rw [ih j hj j rfl (by omega), mul_zero]
      · rw [hlow i j hgt, zero_mul]
    · simp

end Z3Net.Proofs
