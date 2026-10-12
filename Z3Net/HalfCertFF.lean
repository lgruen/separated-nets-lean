module
public import Z3Net.HalfBox

@[expose] public section

/-!
# Entry Half: fraction-free elimination (kernel-evaluable nonsingularity test)

`ffNS n A` (over a commutative ring with decidable equality): find a row `i` with `A i 0 ≠ 0`
(`findPiv`), swap it to the top, replace every other row `r` by `a · row_r - A_r0 · row_0`
(`a` the pivot) and recurse on the lower-right block (`ffStep`). No inverses are used, so it
evaluates in the kernel over `ZMod p`.

* `ffNS_sound`: over a domain, `ffNS n A = true → det A ≠ 0`. With `L` lower triangular
  (`L 0 0 = 1`, `L r r = a`, `L r 0 = -A_r0`), `L B` has first column `(a, 0, …, 0)` and lower
  right block `ffStep`, so `a · det(ffStep) = a^n · det B` and `det B = ± det A`.
* `not_dvd_det_of_ffNS`: for the integer generator `halfIntGen`, `ffNS` over `ZMod p` of the box
  matrix of the reduced generators gives `¬ p ∣ det` of the integer box matrix.
-/

namespace Z3NetHL.Proofs

open Matrix Finset

/-- First index `i` with `f i ≠ 0`. -/
def findPiv {K : Type*} [Zero K] [DecidableEq K] : (n : ℕ) → (Fin n → K) → Option (Fin n)
  | 0, _ => none
  | n + 1, f => if f 0 = 0 then (findPiv n (fun i => f i.succ)).map Fin.succ else some 0

/-- One fraction-free elimination step with pivot row `i`. -/
def ffStep {K : Type*} [CommRing K] (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → K) (i : Fin (n + 1)) :
    Fin n → Fin n → K :=
  fun r c => A (Equiv.swap 0 i 0) 0 * A (Equiv.swap 0 i r.succ) c.succ -
    A (Equiv.swap 0 i r.succ) 0 * A (Equiv.swap 0 i 0) c.succ

/-- Fraction-free Gaussian elimination: `true` certifies `det A ≠ 0` over a domain. -/
def ffNS {K : Type*} [CommRing K] [DecidableEq K] : (n : ℕ) → (Fin n → Fin n → K) → Bool
  | 0, _ => true
  | n + 1, A =>
    match findPiv (n + 1) (fun i => A i 0) with
    | none => false
    | some i => ffNS n (ffStep n A i)

lemma findPiv_spec {K : Type*} [Zero K] [DecidableEq K] :
    ∀ (n : ℕ) (f : Fin n → K) (i : Fin n), findPiv n f = some i → f i ≠ 0
  | 0, f, i, h => by simp [findPiv] at h
  | n + 1, f, i, h => by
    simp only [findPiv] at h
    split_ifs at h with h0
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
      exact findPiv_spec n _ j hj
    · cases h; exact h0

/-- The key identity of one step: `a · det(ffStep) = a^n · det B` for `B` with pivot `B 0 0 = a`. -/
lemma det_step {K : Type*} [CommRing K] (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    B 0 0 * (Matrix.of fun r c : Fin n => B 0 0 * B r.succ c.succ - B r.succ 0 * B 0 c.succ).det
      = B 0 0 ^ n * B.det := by
  set a := B 0 0 with ha
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun k j =>
    if k = 0 then (if j = 0 then 1 else 0) else if j = 0 then -B k 0 else if j = k then a else 0
  have hLt : L.BlockTriangular OrderDual.toDual := by
    intro k j hkj
    simp only [OrderDual.toDual_lt_toDual] at hkj
    have hj : j ≠ 0 := fun h => by subst h; exact absurd hkj (Fin.not_lt_zero _)
    have hjk : j ≠ k := fun h => by subst h; exact lt_irrefl _ hkj
    simp only [L, hj, hjk, ite_false]
    split_ifs <;> rfl
  have hdetL : L.det = a ^ n := by
    rw [Matrix.det_of_lowerTriangular L hLt, Fin.prod_univ_succ]
    simp only [L, ite_true, Fin.succ_ne_zero, ite_false, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, one_mul]
  have hC : ∀ k c, (L * B) k c =
      if k = 0 then B 0 c else a * B k c - B k 0 * B 0 c := by
    intro k c
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    by_cases hk : k = 0
    · subst hk
      simp [L]
    · simp only [L, hk, ite_false, ite_true, Fin.succ_ne_zero]
      rw [Finset.sum_eq_single (Fin.pred k hk)]
      · simp only [Fin.succ_pred, ite_true]; ring
      · intro j _ hj
        have : j.succ ≠ k := fun h => hj (by subst h; simp)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hdetC : (L * B).det = a * (Matrix.of fun r c : Fin n =>
      B 0 0 * B r.succ c.succ - B r.succ 0 * B 0 c.succ).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hrest : ∀ i : Fin n, (-1 : K) ^ (i.succ : ℕ) * (L * B) i.succ 0 *
        ((L * B).submatrix (i.succ.succAbove) Fin.succ).det = 0 := by
      intro i
      rw [hC, if_neg (Fin.succ_ne_zero i)]
      ring
    rw [Finset.sum_eq_zero (fun i _ => hrest i), add_zero, hC, if_pos rfl]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    congr 1
    congr 1
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hC, if_neg (Fin.succ_ne_zero r)]
    rfl
  rw [← hdetC, Matrix.det_mul, hdetL]

lemma ffNS_sound {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) K), ffNS n A = true → A.det ≠ 0
  | 0, A, _ => by simp
  | n + 1, A, h => by
    simp only [ffNS] at h
    split at h
    · exact absurd h (by simp)
    · rename_i i hi
      have hpiv := findPiv_spec _ _ i hi
      have ih := ffNS_sound n _ h
      intro hA
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := A.submatrix (Equiv.swap 0 i) id
      have hB : B.det = 0 := by
        simp only [B, Matrix.det_permute, hA, mul_zero]
      have hkey := det_step n B
      rw [hB, mul_zero] at hkey
      have hB0 : B 0 0 ≠ 0 := by
        simp only [B, Matrix.submatrix_apply, Equiv.swap_apply_left, id]; exact hpiv
      rcases mul_eq_zero.1 hkey with h0 | h0
      · exact hB0 h0
      · exact ih h0

/-- Box matrices commute with reducing the generator entries. -/
lemma boxMatrix_map {R S : Type*} [Zero R] [Zero S] {s m : ℕ} (f : R → S) (hf : f 0 = 0)
    (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) :
    boxMatrix (fun c => (C c).map f) d = (boxMatrix C d).map f := by
  ext r l
  simp only [boxMatrix, Matrix.map_apply]
  split_ifs <;> simp [hf]

/-- `ffNS` over `ZMod p` of the reduced box matrix certifies `p ∤ det` of the integer one. -/
lemma not_dvd_det_of_ffNS {s : ℕ} (p : ℕ) (hp : p.Prime) (C : Fin s → Matrix (Fin s) (Fin s) ℤ)
    (d : Fin s → ℕ)
    (h : ffNS s (boxMatrix (fun c => (C c).map (Int.cast : ℤ → ZMod p)) d) = true) :
    ¬ (p : ℤ) ∣ (boxMatrix C d).det := by
  have := Fact.mk hp
  have h1 := ffNS_sound s _ h
  rw [boxMatrix_map _ Int.cast_zero] at h1
  have h2 : (((boxMatrix C d).det : ℤ) : ZMod p) ≠ 0 := by
    have e := RingHom.map_det (Int.castRingHom (ZMod p)) (boxMatrix C d)
    simp only [Int.coe_castRingHom, RingHom.mapMatrix_apply] at e
    rw [e]; exact h1
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2

/-! ## Box checks over all compositions (`s = 6, 8`)

`ck{s}_k p M2 D a₀ … a_{k-1}` checks every composition of `s` with first parts `a₀, …, a_{k-1}`
(`k` coordinates fixed; the last part is `s - ∑`), so that the kernel checks can be split into
slices of bounded size (`all_range_of` reassembles them).
-/

/-- The box check of the composition `d` for the generators `halfIntGen M2 D` reduced mod `p`. -/
def okBoxG (s p : ℕ) (M2 : Fin s → Fin s → ℤ) (D : Fin s → ℕ → Fin s → ℤ) (d : Fin s → ℕ) : Bool :=
  ffNS s (boxMatrix (fun c => (halfIntGen M2 D c).map (Int.cast : ℤ → ZMod p)) d)

lemma all_range_of {f : ℕ → Bool} (n : ℕ) (h : ∀ i, i < n → f i = true) :
    (List.range n).all f = true :=
  List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

/-- `s = 6`: the composition `(a₀, …, a_4, 6 - ∑)`. -/
def ck6_5 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  okBoxG 6 p M2 D ![a0, a1, a2, a3, a4, 6 - a0 - a1 - a2 - a3 - a4]

/-- `s = 6`: all compositions with first parts `a₀, …` (4 fixed). -/
def ck6_4 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (a0 a1 a2 a3 : ℕ) :
    Bool :=
  (List.range (7 - a0 - a1 - a2 - a3)).all fun a4 => ck6_5 p M2 D a0 a1 a2 a3 a4

/-- `s = 6`: all compositions with first parts `a₀, …` (3 fixed). -/
def ck6_3 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (a0 a1 a2 : ℕ) :
    Bool :=
  (List.range (7 - a0 - a1 - a2)).all fun a3 => ck6_4 p M2 D a0 a1 a2 a3

/-- `s = 6`: all compositions with first parts `a₀, …` (2 fixed). -/
def ck6_2 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (a0 a1 : ℕ) :
    Bool :=
  (List.range (7 - a0 - a1)).all fun a2 => ck6_3 p M2 D a0 a1 a2

/-- `s = 6`: all compositions with first parts `a₀, …` (1 fixed). -/
def ck6_1 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (a0 : ℕ) :
    Bool :=
  (List.range (7 - a0)).all fun a1 => ck6_2 p M2 D a0 a1

/-- `s = 6`: all compositions with first parts `a₀, …` (0 fixed). -/
def ck6_0 (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ) :
    Bool :=
  (List.range (7)).all fun a0 => ck6_1 p M2 D a0

lemma ck6_sound (p : ℕ) (M2 : Fin 6 → Fin 6 → ℤ) (D : Fin 6 → ℕ → Fin 6 → ℤ)
    (h : ck6_0 p M2 D = true) (d : Fin 6 → ℕ) (hd : ∑ c, d c = 6) :
    okBoxG 6 p M2 D d = true := by
  rw [Fin.sum_univ_six] at hd
  simp only [ck6_0, ck6_1, ck6_2, ck6_3, ck6_4, ck6_5, List.all_eq_true, List.mem_range] at h
  have h' := h (d 0) (by omega) (d 1) (by omega) (d 2) (by omega) (d 3) (by omega) (d 4) (by omega)
  have e : ![d 0, d 1, d 2, d 3, d 4, 6 - d 0 - d 1 - d 2 - d 3 - d 4] = d := by
    funext c; fin_cases c <;> simp <;> omega
  rwa [e] at h'

theorem net_of_ck6 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (M2 : Fin 6 → Fin 6 → ℤ)
    (D : Fin 6 → ℕ → Fin 6 → ℤ) (h : ck6_0 p M2 D = true) :
    IsNet0 6 p (6 * 1) (GFpoint 6 p 1 (halfPhi 6 p M2 D)) :=
  halfPhi_net_of_int 6 p hp hp2 M2 D
    (fun d hd => not_dvd_det_of_ffNS p hp _ d (ck6_sound p M2 D h d hd))

/-- `s = 8`: the composition `(a₀, …, a_6, 8 - ∑)`. -/
def ck8_7 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 a2 a3 a4 a5 a6 : ℕ) : Bool :=
  okBoxG 8 p M2 D ![a0, a1, a2, a3, a4, a5, a6, 8 - a0 - a1 - a2 - a3 - a4 - a5 - a6]

/-- `s = 8`: all compositions with first parts `a₀, …` (6 fixed). -/
def ck8_6 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 a2 a3 a4 a5 : ℕ) :
    Bool :=
  (List.range (9 - a0 - a1 - a2 - a3 - a4 - a5)).all fun a6 => ck8_7 p M2 D a0 a1 a2 a3 a4 a5 a6

/-- `s = 8`: all compositions with first parts `a₀, …` (5 fixed). -/
def ck8_5 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 a2 a3 a4 : ℕ) :
    Bool :=
  (List.range (9 - a0 - a1 - a2 - a3 - a4)).all fun a5 => ck8_6 p M2 D a0 a1 a2 a3 a4 a5

/-- `s = 8`: all compositions with first parts `a₀, …` (4 fixed). -/
def ck8_4 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 a2 a3 : ℕ) :
    Bool :=
  (List.range (9 - a0 - a1 - a2 - a3)).all fun a4 => ck8_5 p M2 D a0 a1 a2 a3 a4

/-- `s = 8`: all compositions with first parts `a₀, …` (3 fixed). -/
def ck8_3 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 a2 : ℕ) :
    Bool :=
  (List.range (9 - a0 - a1 - a2)).all fun a3 => ck8_4 p M2 D a0 a1 a2 a3

/-- `s = 8`: all compositions with first parts `a₀, …` (2 fixed). -/
def ck8_2 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 a1 : ℕ) :
    Bool :=
  (List.range (9 - a0 - a1)).all fun a2 => ck8_3 p M2 D a0 a1 a2

/-- `s = 8`: all compositions with first parts `a₀, …` (1 fixed). -/
def ck8_1 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (a0 : ℕ) :
    Bool :=
  (List.range (9 - a0)).all fun a1 => ck8_2 p M2 D a0 a1

/-- `s = 8`: all compositions with first parts `a₀, …` (0 fixed). -/
def ck8_0 (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ) :
    Bool :=
  (List.range (9)).all fun a0 => ck8_1 p M2 D a0

lemma ck8_sound (p : ℕ) (M2 : Fin 8 → Fin 8 → ℤ) (D : Fin 8 → ℕ → Fin 8 → ℤ)
    (h : ck8_0 p M2 D = true) (d : Fin 8 → ℕ) (hd : ∑ c, d c = 8) :
    okBoxG 8 p M2 D d = true := by
  rw [Fin.sum_univ_eight] at hd
  simp only [ck8_0, ck8_1, ck8_2, ck8_3, ck8_4, ck8_5, ck8_6, ck8_7, List.all_eq_true, List.mem_range] at h
  have h' := h (d 0) (by omega) (d 1) (by omega) (d 2) (by omega) (d 3) (by omega) (d 4) (by omega) (d 5) (by omega) (d 6) (by omega)
  have e : ![d 0, d 1, d 2, d 3, d 4, d 5, d 6, 8 - d 0 - d 1 - d 2 - d 3 - d 4 - d 5 - d 6] = d := by
    funext c; fin_cases c <;> simp <;> omega
  rwa [e] at h'

theorem net_of_ck8 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (M2 : Fin 8 → Fin 8 → ℤ)
    (D : Fin 8 → ℕ → Fin 8 → ℤ) (h : ck8_0 p M2 D = true) :
    IsNet0 8 p (8 * 1) (GFpoint 8 p 1 (halfPhi 8 p M2 D)) :=
  halfPhi_net_of_int 8 p hp hp2 M2 D
    (fun d hd => not_dvd_det_of_ffNS p hp _ d (ck8_sound p M2 D h d hd))

end Z3NetHL.Proofs
