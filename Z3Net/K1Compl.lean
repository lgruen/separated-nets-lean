/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DeficitDefs
public import Z3Net.FMain

@[expose] public section

/-!
# V14 stage S15′: the `t = 0` completions of `prop:k1designs`(2) (theory)

A graph form over `ℤ/qℤ` with depths `(1, …, 1)` (`m = s`) whose first offset rows are an integer layer `F₀` and whose
deeper rows vanish in their own column ((H2)) is given by its deeper rows. Here they are integer data `D`
(`phiZ F₀ D`, deeper entries on the diagonal forced to `0`), reduced modulo `q`.

* `detM`: Laplace expansion along the first row on lists of rows, `detM_eq`: it is `Matrix.det` (so the kernel can
  evaluate box minors of integer data);
* `compList`: the compositions of `n` into `s` parts, `mem_compList`: every `d` with `∑ d = n` is listed;
* `strip`: removes the factors in a list `S` of primes, `strip_spec`: `strip S n = 1` ⇒ every prime factor of `n` is in
  `S`;
* `net_of_compl` (the integer lift and the Chinese remainder theorem of the proof of `prop:k1designs`(2)): if for every
  prime `p ∣ q` some integer completion `E p` has all box minors prime to `p`, the completion congruent to `E p`
  modulo every prime `p ∣ q` (CRT, entrywise) gives a digital `(0,s,s)`-net over `ℤ/qℤ` (`lem:nie`): its box minors
  reduce modulo each `p ∣ q` to those of `E p`, so they are prime to `q`, i.e. units modulo `q`.
-/

namespace Z3NetF.Proofs.K1Compl

open Matrix Finset Z3NetF

/-- The blocks of the graph form with depths `(1, …, 1)`, first offset rows `F₀`, deeper rows `D` (row `r ≥ 1` of
block `(c, d)` is `D c (r - 1) d`, and `0` on the diagonal blocks). -/
def phiZ {s : ℕ} (F0 : Fin s → Fin s → ℤ) (D : Fin s → Fin (s - 2) → Fin s → ℤ) :
    (c d : Fin s) → Matrix (Fin (s * 1 - 1)) (Fin 1) ℤ :=
  fun c d r _ => if (r : ℕ) = 0 then F0 c d else if c = d then 0 else
    if h : (r : ℕ) - 1 < s - 2 then D c ⟨(r : ℕ) - 1, h⟩ d else 0

/-! ## Determinants by Laplace expansion on lists -/

/-- One row of the Laplace expansion along the first row. -/
def detAux (rec : List (List ℤ) → ℤ) (rs : List (List ℤ)) : List ℤ → ℕ → Bool → ℤ
  | [], _, _ => 0
  | a :: as, j, pos =>
      (if a = 0 then 0 else (if pos then a else -a) * rec (rs.map fun x => x.eraseIdx j)) +
        detAux rec rs as (j + 1) (!pos)

/-- The determinant of an `n × n` matrix given by its list of rows. -/
def detM : ℕ → List (List ℤ) → ℤ
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, r :: rs => detAux (detM n) rs r 0 true

/-- The list of rows of a matrix. -/
def rowsOf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) := List.ofFn fun i => List.ofFn (M i)

lemma detAux_ofFn (rec : List (List ℤ) → ℤ) (rs : List (List ℤ)) :
    ∀ (k : ℕ) (f : Fin k → ℤ) (j0 : ℕ) (pos : Bool),
      detAux rec rs (List.ofFn f) j0 pos =
        ∑ i : Fin k, (if pos then (1 : ℤ) else -1) * (-1) ^ (i : ℕ) * f i *
          rec (rs.map fun x => x.eraseIdx (j0 + i))
  | 0, f, j0, pos => by simp [detAux]
  | k + 1, f, j0, pos => by
    rw [List.ofFn_succ, detAux, detAux_ofFn rec rs k (fun i => f i.succ) (j0 + 1) (!pos), Fin.sum_univ_succ]
    have e : ∀ i : Fin k, j0 + 1 + (i : ℕ) = j0 + ((i.succ : Fin (k + 1)) : ℕ) := by
      intro i; simp only [Fin.val_succ]; omega
    congr 1
    · by_cases h : f 0 = 0
      · simp [h]
      · rw [if_neg h]; cases pos <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [e i]
      simp only [Fin.val_succ, pow_succ]
      cases pos <;> simp <;> ring

lemma ofFn_eraseIdx {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (List.ofFn f).eraseIdx j = List.ofFn (fun k => f (j.succAbove k)) := by
  apply List.ext_getElem
  · have := j.isLt
    simp [List.length_eraseIdx]
    omega
  · intro i h1 h2
    rw [List.getElem_eraseIdx, List.getElem_ofFn]
    simp only [List.getElem_ofFn]
    have hi : i < n := by simpa using h2
    split_ifs with hij
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
      rfl

theorem detM_eq : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ), detM n (rowsOf M) = M.det
  | 0, M => by simp [detM, Matrix.det_fin_zero]
  | n + 1, M => by
    rw [Matrix.det_succ_row_zero]
    have hr : rowsOf M = List.ofFn (M 0) :: List.ofFn (fun i : Fin n => List.ofFn (M i.succ)) := by
      simp [rowsOf, List.ofFn_succ]
    rw [hr, detM, detAux_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrow : (List.ofFn fun i : Fin n => List.ofFn (M i.succ)).map (fun x => x.eraseIdx (0 + (j : ℕ))) =
        rowsOf (M.submatrix Fin.succ j.succAbove) := by
      rw [List.map_ofFn, rowsOf]
      congr 1
      funext i
      simp only [Function.comp_apply, zero_add, ofFn_eraseIdx]
      rfl
    rw [hrow, detM_eq n]
    simp

/-! ## Compositions -/

/-- The compositions `d` of `n` into `s` parts (`∑ d = n`). -/
def compList : (s n : ℕ) → List (Fin s → ℕ)
  | 0, n => if n = 0 then [Fin.elim0] else []
  | s + 1, n => (List.range (n + 1)).flatMap fun a => (compList s (n - a)).map fun t => Fin.cons a t

theorem mem_compList : ∀ (s n : ℕ) (d : Fin s → ℕ), ∑ c, d c = n → d ∈ compList s n
  | 0, n, d, h => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    subst h
    simp only [compList, ite_true, List.mem_singleton]
    funext x; exact x.elim0
  | s + 1, n, d, h => by
    rw [Fin.sum_univ_succ] at h
    simp only [compList, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨d 0, by omega, Fin.tail d, mem_compList s (n - d 0) (Fin.tail d) ?_, Fin.cons_self_tail d⟩
    simp only [Fin.tail]; omega

/-! ## Removing known prime factors -/

/-- Divide `n` by `p` while possible (`f` steps at most). -/
def stripP (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | f + 1, n => if 1 < p ∧ n % p = 0 ∧ 0 < n then stripP p f (n / p) else n

/-- Remove the factors `p ∈ S` from `n`. -/
def strip (S : List ℕ) (n : ℕ) : ℕ := S.foldl (fun n p => stripP p n n) n

lemma stripP_spec (p : ℕ) : ∀ f n, ∃ e, n = stripP p f n * p ^ e
  | 0, n => ⟨0, by simp [stripP]⟩
  | f + 1, n => by
    unfold stripP
    split_ifs with h
    · obtain ⟨e, he⟩ := stripP_spec p f (n / p)
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, ← mul_assoc, ← he]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2.1)).symm
    · exact ⟨0, by simp⟩

lemma dvd_strip (S : List ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℕ) (hq : q.Prime) (hqS : q ∉ S) :
    ∀ n, q ∣ n → q ∣ strip S n := by
  induction S with
  | nil => intro n h; simpa [strip] using h
  | cons p S ih =>
    intro n h
    have hp := hS p (by simp)
    have hqp : q ≠ p := fun e => hqS (by simp [e])
    show q ∣ strip S (stripP p n n)
    apply ih (fun p' hp' => hS p' (by simp [hp'])) (fun h' => hqS (by simp [h']))
    obtain ⟨e, he⟩ := stripP_spec p n n
    rw [he] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · exact h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h1)) hqp

/-- `strip S n = 1` (`S` primes) ⇒ every prime factor of `n` is in `S`. -/
theorem strip_spec (S : List ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) (h : strip S n = 1) (q : ℕ) (hq : q.Prime)
    (hqn : q ∣ n) : q ∈ S := by
  by_contra hqS
  have := dvd_strip S hS q hq hqS n hqn
  rw [h] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-! ## Box minors of the integer data, and their reductions -/

/-- The box minor for `d` of the integer graph form `phiZ F₀ D` (`lem:box`), by `detM`. -/
def boxDetM {s : ℕ} (F0 : Fin s → Fin s → ℤ) (D : Fin s → Fin (s - 2) → Fin s → ℤ) (d : Fin s → ℕ) : ℤ :=
  detM (s * 1) (rowsOf (boxMatrix (graphGenK (m := s * 1) (fun _ => 1) (phiZ F0 D)) d))

lemma graphGenK_map {R S : Type*} [Zero R] [One R] [Zero S] [One S] (f : R → S) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {s m : ℕ} (K : Fin s → ℕ) (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R)
    (c : Fin s) : (graphGenK K Φ c).map f = graphGenK K (fun c d => (Φ c d).map f) c := by
  ext i j
  simp only [Matrix.map_apply, graphGenK]
  split_ifs <;> simp [h0, h1]

lemma boxMatrix_map {R S : Type*} [Zero R] [Zero S] (f : R → S) (h0 : f 0 = 0) {s m : ℕ}
    (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) :
    (boxMatrix C d).map f = boxMatrix (fun c => (C c).map f) d := by
  ext r l
  simp only [Matrix.map_apply, boxMatrix]
  split_ifs <;> simp [h0]

/-- The box matrix over a ring `R` of the reduction of `phiZ F₀ D` is the reduction of the integer box matrix. -/
lemma box_cast {R : Type*} [CommRing R] {s : ℕ} (F0 : Fin s → Fin s → ℤ) (D : Fin s → Fin (s - 2) → Fin s → ℤ)
    (d : Fin s → ℕ) :
    (boxMatrix (graphGenK (m := s * 1) (fun _ => 1)
        (fun c d => (phiZ F0 D c d).map (Int.cast : ℤ → R))) d).det =
      ((boxDetM F0 D d : ℤ) : R) := by
  rw [boxDetM, detM_eq]
  have hm := RingHom.map_det (Int.castRingHom R)
    (boxMatrix (graphGenK (m := s * 1) (fun _ => 1) (phiZ F0 D)) d)
  simp only [eq_intCast, RingHom.mapMatrix_apply, Int.coe_castRingHom] at hm
  rw [hm]
  congr 1
  rw [boxMatrix_map _ (by simp)]
  congr 1
  funext c
  rw [graphGenK_map _ (by simp) (by simp)]

/-- Two integer completions congruent modulo `p` (off the diagonal) have the same box minors modulo `p`. -/
lemma boxDetM_congr {s p : ℕ} (F0 : Fin s → Fin s → ℤ) (D D' : Fin s → Fin (s - 2) → Fin s → ℤ)
    (h : ∀ c r d, ((D c r d : ℤ) : ZMod p) = ((D' c r d : ℤ) : ZMod p)) (d : Fin s → ℕ) :
    ((boxDetM F0 D d : ℤ) : ZMod p) = ((boxDetM F0 D' d : ℤ) : ZMod p) := by
  rw [← box_cast, ← box_cast]
  congr 4
  funext c e
  ext r j
  simp only [Matrix.map_apply, phiZ]
  split_ifs <;> simp [h]

/-! ## The integer lift and the Chinese remainder theorem -/

/-- **`prop:k1designs`(2), lift and CRT**: if for every prime `p ∣ q` the integer completion `E p` has all box minors
prime to `p`, there is a digital `(0,s,s)`-net over `ℤ/qℤ` in graph form with depths `(1, …, 1)`, first offset rows
`F₀`, deeper rows vanishing in their own column ((H2)). -/
theorem net_of_compl {s : ℕ} (q : ℕ) [NeZero q] (F0 : Fin s → Fin s → ℤ)
    (E : ℕ → Fin s → Fin (s - 2) → Fin s → ℤ)
    (hE : ∀ p, p.Prime → p ∣ q → ∀ d ∈ compList s s, ¬ (p : ℤ) ∣ boxDetM F0 (E p) d) :
    ∃ Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F0 c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 s q (s * 1) (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ)) := by
  classical
  set t := q.primeFactors
  have hs : ∀ p ∈ t, id p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have pp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha) (Nat.prime_of_mem_primeFactors hb)).mpr hab
  let X : Fin s → Fin (s - 2) → Fin s → ℤ := fun c r d =>
    ((Nat.chineseRemainderOfFinset (fun p => ((E p c r d) % (p : ℤ)).toNat) id t hs pp : ℕ) : ℤ)
  have hX : ∀ p, p.Prime → p ∣ q → ∀ c r d, ((X c r d : ℤ) : ZMod p) = ((E p c r d : ℤ) : ZMod p) := by
    intro p hp hpq c r d
    have hmem : p ∈ t := Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩
    have hcrt := (Nat.chineseRemainderOfFinset (fun p => ((E p c r d) % (p : ℤ)).toNat) id t hs pp).2 p hmem
    simp only [id] at hcrt
    have e1 : ((X c r d : ℤ) : ZMod p) =
        (((((E p c r d) % (p : ℤ)).toNat : ℕ) : ℤ) : ZMod p) := by
      simp only [X, Int.cast_natCast]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcrt
    rw [e1, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)), ZMod.intCast_mod]
  refine ⟨fun c d => (phiZ F0 X c d).map (Int.cast : ℤ → ZMod q), ?_, ?_, ?_⟩
  · intro c d r hr
    simp [phiZ, hr]
  · intro c r hr j
    simp [phiZ, hr]
  · rw [nie_zmod]
    intro d hd
    rw [box_cast]
    have hmem := mem_compList s s d (by rw [hd, mul_one])
    set z := boxDetM F0 X d
    have hcop : Nat.Coprime z.natAbs q := by
      apply Nat.Coprime.symm
      apply Nat.coprime_of_dvd
      intro p hp hpq hpz
      have hz : ((z : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Int.natCast_dvd.mpr hpz
      rw [boxDetM_congr F0 X (E p) (hX p hp hpq) d, ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      exact hE p hp hpq d hmem hz
    rcases Int.natAbs_eq z with h | h
    · rw [h, Int.cast_natCast]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
    · rw [h, Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hcop

end Z3NetF.Proofs.K1Compl
