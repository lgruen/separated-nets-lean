module
public import Mathlib
public import Z3Net.SUPoly
public import Z3Net.SUBoxMinor

@[expose] public section

/-!
# Entry U, part 11: the frame box minors (exact confluent-Vandermonde value)

For the frame (places `∞, 0, 1, …, s-2`, rows of coordinate `0` first) and every composition `d`
of `m`, `det = ± ∏_{0 < c' < c} (c - c')^(d_c' d_c)`.

Proof: multiply the box matrix `B` on the right by the matrix `P` of the Newton-type basis
`bas n` of `ℤ[t]_{<m}` indexed like the rows: row/column `n` of coordinate `c = 0` ↔
`Ptot · t^(d_0-1-j)`, of a finite coordinate `c` ↔ `N_c (t - a_c)^j` (`N_c = ∏_{0<c'<c} (t - a_c')^(d_c')`,
`Ptot = ∏_{c' > 0} (t - a_c')^(d_c')`). Then `B P` is lower triangular with diagonal `1` resp.
`N_c(a_c)`, and the columns of `P` are monic of pairwise distinct degrees, so `P` is a column
permutation of an upper unitriangular matrix and `det P = ±1`.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

/-! ## Locating rows -/

lemma boxLoc_cover : ∀ (ds : List ℕ) (c0 r : ℕ), r < ds.sum →
    ∃ j i, ∃ hj : j < ds.length, i < ds[j] ∧ r = (ds.take j).sum + i ∧
      boxLoc ds c0 r = (c0 + j, i)
  | [], _, r, h => by simp at h
  | x :: xs, c0, r, h => by
    by_cases hr : r < x
    · exact ⟨0, r, by simp, by simpa using hr, by simp, by simp [boxLoc, hr]⟩
    · simp only [List.sum_cons] at h
      obtain ⟨j, i, hj, hi, hr', hb⟩ := boxLoc_cover xs (c0 + 1) (r - x) (by omega)
      refine ⟨j + 1, i, by simpa using hj, by simpa using hi, ?_, ?_⟩
      · simp only [List.take_succ_cons, List.sum_cons]; omega
      · simp only [boxLoc, if_neg hr, hb]; ring_nf

variable {s m : ℕ} (d : Fin s → ℕ)

/-- Prefix sums `pre c = d_0 + … + d_{c-1}`. -/
def pre (c : ℕ) : ℕ := ((List.ofFn d).take c).sum

lemma pre_succ (c : Fin s) : pre d (c + 1) = pre d c + d c := by
  unfold pre
  rw [List.sum_take_succ _ _ (by simp)]
  simp

lemma pre_mono {a b : ℕ} (h : a ≤ b) : pre d a ≤ pre d b :=
  (List.take_sublist_take_left h).sum_le_sum (fun _ _ => Nat.zero_le _)

lemma pre_le_sum (c : ℕ) : pre d c ≤ ∑ t, d t := by
  unfold pre
  rw [← List.sum_ofFn]
  exact (List.take_sublist _ _).sum_le_sum (fun _ _ => Nat.zero_le _)

lemma pre_eq_sum (c : ℕ) : pre d c = ∑ t ∈ univ.filter (fun t : Fin s => (t : ℕ) < c), d t := by
  induction c with
  | zero => simp [pre]
  | succ c ih =>
    by_cases hc : c < s
    · rw [show pre d (c + 1) = pre d (⟨c, hc⟩ : Fin s) + d ⟨c, hc⟩ from pre_succ d ⟨c, hc⟩, ih]
      have : univ.filter (fun t : Fin s => (t : ℕ) < c + 1) =
          insert ⟨c, hc⟩ (univ.filter (fun t : Fin s => (t : ℕ) < c)) := by
        ext t; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
      rw [this, Finset.sum_insert (by simp)]; ring
    · have h1 : pre d (c + 1) = pre d c := by
        unfold pre
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [h1, ih]
      congr 1; ext t; simp only [mem_filter, mem_univ, true_and]; have := t.isLt; omega

lemma loc_spec (hd : ∑ c, d c = m) (r : Fin m) :
    ∃ c : Fin s, (r : ℕ) = pre d c + (boxLoc (List.ofFn d) 0 r).2 ∧
      (boxLoc (List.ofFn d) 0 r).1 = c ∧ (boxLoc (List.ofFn d) 0 r).2 < d c := by
  have hs : (r : ℕ) < (List.ofFn d).sum := by rw [List.sum_ofFn, hd]; exact r.isLt
  obtain ⟨j, i, hj, hi, hr, hb⟩ := boxLoc_cover (List.ofFn d) 0 r hs
  have hjs : j < s := by simpa using hj
  refine ⟨⟨j, hjs⟩, ?_, ?_, ?_⟩
  · rw [hb]; exact hr
  · rw [hb]; simp
  · rw [hb]; simpa using hi

/-! ## The Newton-type basis -/

/-- `N_c = ∏_{0 < t < c} (X - a_t)^(d_t)`. -/
def Nfac (c : ℕ) : ℤ[X] :=
  ∏ t ∈ univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < c), (X - C ((t : ℤ) - 1)) ^ d t

/-- `Ptot = ∏_{t > 0} (X - a_t)^(d_t)`. -/
def Ptot : ℤ[X] := ∏ t ∈ univ.filter (fun t : Fin s => 0 < (t : ℕ)), (X - C ((t : ℤ) - 1)) ^ d t

/-- The basis polynomial of index `(c, j)`. -/
def basCJ (c j : ℕ) : ℤ[X] :=
  if c = 0 then Ptot d * X ^ (pre d 1 - 1 - j) else Nfac d c * (X - C ((c : ℤ) - 1)) ^ j

lemma monic_Nfac (c : ℕ) : (Nfac d c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma monic_Ptot : (Ptot d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma natDegree_prodX (S : Finset (Fin s)) :
    (∏ t ∈ S, (X - C ((t : ℤ) - 1)) ^ d t).natDegree = ∑ t ∈ S, d t := by
  rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma sum_filter_pos (hs : 0 < s) (c : ℕ) (hc : 1 ≤ c) :
    ∑ t ∈ univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < c), d t = pre d c - pre d 1 := by
  rw [pre_eq_sum, pre_eq_sum]
  have : univ.filter (fun t : Fin s => (t : ℕ) < c) =
      univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < c) ∪
        univ.filter (fun t : Fin s => (t : ℕ) < 1) := by
    ext t; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
  rw [this, Finset.sum_union]
  · simp
  · rw [Finset.disjoint_filter]; intro t _ h; omega

lemma natDegree_Nfac (hs : 0 < s) (c : ℕ) (hc : 1 ≤ c) :
    (Nfac d c).natDegree = pre d c - pre d 1 := by
  rw [Nfac, natDegree_prodX, sum_filter_pos d hs c hc]

lemma natDegree_Ptot (hs : 0 < s) (hd : ∑ c, d c = m) : (Ptot d).natDegree = m - pre d 1 := by
  rw [Ptot, natDegree_prodX]
  have := sum_filter_pos d hs s (by omega)
  have h2 : univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < s) =
      univ.filter (fun t : Fin s => 0 < (t : ℕ)) := by
    ext t; simp only [mem_filter, mem_univ, true_and]; have := t.isLt; omega
  rw [h2] at this
  rw [this]
  congr 1
  rw [pre_eq_sum, ← hd]
  congr 1; ext t; simp [t.isLt]

/-! ## Degrees and readings of the basis -/

lemma pre_zero : pre d 0 = 0 := by simp [pre]

lemma pre_one (hs : 0 < s) : pre d 1 = d ⟨0, hs⟩ := by
  have := pre_succ d ⟨0, hs⟩; simpa [pre_zero] using this

lemma monic_basCJ (c j : ℕ) : (basCJ d c j).Monic := by
  unfold basCJ
  split_ifs
  · exact (monic_Ptot d).mul (monic_X_pow _)
  · exact (monic_Nfac d c).mul ((monic_X_sub_C _).pow _)

lemma natDegree_basCJ0 (hs : 0 < s) (hd : ∑ c, d c = m) (j : ℕ) (hj : j < pre d 1) :
    (basCJ d 0 j).natDegree = m - 1 - j := by
  have h1 : pre d 1 ≤ m := by rw [← hd]; exact pre_le_sum d 1
  rw [basCJ, if_pos rfl, (monic_Ptot d).natDegree_mul (monic_X_pow _), natDegree_Ptot d hs hd,
    natDegree_X_pow]
  omega

lemma natDegree_basCJ (hs : 0 < s) (c j : ℕ) (hc : 1 ≤ c) :
    (basCJ d c j).natDegree = pre d c - pre d 1 + j := by
  rw [basCJ, if_neg (by omega), (monic_Nfac d c).natDegree_mul ((monic_X_sub_C _).pow _),
    natDegree_Nfac d hs c hc, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma pv_coeff {R : Type*} [CommRing R] (P : R[X]) (h : P.natDegree < m) :
    pv (fun l : Fin m => P.coeff l) = P := by
  ext n
  rw [coeff_pv]
  split_ifs with hn
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma reading_fin (c : Fin s) (hc : (c : ℕ) ≠ 0) (P : ℤ[X]) (hP : P.natDegree < m) (i : Fin m) :
    ∑ l : Fin m, frameGen m c i l * P.coeff l = (taylor ((c : ℤ) - 1) P).coeff i := by
  have := frame_fin (R := ℤ) m c hc (fun l : Fin m => P.coeff l) i
  rw [pv_coeff P hP] at this
  simp only [mulVec, dotProduct, map_apply, Int.cast_id] at this
  rw [this]; simp [place]

lemma reading_inf (c : Fin s) (hc : (c : ℕ) = 0) (P : ℤ[X]) (hP : P.natDegree < m) (i : Fin m) :
    ∑ l : Fin m, frameGen m c i l * P.coeff l = P.coeff (m - 1 - i) := by
  have := frame_inf (R := ℤ) m c hc (fun l : Fin m => P.coeff l) i
  rw [pv_coeff P hP] at this
  simp only [mulVec, dotProduct, map_apply, Int.cast_id] at this
  exact this

/-- A finite earlier place divides `N_c`. -/
lemma taylor_Nfac_zero (c : ℕ) (c' : Fin s) (h0 : 0 < (c' : ℕ)) (hlt : (c' : ℕ) < c) (j i : ℕ)
    (hi : i < d c') :
    (taylor ((c' : ℤ) - 1) (Nfac d c * (X - C ((c : ℤ) - 1)) ^ j)).coeff i = 0 := by
  have hmem : c' ∈ univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < c) := by simp [h0, hlt]
  rw [Nfac, ← Finset.mul_prod_erase _ _ hmem, mul_assoc]
  have e : (C ((c' : ℤ) - 1) : ℤ[X]) = C (((c' : ℤ) - 1 : ℤ)) := rfl
  rw [coeff_taylor_X_sub_C_pow_mul, if_neg (by omega)]

lemma taylor_self (c : ℕ) (j i : ℕ) :
    (taylor ((c : ℤ) - 1) (Nfac d c * (X - C ((c : ℤ) - 1)) ^ j)).coeff i =
      if j ≤ i then (taylor ((c : ℤ) - 1) (Nfac d c)).coeff (i - j) else 0 := by
  rw [mul_comm, coeff_taylor_X_sub_C_pow_mul]

/-! ## The matrices `P` and `B P` -/

/-- Coordinate of row/column `n`. -/
def cN (n : Fin m) : ℕ := (boxLoc (List.ofFn d) 0 n).1
/-- Index inside the coordinate. -/
def jN (n : Fin m) : ℕ := (boxLoc (List.ofFn d) 0 n).2
/-- The basis polynomial of column `n`. -/
def bas (n : Fin m) : ℤ[X] := basCJ d (cN d n) (jN d n)
/-- The basis matrix `P` (column `n` = coefficients of `bas n`). -/
def Pm : Matrix (Fin m) (Fin m) ℤ := fun l n => (bas d n).coeff l

variable {d}

lemma loc (hd : ∑ c, d c = m) (n : Fin m) :
    cN d n < s ∧ (n : ℕ) = pre d (cN d n) + jN d n ∧ jN d n < d ⟨cN d n, by
      obtain ⟨c, _, h2, _⟩ := loc_spec d hd n; rw [cN, h2]; exact c.isLt⟩ := by
  obtain ⟨c, h1, h2, h3⟩ := loc_spec d hd n
  have hc : cN d n = c := h2
  refine ⟨by rw [hc]; exact c.isLt, by rw [hc]; exact h1, ?_⟩
  have : (⟨cN d n, by rw [hc]; exact c.isLt⟩ : Fin s) = c := Fin.ext hc
  rw [this]; exact h3

lemma pre1_le (hd : ∑ c, d c = m) : pre d 1 ≤ m := by rw [← hd]; exact pre_le_sum d 1

lemma cN_zero_iff (hs : 0 < s) (hd : ∑ c, d c = m) (n : Fin m) : cN d n = 0 ↔ (n : ℕ) < pre d 1 := by
  obtain ⟨h1, h2, h3⟩ := loc hd n
  constructor
  · intro h0
    have e : (⟨cN d n, h1⟩ : Fin s) = ⟨0, hs⟩ := Fin.ext h0
    have h3' : jN d n < d ⟨0, hs⟩ := by rw [← e]; exact h3
    rw [h2, h0, pre_zero, pre_one d hs]; omega
  · intro hn
    by_contra h0
    have := pre_mono d (show 1 ≤ cN d n by omega)
    omega

lemma natDegree_bas (hs : 0 < s) (hd : ∑ c, d c = m) (n : Fin m) :
    (bas d n).natDegree = if (n : ℕ) < pre d 1 then m - 1 - n else n - pre d 1 := by
  obtain ⟨h1, h2, h3⟩ := loc hd n
  unfold bas
  split_ifs with hn
  · have h0 := (cN_zero_iff hs hd n).mpr hn
    rw [h0, natDegree_basCJ0 d hs hd]
    · rw [h2, h0, pre_zero]; simp
    · rw [h2, h0, pre_zero] at hn; simpa using hn
  · have h0 : cN d n ≠ 0 := fun h => hn ((cN_zero_iff hs hd n).mp h)
    rw [natDegree_basCJ d hs _ _ (by omega)]
    have := pre_mono d (show 1 ≤ cN d n by omega)
    omega

lemma natDegree_bas_lt (hs : 0 < s) (hd : ∑ c, d c = m) (n : Fin m) : (bas d n).natDegree < m := by
  rw [natDegree_bas hs hd]; have := n.isLt; split_ifs <;> omega

lemma BP_entry (hs : 0 < s) (hd : ∑ c, d c = m) (r n : Fin m) :
    ((boxMatrix (frameGen (s := s) m) d * Pm d : Matrix (Fin m) (Fin m) ℤ)) r n =
      if cN d r = 0 then (bas d n).coeff (m - 1 - jN d r)
      else (taylor ((cN d r : ℤ) - 1) (bas d n)).coeff (jN d r) := by
  obtain ⟨h1, h2, h3⟩ := loc hd r
  have hj : jN d r < m := by omega
  rw [Matrix.mul_apply]
  have hrow : ∀ l, boxMatrix (frameGen (s := s) m) d r l = frameGen m (⟨cN d r, h1⟩ : Fin s) ⟨jN d r, hj⟩ l := by
    intro l
    simp only [boxMatrix]
    rw [dif_pos ⟨h1, hj⟩]; rfl
  simp only [hrow, Pm]
  split_ifs with h0
  · rw [reading_inf (⟨cN d r, h1⟩ : Fin s) h0 _ (natDegree_bas_lt hs hd n)]
  · rw [reading_fin (⟨cN d r, h1⟩ : Fin s) h0 _ (natDegree_bas_lt hs hd n)]

lemma cN_le_of_lt (hd : ∑ c, d c = m) (r n : Fin m) (h : r < n) :
    cN d r ≤ cN d n ∧ (cN d r = cN d n → jN d r < jN d n) := by
  obtain ⟨r1, r2, r3⟩ := loc hd r
  obtain ⟨n1, n2, n3⟩ := loc hd n
  have hrn : (r : ℕ) < n := h
  constructor
  · by_contra hc
    have := pre_mono d (show cN d n + 1 ≤ cN d r by omega)
    have := pre_succ d ⟨cN d n, n1⟩
    simp only at this
    omega
  · intro he
    rw [he] at r2; omega

lemma BP_lower (hs : 0 < s) (hd : ∑ c, d c = m) (r n : Fin m) (h : r < n) :
    ((boxMatrix (frameGen (s := s) m) d * Pm d : Matrix (Fin m) (Fin m) ℤ)) r n = 0 := by
  rw [BP_entry hs hd]
  obtain ⟨hle, heq⟩ := cN_le_of_lt hd r n h
  obtain ⟨r1, r2, r3⟩ := loc hd r
  obtain ⟨n1, n2, n3⟩ := loc hd n
  have hrn : (r : ℕ) < n := h
  split_ifs with hr0
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_bas hs hd]
    have hr' : (r : ℕ) < pre d 1 := (cN_zero_iff hs hd r).mp hr0
    rw [r2, hr0, pre_zero, zero_add] at hr'
    have hrj : (r : ℕ) = jN d r := by rw [r2, hr0, pre_zero, zero_add]
    have := n.isLt
    split_ifs <;> omega
  · unfold bas basCJ
    rw [if_neg (by omega)]
    rcases Nat.lt_or_ge (cN d r) (cN d n) with hlt | hge
    · exact taylor_Nfac_zero d (cN d n) ⟨cN d r, r1⟩ (by simp; omega) hlt _ _ r3
    · have he : cN d r = cN d n := le_antisymm hle hge
      have hj := heq he
      rw [he, taylor_self, if_neg (by omega)]

lemma BP_diag (hs : 0 < s) (hd : ∑ c, d c = m) (n : Fin m) :
    ((boxMatrix (frameGen (s := s) m) d * Pm d : Matrix (Fin m) (Fin m) ℤ)) n n =
      if cN d n = 0 then 1 else (Nfac d (cN d n)).eval ((cN d n : ℤ) - 1) := by
  rw [BP_entry hs hd]
  by_cases h0 : cN d n = 0
  · rw [if_pos h0, if_pos h0]
    have hn : (n : ℕ) < pre d 1 := (cN_zero_iff hs hd n).mp h0
    obtain ⟨n1, n2, n3⟩ := loc hd n
    have hj : (n : ℕ) = jN d n := by rw [n2, h0, pre_zero, zero_add]
    have hdeg := natDegree_bas hs hd n
    rw [if_pos hn] at hdeg
    rw [show m - 1 - jN d n = (bas d n).natDegree by rw [hdeg]; omega]
    exact (monic_basCJ d _ _).coeff_natDegree
  · rw [if_neg h0, if_neg h0]
    unfold bas basCJ
    rw [if_neg h0, taylor_self, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]

/-! ## `det P = ±1` -/

/-- The degree of the basis polynomial of column `n`. -/
def tauF (hd : ∑ c, d c = m) (n : Fin m) : Fin m :=
  ⟨if (n : ℕ) < pre d 1 then m - 1 - n else n - pre d 1, by have := n.isLt; split_ifs <;> omega⟩

lemma tauF_inj (hd : ∑ c, d c = m) : Function.Injective (tauF hd (d := d)) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [tauF] at h'
  have ha := a.isLt; have hb := b.isLt
  have hp := pre1_le hd (d := d)
  ext
  split_ifs at h' <;> omega

/-- The degree permutation. -/
def tau (hd : ∑ c, d c = m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (tauF hd) (Finite.injective_iff_bijective.mp (tauF_inj hd))

lemma tau_apply (hd : ∑ c, d c = m) (n : Fin m) : ((tau hd n : Fin m) : ℕ) =
    if (n : ℕ) < pre d 1 then m - 1 - n else n - pre d 1 := rfl

lemma det_Pm (hs : 0 < s) (hd : ∑ c, d c = m) :
    (Pm d : Matrix (Fin m) (Fin m) ℤ).det = 1 ∨ (Pm d : Matrix (Fin m) (Fin m) ℤ).det = -1 := by
  set U : Matrix (Fin m) (Fin m) ℤ := fun l e => (bas d ((tau hd).symm e)).coeff l with hU
  have hPU : Pm d = U.submatrix id (tau hd) := by
    ext l n
    rw [Matrix.submatrix_apply]
    simp only [id, hU, Equiv.symm_apply_apply, Pm]
  have hdegU : ∀ e : Fin m, (bas d ((tau hd).symm e)).natDegree = e := by
    intro e
    have := natDegree_bas hs hd ((tau hd).symm e)
    rw [← tau_apply hd, Equiv.apply_symm_apply] at this
    exact this
  have hUup : U.IsUpperTriangular := by
    intro i j hij
    simp only [hU]
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdegU]; exact hij
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hUup]
    refine Finset.prod_eq_one fun e _ => ?_
    simp only [hU]
    have := (monic_basCJ d (cN d ((tau hd).symm e)) (jN d ((tau hd).symm e))).coeff_natDegree
    rw [← hdegU e]
    exact this
  rw [hPU, Matrix.det_permute', hdetU, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (tau hd)) with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-! ## Assembly -/

lemma fiber_card (hd : ∑ c, d c = m) (c : Fin s) :
    (univ.filter (fun n : Fin m => cN d n = c)).card = d c := by
  rw [← Finset.card_range (d c)]
  apply Finset.card_bij (fun n _ => jN d n)
  · intro n hn
    rw [mem_filter] at hn
    obtain ⟨n1, n2, n3⟩ := loc hd n
    have e : (⟨cN d n, n1⟩ : Fin s) = c := Fin.ext hn.2
    rw [mem_range]; rw [e] at n3; exact n3
  · intro a ha b hb hab
    rw [mem_filter] at ha hb
    obtain ⟨a1, a2, a3⟩ := loc hd a
    obtain ⟨b1, b2, b3⟩ := loc hd b
    ext; rw [a2, b2, ha.2, hb.2, hab]
  · intro k hk
    rw [mem_range] at hk
    have hps := pre_succ d c
    have hle : pre d (c + 1) ≤ m := by rw [← hd]; exact pre_le_sum d _
    have hlt : pre d c + k < m := by omega
    have hloc := boxLoc_spec (List.ofFn d) 0 c k (by simp) (by simpa using hk)
    refine ⟨⟨pre d c + k, hlt⟩, ?_, ?_⟩
    · rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
      show cN d ⟨pre d c + k, hlt⟩ = c
      simp only [cN]; unfold pre at hloc ⊢; rw [hloc]; simp
    · show jN d ⟨pre d c + k, hlt⟩ = k
      simp only [jN]; unfold pre at hloc ⊢; rw [hloc]

/-- Value of `N_c(a_c)`. -/
lemma Nfac_eval (c : ℕ) :
    (Nfac d c).eval ((c : ℤ) - 1) =
      ∏ t ∈ univ.filter (fun t : Fin s => 0 < (t : ℕ) ∧ (t : ℕ) < c), ((c : ℤ) - t) ^ d t := by
  simp only [Nfac, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  exact Finset.prod_congr rfl fun t _ => by ring_nf

/-- **Frame box minors** (confluent Vandermonde; Lemma T_s, exact value). -/
theorem U_frameMinor (s m : ℕ) (hs : 1 ≤ s) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (boxMatrix (frameGen (s := s) m) d).det = ∏ c : Fin s, ∏ c' : Fin s,
        (if 0 < (c' : ℕ) ∧ c' < c then ((c : ℤ) - c') ^ (d c' * d c) else 1) ∨
      (boxMatrix (frameGen (s := s) m) d).det = -∏ c : Fin s, ∏ c' : Fin s,
        (if 0 < (c' : ℕ) ∧ c' < c then ((c : ℤ) - c') ^ (d c' * d c) else 1) := by
  have hs0 : 0 < s := by omega
  set B : Matrix (Fin m) (Fin m) ℤ := boxMatrix (frameGen (s := s) m) d with hB
  have hlow : (B * Pm d : Matrix (Fin m) (Fin m) ℤ).IsLowerTriangular := by
    intro i j hij
    exact BP_lower hs0 hd i j hij
  set g : ℕ → ℤ := fun k => if k = 0 then 1 else (Nfac d k).eval ((k : ℤ) - 1) with hg
  let cF : Fin m → Fin s := fun n => ⟨cN d n, (loc hd n).1⟩
  have hprod : (B * Pm d : Matrix (Fin m) (Fin m) ℤ).det = ∏ c : Fin s, g c ^ d c := by
    rw [Matrix.det_of_isLowerTriangular _ hlow]
    have hdiag : ∀ n, (B * Pm d : Matrix (Fin m) (Fin m) ℤ) n n = g (cF n) := by
      intro n; rw [hB, BP_diag hs0 hd]
    simp only [hdiag]
    rw [← Finset.prod_fiberwise univ cF (fun n => g (cF n))]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun n hn => by rw [(mem_filter.mp hn).2]), prod_const]
    congr 1
    have := fiber_card hd c
    rw [← this]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro n _
    simp [cF, Fin.ext_iff]
  have hV : ∏ c : Fin s, g c ^ d c = ∏ c : Fin s, ∏ c' : Fin s,
      (if 0 < (c' : ℕ) ∧ c' < c then ((c : ℤ) - c') ^ (d c' * d c) else 1) := by
    refine Finset.prod_congr rfl fun c _ => ?_
    by_cases hc : (c : ℕ) = 0
    · simp only [hg, hc, if_true, one_pow]
      symm; refine Finset.prod_eq_one fun c' _ => ?_
      rw [if_neg]; rw [Fin.lt_def]; omega
    · simp only [hg, hc, if_false]
      rw [Nfac_eval, ← Finset.prod_pow, Finset.prod_filter]
      refine Finset.prod_congr rfl fun c' _ => ?_
      have hiff : (0 < (c' : ℕ) ∧ (c' : ℕ) < c) ↔ (0 < (c' : ℕ) ∧ c' < c) := by rw [Fin.lt_def]
      by_cases h : 0 < (c' : ℕ) ∧ c' < c
      · rw [if_pos (hiff.mpr h), if_pos h, ← pow_mul]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hmul : B.det * (Pm d : Matrix (Fin m) (Fin m) ℤ).det = ∏ c : Fin s, ∏ c' : Fin s,
      (if 0 < (c' : ℕ) ∧ c' < c then ((c : ℤ) - c') ^ (d c' * d c) else 1) := by
    rw [← Matrix.det_mul, hprod, hV]
  rcases det_Pm hs0 hd with h | h
  · left; rw [← hmul, h, mul_one]
  · right; rw [← hmul, h]; ring

end

end Z3NetU.Proofs
