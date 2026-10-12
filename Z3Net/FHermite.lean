module
public import Z3Net.FNie

@[expose] public section

/-!
# Entry F, part 4: `lem:hermite` and `lem:Ts` (the confluent Vandermonde determinant)

For the frame with `∞` at an arbitrary coordinate `inf` and finite places `x c` in a commutative
ring, multiply the box matrix `B` on the right by the matrix `P` of the Newton-type basis indexed
like the rows: for a finite coordinate `c`, `N_c (t - x_c)^j` with `N_c = ∏_{t finite, t < c}
(t - x_t)^(d_t)`; for `∞`, `Ptot t^(d_∞-1-j)` with `Ptot = ∏_{t finite} (t - x_t)^(d_t)`. Then
`B P` is lower triangular with diagonal `N_c(x_c)` resp. `1`, and `P` is a column permutation of
an upper unitriangular matrix (the columns are monic of pairwise distinct degrees). This
generalizes entry U's `SUFrame` (places `∞, 0, …, s-2`, `∞` first, over `ℤ`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

section reading

variable {R : Type*} [CommRing R]

lemma pv_coeff' {m : ℕ} (P : R[X]) (h : P.natDegree < m) :
    Z3NetU.Proofs.pv (fun l : Fin m => P.coeff l) = P := by
  ext n
  rw [Z3NetU.Proofs.coeff_pv]
  split_ifs with hn
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma readAt_mul (m : ℕ) (x : R) (P : R[X]) (hP : P.natDegree < m) (i : Fin m) :
    ∑ l : Fin m, Z3NetF.readAt m x i l * P.coeff l = (taylor x P).coeff i := by
  conv_rhs => rw [← pv_coeff' (m := m) P hP]
  rw [Z3NetU.Proofs.pv, map_sum, finset_sum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
  simp only [Z3NetF.readAt]
  ring

lemma readInf_mul (m : ℕ) (P : R[X]) (i : Fin m) :
    ∑ l : Fin m, Z3NetF.readInf (R := R) m i l * P.coeff l = P.coeff (m - 1 - i) := by
  have hi := i.isLt
  rw [Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · simp [Z3NetF.readInf, show m - 1 - (i : ℕ) + i + 1 = m by omega]
  · intro b _ hb
    simp only [Z3NetF.readInf]
    rw [if_neg, zero_mul]
    intro h; apply hb; ext; simp; omega
  · simp

end reading

section frame

variable {R : Type*} [CommRing R] {s m : ℕ} (inf : Fin s) (x : Fin s → R) (d : Fin s → ℕ)

/-- `N_c = ∏_{t finite, t < c} (X - x_t)^(d_t)`. -/
def NfacG (c : Fin s) : R[X] :=
  ∏ t ∈ univ.filter (fun t => t ≠ inf ∧ t < c), (X - C (x t)) ^ d t

/-- `Ptot = ∏_{t finite} (X - x_t)^(d_t)`. -/
def PtotG : R[X] := ∏ t ∈ univ.filter (fun t => t ≠ inf), (X - C (x t)) ^ d t

/-- The basis polynomial of index `(c, j)`. -/
def basG (c : Fin s) (j : ℕ) : R[X] :=
  if c = inf then PtotG inf x d * X ^ (d inf - 1 - j) else NfacG inf x d c * (X - C (x c)) ^ j

lemma natDegree_prodX [Nontrivial R] (S : Finset (Fin s)) :
    (∏ t ∈ S, (X - C (x t)) ^ d t).natDegree = ∑ t ∈ S, d t := by
  rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma monic_NfacG (c : Fin s) : (NfacG inf x d c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma monic_PtotG : (PtotG inf x d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _

lemma monic_basG (c : Fin s) (j : ℕ) : (basG inf x d c j).Monic := by
  unfold basG NfacG PtotG
  split_ifs
  · exact (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _).mul (monic_X_pow _)
  · exact (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)

/-- `∑_{t < c} d_t` splits into finite and `∞` parts. -/
lemma pre_split (c : Fin s) :
    pre d c = ∑ t ∈ univ.filter (fun t => t ≠ inf ∧ t < c), d t + if inf < c then d inf else 0 := by
  rw [show pre d c = Z3NetU.Proofs.pre d (c : ℕ) from rfl, Z3NetU.Proofs.pre_eq_sum]
  have : univ.filter (fun t : Fin s => (t : ℕ) < c) =
      univ.filter (fun t => t ≠ inf ∧ t < c) ∪ (univ.filter (fun t => t = inf ∧ t < c)) := by
    ext t; simp only [mem_filter, mem_univ, true_and, mem_union, Fin.lt_def]; tauto
  rw [this, Finset.sum_union]
  · congr 1
    by_cases h : inf < c
    · rw [if_pos h, Finset.sum_eq_single inf]
      · intro b hb hbi; exact absurd (mem_filter.mp hb).2.1 hbi
      · intro hn; exact absurd (mem_filter.mpr ⟨mem_univ _, rfl, h⟩) hn
    · rw [if_neg h]; apply Finset.sum_eq_zero; intro t ht
      obtain ⟨-, h1, h2⟩ := mem_filter.mp ht; subst h1; exact absurd h2 h
  · rw [Finset.disjoint_filter]; intro t _ h1 h2; exact h1.1 h2.1

lemma sum_fin_eq (hd : ∑ c, d c = m) :
    ∑ t ∈ univ.filter (fun t => t ≠ inf), d t = m - d inf := by
  rw [← hd, ← Finset.sum_filter_add_sum_filter_not univ (fun t => t ≠ inf)]
  have : ∑ t ∈ univ.filter (fun t => ¬t ≠ inf), d t = d inf := by
    rw [Finset.sum_eq_single inf]
    · intro b hb hbi; exact absurd (by simpa using (mem_filter.mp hb).2) hbi
    · intro hn; exact absurd (mem_filter.mpr ⟨mem_univ _, by simp⟩) hn
  rw [this]; omega

/-! ### Rows and columns -/

variable {d}

/-- Coordinate of row/column `n`. -/
def cF (hd : ∑ c, d c = m) (n : Fin m) : Fin s := ⟨Z3NetU.Proofs.cN d n, (Z3NetU.Proofs.loc hd n).1⟩

lemma cF_spec (hd : ∑ c, d c = m) (n : Fin m) :
    (n : ℕ) = pre d (cF hd n) + Z3NetU.Proofs.jN d n ∧ Z3NetU.Proofs.jN d n < d (cF hd n) :=
  ⟨(Z3NetU.Proofs.loc hd n).2.1, (Z3NetU.Proofs.loc hd n).2.2⟩

lemma pre_le_of_lt (c c' : Fin s) (h : c < c') : pre d c + d c ≤ pre d c' := by
  have h1 := Z3NetU.Proofs.pre_succ d c
  have h2 := Z3NetU.Proofs.pre_mono d (show (c : ℕ) + 1 ≤ c' from h)
  simp only [pre] at *; omega

/-- The basis polynomial of column `n`. -/
def basN (hd : ∑ c, d c = m) (n : Fin m) : R[X] := basG inf x d (cF hd n) (Z3NetU.Proofs.jN d n)

/-- The basis matrix (column `n` = coefficients of `basN n`). -/
def PmG (hd : ∑ c, d c = m) : Matrix (Fin m) (Fin m) R := fun l n => (basN inf x hd n).coeff l

/-- The degree of the basis polynomial of column `n`. -/
def tauG (hd : ∑ c, d c = m) (n : ℕ) : ℕ :=
  if n < pre d inf then n else if n < pre d inf + d inf then m - 1 - (n - pre d inf) else n - d inf

lemma pre_inf_le (hd : ∑ c, d c = m) : pre d inf + d inf ≤ m := by
  have h1 := Z3NetU.Proofs.pre_succ d inf
  have h2 := Z3NetU.Proofs.pre_le_sum d ((inf : ℕ) + 1)
  rw [hd] at h2; simp only [pre] at *; omega

lemma cF_cases (hd : ∑ c, d c = m) (n : Fin m) :
    ((n : ℕ) < pre d inf ∧ cF hd n < inf) ∨
      (pre d inf ≤ n ∧ (n : ℕ) < pre d inf + d inf ∧ cF hd n = inf) ∨
      (pre d inf + d inf ≤ n ∧ inf < cF hd n) := by
  obtain ⟨h1, h2⟩ := cF_spec hd n
  rcases lt_trichotomy (cF hd n) inf with hlt | heq | hgt
  · left; have := pre_le_of_lt (d := d) _ _ hlt; exact ⟨by omega, hlt⟩
  · right; left; rw [heq] at h1 h2; exact ⟨by omega, by omega, heq⟩
  · right; right; have := pre_le_of_lt (d := d) _ _ hgt; exact ⟨by omega, hgt⟩

lemma natDegree_basN [Nontrivial R] (hd : ∑ c, d c = m) (n : Fin m) :
    (basN inf x hd n).natDegree = tauG inf hd n := by
  obtain ⟨h1, h2⟩ := cF_spec hd n
  have hpi := pre_inf_le inf hd (d := d)
  unfold basN basG tauG
  rcases cF_cases inf hd n with ⟨hn, hc⟩ | ⟨hn1, hn2, hc⟩ | ⟨hn, hc⟩
  · rw [if_neg (ne_of_lt hc), if_pos hn,
      (monic_NfacG inf x d _).natDegree_mul ((monic_X_sub_C _).pow _), NfacG, natDegree_prodX,
      (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    have := pre_split inf d (cF hd n)
    rw [if_neg (not_lt.mpr (le_of_lt hc))] at this
    omega
  · rw [if_pos hc, if_neg (by omega), if_pos hn2,
      (monic_PtotG inf x d).natDegree_mul (monic_X_pow _),
      PtotG, natDegree_prodX, natDegree_X_pow, sum_fin_eq inf d hd]
    rw [hc] at h1 h2
    omega
  · rw [if_neg (ne_of_gt hc), if_neg (by omega), if_neg (by omega),
      (monic_NfacG inf x d _).natDegree_mul ((monic_X_sub_C _).pow _), NfacG, natDegree_prodX,
      (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    have := pre_split inf d (cF hd n)
    rw [if_pos hc] at this
    omega

lemma tauG_lt (hd : ∑ c, d c = m) (n : Fin m) : tauG inf hd n < m := by
  have := n.isLt; have := pre_inf_le inf hd (d := d)
  unfold tauG; split_ifs <;> omega

lemma tauG_inj (hd : ∑ c, d c = m) (a b : Fin m) (h : tauG inf hd a = tauG inf hd b) : a = b := by
  have ha := a.isLt; have hb := b.isLt; have := pre_inf_le inf hd (d := d)
  unfold tauG at h
  ext
  split_ifs at h <;> omega

/-! ### `B P` is lower triangular -/

lemma box_row_frame (hd : ∑ c, d c = m) (r : Fin m) :
    Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d r =
      Z3NetF.frameRead m inf x (cF hd r) ⟨Z3NetU.Proofs.jN d r, by
        obtain ⟨h1, h2⟩ := cF_spec hd r; omega⟩ := by
  obtain ⟨h1, h2⟩ := cF_spec hd r
  have := box_row_pre (Z3NetF.frameRead m inf x) d hd (cF hd r) _ h2
  have hr : r = ⟨pre d (cF hd r) + Z3NetU.Proofs.jN d r, pre_add_lt d hd _ _ h2⟩ := Fin.ext h1
  conv_lhs => rw [hr]
  rw [this]

lemma BP_entryG [Nontrivial R] (hd : ∑ c, d c = m) (r n : Fin m) :
    (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d * PmG inf x hd) r n =
      if cF hd r = inf then (basN inf x hd n).coeff (m - 1 - Z3NetU.Proofs.jN d r)
      else (taylor (x (cF hd r)) (basN inf x hd n)).coeff (Z3NetU.Proofs.jN d r) := by
  rw [Matrix.mul_apply, box_row_frame inf x hd r]
  simp only [PmG, Z3NetF.frameRead]
  have hdeg : (basN inf x hd n).natDegree < m := by
    rw [natDegree_basN inf x hd n]; exact tauG_lt inf hd n
  split_ifs with h0
  · exact readInf_mul m _ _
  · exact readAt_mul m _ _ hdeg _

lemma cF_le_of_lt (hd : ∑ c, d c = m) (r n : Fin m) (h : r < n) :
    cF hd r ≤ cF hd n ∧ (cF hd r = cF hd n → Z3NetU.Proofs.jN d r < Z3NetU.Proofs.jN d n) := by
  obtain ⟨r1, r2⟩ := cF_spec hd r
  obtain ⟨n1, n2⟩ := cF_spec hd n
  have hrn : (r : ℕ) < n := h
  constructor
  · by_contra hc
    push_neg at hc
    have := pre_le_of_lt (d := d) _ _ hc
    omega
  · intro he
    rw [he] at r1; omega

lemma BP_lowerG [Nontrivial R] (hd : ∑ c, d c = m) (r n : Fin m) (h : r < n) :
    (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d * PmG inf x hd) r n = 0 := by
  rw [BP_entryG inf x hd]
  obtain ⟨hle, heq⟩ := cF_le_of_lt hd r n h
  obtain ⟨r1, r2⟩ := cF_spec hd r
  obtain ⟨n1, n2⟩ := cF_spec hd n
  split_ifs with hr0
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_basN inf x hd n]
    have hpi := pre_inf_le inf hd (d := d)
    rw [hr0] at r1 r2
    rcases cF_cases inf hd n with ⟨hn, hc⟩ | ⟨hn1, hn2, hc⟩ | ⟨hn, hc⟩
    · rw [← hr0] at hc; exact absurd hle (not_le.mpr hc)
    · have hj := heq (hr0.trans hc.symm)
      rw [hc] at n1
      unfold tauG; rw [if_neg (by omega), if_pos hn2]; omega
    · unfold tauG; rw [if_neg (by omega), if_neg (by omega)]; have := n.isLt; omega
  · unfold basN basG
    by_cases hn0 : cF hd n = inf
    · rw [if_pos hn0, PtotG, mul_comm,
        ← Finset.mul_prod_erase _ _ (mem_filter.mpr ⟨mem_univ (cF hd r), hr0⟩), ← mul_assoc,
        mul_comm, ← mul_assoc, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_neg (by omega)]
    · rw [if_neg hn0]
      rcases lt_or_eq_of_le hle with hlt | he
      · rw [NfacG, ← Finset.mul_prod_erase _ _ (mem_filter.mpr ⟨mem_univ (cF hd r), hr0, hlt⟩),
          mul_assoc, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_neg (by omega)]
      · have hj := heq he
        rw [← he, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_neg (by omega)]

lemma BP_diagG [Nontrivial R] (hd : ∑ c, d c = m) (n : Fin m) :
    (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d * PmG inf x hd) n n =
      if cF hd n = inf then 1 else (NfacG inf x d (cF hd n)).eval (x (cF hd n)) := by
  rw [BP_entryG inf x hd]
  by_cases h0 : cF hd n = inf
  · rw [if_pos h0, if_pos h0]
    have hdeg := natDegree_basN inf x hd n
    obtain ⟨n1, n2⟩ := cF_spec hd n
    rw [h0] at n1 n2
    have : tauG inf hd n = m - 1 - Z3NetU.Proofs.jN d n := by
      unfold tauG; rw [if_neg (by omega), if_pos (by omega)]; omega
    rw [show m - 1 - Z3NetU.Proofs.jN d n = (basN inf x hd n).natDegree by rw [hdeg, this]]
    exact (monic_basG inf x d _ _).coeff_natDegree
  · rw [if_neg h0, if_neg h0]
    unfold basN basG
    rw [if_neg h0, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self,
      taylor_coeff_zero]

/-! ### `det P = ±1` -/

lemma det_PmG [Nontrivial R] (hd : ∑ c, d c = m) :
    (PmG inf x hd).det = 1 ∨ (PmG inf x hd).det = -1 := by
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective (fun n => ⟨tauG inf hd n, tauG_lt inf hd n⟩)
    (Finite.injective_iff_bijective.mp fun a b h => tauG_inj inf hd a b (congrArg Fin.val h))
  have hτ : ∀ n, ((τ n : Fin m) : ℕ) = tauG inf hd n := fun n => rfl
  set U : Matrix (Fin m) (Fin m) R := fun l e => (basN inf x hd (τ.symm e)).coeff l with hU
  have hPU : PmG inf x hd = U.submatrix id τ := by
    ext l n
    show (basN inf x hd n).coeff l = (basN inf x hd (τ.symm (τ n))).coeff l
    rw [Equiv.symm_apply_apply]
  have hdegU : ∀ e : Fin m, (basN inf x hd (τ.symm e)).natDegree = e := by
    intro e
    rw [natDegree_basN inf x hd, ← hτ, Equiv.apply_symm_apply]
  have hUup : U.IsUpperTriangular := by
    intro i j hij
    simp only [hU]
    apply coeff_eq_zero_of_natDegree_lt
    rw [hdegU]; exact hij
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hUup]
    refine Finset.prod_eq_one fun e _ => ?_
    simp only [hU]
    have := (monic_basG inf x d (cF hd (τ.symm e)) (Z3NetU.Proofs.jN d (τ.symm e))).coeff_natDegree
    rw [← hdegU e]
    exact this
  rw [hPU, Matrix.det_permute', hdetU, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-! ### Assembly -/

lemma fiber_cardG (hd : ∑ c, d c = m) (c : Fin s) :
    (univ.filter (fun n : Fin m => cF hd n = c)).card = d c := by
  rw [← Z3NetU.Proofs.fiber_card hd c]
  congr 1

theorem frame_minor_core (hd : ∑ c, d c = m) :
    (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d).det = ∏ c : Fin s, ∏ c' : Fin s,
        (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (d c' * d c) else 1) ∨
      (Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d).det = -∏ c : Fin s, ∏ c' : Fin s,
        (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (d c' * d c) else 1) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · left; exact Subsingleton.elim _ _
  set B := Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d with hB
  have hlow : (B * PmG inf x hd).IsLowerTriangular := fun i j hij => BP_lowerG inf x hd i j hij
  set g : Fin s → R := fun c => if c = inf then 1 else (NfacG inf x d c).eval (x c) with hg
  have hprod : (B * PmG inf x hd).det = ∏ c : Fin s, g c ^ d c := by
    rw [Matrix.det_of_isLowerTriangular _ hlow]
    have hdiag : ∀ n, (B * PmG inf x hd) n n = g (cF hd n) := fun n => BP_diagG inf x hd n
    simp only [hdiag]
    rw [← Finset.prod_fiberwise univ (cF hd) (fun n => g (cF hd n))]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun n hn => by rw [(mem_filter.mp hn).2]), prod_const,
      fiber_cardG hd c]
  have hV : ∏ c : Fin s, g c ^ d c = ∏ c : Fin s, ∏ c' : Fin s,
      (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (d c' * d c) else 1) := by
    refine Finset.prod_congr rfl fun c _ => ?_
    by_cases hc : c = inf
    · simp only [hg, hc, if_true, one_pow, ne_eq, not_true_eq_false, false_and, and_false,
        if_false, prod_const_one]
    · simp only [hg, if_neg hc, NfacG, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      rw [← Finset.prod_pow, Finset.prod_filter]
      refine Finset.prod_congr rfl fun c' _ => ?_
      by_cases h : c' ≠ inf ∧ c' < c
      · rw [if_pos h, if_pos ⟨h.2, hc, h.1⟩, ← pow_mul]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.2, h'.1⟩)]
  have hmul : B.det * (PmG inf x hd).det = ∏ c : Fin s, ∏ c' : Fin s,
      (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (d c' * d c) else 1) := by
    rw [← Matrix.det_mul, hprod, hV]
  rcases det_PmG inf x hd with h | h
  · left; rw [← hmul, h, mul_one]
  · right; rw [← hmul, h]; ring

end frame

end

end Z3NetF.Proofs
