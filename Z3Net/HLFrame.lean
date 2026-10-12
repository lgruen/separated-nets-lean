module
public import Mathlib
public import Z3Net.HLDefs
public import Z3Net.SUFrame

@[expose] public section

/-!
# Entry HL, part 1: the split frame and Lemma T′ (exact confluent-Vandermonde box minors)

* `boxLoc_eq`, `boxMatrix_eq`: the entry-HL copies of `boxLoc`/`boxMatrix` agree with entry U's,
  so the row-location lemmas of `Z3Net/SUFrame.lean` apply.
* `split_reading`: row `i` of `splitGen` applied to the coefficients of `P` (degree `< m`) is the
  Taylor coefficient of `P` at `v_c` (`i < k`) resp. at `u_c` (index `i - k`).
* `HL_frameMinor`: multiply the box matrix `B` on the right by the matrix `P` of the Newton-type
  basis `bas n` indexed like the rows: column `(c, i)` is `N_c (t - v_c)^i` (`i < k`) resp.
  `N_c (t - v_c)^k (t - u_c)^(i-k)` (`i ≥ k`) with
  `N_c = ∏_{c' < c} (t - v_c')^(min(d_c',k)) (t - u_c')^(d_c'-k)`. The columns of `P` are monic of
  degree `n`, so `det P = 1`, and `B P` is lower triangular with diagonal `N_c(v_c)` resp.
  `N_c(u_c) (u_c - v_c)^k`.
-/

namespace Z3NetHL.Proofs

open Polynomial Finset Matrix

noncomputable section

/-! ## Bridges to entry U -/

lemma boxLoc_eq : ∀ (ds : List ℕ) (c r : ℕ), Z3NetHL.boxLoc ds c r = Z3NetU.boxLoc ds c r
  | [], _, _ => rfl
  | x :: xs, c, r => by simp only [Z3NetHL.boxLoc, Z3NetU.boxLoc, boxLoc_eq xs]

lemma boxMatrix_eq {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) : Z3NetHL.boxMatrix C d = Z3NetU.boxMatrix C d := by
  funext r l
  simp only [Z3NetHL.boxMatrix, Z3NetU.boxMatrix, boxLoc_eq]

/-! ## Readings of the split frame -/

lemma coeff_taylor_eq (r : ℤ) (m : ℕ) (P : ℤ[X]) (hP : P.natDegree < m) (i : ℕ) :
    (taylor r P).coeff i = ∑ l : Fin m, (((l : ℕ).choose i : ℕ) : ℤ) * r ^ ((l : ℕ) - i) * P.coeff l := by
  have hP' : P = Z3NetU.Proofs.pv (fun l : Fin m => P.coeff l) := (Z3NetU.Proofs.pv_coeff P hP).symm
  conv_lhs => rw [hP']
  rw [Z3NetU.Proofs.pv, map_sum, finset_sum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
  ring

lemma split_reading {s : ℕ} (m k : ℕ) (u v : Fin s → ℤ) (c : Fin s) (P : ℤ[X])
    (hP : P.natDegree < m) (i : Fin m) :
    ∑ l : Fin m, splitGen m k u v c i l * P.coeff l =
      if (i : ℕ) < k then (taylor (v c) P).coeff i else (taylor (u c) P).coeff ((i : ℕ) - k) := by
  simp only [splitGen]
  split_ifs with h
  · rw [coeff_taylor_eq _ m P hP]
  · rw [coeff_taylor_eq _ m P hP]

/-! ## The Newton-type basis -/

section basis

variable {s m : ℕ} (k : ℕ) (u v : Fin s → ℤ) (d : Fin s → ℕ)

/-- `N_c = ∏_{c' < c} (t - v_c')^(min(d_c',k)) (t - u_c')^(d_c'-k)`. -/
def Nf (c : ℕ) : ℤ[X] :=
  ∏ t ∈ univ.filter (fun t : Fin s => (t : ℕ) < c),
    (X - C (v t)) ^ min (d t) k * (X - C (u t)) ^ (d t - k)

/-- The basis polynomial of index `(c, i)`. -/
def basS (c i : ℕ) : ℤ[X] :=
  if h : c < s then
    (if i < k then Nf k u v d c * (X - C (v ⟨c, h⟩)) ^ i
     else Nf k u v d c * (X - C (v ⟨c, h⟩)) ^ k * (X - C (u ⟨c, h⟩)) ^ (i - k))
  else 1

lemma monic_Nf (c : ℕ) : (Nf k u v d c).Monic :=
  monic_prod_of_monic _ _ fun _ _ => ((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)

lemma natDegree_Nf (c : ℕ) : (Nf k u v d c).natDegree = Z3NetU.Proofs.pre d c := by
  rw [Nf, natDegree_prod_of_monic _ _ (fun _ _ => ((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)),
    Z3NetU.Proofs.pre_eq_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [((monic_X_sub_C _).pow _).natDegree_mul ((monic_X_sub_C _).pow _),
    (monic_X_sub_C _).natDegree_pow, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C,
    natDegree_X_sub_C]
  omega

lemma monic_basS (c i : ℕ) : (basS k u v d c i).Monic := by
  unfold basS
  split_ifs
  · exact (monic_Nf k u v d c).mul ((monic_X_sub_C _).pow _)
  · exact ((monic_Nf k u v d c).mul ((monic_X_sub_C _).pow _)).mul ((monic_X_sub_C _).pow _)
  · exact monic_one

lemma natDegree_basS (c i : ℕ) (hc : c < s) :
    (basS k u v d c i).natDegree = Z3NetU.Proofs.pre d c + i := by
  unfold basS
  rw [dif_pos hc]
  split_ifs with hi
  · rw [(monic_Nf k u v d c).natDegree_mul ((monic_X_sub_C _).pow _), natDegree_Nf,
      (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  · rw [((monic_Nf k u v d c).mul ((monic_X_sub_C _).pow _)).natDegree_mul ((monic_X_sub_C _).pow _),
      (monic_Nf k u v d c).natDegree_mul ((monic_X_sub_C _).pow _), natDegree_Nf,
      (monic_X_sub_C _).natDegree_pow, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C,
      natDegree_X_sub_C]
    omega

/-- An earlier coordinate's points divide `N_c` to the right orders. -/
lemma Nf_eq_mul (c : ℕ) (t : Fin s) (ht : (t : ℕ) < c) :
    Nf k u v d c = (X - C (v t)) ^ min (d t) k * ((X - C (u t)) ^ (d t - k) *
      ∏ t' ∈ (univ.filter (fun t : Fin s => (t : ℕ) < c)).erase t,
        (X - C (v t')) ^ min (d t') k * (X - C (u t')) ^ (d t' - k)) := by
  have hmem : t ∈ univ.filter (fun t : Fin s => (t : ℕ) < c) := by simp [ht]
  rw [Nf, ← Finset.mul_prod_erase _ _ hmem, mul_assoc]

lemma Nf_eq_mul' (c : ℕ) (t : Fin s) (ht : (t : ℕ) < c) :
    Nf k u v d c = (X - C (u t)) ^ (d t - k) * ((X - C (v t)) ^ min (d t) k *
      ∏ t' ∈ (univ.filter (fun t : Fin s => (t : ℕ) < c)).erase t,
        (X - C (v t')) ^ min (d t') k * (X - C (u t')) ^ (d t' - k)) := by
  rw [Nf_eq_mul k u v d c t ht]; ring

lemma Nf_eval (c : ℕ) (x : ℤ) :
    (Nf k u v d c).eval x = ∏ t ∈ univ.filter (fun t : Fin s => (t : ℕ) < c),
      (x - v t) ^ min (d t) k * (x - u t) ^ (d t - k) := by
  simp [Nf, eval_prod]

end basis

/-! ## Rows and columns -/

section matrices

variable {s m : ℕ} (k : ℕ) (u v : Fin s → ℤ) (d : Fin s → ℕ)

open Z3NetU.Proofs in
/-- The basis polynomial of column `n`. -/
def basN (n : Fin m) : ℤ[X] := basS k u v d (cN d n) (jN d n)

/-- The basis matrix `P` (column `n` = coefficients of `basN n`). -/
def PmS : Matrix (Fin m) (Fin m) ℤ := fun l n => (basN k u v d n).coeff l

variable {k u v d}

open Z3NetU.Proofs in
lemma natDegree_basN (hd : ∑ c, d c = m) (n : Fin m) : (basN k u v d n).natDegree = n := by
  obtain ⟨h1, h2, _⟩ := loc hd n
  rw [basN, natDegree_basS k u v d _ _ h1, ← h2]

lemma natDegree_basN_lt (hd : ∑ c, d c = m) (n : Fin m) : (basN k u v d n).natDegree < m := by
  rw [natDegree_basN hd]; exact n.isLt

open Z3NetU.Proofs in
lemma BP_entry (hd : ∑ c, d c = m) (r n : Fin m) :
    ((Z3NetHL.boxMatrix (splitGen m k u v) d * PmS k u v d : Matrix (Fin m) (Fin m) ℤ)) r n =
      if jN d r < k then (taylor (v ⟨cN d r, (loc hd r).1⟩) (basN k u v d n)).coeff (jN d r)
      else (taylor (u ⟨cN d r, (loc hd r).1⟩) (basN k u v d n)).coeff (jN d r - k) := by
  obtain ⟨h1, h2, h3⟩ := loc hd r
  have hj : jN d r < m := by omega
  rw [Matrix.mul_apply, boxMatrix_eq]
  have hrow : ∀ l, Z3NetU.boxMatrix (splitGen m k u v) d r l =
      splitGen m k u v (⟨cN d r, h1⟩ : Fin s) ⟨jN d r, hj⟩ l := by
    intro l
    simp only [Z3NetU.boxMatrix]
    rw [dif_pos ⟨h1, hj⟩]; rfl
  simp only [hrow, PmS]
  rw [split_reading m k u v _ _ (natDegree_basN_lt hd n) ⟨jN d r, hj⟩]

lemma basS_eq_Nf_mul (c i : ℕ) (hc : c < s) : ∃ T : ℤ[X], basS k u v d c i = Nf k u v d c * T := by
  unfold basS
  rw [dif_pos hc]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, mul_assoc _ _ _⟩

lemma basS_v_factor (c i : ℕ) (hc : c < s) (t : Fin s) (ht : (t : ℕ) < c) :
    ∃ G : ℤ[X], basS k u v d c i = (X - C (v t)) ^ min (d t) k * G := by
  obtain ⟨T, hT⟩ := basS_eq_Nf_mul (k := k) (u := u) (v := v) (d := d) c i hc
  rw [hT, Nf_eq_mul k u v d c t ht, mul_assoc]
  exact ⟨_, rfl⟩

lemma basS_u_factor (c i : ℕ) (hc : c < s) (t : Fin s) (ht : (t : ℕ) < c) :
    ∃ G : ℤ[X], basS k u v d c i = (X - C (u t)) ^ (d t - k) * G := by
  obtain ⟨T, hT⟩ := basS_eq_Nf_mul (k := k) (u := u) (v := v) (d := d) c i hc
  rw [hT, Nf_eq_mul' k u v d c t ht, mul_assoc]
  exact ⟨_, rfl⟩

lemma basS_self_v (c i : ℕ) (hc : c < s) :
    ∃ G : ℤ[X], basS k u v d c i = (X - C (v ⟨c, hc⟩)) ^ min i k * G := by
  unfold basS
  rw [dif_pos hc]
  split_ifs with hi
  · exact ⟨Nf k u v d c, by rw [min_eq_left hi.le]; ring⟩
  · exact ⟨Nf k u v d c * (X - C (u ⟨c, hc⟩)) ^ (i - k), by rw [min_eq_right (by omega)]; ring⟩

lemma basS_self_u (c i : ℕ) (hc : c < s) (hi : k ≤ i) :
    basS k u v d c i = (X - C (u ⟨c, hc⟩)) ^ (i - k) * (Nf k u v d c * (X - C (v ⟨c, hc⟩)) ^ k) := by
  unfold basS
  rw [dif_pos hc, if_neg (by omega)]; ring

open Z3NetU.Proofs in
lemma BP_lower (hd : ∑ c, d c = m) (r n : Fin m) (h : r < n) :
    ((Z3NetHL.boxMatrix (splitGen m k u v) d * PmS k u v d : Matrix (Fin m) (Fin m) ℤ)) r n = 0 := by
  rw [BP_entry hd]
  obtain ⟨hle, heq⟩ := cN_le_of_lt hd r n h
  obtain ⟨r1, r2, r3⟩ := loc hd r
  obtain ⟨n1, n2, n3⟩ := loc hd n
  have hbas : basN k u v d n = basS k u v d (cN d n) (jN d n) := rfl
  rw [hbas]
  rcases Nat.lt_or_ge (cN d r) (cN d n) with hlt | hge
  · split_ifs with hj
    · obtain ⟨G, hG⟩ := basS_v_factor (k := k) (u := u) (v := v) (d := d) (cN d n) (jN d n) n1
        ⟨cN d r, r1⟩ hlt
      rw [hG, coeff_taylor_X_sub_C_pow_mul, if_neg]
      have : jN d r < min (d ⟨cN d r, r1⟩) k := lt_min r3 hj
      omega
    · obtain ⟨G, hG⟩ := basS_u_factor (k := k) (u := u) (v := v) (d := d) (cN d n) (jN d n) n1
        ⟨cN d r, r1⟩ hlt
      rw [hG, coeff_taylor_X_sub_C_pow_mul, if_neg]
      omega
  · have he : cN d r = cN d n := le_antisymm hle hge
    have hj := heq he
    have r1' : cN d n < s := n1
    have hfin : (⟨cN d r, r1⟩ : Fin s) = ⟨cN d n, n1⟩ := Fin.ext he
    split_ifs with hjk
    · obtain ⟨G, hG⟩ := basS_self_v (k := k) (u := u) (v := v) (d := d) (cN d n) (jN d n) n1
      rw [hfin, hG, coeff_taylor_X_sub_C_pow_mul, if_neg]
      have : jN d r < min (jN d n) k := lt_min hj hjk
      omega
    · rw [hfin, basS_self_u (k := k) (u := u) (v := v) (d := d) (cN d n) (jN d n) n1 (by omega),
        coeff_taylor_X_sub_C_pow_mul, if_neg]
      omega

open Z3NetU.Proofs in
lemma BP_diag (hd : ∑ c, d c = m) (n : Fin m) :
    ((Z3NetHL.boxMatrix (splitGen m k u v) d * PmS k u v d : Matrix (Fin m) (Fin m) ℤ)) n n =
      if jN d n < k then (Nf k u v d (cN d n)).eval (v ⟨cN d n, (loc hd n).1⟩)
      else (Nf k u v d (cN d n)).eval (u ⟨cN d n, (loc hd n).1⟩) *
        (u ⟨cN d n, (loc hd n).1⟩ - v ⟨cN d n, (loc hd n).1⟩) ^ k := by
  rw [BP_entry hd]
  obtain ⟨n1, n2, n3⟩ := loc hd n
  have hbas : basN k u v d n = basS k u v d (cN d n) (jN d n) := rfl
  rw [hbas]
  split_ifs with hjk
  · unfold basS
    rw [dif_pos n1, if_pos hjk, mul_comm, coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self,
      taylor_coeff_zero]
  · rw [basS_self_u (k := k) (u := u) (v := v) (d := d) (cN d n) (jN d n) n1 (by omega),
      coeff_taylor_X_sub_C_pow_mul, if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
    simp

/-! ## `det P = 1` -/

lemma det_PmS (hd : ∑ c, d c = m) : (PmS k u v d : Matrix (Fin m) (Fin m) ℤ).det = 1 := by
  have hup : (PmS k u v d : Matrix (Fin m) (Fin m) ℤ).IsUpperTriangular := by
    intro i j hij
    simp only [PmS]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_basN hd]; exact hij
  rw [Matrix.det_of_isUpperTriangular hup]
  refine Finset.prod_eq_one fun e _ => ?_
  simp only [PmS]
  have := (monic_basS k u v d (Z3NetU.Proofs.cN d e) (Z3NetU.Proofs.jN d e)).coeff_natDegree
  rw [← natDegree_basN hd e]
  exact this

/-! ## Assembly -/

open Z3NetU.Proofs in
lemma prod_fiber (hd : ∑ c, d c = m) (c : Fin s) (f : ℕ → ℤ) :
    ∏ n ∈ univ.filter (fun n : Fin m => cN d n = c), f (jN d n) = ∏ j ∈ range (d c), f j := by
  apply Finset.prod_bij (fun n _ => jN d n)
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
  · intro j hj
    rw [mem_range] at hj
    have hps := pre_succ d c
    have hle : pre d (c + 1) ≤ m := by rw [← hd]; exact pre_le_sum d _
    have hlt : pre d c + j < m := by omega
    have hloc := boxLoc_spec (List.ofFn d) 0 c j (by simp) (by simpa using hj)
    refine ⟨⟨pre d c + j, hlt⟩, ?_, ?_⟩
    · rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
      show cN d ⟨pre d c + j, hlt⟩ = c
      simp only [cN]; unfold pre at hloc ⊢; rw [hloc]; simp
    · show jN d ⟨pre d c + j, hlt⟩ = j
      simp only [jN]; unfold pre at hloc ⊢; rw [hloc]
  · intro _ _; rfl

lemma prod_range_ite (D k : ℕ) (A B : ℤ) :
    ∏ j ∈ range D, (if j < k then A else B) = A ^ min D k * B ^ (D - k) := by
  rw [Finset.prod_ite, prod_const, prod_const]
  congr 2
  · have : (range D).filter (fun j => j < k) = range (min D k) := by
      ext j; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  · have : (range D).filter (fun j => ¬ j < k) = Ico k D := by
      ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [this, Nat.card_Ico]

/-- Determinant of `B` as a product over the coordinates. -/
lemma det_box_coord (hd : ∑ c, d c = m) :
    (Z3NetHL.boxMatrix (splitGen m k u v) d).det =
      ∏ c : Fin s, (Nf k u v d c).eval (v c) ^ min (d c) k *
        ((Nf k u v d c).eval (u c) * (u c - v c) ^ k) ^ (d c - k) := by
  set B := Z3NetHL.boxMatrix (splitGen m k u v) d with hB
  have hlow : (B * PmS k u v d : Matrix (Fin m) (Fin m) ℤ).IsLowerTriangular := by
    intro i j hij
    exact BP_lower hd i j hij
  have hmul : B.det = (B * PmS k u v d : Matrix (Fin m) (Fin m) ℤ).det := by
    rw [Matrix.det_mul, det_PmS hd, mul_one]
  rw [hmul, Matrix.det_of_isLowerTriangular _ hlow]
  let cF : Fin m → Fin s := fun n => ⟨Z3NetU.Proofs.cN d n, (Z3NetU.Proofs.loc hd n).1⟩
  set g : Fin s → ℕ → ℤ := fun c j => if j < k then (Nf k u v d c).eval (v c)
    else (Nf k u v d c).eval (u c) * (u c - v c) ^ k with hg
  have hdiag : ∀ n, (B * PmS k u v d : Matrix (Fin m) (Fin m) ℤ) n n = g (cF n) (Z3NetU.Proofs.jN d n) := by
    intro n; rw [hB, BP_diag hd]
  simp only [hdiag]
  rw [← Finset.prod_fiberwise univ cF (fun n => g (cF n) (Z3NetU.Proofs.jN d n))]
  refine Finset.prod_congr rfl fun c _ => ?_
  have h1 : ∏ n ∈ univ.filter (fun n => cF n = c), g (cF n) (Z3NetU.Proofs.jN d n) =
      ∏ n ∈ univ.filter (fun n : Fin m => Z3NetU.Proofs.cN d n = c), g c (Z3NetU.Proofs.jN d n) := by
    apply Finset.prod_congr
    · ext n; simp [cF, Fin.ext_iff]
    · intro n hn
      rw [mem_filter] at hn
      have : cF n = c := Fin.ext hn.2
      rw [this]
  rw [h1, prod_fiber hd c (g c)]
  simp only [hg]
  rw [prod_range_ite]

end matrices

/-! ## Lemma T′ -/

lemma prod_two_level {s : ℕ} (c : Fin s) (e : Fin 2) (G : Fin s → Fin 2 → ℤ) :
    ∏ c' : Fin s, ∏ e' : Fin 2, (if c' < c ∨ (c' = c ∧ e' < e) then G c' e' else 1) =
      (∏ c' : Fin s, if c' < c then ∏ e' : Fin 2, G c' e' else 1) *
        ∏ e' : Fin 2, (if e' < e then G c e' else 1) := by
  have h : ∀ c' : Fin s, ∀ e' : Fin 2, (if c' < c ∨ (c' = c ∧ e' < e) then G c' e' else 1) =
      (if c' < c then G c' e' else 1) * (if c' = c ∧ e' < e then G c' e' else 1) := by
    intro c' e'
    by_cases h1 : c' < c
    · have : ¬ (c' = c ∧ e' < e) := fun h => (lt_irrefl c) (h.1 ▸ h1)
      simp [h1, this]
    · by_cases h2 : c' = c ∧ e' < e
      · simp [h1, h2]
      · simp [h1, h2]
  simp_rw [h, Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun c' _ => ?_
    split_ifs <;> simp
  · rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun e' _ => ?_
    by_cases he : e' < e
    · simp only [he, and_true]
      rw [Finset.prod_ite_eq']
      simp
    · simp [he]

theorem HL_frameMinor (s m k : ℕ) (u v : Fin s → ℤ) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (Z3NetHL.boxMatrix (splitGen m k u v) d).det =
      ∏ c : Fin s, ∏ e : Fin 2, ∏ c' : Fin s, ∏ e' : Fin 2,
        (if c' < c ∨ (c' = c ∧ e' < e) then
          (splitPt u v c e - splitPt u v c' e') ^ (splitMult k d c' e' * splitMult k d c e)
        else 1) := by
  rw [det_box_coord hd]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_two, prod_two_level, prod_two_level]
  have hN : ∀ x : ℤ, ∀ μ : ℕ, (∏ c' : Fin s, if c' < c then ∏ e' : Fin 2,
      (x - splitPt u v c' e') ^ (splitMult k d c' e' * μ) else 1) = (Nf k u v d c).eval x ^ μ := by
    intro x μ
    rw [Nf_eval, ← Finset.prod_pow, Finset.prod_filter]
    refine Finset.prod_congr rfl fun c' _ => ?_
    have hlt : ((c' : ℕ) < (c : ℕ)) ↔ c' < c := Fin.lt_def.symm
    by_cases h : c' < c
    · rw [if_pos h, if_pos (hlt.mpr h), Fin.prod_univ_two]
      simp only [splitPt, splitMult, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero,
        if_false]
      rw [mul_pow, ← pow_mul, ← pow_mul]
    · rw [if_neg h, if_neg (fun h' => h (hlt.mp h'))]
  have e0 : splitPt u v c 0 = v c := by simp [splitPt]
  have e1 : splitPt u v c 1 = u c := by simp [splitPt]
  have m0 : splitMult k d c 0 = min (d c) k := by simp [splitMult]
  have m1 : splitMult k d c 1 = d c - k := by simp [splitMult]
  simp only [e0, e1, m0, m1] at hN ⊢
  rw [show (∏ c' : Fin s, if c' < c then ∏ e' : Fin 2,
      (v c - splitPt u v c' e') ^ (splitMult k d c' e' * min (d c) k) else 1) = _ from hN (v c) _,
    show (∏ c' : Fin s, if c' < c then ∏ e' : Fin 2,
      (u c - splitPt u v c' e') ^ (splitMult k d c' e' * (d c - k)) else 1) = _ from hN (u c) _]
  simp only [Fin.prod_univ_two, Fin.isValue, lt_self_iff_false, if_false, mul_one,
    Fin.zero_lt_one, if_true, e0, m0, Nat.not_lt_zero]
  have h10 : ¬ ((1 : Fin 2) < 0) := by decide
  rw [if_neg h10, mul_one, mul_one, mul_pow, ← pow_mul]
  by_cases hdk : d c ≤ k
  · rw [Nat.sub_eq_zero_of_le hdk]; simp
  · rw [min_eq_right (by omega)]

end

end Z3NetHL.Proofs
