module
public import Mathlib
public import Z3Net.SUNet

@[expose] public section

/-!
# Entry U, part 5: the first offset row is the design, for every `k` (hypothesis (H1))

* `propN`: Lemma R_s / Proposition N_s in the `E`-basis: `Q_c^(-k) Ψ_cd[0, j] = w_cd y_cd^(k-1-j)`,
  proved by evaluating the cofactor of `(t - a_c)^k` in `E_{d,j}` at `a_c` (finite `c`) resp. by
  the degree of `E_{d,j}` (`c = ∞`).
* `propG`: `w y^n = ∑_{i<s-1} γ_{n,i} w y^i` at every node `y = y_cd` (the remainder of `X^n`
  modulo `∏_{c ≠ d} (X - y_cd)`, computed by `rootsPoly`/`xpowRem`).
* `design_eq`: the design entries are `λ'_c ∑_{n' ≤ n} w y^(n') U'_d[n', n]` (Proposition F; the
  `∞` column via the falling factorial `∑ stir n i a^i = a(a-1)⋯(a-n+1)`).
* `row0`: `Φ'_cd[0, j] = F_{k-1-j}[c][d]` for all `c, d`, `k ≥ 1`.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

variable {R : Type*} [CommRing R] {iv : ℕ → R}

/-! ## Proposition N_s -/

lemma Qinv_eq {s : ℕ} (k : ℕ) (c : Fin s) (hc : (c : ℕ) ≠ 0) :
    Qinv iv k c = ∏ b ∈ univ.erase c, (if (b : ℕ) = 0 then 1 else ivz iv ((c : ℤ) - b)) ^ k := by
  rw [Qinv, if_neg hc, ← Finset.prod_pow, Finset.prod_filter,
    ← Finset.mul_prod_erase _ _ (mem_univ c), if_neg (by simp), one_mul]
  refine prod_congr rfl fun b hb => ?_
  have hbc : b ≠ c := Finset.ne_of_mem_erase hb
  by_cases hb0 : (b : ℕ) = 0
  · simp [hb0]
  · simp [hb0, hbc]

lemma place_sub {s : ℕ} (c b : Fin s) :
    ((place c : ℤ) : R) - ((place b : ℤ) : R) = (((c : ℤ) - b : ℤ) : R) := by
  simp [place]

/-- **Proposition N_s** in the `E`-basis. -/
theorem propN {s : ℕ} (hs : 3 ≤ s) (h : IvOK iv (s - 2)) (k : ℕ) (c d : Fin s) (hcd : c ≠ d)
    (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    Qinv iv k c * (Psi k c d r j : R) = wN iv c d * yN iv c d ^ (k - 1 - (j : ℕ)) := by
  have hs2 : 2 ≤ s := by omega
  have hj := j.isLt
  rw [← Fr_E_off k c d j r]
  have hidx : (⟨k + (r : ℕ), sk_sub_add r⟩ : Fin (s * k)) = ⟨k, by have := sk_sub_add r; omega⟩ := by
    ext; simp [hr]
  rw [hidx]
  by_cases hc : (c : ℕ) = 0
  · have hd : (d : ℕ) ≠ 0 := fun h' => hcd (Fin.ext (by rw [hc, h']))
    rw [Fr_E_inf hs2 k c d j j.isLt hc]
    simp only [Qinv, wN, yN, if_pos hc, true_or, if_true, one_mul]
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    have hdeg := natDegree_EPoly (R := R) k d j
    rw [Esum_fin hs2 k d hd j] at hdeg
    have e2 : (s - 2) * k + k = (s - 1) * k := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
      simp only [Nat.add_sub_cancel, show t + 2 - 1 = t + 1 by omega]; ring
    have e1 := sk_eq hs2 k
    by_cases hjk : (j : ℕ) + 1 = k
    · rw [show s * k - 1 - k = (EPoly R k d j).natDegree by rw [hdeg]; omega,
        (EPoly_monic k d j).coeff_natDegree, show k - 1 - (j : ℕ) = 0 by omega, pow_zero]
      simp [hc]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega),
        zero_pow (by omega)]
      simp
  · rw [Fr_E_fin hs2 k c d j j.isLt hc]
    simp only
    rw [taylor_EPoly_fin k c d j hc, Eexp_ne k c d j hc hcd, if_pos le_rfl, Nat.sub_self,
      taylor_coeff_zero, Rest_eval, Qinv_eq k c hc, ← Finset.prod_mul_distrib]
    have hc0 : c0 (by omega : 0 < s) ∈ univ.erase c := by
      rw [mem_erase]; exact ⟨fun h' => hc (by rw [← h']; rfl), mem_univ _⟩
    have hfin : ∀ b : Fin s, (b : ℕ) ≠ 0 → b ≠ c →
        (if (b : ℕ) = 0 then 1 else ivz iv ((c : ℤ) - b)) ^ k *
          (((place c : ℤ) : R) - ((Eroot b : ℤ) : R)) ^ Eexp k d b j =
        ivz iv ((c : ℤ) - b) ^ k * (((c : ℤ) - b : ℤ) : R) ^ (if b = d then (j : ℕ) else k) := by
      intro b hb0 hbc
      rw [if_neg hb0, Eroot_fin b hb0, place_sub, Eexp_fin k d b j hb0]
    by_cases hd : (d : ℕ) = 0
    · rw [Finset.prod_eq_single_of_mem _ hc0]
      · simp only [c0, if_pos rfl, one_pow, one_mul, Eroot, Eexp, hd, if_true, Int.cast_zero,
          sub_zero, wN, yN, hc, or_true, if_false]
      · intro b hb hb0
        have hb0' : (b : ℕ) ≠ 0 := fun h' => hb0 (Fin.ext h')
        have hbd : b ≠ d := fun h' => hb0' (by rw [h']; exact hd)
        rw [hfin b hb0' (Finset.ne_of_mem_erase hb), if_neg hbd, ← mul_pow,
          mul_comm, ivz_mul h _ (diff_small c b hc hb0' (Ne.symm (Finset.ne_of_mem_erase hb))).1
            (diff_small c b hc hb0' (Ne.symm (Finset.ne_of_mem_erase hb))).2, one_pow]
    · have hdm : d ∈ univ.erase c := by rw [mem_erase]; exact ⟨Ne.symm hcd, mem_univ _⟩
      rw [Finset.prod_eq_single_of_mem _ hdm]
      · rw [hfin d hd (Ne.symm hcd), if_pos rfl]
        simp only [wN, yN, hc, hd, or_self, if_false]
        obtain ⟨h1, h2⟩ := diff_small c d hc hd hcd
        have hzu := ivz_mul h _ h1 h2
        set z := ivz iv ((c : ℤ) - d)
        set u : R := (((c : ℤ) - d : ℤ) : R)
        obtain ⟨t, ht⟩ : ∃ t, k = (j : ℕ) + t + 1 := ⟨k - 1 - j, by omega⟩
        rw [show k - 1 - (j : ℕ) = t by omega, show z ^ k = z ^ ((j : ℕ) + t + 1) by rw [← ht]]
        calc z ^ ((j : ℕ) + t + 1) * u ^ (j : ℕ) = (u * z) ^ (j : ℕ) * (z * z ^ t) := by ring
          _ = z * z ^ t := by rw [hzu, one_pow, one_mul]
      · intro b hb hbd
        by_cases hb0 : (b : ℕ) = 0
        · have : Eexp k d b j = 0 := by simp [Eexp, hb0, hd]
          rw [this, pow_zero, mul_one, if_pos hb0, one_pow]
        · rw [hfin b hb0 (Finset.ne_of_mem_erase hb), if_neg hbd, ← mul_pow,
            mul_comm, ivz_mul h _ (diff_small c b hc hb0 (Ne.symm (Finset.ne_of_mem_erase hb))).1
              (diff_small c b hc hb0 (Ne.symm (Finset.ne_of_mem_erase hb))).2, one_pow]

/-! ## Proposition G_s: the Lagrange remainder -/

lemma rootsPoly_gt : ∀ (ys : List R) (i : ℕ), ys.length < i → rootsPoly ys i = 0
  | [], i, h => by simp [rootsPoly]; omega
  | y :: ys, i, h => by
    simp only [rootsPoly, List.length_cons] at h ⊢
    rw [if_neg (by omega), rootsPoly_gt ys (i - 1) (by omega), rootsPoly_gt ys i (by omega)]
    simp

lemma rootsPoly_top : ∀ ys : List R, rootsPoly ys ys.length = 1
  | [] => by simp [rootsPoly]
  | y :: ys => by
    simp only [rootsPoly, List.length_cons]
    rw [if_neg (by omega), Nat.add_sub_cancel, rootsPoly_top ys, rootsPoly_gt ys _ (by omega)]
    simp

lemma rootsPoly_eval : ∀ (ys : List R) (y : R),
    ∑ i ∈ range (ys.length + 1), rootsPoly ys i * y ^ i = (ys.map (fun y' => y - y')).prod
  | [], y => by simp [rootsPoly]
  | y0 :: ys, y => by
    have ih := rootsPoly_eval ys y
    simp only [List.length_cons, List.map_cons, List.prod_cons]
    rw [← ih]
    simp only [rootsPoly, sub_mul, Finset.sum_sub_distrib]
    have hA : ∑ i ∈ range (ys.length + 1 + 1), (if i = 0 then (0 : R) else rootsPoly ys (i - 1)) * y ^ i
        = y * ∑ i ∈ range (ys.length + 1), rootsPoly ys i * y ^ i := by
      rw [Finset.sum_range_succ' (fun i => (if i = 0 then (0 : R) else rootsPoly ys (i - 1)) * y ^ i),
        Finset.mul_sum]
      simp only [if_true, zero_mul, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    have hB : ∑ i ∈ range (ys.length + 1 + 1), y0 * rootsPoly ys i * y ^ i
        = y0 * ∑ i ∈ range (ys.length + 1), rootsPoly ys i * y ^ i := by
      rw [Finset.sum_range_succ, rootsPoly_gt ys _ (by omega), Finset.mul_sum]
      simp only [mul_zero, zero_mul, add_zero]
      try exact Finset.sum_congr rfl fun i _ => by ring
    rw [hA, hB]
    try ring

lemma xpowRem_eval (p : ℕ → R) (r : ℕ) (hr : 1 ≤ r) (y : R)
    (hp : ∑ i ∈ range r, p i * y ^ i + y ^ r = 0) :
    ∀ n, ∑ i ∈ range r, xpowRem p r n i * y ^ i = y ^ n
  | 0 => by
    simp only [xpowRem]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, zero_mul]) (by simp; omega)]
    simp
  | n + 1 => by
    have ih := xpowRem_eval p r hr y hp n
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hA : ∑ i ∈ range (r' + 1), (if i = 0 then (0 : R) else xpowRem p (r' + 1) n (i - 1)) * y ^ i
        = y * ∑ i ∈ range r', xpowRem p (r' + 1) n i * y ^ i := by
      rw [Finset.sum_range_succ' (fun i => (if i = 0 then (0 : R) else xpowRem p (r' + 1) n (i - 1)) * y ^ i),
        Finset.mul_sum]
      simp only [if_true, zero_mul, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    have hB : ∑ i ∈ range (r' + 1), xpowRem p (r' + 1) n (r' + 1 - 1) * p i * y ^ i
        = xpowRem p (r' + 1) n r' * ∑ i ∈ range (r' + 1), p i * y ^ i := by
      rw [Nat.add_sub_cancel, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    simp only [xpowRem, sub_mul, Finset.sum_sub_distrib]
    rw [hA, hB, eq_neg_of_add_eq_zero_left hp]
    rw [Finset.sum_range_succ] at ih
    rw [pow_succ]
    linear_combination y * ih

lemma nodes_length {s : ℕ} (d : Fin s) : (nodes iv d).length = s - 1 := by
  rw [nodes, List.length_map]
  have h1 := List.length_eq_length_filter_add (l := List.finRange s) (fun c => decide (c ≠ d))
  have h2 : ((List.finRange s).filter (fun c => !decide (c ≠ d))).length = 1 := by
    have : (List.finRange s).filter (fun c => !decide (c ≠ d)) =
        (List.finRange s).filter (fun c => c == d) := by
      congr 1; funext c; simp; rfl
    rw [this, ← List.count_eq_length_filter]
    exact List.count_eq_one_of_mem (List.nodup_finRange s) (List.mem_finRange d)
  rw [List.length_finRange] at h1
  omega

/-- The node `y_cd` is a root of `∏_{c' ≠ d} (X - y_c'd)`. -/
lemma node_root {s : ℕ} (c d : Fin s) (hcd : c ≠ d) :
    ∑ i ∈ range (s - 1), rootsPoly (nodes iv d) i * yN iv c d ^ i + yN iv c d ^ (s - 1) = 0 := by
  have h := rootsPoly_eval (nodes iv d) (yN iv c d)
  rw [nodes_length, Finset.sum_range_succ, ← nodes_length (iv := iv) d, rootsPoly_top, one_mul,
    nodes_length] at h
  rw [h]
  apply List.prod_eq_zero
  rw [List.mem_map]
  refine ⟨yN iv c d, ?_, sub_self _⟩
  rw [nodes, List.mem_map]
  exact ⟨c, List.mem_filter.mpr ⟨List.mem_finRange c, by simpa using hcd⟩, rfl⟩

/-- **Proposition G_s** (defining relation of `γ_n`). -/
theorem propG {s : ℕ} (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) (n : ℕ) :
    wN iv c d * yN iv c d ^ n =
      ∑ i ∈ range (s - 1), gam iv d n i * (wN iv c d * yN iv c d ^ i) := by
  have := xpowRem_eval (rootsPoly (nodes iv d)) (s - 1) (by omega) (yN iv c d) (node_root c d hcd) n
  rw [← this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [gam]; ring

/-! ## The design (Proposition F) -/

lemma stir_succ (n i : ℕ) :
    ((stir (n + 1) i : ℤ) : R) = (if i = 0 then 0 else ((stir n (i - 1) : ℤ) : R)) - (n : R) * stir n i := by
  simp only [stir]; split_ifs <;> push_cast <;> ring

lemma stir_poly : ∀ (n : ℕ) (x : R),
    ∑ i ∈ range (n + 1), (stir n i : R) * x ^ i = ∏ i ∈ range n, (x - (i : R))
  | 0, x => by simp [stir]
  | n + 1, x => by
    have ih := stir_poly n x
    rw [Finset.prod_range_succ, ← ih]
    have hA : ∑ i ∈ range (n + 1 + 1), (if i = 0 then 0 else ((stir n (i - 1) : ℤ) : R)) * x ^ i
        = x * ∑ i ∈ range (n + 1), (stir n i : R) * x ^ i := by
      rw [Finset.sum_range_succ' (fun i => (if i = 0 then 0 else ((stir n (i - 1) : ℤ) : R)) * x ^ i),
        Finset.mul_sum]
      simp only [Nat.succ_ne_zero, if_false, if_true, zero_mul, add_zero, Nat.add_sub_cancel]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    have hB : ∑ i ∈ range (n + 1 + 1), (n : R) * stir n i * x ^ i
        = (n : R) * ∑ i ∈ range (n + 1), (stir n i : R) * x ^ i := by
      rw [Finset.sum_range_succ, stir_eq_zero n (n + 1) (by omega), Finset.mul_sum]
      simp only [Int.cast_zero, mul_zero, zero_mul, add_zero]
      exact Finset.sum_congr rfl fun i _ => by ring
    calc ∑ i ∈ range (n + 1 + 1), (stir (n + 1) i : R) * x ^ i
        = ∑ i ∈ range (n + 1 + 1), ((if i = 0 then 0 else ((stir n (i - 1) : ℤ) : R)) * x ^ i -
            (n : R) * stir n i * x ^ i) :=
          Finset.sum_congr rfl fun i _ => by rw [stir_succ]; ring
      _ = _ := by rw [Finset.sum_sub_distrib, hA, hB]; ring

lemma prod_sub_natCast (a n : ℕ) :
    ∏ i ∈ range n, ((a : ℤ) - (i : ℤ)) = (a.descFactorial n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
    by_cases han : n ≤ a
    · push_cast [han]; ring
    · rw [show a.descFactorial n = 0 from Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

lemma lcm_dvd {s : ℕ} (c d : Fin s) (hc : (c : ℕ) ≠ 0) (hd : (d : ℕ) ≠ 0) (hcd : c ≠ d) (n : ℕ)
    (hn : n < s - 1) : ((c : ℤ) - d) ^ (n + 1) ∣ (Lcst s : ℤ) := by
  have hc1 := c.isLt; have hd1 := d.isLt
  have hne : (c : ℕ) ≠ d := fun h => hcd (Fin.ext h)
  set z : ℕ := ((c : ℤ) - d).natAbs with hz
  have hz1 : 1 ≤ z := by omega
  have hz2 : z ≤ s - 2 := by omega
  have h1 : z ∣ (Finset.Icc 1 (s - 2)).lcm id := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hz1, hz2⟩)
  have h2 : z ^ (n + 1) ∣ Lcst s := by
    unfold Lcst
    exact (pow_dvd_pow_of_dvd h1 (n + 1)).trans (pow_dvd_pow _ (by omega))
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast]
  exact h2

/-- **The design is reachable** (Proposition F): `F_n[c][d] = λ'_c ∑_{n' ≤ n} w y^(n') U'_d[n', n]`. -/
theorem design_eq {s : ℕ} (hs : 3 ≤ s) (h : IvOK iv (s - 2)) (c d : Fin s) (hcd : c ≠ d) (n : ℕ)
    (hn : n < s - 1) :
    ((Fdes s n c d : ℤ) : R) = (lamRes c : R) * ∑ n' ∈ range (n + 1),
      wN iv c d * yN iv c d ^ n' * Ures iv d n' n := by
  rw [Fdes, if_neg hcd, Foff, if_neg (by omega)]
  by_cases hc : (c : ℕ) = 0
  · have hd : (d : ℕ) ≠ 0 := fun h' => hcd (Fin.ext (by rw [hc, h']))
    simp only [if_pos hc, lamRes, wN, yN, hc, true_or, Ures, if_neg hd, Int.cast_one, one_mul]
    rw [Finset.sum_eq_single n (fun b hb hbn => by rw [if_neg hbn, mul_zero]) (by simp)]
    rcases n with _ | n
    · simp
    · simp
  · rw [if_neg hc]
    by_cases hd : (d : ℕ) = 0
    · rw [if_pos hd]
      simp only [lamRes, wN, yN, hc, hd, or_true, if_true, if_false, Ures, one_mul]
      have hpc : ((place c : ℤ) : R) = (((c : ℕ) - 1 : ℕ) : ℤ) := by
        simp [place]; push_cast [Nat.cast_sub (show 1 ≤ (c : ℕ) by omega)]; ring
      have hprod : ∏ i ∈ range n, (((((c : ℕ) - 1 : ℕ) : ℤ) : R) - (i : R)) =
          ((((c : ℕ) - 1).descFactorial n : ℤ) : R) := by
        rw [← prod_sub_natCast]; push_cast; rfl
      have hfact : ((n.factorial : ℕ) : R) * invFact iv n = 1 := by
        unfold invFact
        rw [← Finset.prod_range_add_one_eq_factorial]
        push_cast
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i hi => by
          rw [mem_range] at hi
          have := h (i + 1) (by omega) (by omega)
          push_cast at this; exact this
      have key : ∑ x ∈ range (n + 1), ((place c : ℤ) : R) ^ x * (((stir n x : ℤ) : R) * invFact iv n)
          = ((((c : ℕ) - 1).choose n : ℕ) : R) := by
        have e : ∑ x ∈ range (n + 1), ((place c : ℤ) : R) ^ x * (((stir n x : ℤ) : R) * invFact iv n)
            = (∑ x ∈ range (n + 1), ((stir n x : ℤ) : R) * ((place c : ℤ) : R) ^ x) * invFact iv n := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
        rw [e, stir_poly, hpc, hprod, Nat.descFactorial_eq_factorial_mul_choose]
        push_cast
        calc ((n.factorial : ℕ) : R) * ((((c : ℕ) - 1).choose n : ℕ) : R) * invFact iv n
            = ((((c : ℕ) - 1).choose n : ℕ) : R) * (((n.factorial : ℕ) : R) * invFact iv n) := by ring
          _ = _ := by rw [hfact, mul_one]
      rw [key]; push_cast; ring
    · rw [if_neg hd]
      simp only [lamRes, wN, yN, hc, hd, or_self, if_false, Ures]
      rw [Finset.sum_eq_single n (fun b hb hbn => by rw [if_neg hbn, mul_zero]) (by simp)]
      rw [if_pos rfl, mul_one]
      obtain ⟨Q, hQ⟩ := lcm_dvd c d hc hd hcd n hn
      obtain ⟨h1, h2⟩ := diff_small c d hc hd hcd
      have hzu := ivz_mul h _ h1 h2
      have hne : ((c : ℤ) - d) ^ (n + 1) ≠ 0 := pow_ne_zero _ h1
      have hzu' : (((c : ℕ) : R) - ((d : ℕ) : R)) * ivz iv ((c : ℤ) - d) = 1 := by
        have := hzu; push_cast at this; exact this
      rw [hQ, Int.mul_ediv_cancel_left _ hne]
      push_cast
      calc (Q : R) = (Q : R) * ((((c : ℕ) : R) - ((d : ℕ) : R)) * ivz iv ((c : ℤ) - d)) ^ (n + 1) := by
            rw [hzu', one_pow, mul_one]
        _ = _ := by rw [mul_pow]; ring

/-! ## (H1): the first offset row of every block -/

lemma sum_reflect {s : ℕ} (k : ℕ) (d : Fin s) (f : ℕ → R) (j : Fin k) :
    ∑ j' : Fin k, f (k - 1 - (j' : ℕ)) * Uk iv k d j' j =
      ∑ n' ∈ range k, f n' * Ux iv d n' (k - 1 - (j : ℕ)) := by
  simp only [Uk]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (k - 1 - i) * Ux iv d (k - 1 - i) (k - 1 - (j : ℕ))) k]
  exact Finset.sum_range_reflect (fun n' => f n' * Ux iv d n' (k - 1 - (j : ℕ))) k

/-- **(H1).** Row `0` of every block `Φ'_cd` is the design: level `j` carries `F_{k-1-j}[c][d]`. -/
theorem row0 {s : ℕ} (hs : 3 ≤ s) (h : IvOK iv (s - 2)) (k : ℕ) (c d : Fin s)
    (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    UPhi R iv k c d r j = ((Fdes s (k - 1 - (j : ℕ)) c d : ℤ) : R) := by
  by_cases hcd : c = d
  · subst hcd; simp [UPhi, hr]
  have hj := j.isLt
  have e : UPhi R iv k c d r j = (lamRes c : R) * ∑ j' : Fin k,
      (wN iv c d * yN iv c d ^ (k - 1 - (j' : ℕ))) * Uk iv k d j' j := by
    simp only [UPhi, if_neg hcd, hr, if_true, mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have := propN hs h k c d hcd r hr j'
    calc (lamRes c : R) * (Qinv iv k c * (((Psi k c d r j' : ℤ) : R) * Uk iv k d j' j))
        = (lamRes c : R) * ((Qinv iv k c * ((Psi k c d r j' : ℤ) : R)) * Uk iv k d j' j) := by ring
      _ = _ := by rw [this]; ring
  rw [e, sum_reflect k d (fun n' => wN iv c d * yN iv c d ^ n') j]
  set n := k - 1 - (j : ℕ) with hn
  have hnk : n < k := by omega
  by_cases hns : n < s - 1
  · rw [design_eq hs h c d hcd n hns]
    congr 1
    rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ k by omega)]
    rw [Finset.sum_eq_zero (s := Ico (n + 1) k), add_zero]
    · refine Finset.sum_congr rfl fun n' hn' => ?_
      rw [mem_range] at hn'
      simp only [Ux, if_pos hns, if_pos (show n' < s - 1 by omega)]
    · intro n' hn'
      rw [mem_Ico] at hn'
      rw [Ux_upper d n' n (by omega), mul_zero]
  · have hF : Fdes s n c d = 0 := by
      rw [Fdes, if_neg hcd, Foff, if_pos (by omega)]
    rw [hF, Int.cast_zero]
    have e2 : ∑ n' ∈ range k, wN iv c d * yN iv c d ^ n' * Ux iv d n' n =
        wN iv c d * yN iv c d ^ n - ∑ i ∈ range (s - 1), gam iv d n i * (wN iv c d * yN iv c d ^ i) := by
      have hsplit : ∀ n', wN iv c d * yN iv c d ^ n' * Ux iv d n' n =
          (if n' = n then wN iv c d * yN iv c d ^ n else 0) -
            (if n' < s - 1 then gam iv d n n' * (wN iv c d * yN iv c d ^ n') else 0) := by
        intro n'
        simp only [Ux, if_neg hns]
        by_cases h1 : n' = n
        · rw [if_pos h1, if_pos h1, h1, if_neg hns, mul_one, sub_zero]
        · by_cases h2 : n' < s - 1
          · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; ring
          · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, mul_zero, sub_zero]
      rw [Finset.sum_congr rfl (fun n' _ => hsplit n'), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' (range k) n, if_pos (mem_range.mpr hnk)]
      congr 1
      rw [← Finset.sum_filter, show (range k).filter (fun n' => n' < s - 1) = range (s - 1) by
        ext x; simp only [mem_filter, mem_range]; omega]
    rw [e2, ← propG hs c d hcd n, sub_self, mul_zero]

end

end Z3NetU.Proofs
