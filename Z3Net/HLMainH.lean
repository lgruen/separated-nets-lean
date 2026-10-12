module
public import Mathlib
public import Z3Net.HLSep

@[expose] public section

/-!
# Entry HL, part 9: Theorem HL for the explicit design `H_s` (Lemma 2)

`u_c = 2c`, `v_d = 2d + 1`: every `e_cd = u_c - v_d` is odd with `|e_cd| ≤ 2s - 1`. With
`Λ_c = ∏_{d' ≠ c} e_{cd'}^(s-1)` and `Q_cd = ∏_{d' ≠ c, d} e_{cd'}^(s-1)`, `Λ_c y^i = Q_cd e^(s-1-i)`
for `i ≤ s-1`, so the doubled design is integral: `2F_0[c][d] = Q e^(s-2)` (odd),
`2F_1 = 2Q e^(s-3)`, `2F_n = 2Q (e^(s-2-n) - e^(s-1-n))` (even). The diagonal `-a_c` is the odd
rounding of `A_c`, so the design is dominant by construction, and `B_s` is `Bdom`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## Small integers are units -/

lemma gcd_one_of_small (q : ℕ) (hq : q.Prime) (z : ℤ) (hz : z ≠ 0) (hzq : |z| < q) :
    Int.gcd z q = 1 := by
  have hd : Int.gcd z q ∣ q := by
    have := Int.gcd_dvd_right (a := z) (b := (q : ℤ))
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr this |>.trans (by simp)
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact h
  · exfalso
    have : (q : ℤ) ∣ z := by
      have := Int.gcd_dvd_left (a := z) (b := (q : ℤ)); rw [h] at this; exact this
    have := Int.le_of_dvd (abs_pos.mpr hz) ((dvd_abs _ _).mpr this)
    linarith

lemma coprime_of_small (q : ℕ) (hq : q.Prime) (n : ℕ) (hn : n ≠ 0) (hnq : n < q) : Nat.Coprime n q :=
  (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)))

/-! ## The points -/

variable {s : ℕ}

lemma splitPt_H (c : Fin s) (e : Fin 2) :
    splitPt uH vH c e = 2 * (c : ℤ) + (if (e : ℕ) = 0 then 1 else 0) := by
  unfold splitPt uH vH
  split_ifs <;> ring

lemma eH_odd (c d : Fin s) : Odd (uH c - vH d) := ⟨(c : ℤ) - d - 1, by unfold uH vH; ring⟩

lemma eH_abs (c d : Fin s) : |uH c - vH d| ≤ 2 * s - 1 := by
  unfold uH vH
  have := c.isLt; have := d.isLt
  rw [abs_le]; constructor <;> omega

lemma eH_ne (c d : Fin s) : uH c - vH d ≠ 0 := by
  obtain ⟨t, ht⟩ := eH_odd c d; omega

/-! ## Admissibility -/

lemma coprime_int_prod {ι : Type*} (S : Finset ι) (f : ι → ℤ) (q : ℕ) (n : ℕ)
    (hf : ∀ i ∈ S, Int.gcd (f i) q = 1) : Int.gcd (∏ i ∈ S, f i ^ n) q = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact IsCoprime.prod_left fun i hi => (Int.isCoprime_iff_gcd_eq_one.mpr (hf i hi)).pow_left

/-- `Λ_c = ∏_{d' ≠ c} e_{cd'}^(s-1)`. -/
def LamH (s : ℕ) (c : Fin s) : ℤ := ∏ d' ∈ univ.erase c, (uH c - vH d') ^ (s - 1)

lemma LamH_odd (c : Fin s) : Odd (LamH s c) := by
  unfold LamH
  apply Finset.prod_induction _ (fun z => Odd z) (fun a b ha hb => ha.mul hb) odd_one
  intro d _; exact (eH_odd c d).pow

lemma lamH_eq (c : Fin s) : lamH s c = ((LamH s c : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
  simp [lamH, LamH]

lemma adm_H (hs : 2 ≤ s) (q : ℕ) (hq : q.Prime) (hqs : 2 * s ≤ q) :
    HLAdm s q uH vH (lamH s) gcoH := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqs' : (2 * s : ℤ) ≤ q := by exact_mod_cast hqs
  have hsmall : ∀ z : ℤ, z ≠ 0 → |z| ≤ 2 * s - 1 → Int.gcd z q = 1 :=
    fun z hz hzs => gcd_one_of_small q hq z hz (by linarith)
  have hq2' : Nat.Coprime 2 q := coprime_of_small q hq 2 (by norm_num) (by omega)
  refine ⟨hq2, ?_, ?_, ?_⟩
  · intro c e c' e' hne
    rw [splitPt_H, splitPt_H]
    have hc := c.isLt; have hc' := c'.isLt; have he := e.isLt; have he' := e'.isLt
    have hne' : (c : ℕ) ≠ c' ∨ (e : ℕ) ≠ e' := by
      by_contra h; push_neg at h
      exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    apply hsmall
    · split_ifs <;> omega
    · rw [abs_le]; split_ifs <;> constructor <;> push_cast <;> omega
  · intro c
    have hodd := LamH_odd (s := s) c
    have hcop : Nat.Coprime (LamH s c).natAbs (2 : ℤ).natAbs := by
      change Nat.Coprime _ 2
      rw [Nat.coprime_two_right]
      exact Int.natAbs_odd.mpr hodd
    have hden : (((LamH s c : ℤ) : ℚ) / ((2 : ℤ) : ℚ)).den = 2 := by
      have := Rat.den_div_eq_of_coprime (by norm_num) hcop
      exact_mod_cast this
    rw [lamH_eq, Rat.num_div_eq_of_coprime (by norm_num) hcop, hden]
    refine ⟨?_, hq2'⟩
    unfold LamH
    exact coprime_int_prod _ _ q _ fun d _ => hsmall _ (eH_ne c d) (eH_abs c d)
  · intro d n _
    unfold gcoH
    by_cases h0 : n = 0
    · subst h0; simp
    · simp only [h0, if_false, if_true]
      refine ⟨?_, by simp⟩
      have : ((2 : ℚ)).num = 2 := rfl
      rw [this]
      have := hq2'
      rw [show Int.gcd 2 q = Nat.gcd 2 q by rfl]
      exact this

/-! ## Integrality and parity of the doubled design -/

/-- `gcoH` with integer values. -/
def gcoHZ (n n' : ℕ) : ℤ :=
  if n = 0 then (if n' = 0 then 1 else 0)
  else if n' = n then 2 else if n' + 1 = n ∧ 2 ≤ n then -2 else 0

lemma gcoH_eq (d : Fin s) (n n' : ℕ) : gcoH d n n' = ((gcoHZ n n' : ℤ) : ℚ) := by
  unfold gcoH gcoHZ; split_ifs <;> norm_num

lemma gcoHZ_even (n n' : ℕ) (hn : 1 ≤ n) : Even (gcoHZ n n') := by
  unfold gcoHZ; split_ifs <;> first | omega | decide

/-- `Q_cd = ∏_{d' ≠ c, d} e_{cd'}^(s-1)`. -/
def QH (s : ℕ) (c d : Fin s) : ℤ := ∏ d' ∈ (univ.erase c).erase d, (uH c - vH d') ^ (s - 1)

lemma QH_odd (c d : Fin s) : Odd (QH s c d) := by
  unfold QH
  apply Finset.prod_induction _ (fun z => Odd z) (fun a b ha hb => ha.mul hb) odd_one
  intro d _; exact (eH_odd c d).pow

lemma LamH_split (c d : Fin s) (hcd : c ≠ d) : LamH s c = (uH c - vH d) ^ (s - 1) * QH s c d := by
  unfold LamH QH
  rw [← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨Ne.symm hcd, mem_univ d⟩)]

lemma Lam_y_pow (c d : Fin s) (hcd : c ≠ d) (i : ℕ) (hi : i ≤ s - 1) :
    (LamH s c : ℚ) * (yQ uH vH c d) ^ i = ((QH s c d * (uH c - vH d) ^ (s - 1 - i) : ℤ) : ℚ) := by
  rw [LamH_split c d hcd, yQ]
  have he : ((uH c - vH d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast eH_ne c d
  push_cast
  have e : (((uH c : ℚ) - vH d)) ^ (s - 1) = ((uH c : ℚ) - vH d) ^ (s - 1 - i) * ((uH c : ℚ) - vH d) ^ i := by
    rw [← pow_add]; congr 1; omega
  push_cast at he
  rw [e, inv_pow]
  field_simp

/-- The doubled design of `H_s` (integers). -/
def F2Hf (s : ℕ) (x : ℕ) (c d : Fin s) : ℤ :=
  if s - 1 ≤ x then 0
  else if c = d then (if x = 0 then -(aH2 s c : ℤ) else 0)
  else ∑ n' ∈ range (x + 1), gcoHZ x n' * (QH s c d * (uH c - vH d) ^ (s - 2 - n'))

lemma des_H_off (dg : Fin s → ℕ → ℚ) (x : ℕ) (c d : Fin s) (hcd : c ≠ d) (hx : x < s - 1) :
    2 * HLdes uH vH (lamH s) gcoH dg x c d =
      ((∑ n' ∈ range (x + 1), gcoHZ x n' * (QH s c d * (uH c - vH d) ^ (s - 2 - n')) : ℤ) : ℚ) := by
  simp only [HLdes, if_neg (show ¬ s - 1 ≤ x by omega), if_neg hcd]
  rw [lamH_eq, ← mul_assoc, show (2 : ℚ) * (((LamH s c : ℤ) : ℚ) / ((2 : ℤ) : ℚ)) = (LamH s c : ℚ) by
    push_cast; ring, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun n' hn' => ?_
  rw [mem_range] at hn'
  rw [gcoH_eq, show (LamH s c : ℚ) * (((gcoHZ x n' : ℤ) : ℚ) * yQ uH vH c d ^ (n' + 1)) =
    ((gcoHZ x n' : ℤ) : ℚ) * ((LamH s c : ℚ) * yQ uH vH c d ^ (n' + 1)) by ring,
    Lam_y_pow c d hcd (n' + 1) (by omega), show s - 1 - (n' + 1) = s - 2 - n' by omega]
  push_cast; ring

lemma hF2_H (x : ℕ) (c d : Fin s) :
    2 * HLdes uH vH (lamH s) gcoH (dgH s) x c d = (F2Hf s x c d : ℚ) := by
  by_cases hx : s - 1 ≤ x
  · simp [HLdes, F2Hf, hx]
  by_cases hcd : c = d
  · subst hcd
    simp only [HLdes, F2Hf, if_neg hx, if_true, dgH]
    split_ifs <;> push_cast <;> ring
  · rw [des_H_off (dgH s) x c d hcd (by omega)]
    simp [F2Hf, hx, hcd]

lemma aH2_odd (c : Fin s) : Odd (aH2 s c : ℤ) := by
  unfold aH2
  split_ifs with h
  · obtain ⟨t, ht⟩ := h; exact ⟨t, by push_cast; omega⟩
  · rw [Nat.not_even_iff_odd] at h
    obtain ⟨t, ht⟩ := h; exact ⟨t, by push_cast; omega⟩

lemma F2Hf_half0 (hs : 2 ≤ s) (c d : Fin s) : Odd (F2Hf s 0 c d) := by
  by_cases hcd : c = d
  · subst hcd
    have : F2Hf s 0 c c = -(aH2 s c : ℤ) := by
      unfold F2Hf; rw [if_neg (by omega)]; simp
    rw [this]; exact (aH2_odd c).neg
  · unfold F2Hf
    rw [if_neg (by omega), if_neg hcd, Finset.sum_range_one]
    have : gcoHZ 0 0 = 1 := rfl
    rw [this, one_mul]
    exact (QH_odd c d).mul ((eH_odd c d).pow)

lemma F2Hf_half (x : ℕ) (c d : Fin s) (hx : 1 ≤ x) : Even (F2Hf s x c d) := by
  unfold F2Hf
  split_ifs
  · exact ⟨0, rfl⟩
  · omega
  · exact ⟨0, rfl⟩
  · exact Finset.even_sum _ fun n' _ => (gcoHZ_even x n' hx).mul_right _

lemma F2Hf_diag (x : ℕ) (c : Fin s) (hx : 1 ≤ x) : F2Hf s x c c = 0 := by
  unfold F2Hf; split_ifs <;> first | rfl | omega

lemma F2Hf_off (x : ℕ) (c d : Fin s) (hcd : c ≠ d) : F2Hf s x c d = F2H0 s x c d := by
  unfold F2H0
  by_cases hx : s - 1 ≤ x
  · simp [F2Hf, HLdes, hx]
  · rw [des_H_off (fun _ _ => 0) x c d hcd (by omega), Int.floor_intCast]
    simp [F2Hf, hx, hcd]

lemma A2_H (c : Fin s) : A2 s (F2Hf s) c = A2 s (F2H0 s) c := by
  unfold A2
  refine Finset.sum_congr rfl fun d hd => ?_
  have hcd : c ≠ d := Ne.symm (ne_of_mem_erase hd)
  congr 1; funext j
  unfold M2
  congr 1
  exact Finset.sum_congr rfl fun x _ => F2Hf_off x c d hcd

lemma F2Hf_diag0 (hs : 2 ≤ s) (c : Fin s) : F2Hf s 0 c c = -(aH2 s c : ℤ) := by
  unfold F2Hf; rw [if_neg (by omega)]; simp

lemma dom_H (hs : 2 ≤ s) (c : Fin s) : (A2 s (F2Hf s) c : ℤ) ≤ -F2Hf s 0 c c := by
  rw [F2Hf_diag0 hs, neg_neg, A2_H]
  unfold aH2
  split_ifs <;> push_cast <;> omega

lemma Bdom_H (hs : 2 ≤ s) : Bdom s (F2Hf s) = BH s := by
  unfold Bdom BH
  congr 1; funext c
  rw [F2Hf_diag0 hs, neg_neg, A2_H]
  simp

lemma den_H (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : HLDen s q gcoH (dgH s) := by
  have hq2' : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  refine ⟨fun d n _ n' _ => ?_, fun c n _ => ?_⟩
  · rw [gcoH_eq]; simp
  · unfold dgH
    split_ifs
    · have h := den_dvd_of_mul (-(aH2 s c : ℚ) / 2) (-(aH2 s c : ℤ)) 2 (by push_cast; ring)
      exact Nat.Coprime.coprime_dvd_left h hq2'
    · simp

/-! ## Theorem HL -/

theorem HL_main (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) (hqB : 2 * BH s + 2 ≤ q)
    (hk : 1 ≤ k) :
    Z3NetHL.IsNet0 s q (s * k) (HLpoint s q k uH vH (lamH s) gcoH (dgH s)) ∧
      ∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (q : ℤ) ^ (2 * (s * k - k - 1)) *
            min ((s : ℤ) * ((q : ℤ) - 2 * BH s - 2) ^ 2) (8 * ((q : ℤ) - BH s - 1) ^ 2) ≤
          4 * (torusDist2 (q ^ (s * k)) (HLpoint s q k uH vH (lamH s) gcoH (dgH s) x)
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y) : ℤ) := by
  have hadm := adm_H hs q hq hqs
  have hq2 : q ≠ 2 := by omega
  have hden := den_H (s := s) q hq hq2
  refine ⟨HL_net s q k uH vH (lamH s) gcoH (dgH s) hs hadm hk, fun x y hxy => ?_⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h := HL_dom s q k uH vH (lamH s) gcoH (dgH s) (F2Hf s) hs hadm hden hqodd
    (fun x c d => hF2_H x c d) (F2Hf_half0 hs) (fun x c d hx => F2Hf_half x c d hx)
    (fun x c hx => F2Hf_diag x c hx) (dom_H hs) (by rw [Bdom_H hs]; exact hqB) hk x y hxy
  rw [Bdom_H hs] at h
  exact h

theorem HL_main_real (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqB : 2 * BH s + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BH s : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((BH s : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℤ) -
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hadm := adm_H hs q hq hqs
  have hq2 : q ≠ 2 := by omega
  have hden := den_H (s := s) q hq hq2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h := HL_dom_real s q k uH vH (lamH s) gcoH (dgH s) (F2Hf s) hs hadm hden hqodd
    (fun x c d => hF2_H x c d) (F2Hf_half0 hs) (fun x c d hx => F2Hf_half x c d hx)
    (fun x c hx => F2Hf_diag x c hx) (dom_H hs) (by rw [Bdom_H hs]; exact hqB) hk x y hxy
  rw [Bdom_H hs] at h
  exact h

end

end Z3NetHL.Proofs
