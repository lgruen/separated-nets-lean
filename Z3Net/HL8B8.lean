module
public import Mathlib
public import Z3Net.HL8Dom

@[expose] public section

/-!
# Entry HL8, part 4: the `s = 8` design

* `B8_design`: `2 F_x[c][d] = F2[x][c][d]` (the witness matrix), by `decide +kernel` on the 448
  entries `x < 7` (exact rational arithmetic).
* `B8_dom`: (Half), zero deeper diagonal, dominance, `B = 328183862` (`decide +kernel`).
* Exceptional primes, without primality certificates: every point difference, `λ'_c`, every
  denominator, and the leading coefficients `gco d n n` for `n ≤ 4` divide
  `N_sm = ∏_{p ∈ L_sm} p^12`, where `L_sm` lists the 35 exceptional primes of `app:designs` below
  `2B + 2 = 656367726`; the leading coefficients at level `5` divide `N_sm · 736578889^12`, those
  at level `6` divide `N_sm · (743720623 · 979256059 · 5526505499 · 3061420595773)^12`
  (`decide +kernel`). A prime `q ≥ 656367726` divides no element of `L_sm`, and if it divides one
  of the five large numbers `P` it equals `P` (no `t ∈ [2, P / 656367726]` divides `P`).
* `B8_sep_real` from `HL_dom_lev_real`; `B8_main` from it with `η < 1/2 - 1/√8`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## The witness identity and the dominance data -/

set_option maxRecDepth 100000 in
lemma B8_design_lt : ∀ x : Fin 7, ∀ c d : Fin 8,
    2 * HLdes uB8 vB8 lamB8 gcoB8 dgB8 x c d = F2B8 x c d := by
  decide +kernel

lemma F2B8_ge (x : ℕ) (hx : 7 ≤ x) (c d : Fin 8) : F2B8 x c d = 0 := by
  unfold F2B8
  have : F2TabB8.getD x [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [F2TabB8]; omega)]; rfl
  rw [this]; simp

theorem B8_design (x : ℕ) (c d : Fin 8) :
    2 * HLdes uB8 vB8 lamB8 gcoB8 dgB8 x c d = F2B8 x c d := by
  by_cases hx : x < 7
  · exact B8_design_lt ⟨x, hx⟩ c d
  · have h1 : HLdes uB8 vB8 lamB8 gcoB8 dgB8 x c d = 0 := by
      simp [HLdes, show 8 - 1 ≤ x by omega]
    rw [h1, F2B8_ge x (by omega) c d]; simp

lemma B8_odd0 : ∀ c d : Fin 8, F2B8 0 c d % 2 = 1 := by decide +kernel

lemma B8_even_lt : ∀ x : Fin 7, ∀ c d : Fin 8, 1 ≤ (x : ℕ) → F2B8 x c d % 2 = 0 := by decide +kernel

lemma B8_diag_lt : ∀ x : Fin 7, ∀ c : Fin 8, 1 ≤ (x : ℕ) → F2B8 x c c = 0 := by decide +kernel

set_option maxRecDepth 100000 in
lemma B8_dom_c : ∀ c : Fin 8, (A2 8 F2B8 c : ℤ) ≤ -F2B8 0 c c := by decide +kernel

set_option maxRecDepth 100000 in
lemma B8_B : Bdom 8 F2B8 = 328183862 := by decide +kernel

theorem B8_dom :
    (∀ c d, Odd (F2B8 0 c d)) ∧ (∀ x c d, 1 ≤ x → Even (F2B8 x c d)) ∧
      (∀ x c, 1 ≤ x → F2B8 x c c = 0) ∧ (∀ c, (A2 8 F2B8 c : ℤ) ≤ -F2B8 0 c c) ∧
      Bdom 8 F2B8 = 328183862 := by
  refine ⟨fun c d => Int.odd_iff.mpr (B8_odd0 c d), fun x c d hx => ?_, fun x c hx => ?_, B8_dom_c, B8_B⟩
  · by_cases h : x < 7
    · exact Int.even_iff.mpr (B8_even_lt ⟨x, h⟩ c d hx)
    · rw [F2B8_ge x (by omega)]; exact ⟨0, by simp⟩
  · by_cases h : x < 7
    · exact B8_diag_lt ⟨x, h⟩ c hx
    · exact F2B8_ge x (by omega) c c

/-! ## Exceptional primes -/

/-- The 35 exceptional primes of `app:designs` below `656367726`. -/
def Lsm : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 97, 281, 773, 1193, 2543, 3119, 5647, 61,
  211, 257, 271, 1171, 2903, 10331, 58831, 7623037, 233, 293, 11833, 52541, 203381, 656303,
  1171699, 1717117, 7819033]

def Nsm : ℕ := (Lsm.map (· ^ 12)).prod

def N5 : ℕ := Nsm * 736578889 ^ 12

def N6 : ℕ := Nsm * (743720623 * 979256059 * 5526505499 * 3061420595773) ^ 12

lemma Lsm_small : ∀ p ∈ Lsm, 0 < p ∧ p < 656367726 := by decide +kernel

lemma not_dvd_Nsm (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) : ¬ q ∣ Nsm := by
  intro h
  unfold Nsm at h
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_prod_iff hq.prime).mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have h1 := hq.dvd_of_dvd_pow hqa
  have h2 := Lsm_small p hp
  have := Nat.le_of_dvd h2.1 h1
  omega

lemma eq_of_dvd_big (P b q : ℕ) (_hq : q.Prime) (hb : b ≤ q) (hb0 : 0 < b) (hP : 0 < P)
    (hqP : q ∣ P) (hchk : ∀ t < P / b + 1, 2 ≤ t → P % t ≠ 0) : q = P := by
  obtain ⟨t, rfl⟩ := hqP
  have ht0 : t ≠ 0 := by rintro rfl; simp at hP
  by_cases ht1 : t = 1
  · subst ht1; simp
  · exfalso
    have htb : t * b ≤ q * t := by rw [mul_comm q]; exact Nat.mul_le_mul_left t hb
    have : t ≤ q * t / b := (Nat.le_div_iff_mul_le hb0).mpr htb
    exact hchk t (by omega) (by omega) (by simp)

lemma big1 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h : q ∣ 736578889) : q = 736578889 :=
  eq_of_dvd_big _ _ q hq hb (by norm_num) (by norm_num) h (by decide)

lemma big2 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h : q ∣ 743720623) : q = 743720623 :=
  eq_of_dvd_big _ _ q hq hb (by norm_num) (by norm_num) h (by decide)

lemma big3 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h : q ∣ 979256059) : q = 979256059 :=
  eq_of_dvd_big _ _ q hq hb (by norm_num) (by norm_num) h (by decide)

lemma big4 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h : q ∣ 5526505499) : q = 5526505499 :=
  eq_of_dvd_big _ _ q hq hb (by norm_num) (by norm_num) h (by decide +kernel)

set_option maxRecDepth 200000 in
lemma chk5_HL8 : ∀ t < 3061420595773 / 656367726 + 1, 2 ≤ t → 3061420595773 % t ≠ 0 := by
  decide +kernel

lemma big5 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h : q ∣ 3061420595773) :
    q = 3061420595773 :=
  eq_of_dvd_big _ _ q hq hb (by norm_num) (by norm_num) h chk5_HL8

lemma not_dvd_N5 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (hne : q ≠ 736578889) :
    ¬ q ∣ N5 := by
  intro h
  unfold N5 at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact not_dvd_Nsm q hq hb h
  · exact hne (big1 q hq hb (hq.dvd_of_dvd_pow h))

lemma not_dvd_N6 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q)
    (hne : q ∉ ({743720623, 979256059, 5526505499, 3061420595773} : Finset ℕ)) : ¬ q ∣ N6 := by
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  unfold N6 at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact not_dvd_Nsm q hq hb h
  · have h := hq.dvd_of_dvd_pow h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · exact hne.1 (big2 q hq hb h)
        · exact hne.2.1 (big3 q hq hb h)
      · exact hne.2.2.1 (big4 q hq hb h)
    · exact hne.2.2.2 (big5 q hq hb h)

lemma gcd_one_of_not_dvd (q N : ℕ) (hq : q.Prime) (hN : ¬ q ∣ N) (z : ℤ) (hz : z ∣ (N : ℤ)) :
    Int.gcd z q = 1 := by
  have hd : Int.gcd z q ∣ q := by
    have := Int.gcd_dvd_right (a := z) (b := (q : ℤ))
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr this |>.trans (by simp)
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact h
  · exfalso
    have h1 : (q : ℤ) ∣ z := by
      have := Int.gcd_dvd_left (a := z) (b := (q : ℤ)); rw [h] at this; exact this
    exact hN (by exact_mod_cast h1.trans hz)

lemma coprime_of_not_dvd (q N : ℕ) (hq : q.Prime) (hN : ¬ q ∣ N) (n : ℕ) (hn : n ∣ N) :
    Nat.Coprime n q := by
  have := gcd_one_of_not_dvd q N hq hN (n : ℤ) (by exact_mod_cast hn)
  rw [Int.gcd_natCast_natCast] at this
  exact this

lemma B8_pts_dvd : ∀ c : Fin 8, ∀ e : Fin 2, ∀ c' : Fin 8, ∀ e' : Fin 2, (c, e) ≠ (c', e') →
    (splitPt uB8 vB8 c e - splitPt uB8 vB8 c' e') ∣ (Nsm : ℤ) := by
  decide +kernel

lemma B8_lam_dvd : ∀ c : Fin 8, (lamB8 c).num ∣ (Nsm : ℤ) ∧ (lamB8 c).den ∣ Nsm := by
  decide +kernel

lemma B8_lead_dvd4 : ∀ d : Fin 8, ∀ n : Fin 5,
    (gcoB8 d n n).num ∣ (Nsm : ℤ) ∧ (gcoB8 d n n).den ∣ Nsm := by
  decide +kernel

lemma B8_lead_dvd5 : ∀ d : Fin 8, (gcoB8 d 5 5).num ∣ (N5 : ℤ) ∧ (gcoB8 d 5 5).den ∣ Nsm := by
  decide +kernel

lemma B8_lead_dvd6 : ∀ d : Fin 8, (gcoB8 d 6 6).num ∣ (N6 : ℤ) ∧ (gcoB8 d 6 6).den ∣ Nsm := by
  decide +kernel

lemma B8_den_dvd : ∀ d : Fin 8, ∀ n : Fin 7, ∀ n' : Fin 7, (gcoB8 d n n').den ∣ Nsm := by
  decide +kernel

lemma B8_dg_dvd : ∀ c : Fin 8, ∀ n : Fin 7, (dgB8 c n).den ∣ Nsm := by
  decide +kernel

lemma adm_B8 (q k : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) (h6 : 6 ≤ k → q ≠ 736578889)
    (h7 : 7 ≤ k → q ∉ ({743720623, 979256059, 5526505499, 3061420595773} : Finset ℕ)) :
    HLAdmL 8 q (min k (8 - 1)) uB8 vB8 lamB8 gcoB8 := by
  have hs := not_dvd_Nsm q hq hb
  refine ⟨hq.two_le, fun c e c' e' h => gcd_one_of_not_dvd q _ hq hs _ (B8_pts_dvd c e c' e' h),
    fun c => ⟨gcd_one_of_not_dvd q _ hq hs _ (B8_lam_dvd c).1,
      coprime_of_not_dvd q _ hq hs _ (B8_lam_dvd c).2⟩, fun d n hn => ?_⟩
  have hn7 : n < 7 := lt_of_lt_of_le hn (min_le_right _ _)
  have hnk : n < k := lt_of_lt_of_le hn (min_le_left _ _)
  by_cases h4 : n ≤ 4
  · have := B8_lead_dvd4 d ⟨n, by omega⟩
    exact ⟨gcd_one_of_not_dvd q _ hq hs _ this.1, coprime_of_not_dvd q _ hq hs _ this.2⟩
  by_cases h5 : n = 5
  · subst h5
    have := B8_lead_dvd5 d
    exact ⟨gcd_one_of_not_dvd q _ hq (not_dvd_N5 q hq hb (h6 (by omega))) _ this.1,
      coprime_of_not_dvd q _ hq hs _ this.2⟩
  · have h6' : n = 6 := by omega
    subst h6'
    have := B8_lead_dvd6 d
    exact ⟨gcd_one_of_not_dvd q _ hq (not_dvd_N6 q hq hb (h7 (by omega))) _ this.1,
      coprime_of_not_dvd q _ hq hs _ this.2⟩

lemma den_B8 (q : ℕ) (hq : q.Prime) (hb : 656367726 ≤ q) : HLDen 8 q gcoB8 dgB8 :=
  ⟨fun d n hn n' hn' => coprime_of_not_dvd q _ hq (not_dvd_Nsm q hq hb) _
      (B8_den_dvd d ⟨n, by omega⟩ ⟨n', by omega⟩),
    fun c n hn => coprime_of_not_dvd q _ hq (not_dvd_Nsm q hq hb) _ (B8_dg_dvd c ⟨n, by omega⟩)⟩

/-! ## Separation -/

theorem B8_sep_real (q k : ℕ) (hq : q.Prime) (hqB : 656367726 ≤ q) (hk : 1 ≤ k)
    (h6 : 6 ≤ k → q ≠ 736578889)
    (h7 : 7 ≤ k → q ∉ ({743720623, 979256059, 5526505499, 3061420595773} : Finset ℕ))
    (x y : Fin (8 * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt 8 * (1 / 2 - ((328183862 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((328183862 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (8 * k))
          ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
            (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2) := by
  obtain ⟨hodd, heven, hdiag, hdom, hB⟩ := B8_dom
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have h := HL_dom_lev_real 8 q k uB8 vB8 lamB8 gcoB8 dgB8 F2B8 (by norm_num)
    (adm_B8 q k hq hqB h6 h7) (den_B8 q hq hqB) hqodd B8_design hodd heven hdiag hdom
    (by rw [hB]; omega) hk x y hxy
  rw [hB] at h
  exact_mod_cast h

theorem B8_main (q k : ℕ) (hq : q.Prime) (hq0 : 2250000000 < q) (hk : 1 ≤ k)
    (hexc : 7 ≤ k → q ≠ 5526505499 ∧ q ≠ 3061420595773) :
    Z3NetHL.IsNet0 8 q (8 * k) (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8) ∧
      ∀ x y : Fin (8 * k) → ZMod q, x ≠ y →
        ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
          < Real.sqrt (∑ c, ((cres (q ^ (8 * k))
              ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
                (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2) := by
  have hqB : 656367726 ≤ q := by omega
  have h6 : 6 ≤ k → q ≠ 736578889 := fun _ => by omega
  have h7 : 7 ≤ k → q ∉ ({743720623, 979256059, 5526505499, 3061420595773} : Finset ℕ) := by
    intro hk7
    obtain ⟨a, b⟩ := hexc hk7
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by omega, by omega, a, b⟩
  refine ⟨HL_net_lev 8 q k uB8 vB8 lamB8 gcoB8 dgB8 (by norm_num) (adm_B8 q k hq hqB h6 h7) hk,
    fun x y hxy => ?_⟩
  have h := B8_sep_real q k hq hqB hk h6 h7 x y hxy
  have hN : 0 < ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) := by positivity
  -- `η = (B + 1)/q < 0.1459`, so both terms of the minimum exceed `1`
  have hq' : (2250000000 : ℝ) < q := by exact_mod_cast hq0
  have hqpos : (0 : ℝ) < q := by linarith
  have heta : ((328183862 : ℝ) + 1) / q < 0.1459 := by
    rw [div_lt_iff₀ hqpos]; linarith
  have heta0 : 0 ≤ ((328183862 : ℝ) + 1) / q := by positivity
  have hs8 : (2.828 : ℝ) < Real.sqrt 8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : (1.414 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h1 : 1 < Real.sqrt 8 * (1 / 2 - ((328183862 : ℝ) + 1) / q) := by
    have : (0.3541 : ℝ) < 1 / 2 - ((328183862 : ℝ) + 1) / q := by linarith
    nlinarith
  have h2 : 1 < Real.sqrt 2 * (1 - ((328183862 : ℝ) + 1) / q) := by
    have : (0.85 : ℝ) < 1 - ((328183862 : ℝ) + 1) / q := by linarith
    nlinarith
  have hmin : 1 < min (Real.sqrt 8 * (1 / 2 - ((328183862 : ℝ) + 1) / q))
      (Real.sqrt 2 * (1 - ((328183862 : ℝ) + 1) / q)) := lt_min h1 h2
  calc ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) = 1 * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) := by ring
    _ < min _ _ * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) := mul_lt_mul_of_pos_right hmin hN
    _ ≤ _ := h


/-! ## The net at every prime outside the listed numbers, per level -/

/-- `N_n = ∏_{j ≤ n} ∏_{p ∈ B8exc j} p^12`. -/
def Nlev (n : ℕ) : ℕ := (((List.range (n + 1)).flatMap B8exc).map (· ^ 12)).prod

lemma B8_pts_dvd0 : ∀ c : Fin 8, ∀ e : Fin 2, ∀ c' : Fin 8, ∀ e' : Fin 2, (c, e) ≠ (c', e') →
    (splitPt uB8 vB8 c e - splitPt uB8 vB8 c' e') ∣ (Nlev 0 : ℤ) := by
  decide +kernel

lemma B8_lam_dvd0 : ∀ c : Fin 8, (lamB8 c).num ∣ (Nlev 0 : ℤ) ∧ (lamB8 c).den ∣ Nlev 0 := by
  decide +kernel

lemma B8_lead_dvdlev : ∀ d : Fin 8, ∀ n : Fin 7,
    (gcoB8 d n n).num ∣ (Nlev n : ℤ) ∧ (gcoB8 d n n).den ∣ Nlev 0 := by
  decide +kernel

lemma not_dvd_Nlev (q k : ℕ) (hq : q.Prime) (hexc : ∀ j < min k 7, ∀ p ∈ B8exc j, ¬ q ∣ p)
    (n : ℕ) (hn : n < min k 7) : ¬ q ∣ Nlev n := by
  intro h
  unfold Nlev at h
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_prod_iff hq.prime).mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.mp hp
  rw [List.mem_range] at hj
  exact hexc j (by omega) p hpj (hq.dvd_of_dvd_pow hqa)

theorem B8_net (q k : ℕ) (hq : q.Prime) (hk : 1 ≤ k)
    (hexc : ∀ j < min k 7, ∀ p ∈ B8exc j, ¬ q ∣ p) :
    Z3NetHL.IsNet0 8 q (8 * k) (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8) := by
  have h0 := not_dvd_Nlev q k hq hexc 0 (by omega)
  refine HL_net_lev 8 q k uB8 vB8 lamB8 gcoB8 dgB8 (by norm_num) ⟨hq.two_le,
    fun c e c' e' h => gcd_one_of_not_dvd q _ hq h0 _ (B8_pts_dvd0 c e c' e' h),
    fun c => ⟨gcd_one_of_not_dvd q _ hq h0 _ (B8_lam_dvd0 c).1,
      coprime_of_not_dvd q _ hq h0 _ (B8_lam_dvd0 c).2⟩, fun d n hn => ?_⟩ hk
  have := B8_lead_dvdlev d ⟨n, lt_of_lt_of_le hn (min_le_right _ _)⟩
  exact ⟨gcd_one_of_not_dvd q _ hq (not_dvd_Nlev q k hq hexc n hn) _ this.1,
    coprime_of_not_dvd q _ hq h0 _ this.2⟩

end

end Z3NetHL.Proofs
