module
public import Z3Net.HalfSep
public import Z3Net.HalfLam68
public import Z3Net.HalfCertDetK
public import Z3Net.HalfCertT5
public import Z3Net.HalfCertT6
public import Z3Net.HalfCertT8
public import Z3Net.HalfCertP0
public import Z3Net.HalfCertP1
public import Z3Net.HalfCertP2
public import Z3Net.HalfCertP3
public import Z3Net.HalfCertInf
public import Z3Net.HalfCertW6_211
public import Z3Net.HalfCertW6_1009
public import Z3Net.HalfCertW6_10007
public import Z3Net.HalfCertW6_1000003
public import Z3Net.HalfCertW8_1009b
public import Z3Net.HalfCertW8_10007b
public import Z3Net.HalfCertW8_1000003b

@[expose] public section

/-!
# Entry Half: `tab:half` and "Positioning" (assembly)

The certified values of `tab:half` (`half_tab_LB2`) from the kernel certificates
`HalfCertT5/T6/T8` (for the dominant `s = 6, 8` designs the steps with some `|E_c| = 2` are
handled by `ell_ge_three_halves`, `lb_dom_full`), the separation bounds `half{5,6,8}_tab_sep`
(`half_sep`), the `s = 5` design: `half5_lam` (`HalfCertInf`), `half5_net` (`HalfCertDetK`,
`halfPhi_net_of_int`), `half5_threshold` (`p = 83`: the step `(-1,1,-1,-1,1)`; `89 ≤ p < 269`:
`HalfCertT5`, `HalfCertP0`–`P3`; `p ≥ 269`: `half_LB2_ge` with `λ = √5/2`, `2A = 13`),
`half5_main`; `half_tab_t0` (`HalfCertW6_*`, `HalfCertW8_*`: the deeper rows of
`eis_link_t0_witnesses.json`, every box checked by fraction-free elimination over `ZMod p`).
-/

namespace Z3NetHL.Proofs

open Finset

/-! ## Small facts about the designs -/

theorem halfA2_M5h : halfA2 M5h = 13 := by decide +kernel
theorem halfA2_M6h : halfA2 M6h = 46 := by decide +kernel
theorem halfA2_M8h : halfA2 M8h = 86 := by decide +kernel
theorem M5h_odd : ∀ c d, Odd (M5h c d) := by decide +kernel
theorem M6h_odd : ∀ c d, Odd (M6h c d) := by decide +kernel
theorem M8h_odd : ∀ c d, Odd (M8h c d) := by decide +kernel

lemma dec_le {x q : ℝ} (n : ℕ) (e : q = (n : ℝ) / 10 ^ 4) (h : (n : ℝ) / 10 ^ 4 ≤ x) : q ≤ x :=
  e ▸ h

/-- For a dominant design: the steps with some `|E_c| = 2` satisfy `|ℓ(E)| ≥ 3/2 - (2A+1)/p`. -/
lemma lb_dom_full {s : ℕ} (p : ℕ) (hp : 1 ≤ p) (M2 : Fin s → Fin s → ℤ)
    (hdom : ∀ c, M2 c c ≤ -∑ d ∈ univ.erase c, |M2 c d|) (v : ℝ)
    (h3 : v ≤ 3 / 2 - ((halfA2 M2 : ℝ) + 1) / p)
    (hsmall : ∀ E ∈ halfSteps s, (∀ c, -1 ≤ E c ∧ E c ≤ 1) →
      v ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2)) :
    ∀ E ∈ halfSteps s, v ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2) := by
  intro E hE
  by_cases hs : ∀ c, -1 ≤ E c ∧ E c ≤ 1
  · exact hsmall E hE hs
  · push Not at hs
    obtain ⟨c, hc⟩ := hs
    have hmax : ∀ d, |E d| ≤ 2 := (mem_halfSteps.mp hE).1
    have hc2 : |E c| = 2 := by
      have hm := hmax c
      rw [abs_le] at hm
      rcases le_or_gt (-1) (E c) with h | h
      · have := hc h
        rw [abs_of_pos (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    have h1 := ell_ge_three_halves p M2 hdom E hE c hc2 hmax hp
    have h2 : halfEll p M2 E c ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun c => halfEll p M2 E c ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ c))
    linarith

/-! ## `tab:half`: the values of `LB₂` -/

theorem half_tab_LB2 :
    ((1.0056 : ℝ) ≤ halfLB2 89 M5h ∧ (1.0188 : ℝ) ≤ halfLB2 101 M5h ∧
      (1.0704 : ℝ) ≤ halfLB2 211 M5h ∧ (1.1080 : ℝ) ≤ halfLB2 1009 M5h ∧
      (1.1179 : ℝ) ≤ halfLB2 100003 M5h) ∧
    ((1.1113 : ℝ) ≤ halfLB2 211 M6h ∧ (1.2009 : ℝ) ≤ halfLB2 1009 M6h ∧
      (1.2223 : ℝ) ≤ halfLB2 10007 M6h ∧ (1.2247 : ℝ) ≤ halfLB2 1000003 M6h) ∧
    ((1.3488 : ℝ) ≤ halfLB2 1009 M8h ∧ (1.4076 : ℝ) ≤ halfLB2 10007 M8h ∧
      (1.4141 : ℝ) ≤ halfLB2 1000003 M8h) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact dec_le 10056 (by norm_num) (le_halfLB2_of 89 M5h _ (by norm_num) (by norm_num) lb5_89)
  · exact dec_le 10188 (by norm_num) (le_halfLB2_of 101 M5h _ (by norm_num) (by norm_num) lb5_101)
  · exact dec_le 10704 (by norm_num) (le_halfLB2_of 211 M5h _ (by norm_num) (by norm_num) lb5_211)
  · exact dec_le 11080 (by norm_num) (le_halfLB2_of 1009 M5h _ (by norm_num) (by norm_num) lb5_1009)
  · exact dec_le 11179 (by norm_num) (le_halfLB2_of 100003 M5h _ (by norm_num) (by norm_num) lb5_100003)
  · exact dec_le 11113 (by norm_num) (le_halfLB2_of 211 M6h _ (by norm_num) (by norm_num)
      (lb_dom_full 211 (by norm_num) M6h M6h_dom _ (by rw [halfA2_M6h]; norm_num) lb6_211))
  · exact dec_le 12009 (by norm_num) (le_halfLB2_of 1009 M6h _ (by norm_num) (by norm_num)
      (lb_dom_full 1009 (by norm_num) M6h M6h_dom _ (by rw [halfA2_M6h]; norm_num) lb6_1009))
  · exact dec_le 12223 (by norm_num) (le_halfLB2_of 10007 M6h _ (by norm_num) (by norm_num)
      (lb_dom_full 10007 (by norm_num) M6h M6h_dom _ (by rw [halfA2_M6h]; norm_num) lb6_10007))
  · exact dec_le 12247 (by norm_num) (le_halfLB2_of 1000003 M6h _ (by norm_num) (by norm_num)
      (lb_dom_full 1000003 (by norm_num) M6h M6h_dom _ (by rw [halfA2_M6h]; norm_num) lb6_1000003))
  · exact dec_le 13488 (by norm_num) (le_halfLB2_of 1009 M8h _ (by norm_num) (by norm_num)
      (lb_dom_full 1009 (by norm_num) M8h M8h_dom _ (by rw [halfA2_M8h]; norm_num) lb8_1009))
  · exact dec_le 14076 (by norm_num) (le_halfLB2_of 10007 M8h _ (by norm_num) (by norm_num)
      (lb_dom_full 10007 (by norm_num) M8h M8h_dom _ (by rw [halfA2_M8h]; norm_num) lb8_10007))
  · exact dec_le 14141 (by norm_num) (le_halfLB2_of 1000003 M8h _ (by norm_num) (by norm_num)
      (lb_dom_full 1000003 (by norm_num) M8h M8h_dom _ (by rw [halfA2_M8h]; norm_num) lb8_1000003))

/-! ## `tab:half` as separation bounds -/

lemma tab_sep_of {s : ℕ} (hs : 3 ≤ s) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (M2 : Fin s → Fin s → ℤ) (hodd : ∀ c d, Odd (M2 c d)) (hpA : 2 * halfA2 M2 + 2 < p) (v : ℝ)
    (hv : v ≤ halfLB2 p M2)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign s p 1 Φ (fun _ => M2)) (x y : Fin (s * 1) → ZMod p) (hxy : x ≠ y) :
    v * ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * 1))
          ((GFpoint s p 1 Φ x c : ℤ) - (GFpoint s p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (s * 1)) ^ 2) :=
  (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg (by positivity) _)).trans
    (half_sep s p hs hp hp2 M2 hodd hpA Φ hrow x y hxy)

theorem half5_tab_sep (p : ℕ) (v : ℝ)
    (hv : (p = 89 ∧ v = 1.0056) ∨
      (p = 101 ∧ v = 1.0188) ∨
      (p = 211 ∧ v = 1.0704) ∨
      (p = 1009 ∧ v = 1.1080) ∨
      (p = 100003 ∧ v = 1.1179))
    (Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 5 p 1 Φ (fun _ => M5h)) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    v * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1))
          ((GFpoint 5 p 1 Φ x c : ℤ) - (GFpoint 5 p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2) := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tab_sep_of (by norm_num) 89 (by norm_num) (by norm_num) M5h M5h_odd
      (by rw [halfA2_M5h]; norm_num) _ half_tab_LB2.1.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 101 (by norm_num) (by norm_num) M5h M5h_odd
      (by rw [halfA2_M5h]; norm_num) _ half_tab_LB2.1.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 211 (by norm_num) (by norm_num) M5h M5h_odd
      (by rw [halfA2_M5h]; norm_num) _ half_tab_LB2.1.2.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 1009 (by norm_num) (by norm_num) M5h M5h_odd
      (by rw [halfA2_M5h]; norm_num) _ half_tab_LB2.1.2.2.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 100003 (by norm_num) (by norm_num) M5h M5h_odd
      (by rw [halfA2_M5h]; norm_num) _ half_tab_LB2.1.2.2.2.2 Φ hrow x y hxy

theorem half6_tab_sep (p : ℕ) (v : ℝ)
    (hv : (p = 211 ∧ v = 1.1113) ∨
      (p = 1009 ∧ v = 1.2009) ∨
      (p = 10007 ∧ v = 1.2223) ∨
      (p = 1000003 ∧ v = 1.2247))
    (Φ : Fin 6 → Fin 6 → Matrix (Fin (6 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 6 p 1 Φ (fun _ => M6h)) (x y : Fin (6 * 1) → ZMod p) (hxy : x ≠ y) :
    v * ((p : ℝ) ^ (6 * 1)) ^ (-(1 / (6 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (6 * 1))
          ((GFpoint 6 p 1 Φ x c : ℤ) - (GFpoint 6 p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (6 * 1)) ^ 2) := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tab_sep_of (by norm_num) 211 (by norm_num) (by norm_num) M6h M6h_odd
      (by rw [halfA2_M6h]; norm_num) _ half_tab_LB2.2.1.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 1009 (by norm_num) (by norm_num) M6h M6h_odd
      (by rw [halfA2_M6h]; norm_num) _ half_tab_LB2.2.1.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 10007 (by norm_num) (by norm_num) M6h M6h_odd
      (by rw [halfA2_M6h]; norm_num) _ half_tab_LB2.2.1.2.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 1000003 (by norm_num) (by norm_num) M6h M6h_odd
      (by rw [halfA2_M6h]; norm_num) _ half_tab_LB2.2.1.2.2.2 Φ hrow x y hxy

theorem half8_tab_sep (p : ℕ) (v : ℝ)
    (hv : (p = 1009 ∧ v = 1.3488) ∨
      (p = 10007 ∧ v = 1.4076) ∨
      (p = 1000003 ∧ v = 1.4141))
    (Φ : Fin 8 → Fin 8 → Matrix (Fin (8 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 8 p 1 Φ (fun _ => M8h)) (x y : Fin (8 * 1) → ZMod p) (hxy : x ≠ y) :
    v * ((p : ℝ) ^ (8 * 1)) ^ (-(1 / (8 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (8 * 1))
          ((GFpoint 8 p 1 Φ x c : ℤ) - (GFpoint 8 p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (8 * 1)) ^ 2) := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact tab_sep_of (by norm_num) 1009 (by norm_num) (by norm_num) M8h M8h_odd
      (by rw [halfA2_M8h]; norm_num) _ half_tab_LB2.2.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 10007 (by norm_num) (by norm_num) M8h M8h_odd
      (by rw [halfA2_M8h]; norm_num) _ half_tab_LB2.2.2.2.1 Φ hrow x y hxy
  · exact tab_sep_of (by norm_num) 1000003 (by norm_num) (by norm_num) M8h M8h_odd
      (by rw [halfA2_M8h]; norm_num) _ half_tab_LB2.2.2.2.2 Φ hrow x y hxy

/-! ## The `s = 5` design -/

lemma E1_mem : (fun _ : Fin 5 => (-1 : ℤ)) ∈ halfSteps 5 :=
  mem_halfSteps.mpr ⟨fun _ => by norm_num, fun h => by have := congrFun h 0; simp at this⟩

lemma lam5_E1 : Real.sqrt (∑ c, halfEllInf M5h (fun _ => -1) c ^ 2) = Real.sqrt 5 / 2 := by
  rw [sum_halfEllInf_sq]
  have h : (∑ c, hLinf (oddB (fun _ : Fin 5 => (-1 : ℤ))) ((fun _ : Fin 5 => (-1 : ℤ)) c)
      (∑ d, M5h c d * (fun _ : Fin 5 => (-1 : ℤ)) d) ^ 2) = 5 := by decide +kernel
  rw [h, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem half5_lam :
    halfLam M5h = Real.sqrt 5 / 2 ∧
      Real.sqrt (∑ c, halfEllInf M5h (fun _ => -1) c ^ 2) = Real.sqrt 5 / 2 ∧
      halfA2 M5h = 13 ∧ ¬ ∀ c, M5h c c ≤ -∑ d ∈ univ.erase c, |M5h c d| := by
  refine ⟨le_antisymm ?_ (le_halfLam_of M5h _ (by norm_num) lam5_ge), lam5_E1, halfA2_M5h,
    by decide +kernel⟩
  exact lam5_E1 ▸ halfLam_le_of M5h _ E1_mem

theorem half5_net (p : ℕ) (hp : p.Prime)
    (hS : p ∉ ({2, 3, 5, 7, 11, 13, 17, 29, 41, 47, 257} : Finset ℕ)) :
    IsNet0 5 p (5 * 1) (GFpoint 5 p 1 (halfPhi 5 p M5h D5h)) :=
  halfPhi_net_of_int 5 p hp (by rintro rfl; exact hS (by decide)) M5h D5h
    (fun d hd => half5_box_ndvd p hp hS d hd)

lemma one_lt_of_lb5 (p n : ℕ) (hn : 10000 < n ∧ n ≤ 20000)
    (h : ∀ E ∈ halfSteps 5, (n : ℝ) / 10 ^ 4 ≤ Real.sqrt (∑ c, halfEll p M5h E c ^ 2)) :
    1 < halfLB2 p M5h := by
  have hn' : (10000 : ℝ) < n := by exact_mod_cast hn.1
  have hn2 : (n : ℝ) ≤ 20000 := by exact_mod_cast hn.2
  have := le_halfLB2_of p M5h ((n : ℝ) / 10 ^ 4) (by norm_num)
    (by rw [div_le_iff₀ (by norm_num)]; linarith) h
  have h1 : (1 : ℝ) < (n : ℝ) / 10 ^ 4 := by rw [lt_div_iff₀ (by norm_num)]; linarith
  linarith

lemma one_lt_big (p : ℕ) (hp : 269 ≤ p) : 1 < halfLB2 p M5h := by
  have h := half_LB2_ge 5 p (by norm_num) (by omega) M5h
  rw [half5_lam.1, halfA2_M5h] at h
  simp only [Nat.cast_ofNat] at h
  have hp' : (269 : ℝ) ≤ p := by exact_mod_cast hp
  have h5 : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hb : Real.sqrt 5 * ((13 : ℝ) + 1) / p ≤ Real.sqrt 5 * 14 / 269 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.sqrt_nonneg 5]
  linarith

lemma lb83 : halfLB2 83 M5h < 1 := by
  refine lt_of_le_of_lt (halfLB2_le_of 83 M5h ![-1, 1, -1, -1, 1]
    (mem_halfSteps.mpr ⟨fun d => by fin_cases d <;> decide, fun h => by
      have := congrFun h 0; simp at this⟩)) ?_
  exact sqrt_lt_one_of_cert 83 (by norm_num) M5h _ (by decide +kernel)

theorem half5_threshold :
    halfLB2 83 M5h < 1 ∧ ∀ p : ℕ, p.Prime → 89 ≤ p → 1 < halfLB2 p M5h := by
  refine ⟨lb83, fun p hp h89 => ?_⟩
  by_cases hbig : 269 ≤ p
  · exact one_lt_big p hbig
  · push Not at hbig
    have key : p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨ p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨ p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173 ∨ p = 179 ∨ p = 181 ∨ p = 191 ∨ p = 193 ∨ p = 197 ∨ p = 199 ∨ p = 211 ∨ p = 223 ∨ p = 227 ∨ p = 229 ∨ p = 233 ∨ p = 239 ∨ p = 241 ∨ p = 251 ∨ p = 257 ∨ p = 263 := by
      interval_cases p <;> first | decide | (exfalso; norm_num at hp)
    rcases key with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_lt_of_lb5 89 10056 (by norm_num) lb5_89
    · exact one_lt_of_lb5 97 10001 (by norm_num) lb5_97
    · exact one_lt_of_lb5 101 10188 (by norm_num) lb5_101
    · exact one_lt_of_lb5 103 10001 (by norm_num) lb5_103
    · exact one_lt_of_lb5 107 10001 (by norm_num) lb5_107
    · exact one_lt_of_lb5 109 10001 (by norm_num) lb5_109
    · exact one_lt_of_lb5 113 10001 (by norm_num) lb5_113
    · exact one_lt_of_lb5 127 10001 (by norm_num) lb5_127
    · exact one_lt_of_lb5 131 10001 (by norm_num) lb5_131
    · exact one_lt_of_lb5 137 10001 (by norm_num) lb5_137
    · exact one_lt_of_lb5 139 10001 (by norm_num) lb5_139
    · exact one_lt_of_lb5 149 10001 (by norm_num) lb5_149
    · exact one_lt_of_lb5 151 10001 (by norm_num) lb5_151
    · exact one_lt_of_lb5 157 10001 (by norm_num) lb5_157
    · exact one_lt_of_lb5 163 10001 (by norm_num) lb5_163
    · exact one_lt_of_lb5 167 10001 (by norm_num) lb5_167
    · exact one_lt_of_lb5 173 10001 (by norm_num) lb5_173
    · exact one_lt_of_lb5 179 10001 (by norm_num) lb5_179
    · exact one_lt_of_lb5 181 10001 (by norm_num) lb5_181
    · exact one_lt_of_lb5 191 10001 (by norm_num) lb5_191
    · exact one_lt_of_lb5 193 10001 (by norm_num) lb5_193
    · exact one_lt_of_lb5 197 10001 (by norm_num) lb5_197
    · exact one_lt_of_lb5 199 10001 (by norm_num) lb5_199
    · exact one_lt_of_lb5 211 10704 (by norm_num) lb5_211
    · exact one_lt_of_lb5 223 10001 (by norm_num) lb5_223
    · exact one_lt_of_lb5 227 10001 (by norm_num) lb5_227
    · exact one_lt_of_lb5 229 10001 (by norm_num) lb5_229
    · exact one_lt_of_lb5 233 10001 (by norm_num) lb5_233
    · exact one_lt_of_lb5 239 10001 (by norm_num) lb5_239
    · exact one_lt_of_lb5 241 10001 (by norm_num) lb5_241
    · exact one_lt_of_lb5 251 10001 (by norm_num) lb5_251
    · exact one_lt_of_lb5 257 10001 (by norm_num) lb5_257
    · exact one_lt_of_lb5 263 10001 (by norm_num) lb5_263

theorem half5_main (p : ℕ) (hp : p.Prime) (hp89 : 89 ≤ p) :
    (p ≠ 257 → IsNet0 5 p (5 * 1) (GFpoint 5 p 1 (halfPhi 5 p M5h D5h))) ∧
    ∀ Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod p),
      RowDesign 5 p 1 Φ (fun _ => M5h) → ∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
        ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
          < Real.sqrt (∑ c, ((cres (p ^ (5 * 1))
              ((GFpoint 5 p 1 Φ x c : ℤ) - (GFpoint 5 p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2) := by
  refine ⟨fun h257 => half5_net p hp ?_, fun Φ hrow x y hxy => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  · have hpos : 0 < ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) :=
      Real.rpow_pos_of_pos (by have := hp.pos; positivity) _
    have h1 := (half5_threshold.2 p hp hp89)
    have h2 := half_sep 5 p (by norm_num) hp (by omega) M5h M5h_odd
      (by rw [halfA2_M5h]; omega) Φ hrow x y hxy
    calc ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
        < halfLB2 p M5h * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
          exact lt_mul_left hpos h1
      _ ≤ _ := h2

/-! ## `tab:half`, `t = 0` for `s = 6, 8` -/

theorem half_tab_t0 :
    (∀ p ∈ ({211, 1009, 10007, 1000003} : Finset ℕ), ∃ D : Fin 6 → ℕ → Fin 6 → ℤ,
      IsNet0 6 p (6 * 1) (GFpoint 6 p 1 (halfPhi 6 p M6h D))) ∧
    (∀ p ∈ ({1009, 10007, 1000003} : Finset ℕ), ∃ D : Fin 8 → ℕ → Fin 8 → ℤ,
      IsNet0 8 p (8 * 1) (GFpoint 8 p 1 (halfPhi 8 p M8h D))) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨_, net6_211⟩
    · exact ⟨_, net6_1009⟩
    · exact ⟨_, net6_10007⟩
    · exact ⟨_, net6_1000003⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨_, net8_1009⟩
    · exact ⟨_, net8_10007⟩
    · exact ⟨_, net8_1000003⟩

end Z3NetHL.Proofs
