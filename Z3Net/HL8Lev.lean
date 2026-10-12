module
public import Mathlib
public import Z3Net.HL8Defs
public import Z3Net.HLSep

@[expose] public section

/-!
# Entry HL8, part 1: level-truncated admissibility

The net with `k` cell levels uses the column polynomials `gco d n ·` only for `n < k` (through
the gauge `UkZ`, whose entries have `x`-indices `< k`). We replace them at the levels `n ≥ k` by
`gcoT d n = T_{d,n} · y^n` with the integer
`T_{d,n} = ∏_c den(λ'_c) · ∏_{c ≠ d} (u_c - v_d)^(n+1)`:

* the net is unchanged (`HLpoint_gcoT`), and so is the design on the levels `< k`;
* the new leading coefficients `T_{d,n}` are units modulo `q` (products of point differences and
  denominators of `λ'`), so `HLAdmL s q (min k (s-1))` gives the full `HLAdm` for `gcoT`;
* the new design is integral on the new levels (`λ'_c T_{d,n} / (u_c - v_d)^(n+1) ∈ ℤ`), so the
  entry-HL theorems apply to `gcoT` with a doubled design `F2'` that agrees with `F2` below `k`;
  the relaxation uses only the levels `< min(k, s-1)`, so its conclusion is the same for `F2`.
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

variable {s : ℕ} (k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)

/-- `T_{d,n} = ∏_c den(λ'_c) · ∏_{c ≠ d} (u_c - v_d)^(n+1)`. -/
def Tt (d : Fin s) (n : ℕ) : ℤ :=
  (∏ c, ((lam c).den : ℤ)) * ∏ c ∈ univ.erase d, (u c - v d) ^ (n + 1)

/-- The column polynomials replaced at the levels `n ≥ k`. -/
def gcoT : Fin s → ℕ → ℕ → ℚ := fun d n n' =>
  if n < k then gco d n n' else if n' = n then ((Tt u v lam d n : ℤ) : ℚ) else 0

lemma UkZ_gcoT (q : ℕ) (_hk : 1 ≤ k) (d : Fin s) :
    UkZ q u v (gcoT k u v lam gco) k d = UkZ q u v gco k d := by
  funext i j
  have h : k - 1 - (j : ℕ) < k := by have := j.isLt; omega
  unfold UkZ UxZ gcoT
  simp only [h, ite_true]

lemma HLPhi_gcoT (q : ℕ) (hk : 1 ≤ k) (dg : Fin s → ℕ → ℚ) :
    HLPhi s q k u v lam (gcoT k u v lam gco) dg = HLPhi s q k u v lam gco dg := by
  funext c d r j
  unfold HLPhi
  rw [UkZ_gcoT k u v lam gco q hk d]

lemma HLpoint_gcoT (q : ℕ) (hk : 1 ≤ k) (dg : Fin s → ℕ → ℚ) :
    HLpoint s q k u v lam (gcoT k u v lam gco) dg = HLpoint s q k u v lam gco dg := by
  unfold HLpoint HLGen
  rw [HLPhi_gcoT k u v lam gco q hk dg]

lemma HLdes_gcoT (dg : Fin s → ℕ → ℚ) (x : ℕ) (hx : x < k) (c d : Fin s) :
    HLdes u v lam (gcoT k u v lam gco) dg x c d = HLdes u v lam gco dg x c d := by
  unfold HLdes gcoT
  simp only [hx, ite_true]

lemma ne_zero_of_gcd {q : ℕ} (hq : 2 ≤ q) {z : ℤ} (h : Int.gcd z q = 1) : z ≠ 0 := by
  rintro rfl
  simp at h
  omega

lemma Tt_coprime {q L : ℕ} (hq : HLAdmL s q L u v lam gco) (d : Fin s) (n : ℕ) :
    IsCoprime (Tt u v lam d n) (q : ℤ) := by
  obtain ⟨_, hpts, hlam, _⟩ := hq
  unfold Tt
  refine IsCoprime.mul_left (IsCoprime.prod_left fun c _ => ?_) (IsCoprime.prod_left fun c hc => ?_)
  · exact Nat.isCoprime_iff_coprime.mpr (hlam c).2
  · refine IsCoprime.pow_left ?_
    have := hpts c 1 d 0 (by simp)
    simp only [splitPt] at this
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using this)

lemma adm_gcoT {q : ℕ} (hq : HLAdmL s q (min k (s - 1)) u v lam gco) :
    HLAdm s q u v lam (gcoT k u v lam gco) := by
  refine ⟨hq.1, hq.2.1, hq.2.2.1, fun d n hn => ?_⟩
  by_cases hnk : n < k
  · simp only [gcoT, hnk, ite_true]
    exact hq.2.2.2 d n (lt_min hnk hn)
  · simp only [gcoT, hnk, ite_false, ite_true, Rat.num_intCast, Rat.den_intCast]
    exact ⟨Int.isCoprime_iff_gcd_eq_one.mp (Tt_coprime u v lam gco hq d n), Nat.coprime_one_left _⟩

lemma den_gcoT {q : ℕ} (dg : Fin s → ℕ → ℚ) (hden : HLDen s q gco dg) :
    HLDen s q (gcoT k u v lam gco) dg := by
  refine ⟨fun d n hn n' hn' => ?_, hden.2⟩
  by_cases hnk : n < k
  · simp only [gcoT, hnk, ite_true]
    exact hden.1 d n hn n' hn'
  · simp only [gcoT, hnk, ite_false]
    split_ifs
    · simp
    · simp

/-- The replaced design is integral on the new levels. -/
lemma des_gcoT_int {q : ℕ} (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (dg : Fin s → ℕ → ℚ)
    (F2 : ℕ → Fin s → Fin s → ℤ) (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (x : ℕ) (c d : Fin s) : ∃ z : ℤ, 2 * HLdes u v lam (gcoT k u v lam gco) dg x c d = z := by
  by_cases hx : s - 1 ≤ x
  · exact ⟨0, by simp [HLdes, hx]⟩
  by_cases hcd : c = d
  · refine ⟨F2 x c d, ?_⟩
    rw [← hF2 x c d]
    simp [HLdes, hx, hcd]
  by_cases hxk : x < k
  · exact ⟨F2 x c d, by rw [HLdes_gcoT k u v lam gco dg x hxk, hF2]⟩
  -- the new level: `λ'_c T_{d,x} y_cd^(x+1)`
  have hsum : ∑ n' ∈ range (x + 1), gcoT k u v lam gco d x n' * yQ u v c d ^ (n' + 1) =
      ((Tt u v lam d x : ℤ) : ℚ) * yQ u v c d ^ (x + 1) := by
    rw [Finset.sum_eq_single x]
    · simp [gcoT, hxk]
    · intro n' _ hn'; simp [gcoT, hxk, hn']
    · intro h; simp at h
  have hdes : HLdes u v lam (gcoT k u v lam gco) dg x c d =
      lam c * (((Tt u v lam d x : ℤ) : ℚ) * yQ u v c d ^ (x + 1)) := by
    simp only [HLdes, hx, ite_false, hcd, hsum]
  have hθ : (u c - v d : ℤ) ≠ 0 := by
    have := hq.2.1 c 1 d 0 (by simp)
    simp only [splitPt] at this
    exact ne_zero_of_gcd hq.1 (by simpa using this)
  have hθQ : ((u c - v d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hθ
  have hc : c ∈ univ.erase d := mem_erase.mpr ⟨hcd, mem_univ c⟩
  have hc' : c ∈ (univ : Finset (Fin s)) := mem_univ c
  refine ⟨2 * (lam c).num * (∏ c' ∈ univ.erase c, ((lam c').den : ℤ)) *
      ∏ c' ∈ (univ.erase d).erase c, (u c' - v d) ^ (x + 1), ?_⟩
  rw [hdes]
  unfold Tt
  rw [← Finset.mul_prod_erase _ _ hc, ← Finset.mul_prod_erase _ _ hc']
  have hnum : lam c * ((lam c).den : ℚ) = ((lam c).num : ℚ) := Rat.mul_den_eq_num (lam c)
  simp only [yQ]
  push_cast
  have hθp : ((u c : ℚ) - v d) ^ (x + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hθ)
  rw [inv_pow]
  calc 2 * (lam c * ((((lam c).den : ℚ) * ∏ c' ∈ univ.erase c, ((lam c').den : ℚ)) *
        (((u c : ℚ) - v d) ^ (x + 1) * ∏ c' ∈ (univ.erase d).erase c, ((u c' : ℚ) - v d) ^ (x + 1)) *
        (((u c : ℚ) - v d) ^ (x + 1))⁻¹))
      = 2 * (lam c * ((lam c).den : ℚ)) * (∏ c' ∈ univ.erase c, ((lam c').den : ℚ)) *
        (∏ c' ∈ (univ.erase d).erase c, ((u c' : ℚ) - v d) ^ (x + 1)) *
        (((u c : ℚ) - v d) ^ (x + 1) * (((u c : ℚ) - v d) ^ (x + 1))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hθp, hnum]; ring

/-! ## The truncated theorems -/

theorem HL_row0_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdmL s q (min k (s - 1)) u v lam gco)
    (hden : HLDen s q gco dg) (hk : 1 ≤ k) (c d : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0)
    (j : Fin k) :
    HLPhi s q k u v lam gco dg c d r j = qr q (HLdes u v lam gco dg (k - 1 - (j : ℕ)) c d) := by
  have h := HL_row0 s q k u v lam (gcoT k u v lam gco) dg hs (adm_gcoT k u v lam gco hq)
    (den_gcoT k u v lam gco dg hden) hk c d r hr j
  rwa [HLPhi_gcoT k u v lam gco q hk dg,
    HLdes_gcoT k u v lam gco dg _ (by have := j.isLt; omega)] at h

theorem HL_net_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hk : 1 ≤ k) :
    Z3NetHL.IsNet0 s q (s * k) (HLpoint s q k u v lam gco dg) := by
  have h := HL_net s q k u v lam (gcoT k u v lam gco) dg hs (adm_gcoT k u v lam gco hq) hk
  rwa [HLpoint_gcoT k u v lam gco q hk dg] at h

lemma sig2_congr (F2 F2' : ℕ → Fin s → Fin s → ℤ) (k : ℕ) (hF : ∀ x c d, x < k → F2' x c d = F2 x c d)
    (hk : 1 ≤ k) (E : Fin s → ℤ) (J : Fin s → ℕ) (hJ : ∀ d, J d < k) (c : Fin s) :
    sig2 F2' E J c = sig2 F2 E J c := by
  unfold sig2
  refine sum_congr rfl fun d _ => ?_
  rw [hF 0 c d (by omega)]
  congr 2
  refine sum_congr rfl fun x hx => ?_
  rw [mem_Icc] at hx
  exact hF x c d (lt_of_le_of_lt hx.2 (hJ d))

theorem HL_relax_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) := by
  have hint := des_gcoT_int k u v lam gco hq dg F2 hF2
  choose f hf using hint
  set F2' : ℕ → Fin s → Fin s → ℤ := fun x c d => if x < k then F2 x c d else f x c d with hF2'
  have hF2'' : ∀ x c d, 2 * HLdes u v lam (gcoT k u v lam gco) dg x c d = F2' x c d := by
    intro x c d
    by_cases hx : x < k
    · simp only [hF2', hx, ite_true]
      rw [HLdes_gcoT k u v lam gco dg x hx, hF2]
    · simp only [hF2', hx, ite_false]
      exact hf x c d
  have hagree : ∀ x c d, x < k → F2' x c d = F2 x c d := fun x c d hx => by simp [hF2', hx]
  have h := HL_relax s q k u v lam (gcoT k u v lam gco) dg F2' hs (adm_gcoT k u v lam gco hq)
    (den_gcoT k u v lam gco dg hden) hq7 hF2'' hk x y hxy
  rw [HLpoint_gcoT k u v lam gco q hk dg] at h
  rcases h with h | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
  · exact Or.inl h
  · refine Or.inr ⟨E, J, Δ, hE, hne, hJ, fun c => ?_, hΔ, hbd⟩
    rw [← sig2_congr F2 F2' k hagree hk E J (fun d => lt_of_lt_of_le (hJ d) (min_le_left _ _)) c]
    exact hdvd c

end

end Z3NetHL.Proofs
