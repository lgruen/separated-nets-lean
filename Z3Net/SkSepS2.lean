module
public import Mathlib
public import Z3Net.S2Defs
public import Z3Net.SkSepGraph

@[expose] public section

/-!
# Entry S2, separation core (`thm:S2`, proof "Separation"; `def:S2`)

For a graph form with the skeleton digits of `def:S2` (`IsS2skel`, `s ≥ 4`, `k ≥ 1`) and any `L`
such that every nonzero `(x, z) ∈ ℤ^(r+2)` with `z ≡ A x (mod p)` has maximum norm `≥ L`
(`A = S2A s p`), two distinct points satisfy `(L - F - 1)² f² ≤ N² δ²` (`F = Fs s`, provided
`|D_1|, |D_2| ≤ F - 1`). Proof as in the paper: with the floor changes `ξ = ξ_{·,1}` of
`lem:skelred`(ii), `u = (a_x, a_{z1} - ∑_{D1} ξ_{x_d} - ξ_{z2}, a_{z2} - ∑_{D2} ξ_{x_d} + ξ_{z1})`
lies in `Λ_A` with `|u|_∞ ≤ |a|_∞ + F`; `u = 0` is excluded by the skew signs of the faults.
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

open Z3NetKN.Geom (vz)

lemma xi_abs (x a : ℤ) (h : x = 0 ∨ x = a.sign) : |x| ≤ 1 := by
  rcases h with rfl | rfl
  · simp
  · rcases lt_trichotomy a 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; simp
    · subst h; simp
    · rw [Int.sign_eq_one_of_pos h]; simp

lemma xi_zero (x a : ℤ) (h : x = 0 ∨ x = a.sign) (ha : a = 0) : x = 0 := by
  rcases h with h | h <;> simp [h, ha]

lemma sign_cases (a : ℤ) : a.sign = -1 ∧ a < 0 ∨ a.sign = 0 ∧ a = 0 ∨ a.sign = 1 ∧ 0 < a := by
  rcases lt_trichotomy a 0 with h | h | h
  · exact Or.inl ⟨Int.sign_eq_neg_one_of_neg h, h⟩
  · exact Or.inr (Or.inl ⟨by simp [h], h⟩)
  · exact Or.inr (Or.inr ⟨Int.sign_eq_one_of_pos h, h⟩)

/-- The skew-sign step of the proof of `thm:S2`. -/
lemma skew (a1 a2 x1 x2 : ℤ) (h1 : x1 = 0 ∨ x1 = a1.sign) (h2 : x2 = 0 ∨ x2 = a2.sign)
    (e1 : a1 = x2) (e2 : a2 = -x1) : a1 = 0 ∧ a2 = 0 := by
  have s1 := sign_cases a1
  have s2 := sign_cases a2
  omega

/-- Contribution of block `d` to the change of row `k` of coordinate `z`. -/
def rowBlk {s p k : ℕ} (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (z : Fin s) (v w : Fin (s * k + (s - 2)) → ZMod p) (d : ℕ) : ZMod p :=
  ∑ l ∈ range (depthN (s - 2) k d), ent (C z) k (skOff (s - 2) k d + l) *
    (vz w (skOff (s - 2) k d + l) - vz v (skOff (s - 2) k d + l))

lemma sum_beta_bound (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (ξ : ℕ → ℤ)
    (hξ : ∀ d, d < n → |ξ d| ≤ 1) :
    |∑ d ∈ range n, (if P d then (1 : ℤ) else 0) * ξ d| ≤ (#{x ∈ range n | P x} : ℕ) := by
  calc |∑ d ∈ range n, (if P d then (1 : ℤ) else 0) * ξ d|
      ≤ ∑ d ∈ range n, |(if P d then (1 : ℤ) else 0) * ξ d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ range n, (if P d then (1 : ℤ) else 0) := by
        refine sum_le_sum fun d hd => ?_
        split_ifs
        · rw [one_mul]; exact hξ d (mem_range.mp hd)
        · simp
    _ = _ := by rw [Finset.sum_boole]

lemma betaD_zero (D1 : Finset ℕ) (d : ℕ) : betaD D1 0 d = if d ∈ D1 then 1 else 0 := by
  simp [betaD]

lemma betaD_one (D1 : Finset ℕ) (d : ℕ) : betaD D1 1 d = if d ∉ D1 then 1 else 0 := by
  unfold betaD; simp only [Fin.isValue, Fin.val_one, one_ne_zero, if_false]; split_ifs <;> simp_all

/-- Total accessor. -/
def totN {s : ℕ} (f : Fin s → ℤ) (d : ℕ) : ℤ := if h : d < s then f ⟨d, h⟩ else 0

end SkSep

open SkSep Z3NetKN.Geom

/-- **Separation core of `thm:S2`** with an abstract lattice minimum `L`. -/
theorem S2_core (s p k L : ℕ) (hp : p.Prime) (hs : 4 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : ((range (s - 2)).filter (· ∈ D1)).card + 1 ≤ Fs s)
    (hD2 : ((range (s - 2)).filter (· ∉ D1)).card + 1 ≤ Fs s)
    (hL : ∀ (x : Fin (s - 2) → ℤ) (z : Fin 2 → ℤ),
      (∀ i, (p : ℤ) ∣ z i - ∑ d : Fin (s - 2), S2A s p i (d : ℕ) * x d) → ¬(x = 0 ∧ z = 0) →
        (L : ℤ) ≤ |z 0| ∨ (L : ℤ) ≤ |z 1| ∨ ∃ d, (L : ℤ) ≤ |x d|)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    (L - Fs s - 1) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
      torusDist2 (p ^ (s * k + (s - 2))) (digPoint p (s * k + (s - 2)) C v)
        (digPoint p (s * k + (s - 2)) C w) := by
  have hp2 := hp.two_le
  have : NeZero p := ⟨by omega⟩
  have hr : s - 2 ≤ s := Nat.sub_le _ _
  have hkm : k + 1 ≤ s * k + (s - 2) := by nlinarith
  have hmk : s * k + (s - 2) - (k + 1) = (s - 1) * k + s - 3 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 4 := ⟨s - 4, by omega⟩
    have e1 : (t + 4) * k = t * k + 4 * k := by ring
    have e2 : (t + 4 - 1) * k = t * k + 3 * k := by
      rw [show t + 4 - 1 = t + 3 by omega]; ring
    omega
  rw [← hmk]
  rcases Nat.lt_or_ge L (Fs s + 2) with hLF | hLF
  · rw [show L - Fs s - 1 = 0 by omega]; simp
  apply skelred_sep p _ k (L - Fs s) hp2 hkm C v w
  by_contra hcon
  push Not at hcon
  set a := aDiff p k C v w with ha
  have hlt : ∀ c, |a c| < ((L - Fs s : ℕ) : ℤ) := fun c => hcon c
  -- `L ≤ p` (the lattice vector `(p, …, p, 0, 0)`)
  have hLp : L ≤ p := by
    have h := hL (fun _ => (p : ℤ)) 0 (fun i => by
      simp only [Pi.zero_apply, zero_sub, dvd_neg]
      exact Finset.dvd_sum fun d _ => dvd_mul_left _ _)
      (fun h => by
        have := congrFun h.1 ⟨0, by omega⟩
        simp only [Pi.zero_apply, Nat.cast_eq_zero] at this; omega)
    simp only [Pi.zero_apply, abs_zero, Nat.abs_cast] at h
    rcases h with h | h | ⟨_, h⟩ <;> omega
  have hFp : 1 ≤ Fs s := by unfold Fs; omega
  have hap : ∀ c, |a c| < p := fun c => by have := hlt c; push_cast [Nat.cast_sub (by omega : Fs s ≤ L)] at this; omega
  -- carries
  have hcar : ∀ c : Fin s, ∃ x : ℤ,
      ((finePos p (s * k + (s - 2)) k C w c / p ^ 1 : ℕ) : ℤ) - (finePos p (s * k + (s - 2)) k C v c / p ^ 1 : ℕ)
        ≡ x [ZMOD (p : ℤ) ^ (k + 1 - 1)] ∧ (x = 0 ∨ x = Int.sign (a c)) := by
    intro c
    obtain ⟨ξ, h1, -⟩ := skelred_carry p k (finePos p (s * k + (s - 2)) k C v c)
      (finePos p (s * k + (s - 2)) k C w c) hp2 (finePos_lt k hkm C v c) (finePos_lt k hkm C w c) (hap c)
    exact ⟨ξ 1, h1 1 le_rfl hk⟩
  choose ξ hξ using hcar
  have hξcast : ∀ c, ((ξ c : ℤ) : ZMod p) = vz (C c *ᵥ w) (k - 1) - vz (C c *ᵥ v) (k - 1) := by
    intro c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (p : ℤ) (by omega : k + 1 - 1 ≠ 0)) (hξ c).1
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [← this, ← ZMod.natCast_mod (finePos p (s * k + (s - 2)) k C w c / p ^ 1) p,
      ← ZMod.natCast_mod (finePos p (s * k + (s - 2)) k C v c / p ^ 1) p,
      finePos_div_mod k hk hkm, finePos_div_mod k hk hkm]
  -- totals
  set aN := totN a with haN
  set ξN := totN ξ with hξN
  have haN' : ∀ d (hd : d < s), aN d = a ⟨d, hd⟩ := fun d hd => by simp [haN, totN, hd]
  have hξN' : ∀ d (hd : d < s), ξN d = ξ ⟨d, hd⟩ := fun d hd => by simp [hξN, totN, hd]
  have hdigk : ∀ d (hd : d < s - 2), vz w (skOff (s - 2) k d + k) - vz v (skOff (s - 2) k d + k) =
      ((aN d : ℤ) : ZMod p) := by
    intro d hd
    have hdep : k < skDepth (s - 2) k (⟨d, by omega⟩ : Fin s) := by
      unfold skDepth; simp only; rw [if_pos hd]; omega
    rw [haN' d (by omega), ha, aDiff_cast k hkm, graph_digit hr hC.1 w _ k hdep,
      graph_digit hr hC.1 v _ k hdep]
  have hdigk1 : ∀ d (hd : d < s), vz w (skOff (s - 2) k d + (k - 1)) - vz v (skOff (s - 2) k d + (k - 1)) =
      ((ξN d : ℤ) : ZMod p) := by
    intro d hd
    have hdep : k - 1 < skDepth (s - 2) k (⟨d, hd⟩ : Fin s) := by
      unfold skDepth; simp only; split_ifs <;> omega
    rw [hξN' d hd, hξcast, graph_digit hr hC.1 w _ _ hdep, graph_digit hr hC.1 v _ _ hdep]
  -- the skeleton rows
  have hrow : ∀ z : Fin s, ((a z : ℤ) : ZMod p) = ∑ d ∈ range s, rowBlk C z v w d := by
    intro z
    rw [ha, aDiff_cast k hkm, row_diff hr _ v w k (by omega)]
    exact Fin.sum_univ_eq_sum_range (fun d => rowBlk C z v w d) s
  have hent : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d (hd : d < s), ∀ l < depthN (s - 2) k d,
      ent (C z) k (skOff (s - 2) k d + l) =
        sk2Coef (s - 2) k (fun i d => ((S2A s p i d : ℤ) : ZMod p))
          (fun i d => ((betaD D1 i d : ℤ) : ZMod p)) ![1, -1] 0 i d l :=
    fun i z hz d hd l hl => hC.2 i z ⟨d, hd⟩ hz l hl
  have blk_full : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d < s - 2 →
      rowBlk C z v w d = ((S2A s p i d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 i d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p) := by
    intro i z hz d hd
    have hdep : depthN (s - 2) k d = k - 1 + 1 + 1 := by unfold depthN; rw [if_pos hd]; omega
    unfold rowBlk
    rw [hdep, sum_range_succ, sum_range_succ, sum_eq_zero (fun l hl => by
      simp only [mem_range] at hl
      rw [hent i z hz d (by omega) l (by rw [hdep]; omega)]
      simp only [sk2Coef, if_pos hd, if_neg (show l ≠ k by omega), if_neg (show l + 1 ≠ k by omega),
        zero_mul]), zero_add,
      hent i z hz d (by omega) _ (by rw [hdep]; omega), hent i z hz d (by omega) _ (by rw [hdep]; omega)]
    simp only [sk2Coef, if_pos hd, if_neg (show k - 1 ≠ k by omega), if_pos (show k - 1 + 1 = k by omega),
      if_pos (show k - 1 + 1 = k by omega)]
    rw [hdigk1 d (by omega), show k - 1 + 1 = k by omega, hdigk d hd]
    ring
  have blk_own : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d = s - 2 + (i : ℕ) →
      rowBlk C z v w d = 0 := by
    intro i z hz d hdi
    unfold rowBlk
    refine sum_eq_zero fun l hl => ?_
    simp only [mem_range] at hl
    have hd : d < s := by omega
    rw [hent i z hz _ hd l hl]
    simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_pos hdi, Pi.zero_apply]
    split_ifs <;> simp
  have blk_oth : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d < s → s - 2 ≤ d →
      d ≠ s - 2 + (i : ℕ) → rowBlk C z v w d = (![(1 : ZMod p), -1] i) * ((ξN d : ℤ) : ZMod p) := by
    intro i z hz d hd hd2 hdi
    have hdep : depthN (s - 2) k d = k - 1 + 1 := by unfold depthN; rw [if_neg (by omega)]; omega
    unfold rowBlk
    rw [hdep, sum_range_succ, sum_eq_zero (fun l hl => by
      simp only [mem_range] at hl
      rw [hent i z hz d hd l (by rw [hdep]; omega)]
      simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_neg hdi,
        if_neg (show l + 1 ≠ k by omega), zero_mul]), zero_add,
      hent i z hz d hd _ (by rw [hdep]; omega)]
    simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_neg hdi, if_pos (show k - 1 + 1 = k by omega)]
    rw [hdigk1 d hd]
  have hsplit : ∀ z : Fin s, ∑ d ∈ range s, rowBlk C z v w d =
      ∑ d ∈ range (s - 2), rowBlk C z v w d + rowBlk C z v w (s - 2) + rowBlk C z v w (s - 1) := by
    intro z
    rw [show s - 1 = s - 2 + 1 by omega, ← sum_range_succ, ← sum_range_succ,
      show s - 2 + 1 + 1 = s by omega]
  set z1 : Fin s := ⟨s - 2, by omega⟩
  set z2 : Fin s := ⟨s - 1, by omega⟩
  have hz1 : s - 2 < s := by omega
  have hz2 : s - 1 < s := by omega
  have R0 : ((aN (s - 2) : ℤ) : ZMod p) =
      ∑ d ∈ range (s - 2), (((S2A s p 0 d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 0 d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p)) + ((ξN (s - 1) : ℤ) : ZMod p) := by
    rw [haN' _ hz1, hrow ⟨_, hz1⟩, hsplit,
      sum_congr rfl fun d hd => blk_full 0 ⟨_, hz1⟩ (by simp) d (mem_range.mp hd),
      blk_own 0 ⟨_, hz1⟩ (by simp) (s - 2) (by simp),
      blk_oth 0 ⟨_, hz1⟩ (by simp) (s - 1) hz2 (by omega) (by simp <;> omega)]
    simp
  have R1 : ((aN (s - 1) : ℤ) : ZMod p) =
      ∑ d ∈ range (s - 2), (((S2A s p 1 d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 1 d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p)) - ((ξN (s - 2) : ℤ) : ZMod p) := by
    have e : ((⟨s - 1, hz2⟩ : Fin s) : ℕ) = s - 2 + ((1 : Fin 2) : ℕ) := by simp <;> omega
    rw [haN' _ hz2, hrow ⟨_, hz2⟩, hsplit,
      sum_congr rfl fun d hd => blk_full 1 ⟨_, hz2⟩ e d (mem_range.mp hd),
      blk_own 1 ⟨_, hz2⟩ e (s - 1) (by simp <;> omega),
      blk_oth 1 ⟨_, hz2⟩ e (s - 2) hz1 le_rfl (by simp <;> omega)]
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  -- bounds on `a` and `ξ`
  have hM0 : ((L - Fs s : ℕ) : ℤ) = (L : ℤ) - Fs s := by push_cast [Nat.cast_sub (by omega : Fs s ≤ L)]; ring
  have haB : ∀ d, d < s → |aN d| ≤ (L : ℤ) - Fs s - 1 := by
    intro d hd; have := hlt ⟨d, hd⟩; rw [hM0] at this; rw [haN' d hd]; omega
  have hsg : ∀ d, d < s → ξN d = 0 ∨ ξN d = (aN d).sign := by
    intro d hd; rw [hξN' d hd, haN' d hd]; exact (hξ _).2
  have hξB : ∀ d, d < s → |ξN d| ≤ 1 := fun d hd => xi_abs _ _ (hsg d hd)
  have hξB' : ∀ d, d < s - 2 → |ξN d| ≤ 1 := fun d hd => hξB d (by omega)
  have hcard0 : |∑ d ∈ range (s - 2), betaD D1 0 d * ξN d| ≤ (Fs s : ℤ) - 1 := by
    have := sum_beta_bound (s - 2) (· ∈ D1) ξN hξB'
    rw [sum_congr rfl fun d _ => by rw [betaD_zero]]
    have h1 : ((#{x ∈ range (s - 2) | x ∈ D1} : ℕ) : ℤ) + 1 ≤ Fs s := by exact_mod_cast hD1
    linarith
  have hcard1 : |∑ d ∈ range (s - 2), betaD D1 1 d * ξN d| ≤ (Fs s : ℤ) - 1 := by
    have := sum_beta_bound (s - 2) (· ∉ D1) ξN hξB'
    rw [sum_congr rfl fun d _ => by rw [betaD_one]]
    have h1 : ((#{x ∈ range (s - 2) | x ∉ D1} : ℕ) : ℤ) + 1 ≤ Fs s := by exact_mod_cast hD2
    linarith
  -- the lattice vector `u`
  set u0 : ℤ := aN (s - 2) - ∑ d ∈ range (s - 2), betaD D1 0 d * ξN d - ξN (s - 1) with hu0
  set u1 : ℤ := aN (s - 1) - ∑ d ∈ range (s - 2), betaD D1 1 d * ξN d + ξN (s - 2) with hu1
  have hdiv : ∀ i : Fin 2, (p : ℤ) ∣ ![u0, u1] i - ∑ d : Fin (s - 2), S2A s p i (d : ℕ) * aN d := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have e := Fin.sum_univ_eq_sum_range (fun d => S2A s p i d * aN d) (s - 2)
    rw [e]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hu0]; push_cast
      rw [R0, sum_add_distrib]; ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hu1]; push_cast
      rw [R1, sum_add_distrib]; ring
  by_cases hzero : (fun d : Fin (s - 2) => aN d) = 0 ∧ ![u0, u1] = 0
  · have hx0 : ∀ d, d < s - 2 → aN d = 0 := fun d hd => by
      have := congrFun hzero.1 ⟨d, hd⟩; simpa using this
    have hξ0 : ∀ d, d < s - 2 → ξN d = 0 := fun d hd => xi_zero _ _ (hsg d (by omega)) (hx0 d hd)
    have hs0 : ∀ i : Fin 2, ∑ d ∈ range (s - 2), betaD D1 i d * ξN d = 0 := fun i =>
      sum_eq_zero fun d hd => by rw [hξ0 d (mem_range.mp hd), mul_zero]
    have e0 : u0 = 0 := by have := congrFun hzero.2 0; simpa using this
    have e1 : u1 = 0 := by have := congrFun hzero.2 1; simpa using this
    rw [hu0, hs0 0] at e0
    rw [hu1, hs0 1] at e1
    obtain ⟨h1, h2⟩ := skew (aN (s - 2)) (aN (s - 1)) (ξN (s - 2)) (ξN (s - 1)) (hsg _ hz1) (hsg _ hz2)
      (by linarith) (by linarith)
    obtain ⟨c, hc⟩ := ne_zero_of_ne hr hC.1 hkm v w hvw
    apply hc
    have : aN c = 0 := by
      rcases Nat.lt_or_ge (c : ℕ) (s - 2) with h | h
      · exact hx0 c h
      · rcases (show (c : ℕ) = s - 2 ∨ (c : ℕ) = s - 1 by omega) with h' | h'
        · rw [h']; exact h1
        · rw [h']; exact h2
    rw [haN' c c.isLt] at this
    exact this
  · have hb0 := hcard0
    have hb1 := hcard1
    have a1 := abs_le.mp (haB (s - 2) hz1)
    have a2 := abs_le.mp (haB (s - 1) hz2)
    have x1 := abs_le.mp (hξB (s - 2) hz1)
    have x2 := abs_le.mp (hξB (s - 1) hz2)
    have c0 := abs_le.mp hb0
    have c1 := abs_le.mp hb1
    rcases hL (fun d => aN d) ![u0, u1] hdiv hzero with h | h | ⟨d, h⟩
    · simp only [Matrix.cons_val_zero] at h
      have : |u0| < L := abs_lt.mpr ⟨by rw [hu0]; linarith, by rw [hu0]; linarith⟩
      linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      have : |u1| < L := abs_lt.mpr ⟨by rw [hu1]; linarith, by rw [hu1]; linarith⟩
      linarith
    · have := haB d (by omega)
      have : (Fs s : ℤ) ≥ 1 := by exact_mod_cast hFp
      linarith

end Z3NetF.Proofs
