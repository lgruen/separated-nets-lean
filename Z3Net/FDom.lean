module
public import Z3Net.FBasic
public import Z3Net.SUSep

@[expose] public section

/-!
# Entry F, part 12: `prop:D` (diagonal dominance) for an arbitrary design

Every `b_i` of `lem:Ss` is `max(0, |e_i q + t| - jit_i)` for a representative `t ≡ σ_i (mod q)`,
`|t| < q` (`bval_spec`); with dominance every moving coordinate is backward with `|σ_i| ≤ 2a`,
and the own-axis step has `|σ_i| = α_i ≤ a`; then entry U's abstract `key_sym` applies.
-/

namespace Z3NetF.Proofs

open Finset

noncomputable section

lemma bval_spec {s : ℕ} (q : ℕ) (hq : 0 < q) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ)
    (j : Fin s → ℕ) (i : Fin s) :
    ∃ t : ℤ, t ≡ Z3NetF.sigma F L e j i [ZMOD q] ∧ |t| < q ∧
      Z3NetF.bval q F L e j i = max 0 (|e i * q + t| - if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1) := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set σ := Z3NetF.sigma F L e j i
  set jit : ℤ := if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1
  have hδ0 : 0 ≤ σ % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have hδ1 : σ % (q : ℤ) < q := Int.emod_lt_of_pos _ hq'
  have hmod : σ % (q : ℤ) ≡ σ [ZMOD q] := Int.mod_modEq _ _
  unfold Z3NetF.bval
  simp only []
  by_cases h0 : σ % (q : ℤ) = 0
  · refine ⟨0, ?_, show |(0 : ℤ)| < q by simpa using hq', ?_⟩
    · rw [← h0]; exact hmod
    · rw [if_pos h0, add_zero]
  · rw [if_neg h0]
    rcases min_choice (max 0 (|e i * q + σ % (q : ℤ)| - jit)) (max 0 (|e i * q + σ % (q : ℤ) - q| - jit)) with h | h
    · refine ⟨σ % (q : ℤ), hmod, by rw [abs_lt]; constructor <;> omega, ?_⟩
      rw [h]
    · refine ⟨σ % (q : ℤ) - q, ?_, by rw [abs_lt]; constructor <;> omega, ?_⟩
      · exact (Int.ModEq.sub_right _ hmod).trans (by simp [Int.ModEq])
      · rw [h, add_sub_assoc]

lemma bval_nonneg {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ)
    (j : Fin s → ℕ) (i : Fin s) : 0 ≤ Z3NetF.bval q F L e j i := by
  unfold Z3NetF.bval
  simp only []
  split_ifs <;> first | exact le_max_left _ _ | exact le_min (le_max_left _ _) (le_max_left _ _)

section dom

variable {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (α : Fin s → ℕ) (a : ℕ)

lemma Msum_diag (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0) (c : Fin s)
    (J : ℕ) : Z3NetF.Msum F J c c = -(α c : ℤ) := by
  unfold Z3NetF.Msum
  rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun t _ => hdiag (t + 1) c (by omega)), zero_add, h0]

lemma off_bound (hLs : L ≤ s - 1) (hL : 1 ≤ L)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Z3NetF.Msum F j c d).natAbs) ≤ α c)
    (i : Fin s) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (j : Fin s → ℕ) :
    |∑ d ∈ univ.erase i, e d * Z3NetF.Msum F (min (j d) (L - 1)) i d| ≤ (α i : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hd := hdom i
  rw [Finset.filter_ne'] at hd
  have hd' : ((∑ d ∈ univ.erase i, (range (s - 1)).sup (fun j => (Z3NetF.Msum F j i d).natAbs) : ℕ) : ℤ)
      ≤ (α i : ℤ) := by exact_mod_cast hd
  refine le_trans ?_ hd'
  push_cast
  refine Finset.sum_le_sum fun d _ => ?_
  rw [abs_mul]
  have h1 : |e d| ≤ 1 := abs_le.mpr ⟨(he d).1, (he d).2⟩
  have h2 : |Z3NetF.Msum F (min (j d) (L - 1)) i d| ≤
      (((range (s - 1)).sup fun j => (Z3NetF.Msum F j i d).natAbs : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.le_sup (f := fun j => (Z3NetF.Msum F j i d).natAbs)
      (mem_range.mpr (by omega : min (j d) (L - 1) < s - 1))
  calc |e d| * |Z3NetF.Msum F (min (j d) (L - 1)) i d| ≤ 1 * |Z3NetF.Msum F (min (j d) (L - 1)) i d| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h2

lemma sigma_split' (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (i : Fin s) (e : Fin s → ℤ) (j : Fin s → ℕ) :
    Z3NetF.sigma F L e j i = -(e i * (α i : ℤ)) +
      ∑ d ∈ univ.erase i, e d * Z3NetF.Msum F (min (j d) (L - 1)) i d := by
  unfold Z3NetF.sigma
  rw [← Finset.add_sum_erase _ _ (mem_univ i), Msum_diag F α h0 hdiag]; ring

theorem D_LB_core (hL : 1 ≤ L) (hLs : L ≤ s - 1)
    (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Z3NetF.Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (q k : ℕ) (hq : 5 * a + 4 ≤ q) :
    ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 ∧
      ∀ e j, Z3NetF.IsConfig k e j → ((q : ℤ) - a) ^ 2 ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2 := by
  have hqz : (5 : ℤ) * a + 4 ≤ q := by exact_mod_cast hq
  have ha0 : (0 : ℤ) ≤ a := by positivity
  refine ⟨by nlinarith, fun e j hcfg => ?_⟩
  obtain ⟨he, hne, -⟩ := hcfg
  have hq0 : 0 < q := by omega
  choose t ht1 ht2 ht3 using fun i => bval_spec q hq0 F L e j i
  refine Z3NetU.Proofs.key_sym s (q : ℤ) (a : ℤ) ha0 hqz e he hne (fun i => Z3NetF.sigma F L e j i) t
    (fun i => Z3NetF.bval q F L e j i) ?_ ?_ (fun i => ⟨ht1 i, ht2 i⟩)
    (fun i => bval_nonneg q F L e j i) ?_
  · intro i hi
    rw [sigma_split' F L α h0 hdiag]
    have hR := off_bound F L α hLs hL hdom i e he j
    have ha' : (α i : ℤ) ≤ a := by exact_mod_cast ha i
    set R := ∑ d ∈ univ.erase i, e d * Z3NetF.Msum F (min (j d) (L - 1)) i d
    rw [abs_le] at hR
    rcases Z3NetU.Proofs.unit_sign (e i) (he i).1 (he i).2 hi with h | h <;> rw [h] <;> constructor
    · linarith
    · rw [abs_le]; constructor <;> linarith
    · linarith
    · rw [abs_le]; constructor <;> linarith
  · intro i hi hoth
    rw [sigma_split' F L α h0 hdiag, Finset.sum_eq_zero (fun d hd => by
      rw [hoth d (Finset.ne_of_mem_erase hd), zero_mul]), add_zero, abs_neg, abs_mul]
    have ha' : (α i : ℤ) ≤ a := by exact_mod_cast ha i
    rcases Z3NetU.Proofs.unit_sign (e i) (he i).1 (he i).2 hi with h | h <;> rw [h] <;> simpa using ha'
  · intro i
    rw [ht3 i]
    split_ifs with hj
    · simp only [sub_zero]; exact le_max_right _ _
    · exact le_max_right _ _

end dom

end

end Z3NetF.Proofs
