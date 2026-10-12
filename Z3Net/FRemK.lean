module
public import Z3Net.FDefs

@[expose] public section

/-!
# Entry F, stage 6: `rem:K`, the first-order expansion of the relaxation of `lem:Ss`

For `q` large compared with `S = max |σ_i|`, every `b_i` is explicit (`bv_small`, `bv_back`): a
still or forward coordinate has `0 ≤ b_i ≤ |σ_i|`, a backward one has `b_i = q - |σ_i| - jit_i`.
So a step without backward coordinate has `∑ b_i² ≤ s S²` (`remK_bad`), a step with two has
`∑ b_i² ≥ q²`, and a step with one has `∑ b_i² = (q - |σ_b| - jit_b)² + O(1)`; `K` is the largest
cost `|σ_b| + jit_b` (`remK_good`).
-/

namespace Z3NetF.Proofs.RemK

open Finset Z3NetF

/-! ## The `b_i` for large `q` -/

lemma abs_le_natAbs (x : ℤ) : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm

/-- Still or forward coordinate: `0 ≤ b_i ≤ |σ_i|`. -/
lemma bv_small {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ)
    (i : Fin s) (he : -1 ≤ e i ∧ e i ≤ 1) (hq : 2 * |sigma F L e j i| < q)
    (hf : e i = 0 ∨ 0 < e i * sigma F L e j i) :
    0 ≤ bval q F L e j i ∧ bval q F L e j i ≤ |sigma F L e j i| := by
  set σ := sigma F L e j i with hσ
  have hq0 : (0 : ℤ) < q := by have := abs_nonneg σ; omega
  unfold bval
  simp only [← hσ]
  generalize hjit : (if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1) = jit
  have hj : jit = 0 ∨ jit = 1 := by rw [← hjit]; split_ifs <;> simp
  rcases abs_cases σ with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at hq ⊢
  · -- σ ≥ 0
    have hd : σ % (q : ℤ) = σ := Int.emod_eq_of_lt hs (by omega)
    rw [hd]
    rcases he with ⟨h1, h2⟩
    have : e i = -1 ∨ e i = 0 ∨ e i = 1 := by omega
    rcases this with h | h | h <;> rw [h] at hf ⊢ <;>
      simp only [abs_eq_max_neg, max_def, min_def] <;> split_ifs <;> omega
  · -- σ < 0
    have hd : σ % (q : ℤ) = σ + q := by
      rw [show σ % (q : ℤ) = (σ + q) % q by simp, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hd]
    rcases he with ⟨h1, h2⟩
    have : e i = -1 ∨ e i = 0 ∨ e i = 1 := by omega
    rcases this with h | h | h <;> rw [h] at hf ⊢ <;>
      simp only [abs_eq_max_neg, max_def, min_def] <;> split_ifs <;> omega

/-- Backward coordinate: `b_i = q - |σ_i| - jit_i`. -/
lemma bv_back {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ)
    (i : Fin s) (he : -1 ≤ e i ∧ e i ≤ 1) (hq : 2 * |sigma F L e j i| + 2 < q)
    (hb : e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0) :
    bval q F L e j i = q - |sigma F L e j i| -
      (if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1) := by
  set σ := sigma F L e j i with hσ
  unfold bval
  simp only [← hσ]
  generalize hjit : (if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1) = jit
  have hj : jit = 0 ∨ jit = 1 := by rw [← hjit]; split_ifs <;> simp
  rcases abs_cases σ with ⟨ha, hs⟩ | ⟨ha, hs⟩ <;> rw [ha] at hq ⊢
  · have hd : σ % (q : ℤ) = σ := Int.emod_eq_of_lt hs (by omega)
    rw [hd]
    rcases he with ⟨h1, h2⟩
    have : e i = -1 ∨ e i = 1 := by omega
    rcases this with h | h <;> rw [h] at hb ⊢ <;>
      simp only [abs_eq_max_neg, max_def, min_def] <;> split_ifs <;> omega
  · have hd : σ % (q : ℤ) = σ + q := by
      rw [show σ % (q : ℤ) = (σ + q) % q by simp, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hd]
    rcases he with ⟨h1, h2⟩
    have : e i = -1 ∨ e i = 1 := by omega
    rcases this with h | h <;> rw [h] at hb ⊢ <;>
      simp only [abs_eq_max_neg, max_def, min_def] <;> split_ifs <;> omega

lemma bv_nonneg {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ)
    (j : Fin s → ℕ) (i : Fin s) : 0 ≤ bval q F L e j i := by
  unfold bval
  simp only
  split_ifs <;> simp

/-! ## The finite set of steps -/

lemma mem_cfgs {s k : ℕ} (e : Fin s → ℤ) (j : Fin s → ℕ) : (e, j) ∈ cfgs s k ↔ IsConfig k e j := by
  simp only [cfgs, IsConfig, mem_product, mem_filter, Fintype.mem_piFinset, mem_insert,
    mem_singleton, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun d => by rcases h1 d with h | h | h <;> omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun d => by have := h1 d; omega, h2⟩, h3⟩

/-- `S = max |σ_i|` over all steps. -/
def Smax {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) : ℕ :=
  (cfgs s k).sup fun ej => univ.sup fun i => (sigma F L ej.1 ej.2 i).natAbs

lemma sig_le {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) {ej : (Fin s → ℤ) × (Fin s → ℕ)}
    (h : ej ∈ cfgs s k) (i : Fin s) : |sigma F L ej.1 ej.2 i| ≤ (Smax F L k : ℤ) := by
  rw [abs_le_natAbs]
  have h1 : (sigma F L ej.1 ej.2 i).natAbs ≤ univ.sup fun i => (sigma F L ej.1 ej.2 i).natAbs :=
    Finset.le_sup (f := fun i => (sigma F L ej.1 ej.2 i).natAbs) (mem_univ i)
  have h2 := Finset.le_sup (f := fun ej : (Fin s → ℤ) × (Fin s → ℕ) =>
    univ.sup fun i => (sigma F L ej.1 ej.2 i).natAbs) h
  exact_mod_cast h1.trans h2

lemma cfg_e {s k : ℕ} {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s k) (i : Fin s) :
    -1 ≤ ej.1 i ∧ ej.1 i ≤ 1 := by
  obtain ⟨e, j⟩ := ej
  exact ((mem_cfgs e j).1 h).1 i

lemma bmin_le_sq {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) : Bmin q F L k ≤ (q : ℤ) ^ 2 :=
  (Finset.fold_min_le _).2 (Or.inl le_rfl)

lemma bmin_le_cfg {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ)
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s k) :
    Bmin q F L k ≤ ∑ i, bval q F L ej.1 ej.2 i ^ 2 :=
  (Finset.fold_min_le _).2 (Or.inr ⟨ej, h, le_rfl⟩)

lemma bmin_nonneg {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) : 0 ≤ Bmin q F L k :=
  (Finset.le_fold_min _).2 ⟨by positivity, fun ej _ => Finset.sum_nonneg fun i _ => sq_nonneg _⟩

/-- The single-axis step `e = e_a` with all carry lengths `j₀`. -/
def e1 {s : ℕ} (a : Fin s) : Fin s → ℤ := fun d => if d = a then 1 else 0

lemma sigma_e1 {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (a i : Fin s) (j0 : ℕ) :
    sigma F L (e1 a) (fun _ => j0) i = Msum F (min j0 (L - 1)) i a := by
  unfold sigma e1
  rw [Finset.sum_eq_single a (fun d _ hd => by simp [hd]) (by simp)]
  simp

lemma e1_mem {s k : ℕ} (a : Fin s) (j0 : ℕ) (hj : j0 < k) : (e1 a, fun _ => j0) ∈ cfgs s k :=
  (mem_cfgs _ _).2 ⟨fun d => by unfold e1; split_ifs <;> norm_num, ⟨a, by simp [e1]⟩,
    fun _ => hj⟩

/-- A still or forward coordinate contributes at most `S²`. -/
lemma small_sq {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ)
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s k) (hq : 2 * (Smax F L k : ℤ) < q) (i : Fin s)
    (hf : ej.1 i = 0 ∨ 0 < ej.1 i * sigma F L ej.1 ej.2 i) :
    bval q F L ej.1 ej.2 i ^ 2 ≤ (Smax F L k : ℤ) ^ 2 := by
  have hs := sig_le F L k h i
  obtain ⟨h0, h1⟩ := bv_small q F L ej.1 ej.2 i (cfg_e h i) (by omega) hf
  exact pow_le_pow_left₀ h0 (h1.trans hs) 2

/-- The sum over a step with every coordinate still or forward is at most `s S²`. -/
lemma sum_small {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ)
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s k) (hq : 2 * (Smax F L k : ℤ) < q)
    (hf : ∀ i, ej.1 i = 0 ∨ 0 < ej.1 i * sigma F L ej.1 ej.2 i) :
    ∑ i, bval q F L ej.1 ej.2 i ^ 2 ≤ s * (Smax F L k : ℤ) ^ 2 := by
  calc ∑ i, bval q F L ej.1 ej.2 i ^ 2 ≤ ∑ _i : Fin s, (Smax F L k : ℤ) ^ 2 :=
        Finset.sum_le_sum fun i _ => small_sq q F L k h hq i (hf i)
    _ = s * (Smax F L k : ℤ) ^ 2 := by simp

theorem remK_bad_core {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ)
    (hbad : (∃ a, ∃ j < L, 0 < Msum F j a a) ∨
      ∃ e j, IsConfig k e j ∧ 2 ≤ (moving e).card ∧ ∀ i, e i ≠ 0 → 0 < e i * sigma F L e j i) :
    ∃ C : ℝ, ∀ q : ℕ, 1 ≤ q → LBval q F L k ≤ C / q := by
  set S := (Smax F L k : ℤ) with hS
  -- a step all of whose coordinates are still or forward
  obtain ⟨ej, hmem, hf⟩ : ∃ ej ∈ cfgs s k, ∀ i, ej.1 i = 0 ∨ 0 < ej.1 i * sigma F L ej.1 ej.2 i := by
    rcases hbad with ⟨a, j0, hj0, hpos⟩ | ⟨e, j, hc, _, hall⟩
    · refine ⟨(e1 a, fun _ => j0), e1_mem a j0 (by omega), fun i => ?_⟩
      by_cases hi : i = a
      · subst hi; right
        simp only
        rw [sigma_e1, show min j0 (L - 1) = j0 by omega]
        simp [e1, hpos]
      · left; simp [e1, hi]
    · refine ⟨(e, j), (mem_cfgs e j).2 hc, fun i => ?_⟩
      by_cases hi : e i = 0
      · exact Or.inl hi
      · exact Or.inr (hall i hi)
  refine ⟨Real.sqrt ((s : ℝ) * S ^ 2 + (2 * S + 1) ^ 2), fun q hq => ?_⟩
  have hB : (Bmin q F L k : ℝ) ≤ (s : ℝ) * S ^ 2 + (2 * S + 1) ^ 2 := by
    have hS0 : (0 : ℤ) ≤ S := by positivity
    by_cases hqS : 2 * S < q
    · have := (bmin_le_cfg q F L k hmem).trans (sum_small q F L k hmem hqS hf)
      have h2 : (0 : ℤ) ≤ (2 * S + 1) ^ 2 := by positivity
      exact_mod_cast (by linarith : Bmin q F L k ≤ (s : ℤ) * S ^ 2 + (2 * S + 1) ^ 2)
    · have h1 := bmin_le_sq q F L k
      have h2 : (q : ℤ) ^ 2 ≤ (2 * S + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by omega) 2
      have h3 : (0 : ℤ) ≤ s * S ^ 2 := by positivity
      exact_mod_cast (by linarith : Bmin q F L k ≤ (s : ℤ) * S ^ 2 + (2 * S + 1) ^ 2)
  unfold LBval
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hB) hq'.le

/-! ## The expansion -/

lemma jit_own {s : ℕ} (e : Fin s → ℤ) (a : Fin s) (ha : e a ≠ 0) (h0 : ∀ d, d ≠ a → e d = 0) :
    (if e a ≠ 0 ∧ ∀ d, d ≠ a → e d = 0 then (0 : ℤ) else 1) = 0 := if_pos ⟨ha, h0⟩

lemma jit_multi {s : ℕ} (e : Fin s → ℤ) (h2 : 2 ≤ (moving e).card) (i : Fin s) :
    (if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1) = 1 := by
  rw [if_neg]
  rintro ⟨_, h⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (moving e).card)
  simp only [moving, mem_filter, mem_univ, true_and] at ha hb
  by_cases hai : a = i
  · subst hai; exact hb (h b (Ne.symm hab))
  · exact ha (h a hai)

lemma sigma_own {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ)
    (a : Fin s) (h0 : ∀ d, d ≠ a → e d = 0) :
    sigma F L e j a = e a * Msum F (min (j a) (L - 1)) a a := by
  unfold sigma
  rw [Finset.sum_eq_single a (fun d _ hd => by rw [h0 d hd, zero_mul]) (by simp)]

lemma K_own {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) (a : Fin s) (j : ℕ) (hj : j < L) :
    ((Msum F j a a).natAbs : ℤ) ≤ (Kexp F L k : ℤ) := by
  have h : (Msum F j a a).natAbs ≤ (univ ×ˢ range L).sup
      (fun aj : Fin s × ℕ => (Msum F aj.2 aj.1 aj.1).natAbs) :=
    Finset.le_sup (f := fun aj : Fin s × ℕ => (Msum F aj.2 aj.1 aj.1).natAbs) (b := (a, j))
      (mem_product.2 ⟨mem_univ a, mem_range.2 hj⟩)
  exact_mod_cast h.trans (le_max_left _ _)

lemma K_multi {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ) {ej : (Fin s → ℤ) × (Fin s → ℕ)}
    (h : ej ∈ cfgs s k) (h2 : 2 ≤ (moving ej.1).card) (i : Fin s)
    (hb : bwd F L ej.1 ej.2 = {i}) :
    ((sigma F L ej.1 ej.2 i).natAbs : ℤ) + 1 ≤ (Kexp F L k : ℤ) := by
  have hm : ej ∈ (cfgs s k).filter fun ej => 2 ≤ (moving ej.1).card ∧ (bwd F L ej.1 ej.2).card = 1 :=
    mem_filter.2 ⟨h, h2, by rw [hb]; rfl⟩
  have := Finset.le_sup (f := fun ej : (Fin s → ℤ) × (Fin s → ℕ) =>
    ∑ i ∈ bwd F L ej.1 ej.2, ((sigma F L ej.1 ej.2 i).natAbs + 1)) hm
  simp only [hb, sum_singleton] at this
  exact_mod_cast this.trans (le_max_right _ _)

lemma mem_bwd {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ)
    (i : Fin s) : i ∈ bwd F L e j ↔ e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0 := by
  simp [bwd]

/-- One designated coordinate `b`, all others still or forward: `∑ b_i² ≤ b_b² + s S²`. -/
lemma sum_split {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L k : ℕ)
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s k) (hq : 2 * (Smax F L k : ℤ) < q)
    (b : Fin s) (hf : ∀ i, i ≠ b → ej.1 i = 0 ∨ 0 < ej.1 i * sigma F L ej.1 ej.2 i) :
    ∑ i, bval q F L ej.1 ej.2 i ^ 2 ≤ bval q F L ej.1 ej.2 b ^ 2 + s * (Smax F L k : ℤ) ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ b)]
  have h1 : ∑ i ∈ univ.erase b, bval q F L ej.1 ej.2 i ^ 2 ≤
      ∑ i ∈ univ.erase b, (Smax F L k : ℤ) ^ 2 :=
    Finset.sum_le_sum fun i hi => small_sq q F L k h hq i (hf i (Finset.ne_of_mem_erase hi))
  have h2 : ∑ i ∈ univ.erase b, (Smax F L k : ℤ) ^ 2 ≤ ∑ i : Fin s, (Smax F L k : ℤ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
  have h3 : ∑ i : Fin s, (Smax F L k : ℤ) ^ 2 = s * (Smax F L k : ℤ) ^ 2 := by simp
  linarith

theorem remK_good_core {s L k : ℕ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ)
    (hown : ∀ a, ∀ j < L, Msum F j a a ≤ 0)
    (hmulti : ∀ e j, IsConfig k e j → 2 ≤ (moving e).card → ∃ i, e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0) :
    ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      1 - (Kexp F L k : ℝ) / q ≤ LBval q F L k ∧
        LBval q F L k ≤ 1 - (Kexp F L k : ℝ) / q + C / (q : ℝ) ^ 2 := by
  set S := Smax F L k with hSd
  set K := Kexp F L k with hKd
  set R : ℤ := s * (S : ℤ) ^ 2 with hR
  refine ⟨2 * R, 4 * (S + 1) + 2 * K + 4, fun q hq => ?_⟩
  have hqS : 2 * (S : ℤ) + 2 < q := by omega
  have hqS' : 2 * (S : ℤ) < q := by omega
  have hqK : 2 * (K : ℤ) + 1 ≤ q := by omega
  have hq4 : 4 * ((S : ℤ) + 1) ≤ q := by omega
  -- the lower bound for every step
  have hlow : ∀ ej ∈ cfgs s k, ((q : ℤ) - K) ^ 2 ≤ ∑ i, bval q F L ej.1 ej.2 i ^ 2 := by
    intro ej hej
    have hsq : ∀ i, bval q F L ej.1 ej.2 i ^ 2 ≤ ∑ i, bval q F L ej.1 ej.2 i ^ 2 := fun i =>
      Finset.single_le_sum (f := fun i => bval q F L ej.1 ej.2 i ^ 2)
        (fun i _ => sq_nonneg _) (mem_univ i)
    have hne : (moving ej.1).Nonempty := by
      obtain ⟨e, j⟩ := ej
      obtain ⟨_, ⟨d, hd⟩, _⟩ := (mem_cfgs e j).1 hej
      exact ⟨d, by simp [moving, hd]⟩
    by_cases h1 : (moving ej.1).card ≤ 1
    · -- a single-axis step
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (le_antisymm h1 (Finset.card_pos.2 hne))
      have hea : ej.1 a ≠ 0 := by
        have : a ∈ moving ej.1 := by rw [ha]; exact mem_singleton_self a
        simpa [moving] using this
      have h0 : ∀ d, d ≠ a → ej.1 d = 0 := by
        intro d hd
        by_contra hc
        have : d ∈ moving ej.1 := by simp [moving, hc]
        rw [ha] at this; exact hd (mem_singleton.1 this)
      have hσ := sigma_own F L ej.1 ej.2 a h0
      have hM := hown a (min (ej.2 a) (L - 1)) (by omega)
      have he := cfg_e hej a
      have hsq1 : ej.1 a * ej.1 a = 1 := by
        rcases (show ej.1 a = 1 ∨ ej.1 a = -1 by omega) with h | h <;> rw [h] <;> norm_num
      have hback : ej.1 a ≠ 0 ∧ ej.1 a * sigma F L ej.1 ej.2 a ≤ 0 := by
        refine ⟨hea, ?_⟩
        rw [hσ, ← mul_assoc, hsq1, one_mul]; exact hM
      have hb := bv_back q F L ej.1 ej.2 a he (by have := sig_le F L k hej a; omega) hback
      rw [jit_own _ a hea h0, sub_zero] at hb
      have hK : |sigma F L ej.1 ej.2 a| ≤ (K : ℤ) := by
        rw [hσ, abs_mul]
        have : |ej.1 a| = 1 := by
          rcases (show ej.1 a = 1 ∨ ej.1 a = -1 by omega) with h | h <;> rw [h] <;> norm_num
        rw [this, one_mul, abs_le_natAbs]
        exact K_own F L k a _ (by omega)
      have hpos : 0 ≤ (q : ℤ) - K := by omega
      have : ((q : ℤ) - K) ^ 2 ≤ bval q F L ej.1 ej.2 a ^ 2 :=
        pow_le_pow_left₀ hpos (by rw [hb]; linarith) 2
      exact this.trans (hsq a)
    · have h2 : 2 ≤ (moving ej.1).card := by omega
      obtain ⟨i, hi⟩ := hmulti ej.1 ej.2 ((mem_cfgs ej.1 ej.2).1 hej) h2
      have hib : i ∈ bwd F L ej.1 ej.2 := (mem_bwd F L ej.1 ej.2 i).2 hi
      by_cases hc : (bwd F L ej.1 ej.2).card = 1
      · obtain ⟨i', hi'⟩ := Finset.card_eq_one.1 hc
        have hii : i = i' := by rw [hi'] at hib; exact mem_singleton.1 hib
        subst hii
        have hb := bv_back q F L ej.1 ej.2 i (cfg_e hej i) (by have := sig_le F L k hej i; omega) hi
        rw [jit_multi _ h2 i] at hb
        have hK := K_multi F L k hej h2 i hi'
        rw [← abs_le_natAbs] at hK
        have hpos : 0 ≤ (q : ℤ) - K := by omega
        have : ((q : ℤ) - K) ^ 2 ≤ bval q F L ej.1 ej.2 i ^ 2 :=
          pow_le_pow_left₀ hpos (by rw [hb]; linarith) 2
        exact this.trans (hsq i)
      · have h1' : 1 < (bwd F L ej.1 ej.2).card := by
          have := Finset.card_pos.2 ⟨i, hib⟩; omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1'
        have ha' := (mem_bwd F L ej.1 ej.2 a).1 ha
        have hb' := (mem_bwd F L ej.1 ej.2 b).1 hb
        have va := bv_back q F L ej.1 ej.2 a (cfg_e hej a)
          (by have := sig_le F L k hej a; omega) ha'
        have vb := bv_back q F L ej.1 ej.2 b (cfg_e hej b)
          (by have := sig_le F L k hej b; omega) hb'
        rw [jit_multi _ h2 a] at va
        rw [jit_multi _ h2 b] at vb
        have sa := sig_le F L k hej a
        have sb := sig_le F L k hej b
        have hpair : bval q F L ej.1 ej.2 a ^ 2 + bval q F L ej.1 ej.2 b ^ 2 ≤
            ∑ i, bval q F L ej.1 ej.2 i ^ 2 := by
          have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => bval q F L ej.1 ej.2 i ^ 2)
            (subset_univ {a, b}) (fun _ _ _ => sq_nonneg _)
          rwa [Finset.sum_pair hab] at this
        have hA : (q : ℤ) - S - 1 ≤ bval q F L ej.1 ej.2 a := by rw [va]; linarith
        have hB : (q : ℤ) - S - 1 ≤ bval q F L ej.1 ej.2 b := by rw [vb]; linarith
        have hpos : 0 ≤ (q : ℤ) - S - 1 := by omega
        have e1' := pow_le_pow_left₀ hpos hA 2
        have e2' := pow_le_pow_left₀ hpos hB 2
        have hK0 : (0 : ℤ) ≤ K := by positivity
        have : ((q : ℤ) - K) ^ 2 ≤ 2 * ((q : ℤ) - S - 1) ^ 2 := by nlinarith
        linarith
  have hBlow : ((q : ℤ) - K) ^ 2 ≤ Bmin q F L k := by
    refine (Finset.le_fold_min _).2 ⟨?_, hlow⟩
    have hK0 : (0 : ℤ) ≤ K := by positivity
    nlinarith
  -- the upper bound: a step attaining `K`
  have hBup : Bmin q F L k ≤ ((q : ℤ) - K) ^ 2 + R := by
    by_cases hAB : ((((cfgs s k).filter fun ej => 2 ≤ (moving ej.1).card ∧
        (bwd F L ej.1 ej.2).card = 1).sup
          fun ej => ∑ i ∈ bwd F L ej.1 ej.2, ((sigma F L ej.1 ej.2 i).natAbs + 1)) ≤
        (univ ×ˢ range L).sup fun aj : Fin s × ℕ => (Msum F aj.2 aj.1 aj.1).natAbs)
    · have hKA : K = (univ ×ˢ range L).sup fun aj : Fin s × ℕ => (Msum F aj.2 aj.1 aj.1).natAbs :=
        max_eq_left hAB
      have hne : (univ ×ˢ range L : Finset (Fin s × ℕ)).Nonempty :=
        ⟨(⟨0, hs⟩, 0), mem_product.2 ⟨mem_univ _, mem_range.2 (by omega)⟩⟩
      obtain ⟨⟨a, j0⟩, hmem, hval⟩ := Finset.exists_mem_eq_sup _ hne
        (fun aj : Fin s × ℕ => (Msum F aj.2 aj.1 aj.1).natAbs)
      have hj0 : j0 < L := mem_range.1 (mem_product.1 hmem).2
      have hc := e1_mem (k := k) a j0 (by omega)
      have hσ : sigma F L (e1 a) (fun _ => j0) a = Msum F j0 a a := by
        rw [sigma_e1, show min j0 (L - 1) = j0 by omega]
      have hea : e1 a a = 1 := by simp [e1]
      have h0 : ∀ d, d ≠ a → e1 a d = 0 := fun d hd => by simp [e1, hd]
      have hb := bv_back q F L (e1 a) (fun _ => j0) a (by rw [hea]; norm_num)
        (by have := sig_le F L k hc a; simp only at this; omega) ⟨by rw [hea]; norm_num, by
          rw [hea, hσ, one_mul]; exact hown a j0 hj0⟩
      rw [jit_own _ a (by rw [hea]; norm_num) h0, sub_zero, hσ] at hb
      have hbK : bval q F L (e1 a) (fun _ => j0) a = (q : ℤ) - K := by
        rw [hb, hKA, hval, abs_le_natAbs]
      have := sum_split q F L k hc hqS' a (fun i hi => Or.inl (h0 i hi))
      rw [hbK] at this
      exact (bmin_le_cfg q F L k hc).trans this
    · push_neg at hAB
      have hKB : K = ((cfgs s k).filter fun ej => 2 ≤ (moving ej.1).card ∧
          (bwd F L ej.1 ej.2).card = 1).sup
            fun ej => ∑ i ∈ bwd F L ej.1 ej.2, ((sigma F L ej.1 ej.2 i).natAbs + 1) :=
        max_eq_right hAB.le
      have hne : ((cfgs s k).filter fun ej => 2 ≤ (moving ej.1).card ∧
          (bwd F L ej.1 ej.2).card = 1).Nonempty := by
        by_contra hc
        rw [Finset.not_nonempty_iff_eq_empty] at hc
        rw [hc, Finset.sup_empty] at hAB
        exact absurd hAB (Nat.not_lt_zero _)
      obtain ⟨ej, hmem, hval⟩ := Finset.exists_mem_eq_sup _ hne
        (fun ej : (Fin s → ℤ) × (Fin s → ℕ) =>
          ∑ i ∈ bwd F L ej.1 ej.2, ((sigma F L ej.1 ej.2 i).natAbs + 1))
      obtain ⟨hc, h2, hc1⟩ := mem_filter.1 hmem
      obtain ⟨b, hb1⟩ := Finset.card_eq_one.1 hc1
      have hbb : b ∈ bwd F L ej.1 ej.2 := by rw [hb1]; exact mem_singleton_self b
      have hv := bv_back q F L ej.1 ej.2 b (cfg_e hc b) (by have := sig_le F L k hc b; omega)
        ((mem_bwd F L ej.1 ej.2 b).1 hbb)
      rw [jit_multi _ h2 b] at hv
      have hbK : bval q F L ej.1 ej.2 b = (q : ℤ) - K := by
        rw [hv, hKB, hval, hb1, sum_singleton, abs_le_natAbs]; push_cast; ring
      have hrest : ∀ i, i ≠ b → ej.1 i = 0 ∨ 0 < ej.1 i * sigma F L ej.1 ej.2 i := by
        intro i hi
        by_cases h0 : ej.1 i = 0
        · exact Or.inl h0
        · right
          by_contra hle
          push_neg at hle
          have : i ∈ bwd F L ej.1 ej.2 := (mem_bwd F L ej.1 ej.2 i).2 ⟨h0, hle⟩
          rw [hb1] at this; exact hi (mem_singleton.1 this)
      have := sum_split q F L k hc hqS' b hrest
      rw [hbK] at this
      exact (bmin_le_cfg q F L k hc).trans this
  -- real analysis
  have hqpos : (0 : ℝ) < q := by have : (0 : ℤ) < q := by omega
                                 exact_mod_cast this
  have hxpos : (0 : ℝ) < (q : ℝ) - K := by
    have : (K : ℤ) < q := by omega
    have : (K : ℝ) < q := by exact_mod_cast this
    linarith
  have hx2 : (q : ℝ) ≤ 2 * ((q : ℝ) - K) := by
    have : 2 * (K : ℝ) + 1 ≤ q := by exact_mod_cast hqK
    linarith
  have hBlowR : ((q : ℝ) - K) ^ 2 ≤ (Bmin q F L k : ℝ) := by exact_mod_cast hBlow
  have hBupR : (Bmin q F L k : ℝ) ≤ ((q : ℝ) - K) ^ 2 + R := by exact_mod_cast hBup
  have hR0 : (0 : ℝ) ≤ R := by
    have : (0 : ℤ) ≤ R := by positivity
    exact_mod_cast this
  unfold LBval
  constructor
  · rw [show 1 - (K : ℝ) / q = ((q : ℝ) - K) / q by field_simp]
    apply div_le_div_of_nonneg_right _ hqpos.le
    calc (q : ℝ) - K = Real.sqrt (((q : ℝ) - K) ^ 2) := (Real.sqrt_sq hxpos.le).symm
      _ ≤ Real.sqrt (Bmin q F L k) := Real.sqrt_le_sqrt hBlowR
  · set x := (q : ℝ) - K with hx
    have hs1 : Real.sqrt (Bmin q F L k) ≤ x + R / x := by
      rw [Real.sqrt_le_left (by positivity)]
      calc (Bmin q F L k : ℝ) ≤ x ^ 2 + R := hBupR
        _ ≤ (x + R / x) ^ 2 := by
          have : (x + R / x) ^ 2 = x ^ 2 + 2 * R + (R / x) ^ 2 := by field_simp; ring
          rw [this]; nlinarith [sq_nonneg (R / x)]
    have hRx : R / x ≤ 2 * R / q := by
      rw [div_le_div_iff₀ hxpos hqpos]; nlinarith
    calc Real.sqrt (Bmin q F L k) / q ≤ (x + R / x) / q :=
          div_le_div_of_nonneg_right hs1 hqpos.le
      _ ≤ (x + 2 * R / q) / q := div_le_div_of_nonneg_right (by linarith) hqpos.le
      _ = 1 - (K : ℝ) / q + 2 * (R : ℝ) / (q : ℝ) ^ 2 := by
          rw [hx]; field_simp <;> ring

end Z3NetF.Proofs.RemK
