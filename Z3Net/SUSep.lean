module
public import Mathlib
public import Z3Net.SUGeom

@[expose] public section

/-!
# Entry U, part 7: Theorem U(2) — separation

Assembly of Lemma S_s (soundness of the relaxation: carries, residue representatives, jitter;
adapted from the 4D entry) and **Theorem D** (diagonal dominance), proved symbolically in `s`:
every moving coordinate is backward (`e_i σ_i ≤ 0`, `|σ_i| ≤ 2 a`), so a moving coordinate
contributes `≥ q - |σ_i| - jitter`; the own-axis step costs exactly `a_c ≤ a` (no jitter, (H2)),
and a multi-axis step has two coordinates each `≥ q - 2a - 1`, with `2 (q - 2a - 1)² ≥ (q - a)²`
for `q ≥ 5a + 4`. The toroidal residue lemmas are copied from the 4D entry for the entry-U `cres`.
-/

namespace Z3NetU.Proofs

open Finset Z3NetU

noncomputable section

/-! ## Toroidal residues (copied from the 3D entry) -/

lemma cres_add_mul (N : ℕ) (u z : ℤ) : cres N (u + z * N) = cres N u := by
  unfold cres; rw [Int.add_mul_emod_self_right]

lemma cres_eq_abs (N : ℕ) (u : ℤ) (h : 2 * |u| ≤ N) : (cres N u : ℤ) = |u| := by
  unfold cres
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [abs_of_neg hu] at h ⊢
    have hm : u % (N : ℤ) = u + N := by
      rw [show u = (u + N) + (-1) * N by ring, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (by omega) (by omega)]; ring
    rw [hm]
    have : N - (u + N).toNat ≤ (u + N).toNat := by omega
    rw [min_eq_right this]; omega
  · subst hu; simp
  · rw [abs_of_pos hu] at h ⊢
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have : u.toNat ≤ N - u.toNat := by omega
    rw [min_eq_left this]; omega

lemma cres_eq_abs_sub (N : ℕ) (hN : 0 < N) (u : ℤ) : ∃ z : ℤ, (cres N u : ℤ) = |u - z * N| := by
  have h0 := Int.emod_nonneg u (show (N : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos u (show (0 : ℤ) < N by omega)
  have hd := Int.mul_ediv_add_emod u (N : ℤ)
  unfold cres
  rcases le_total (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) with h | h
  · refine ⟨u / N, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    rw [this]; linarith
  · refine ⟨u / N + 1, ?_⟩
    rw [min_eq_right h, abs_of_nonpos (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    push_cast [Nat.cast_sub (show (u % (N : ℤ)).toNat ≤ N by omega), this]
    linarith

lemma far_gen (N : ℕ) (G P : ℤ) (hG : 0 < G) (hP : 0 < P) (hN : (N : ℤ) = G * P) (Δn R : ℤ)
    (hR : |R| < G) (hfar : ∀ z : ℤ, 2 ≤ |Δn - z * P|) : G ≤ cres N (G * Δn + R) := by
  have hN0 : 0 < N := by
    have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  obtain ⟨z, hz⟩ := cres_eq_abs_sub N hN0 (G * Δn + R)
  rw [hz, hN]
  have h2 := hfar z
  have e : G * Δn + R - z * (G * P) = G * (Δn - z * P) + R := by ring
  rw [e]
  have h3 : |G * (Δn - z * P)| = G * |Δn - z * P| := by rw [abs_mul, abs_of_pos hG]
  have h4 := abs_add_le (G * (Δn - z * P) + R) (-R)
  rw [add_neg_cancel_right, abs_neg, h3] at h4
  nlinarith

lemma near_gen (N : ℕ) (u V Δt z : ℤ) (hu : 0 < u) (ht : |Δt| < u)
    (hsmall : 2 * |u * V + Δt| ≤ N) :
    0 ≤ (cres N (u * V + Δt + z * N) : ℤ) / u ∧
    |V| - 1 ≤ (cres N (u * V + Δt + z * N) : ℤ) / u ∧
    (Δt = 0 → |V| ≤ (cres N (u * V + Δt + z * N) : ℤ) / u) ∧
    u * ((cres N (u * V + Δt + z * N) : ℤ) / u) ≤ cres N (u * V + Δt + z * N) := by
  rw [cres_add_mul, cres_eq_abs N _ hsmall]
  refine ⟨Int.ediv_nonneg (abs_nonneg _) hu.le, ?_, ?_, ?_⟩
  · apply Int.le_ediv_of_mul_le hu
    have h1 := abs_add_le (u * V + Δt) (-Δt)
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos hu] at h1
    nlinarith
  · intro h0; subst h0
    apply Int.le_ediv_of_mul_le hu
    rw [add_zero, abs_mul, abs_of_pos hu]; linarith
  · rw [mul_comm]; exact Int.ediv_mul_le _ hu.ne'

/-- Cell-step trichotomy on `ℤ/Pℤ` (`P ≥ 3`). -/
lemma step_cases (P a b : ℕ) (hP : 3 ≤ P) (ha : a < P) (hb : b < P) :
    b = a ∨ b = (a + 1) % P ∨ a = (b + 1) % P ∨ ∀ z : ℤ, 2 ≤ |(b : ℤ) - a - z * P| := by
  by_cases h0 : b = a; · exact Or.inl h0
  by_cases h1 : b = a + 1; · right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h1
  by_cases h2 : a = b + 1; · right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  by_cases h3 : b = 0 ∧ a = P - 1
  · right; left; rw [h3.1, h3.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  by_cases h4 : a = 0 ∧ b = P - 1
  · right; right; left; rw [h4.1, h4.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  right; right; right
  intro z
  rw [le_abs]
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rcases eq_or_lt_of_le (show z ≤ -1 by omega) with hz1 | hz1
    · subst hz1; left; omega
    · left; nlinarith
  · subst hz; simp only [zero_mul, sub_zero]; omega
  · rcases eq_or_lt_of_le (show 1 ≤ z by omega) with hz1 | hz1
    · subst hz1; right; omega
    · right; nlinarith

/-! ## Theorem D: diagonal dominance, symbolically in `s` -/

lemma PJ_diag (s : ℕ) (i : Fin s) (J : ℕ) : PJ s i i J = -(acoef s i : ℤ) := by
  unfold PJ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Fdes]
  · intro t _; simp [Fdes]

lemma PJ_off (s : ℕ) (i d : Fin s) (hid : i ≠ d) (J : ℕ) : PJ s i d J = Msum s J i d := by
  unfold PJ Msum; exact Finset.sum_congr rfl fun t _ => by simp [Fdes, hid]

lemma acoef_le_aU (s : ℕ) (c : Fin s) : acoef s c ≤ aU s := Finset.le_sup (mem_univ c)

lemma off_sum_bound (s : ℕ) (i : Fin s) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (J : Fin s → ℕ) (hJ : ∀ d, J d ≤ s - 2) :
    |∑ d ∈ univ.erase i, e d * PJ s i d (J d)| ≤ (acoef s i : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hac : (acoef s i : ℤ) = ∑ d ∈ univ.erase i,
      (((range (s - 1)).sup fun j => (Msum s j i d).natAbs : ℕ) : ℤ) := by
    rw [acoef, ← Finset.filter_ne', Nat.cast_sum]
  rw [hac]
  refine Finset.sum_le_sum fun d hd => ?_
  have hid : i ≠ d := Ne.symm (Finset.ne_of_mem_erase hd)
  rw [abs_mul, PJ_off s i d hid]
  have h1 : |e d| ≤ 1 := abs_le.mpr ⟨(he d).1, (he d).2⟩
  have h2 : |Msum s (J d) i d| ≤ (((range (s - 1)).sup fun j => (Msum s j i d).natAbs : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    have hJs : J d ≤ s - 2 := hJ d
    exact_mod_cast Finset.le_sup (f := fun j => (Msum s j i d).natAbs)
      (mem_range.mpr (by omega : J d < s - 1))
  calc |e d| * |Msum s (J d) i d| ≤ 1 * |Msum s (J d) i d| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h2

lemma sigma_split (s : ℕ) (i : Fin s) (e : Fin s → ℤ) (J : Fin s → ℕ) :
    ∑ d, e d * PJ s i d (J d) = -(e i * (acoef s i : ℤ)) + ∑ d ∈ univ.erase i, e d * PJ s i d (J d) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i), PJ_diag]; ring

lemma unit_sign (e : ℤ) (h1 : -1 ≤ e) (h2 : e ≤ 1) (h0 : e ≠ 0) : e = 1 ∨ e = -1 := by omega

/-- Every moving coordinate is backward, `|σ_i| ≤ 2 a`. -/
lemma sigma_moving (s : ℕ) (i : Fin s) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (J : Fin s → ℕ) (hJ : ∀ d, J d ≤ s - 2) (hi : e i ≠ 0) :
    e i * (∑ d, e d * PJ s i d (J d)) ≤ 0 ∧ |∑ d, e d * PJ s i d (J d)| ≤ 2 * (aU s : ℤ) := by
  rw [sigma_split]
  have hR := off_sum_bound s i e he J hJ
  have ha := acoef_le_aU s i
  have ha' : (acoef s i : ℤ) ≤ aU s := by exact_mod_cast ha
  set R := ∑ d ∈ univ.erase i, e d * PJ s i d (J d)
  set A : ℤ := (acoef s i : ℤ)
  rw [abs_le] at hR
  rcases unit_sign (e i) (he i).1 (he i).2 hi with h | h <;> rw [h] <;> constructor
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith
  · rw [abs_le]; constructor <;> linarith

/-- The own-axis step costs `a_i ≤ a`. -/
lemma sigma_own (s : ℕ) (i : Fin s) (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (J : Fin s → ℕ) (hi : e i ≠ 0) (hother : ∀ d, d ≠ i → e d = 0) :
    |∑ d, e d * PJ s i d (J d)| ≤ (aU s : ℤ) := by
  rw [sigma_split, Finset.sum_eq_zero (fun d hd => by
    rw [hother d (Finset.ne_of_mem_erase hd), zero_mul]), add_zero, abs_neg, abs_mul]
  have ha' : (acoef s i : ℤ) ≤ aU s := by exact_mod_cast acoef_le_aU s i
  rcases unit_sign (e i) (he i).1 (he i).2 hi with h | h <;> rw [h] <;> simpa using ha'

/-- A moving backward coordinate contributes at least `q - |σ|`. -/
lemma moving_bound (q a e σ δ : ℤ) (hq : 2 * a < q) (he : e = 1 ∨ e = -1) (hes : e * σ ≤ 0)
    (hσ : |σ| ≤ 2 * a) (hδ : δ ≡ σ [ZMOD q]) (hδq : |δ| < q) : q - |σ| ≤ |e * q + δ| := by
  obtain ⟨t, ht⟩ := hδ.dvd
  rw [abs_le] at hσ
  rw [abs_lt] at hδq
  have hq0 : 0 < q := by linarith
  have ht1 : t < 2 := by
    by_contra h; push_neg at h; nlinarith
  have ht2 : -2 < t := by
    by_contra h; push_neg at h; nlinarith
  have hδ' : δ = σ - q * t := by linarith
  rw [hδ']
  interval_cases t <;> rcases he with rfl | rfl <;>
    simp only [one_mul, neg_mul, mul_zero, mul_one, mul_neg, sub_zero, sub_neg_eq_add] at hes ⊢ <;>
    first
    | (rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith)
    | (rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith)
    | (rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith)
    | (rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith)
    | (exfalso; linarith)

/-- **Theorem D, abstract form.** -/
theorem key_sym (s : ℕ) (q a : ℤ) (ha : 0 ≤ a) (hq : 5 * a + 4 ≤ q)
    (e : Fin s → ℤ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0)
    (σ δ x : Fin s → ℤ)
    (hσ : ∀ i, e i ≠ 0 → e i * σ i ≤ 0 ∧ |σ i| ≤ 2 * a)
    (hσo : ∀ i, e i ≠ 0 → (∀ d, d ≠ i → e d = 0) → |σ i| ≤ a)
    (hδ : ∀ i, δ i ≡ σ i [ZMOD q] ∧ |δ i| < q) (hx0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, (if (e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0) then |e i * q + δ i|
      else |e i * q + δ i| - 1) ≤ x i) :
    (q - a) ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hmv : ∀ i, e i ≠ 0 → q - |σ i| ≤ |e i * q + δ i| := fun i hi =>
    moving_bound q a (e i) (σ i) (δ i) (by linarith) (unit_sign _ (he i).1 (he i).2 hi)
      (hσ i hi).1 (hσ i hi).2 (hδ i).1 (hδ i).2
  have hnn : ∀ i ∈ (univ : Finset (Fin s)), 0 ≤ x i ^ 2 := fun i _ => sq_nonneg _
  by_cases hown : ∃ i, e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0
  · obtain ⟨i, hi, hoth⟩ := hown
    have h1 := hx i
    rw [if_pos ⟨hi, hoth⟩] at h1
    have h2 := hmv i hi
    have h3 := hσo i hi hoth
    have hxi : q - a ≤ x i := by linarith
    calc (q - a) ^ 2 ≤ x i ^ 2 := pow_le_pow_left₀ (by linarith) hxi 2
      _ ≤ ∑ i, x i ^ 2 := Finset.single_le_sum hnn (mem_univ i)
  · push_neg at hown
    obtain ⟨i, hi⟩ := hne
    obtain ⟨d, hdi, hd⟩ := hown i hi
    have hnot : ∀ c, e c ≠ 0 → ¬ (e c ≠ 0 ∧ ∀ d, d ≠ c → e d = 0) := fun c hc h => by
      obtain ⟨d', hd', he'⟩ := hown c hc; exact he' (h.2 d' hd')
    have hb : ∀ c, e c ≠ 0 → q - 2 * a - 1 ≤ x c := by
      intro c hc
      have h1 := hx c
      rw [if_neg (hnot c hc)] at h1
      have := hmv c hc
      have := (hσ c hc).2
      linarith
    have hxi := hb i hi
    have hxd := hb d hd
    have hpair : x i ^ 2 + x d ^ 2 ≤ ∑ c, x c ^ 2 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c => x c ^ 2)
        (subset_univ ({i, d} : Finset (Fin s))) (fun c _ _ => sq_nonneg _)
      rwa [Finset.sum_pair (Ne.symm hdi)] at this
    have hpos : 0 ≤ q - 2 * a - 1 := by linarith
    nlinarith [pow_le_pow_left₀ hpos hxi 2, pow_le_pow_left₀ hpos hxd 2]

/-! ## One coordinate -/

variable (s q : ℕ) [NeZero q]

/-- First offset digit and tail of coordinate `c`. -/
def o0 (k : ℕ) (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := dv s q k (Dg s q k c v) k
def tl (k : ℕ) (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := tail s q k (Dg s q k c v)

lemma X_decomp (k : ℕ) (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    (Upoint s q k v c : ℤ) = (q : ℤ) ^ (s * k - k) * cellN s q k v c +
      (q : ℤ) ^ (s * k - k - 1) * o0 s q k v c + tl s q k v c := by
  rw [Upoint_eq, coord_split s q k hsk, cell_part]
  push_cast
  simp only [o0, tl]

lemma o0_cast (k : ℕ) (v : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) :
    ((o0 s q k v c : ℕ) : ZMod q) = Dg s q k c v ⟨k + r, sk_sub_add r⟩ := by
  have hk : k < s * k := by have := sk_sub_add r; omega
  simp only [o0, dv, dif_pos hk, ZMod.natCast_zmod_val, hr, add_zero]

/-- Equal cells on all axes force equal indices (graph form: the index is the cells). -/
lemma eq_of_cellN (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q)
    (h : ∀ d, cellN s q k w d = cellN s q k v d) : w = v := by
  funext j
  obtain ⟨d, l, rfl⟩ := ix_surj k j
  exact digits_eq_of_cellN_eq s q hq k v w d (h d) l

/-- The step of axis `d` is "far" (toroidal cell difference outside `{-1,0,1}`). -/
def Far (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s) : Prop :=
  ∀ z : ℤ, 2 ≤ |(cellN s q k w d : ℤ) - cellN s q k v d - z * (q : ℤ) ^ k|

lemma axis_classify (hq : 2 ≤ q) (k : ℕ) (hk : 2 ≤ k) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (hnf : ¬ Far s q k v w d) :
    ∃ e : ℤ, ∃ J : ℕ, (-1 ≤ e ∧ e ≤ 1) ∧ J ≤ s - 2 ∧ J < k ∧ AxisStep s q k v w d e J ∧
      (∃ z : ℤ, (cellN s q k w d : ℤ) - cellN s q k v d = e + z * (q : ℤ) ^ k) ∧
      (e = 0 → cellN s q k w d = cellN s q k v d) := by
  have hq1 : 1 < q := by omega
  have hP : 3 ≤ q ^ k := by
    calc 3 ≤ q ^ 2 := by nlinarith
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hJ1 : ∀ n, Jof s q k n ≤ s - 2 := fun n => (Jof_le s q k n).trans (min_le_left _ _)
  have hJ2 : ∀ n, Jof s q k n < k := fun n => by have := (Jof_le s q k n).trans (min_le_right _ _); omega
  rcases step_cases (q ^ k) (cellN s q k v d) (cellN s q k w d) hP (cellN_lt s q k v d)
    (cellN_lt s q k w d) with h | h | h | h
  · exact ⟨0, 0, by norm_num, by omega, by omega, axisStep_zero s q hq1 k v w d h,
      ⟨0, by rw [h]; ring⟩, fun _ => h⟩
  · refine ⟨1, Jof s q k (cellN s q k v d), by norm_num, hJ1 _, hJ2 _,
      axisStep_plus s q hq1 k v w d h, ⟨-(((cellN s q k v d + 1) / q ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN s q k v d + 1) (q ^ k)
    rw [← h] at this
    have h' : ((cellN s q k w d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN s q k v d + 1) / q ^ k : ℕ) : ℤ)
        = (cellN s q k v d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · refine ⟨-1, Jof s q k (cellN s q k w d), by norm_num, hJ1 _, hJ2 _,
      axisStep_minus s q hq1 k v w d h, ⟨(((cellN s q k w d + 1) / q ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN s q k w d + 1) (q ^ k)
    rw [← h] at this
    have h' : ((cellN s q k v d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN s q k w d + 1) / q ^ k : ℕ) : ℤ)
        = (cellN s q k w d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · exact absurd h hnf

lemma tl_eq_of_only (hq : 1 < q) (k : ℕ) (c : Fin s) (v w : Fin (s * k) → ZMod q)
    (hother : ∀ d, d ≠ c → cellN s q k w d = cellN s q k v d) : tl s q k w c = tl s q k v c := by
  unfold tl tail
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Ico] at hj
  congr 1
  unfold dv
  rw [dif_pos hj.2, dif_pos hj.2]
  have e := Dg_off_eq_of_only s q hq k c v w hother ⟨j - k, by omega⟩ (by simp; omega)
  have hj' : (⟨j, hj.2⟩ : Fin (s * k)) =
      ⟨k + ((⟨j - k, by omega⟩ : Fin (s * k - k)) : ℕ), sk_sub_add ⟨j - k, by omega⟩⟩ := by
    ext; simp; omega
  rw [hj', e]

lemma o_bound (k : ℕ) (v w : Fin (s * k) → ZMod q) (c : Fin s) :
    |(o0 s q k w c : ℤ) - o0 s q k v c| < q := by
  have h1 := dv_lt s q k (Dg s q k c w) k; have h2 := dv_lt s q k (Dg s q k c v) k
  simp only [o0]
  rw [abs_lt]; constructor <;> omega

/-- **Theorem U(2), integer form.** -/
theorem main_bound (hs : 3 ≤ s) (hq : Admissible s q) (hqa : 5 * aU s + 4 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aU s) ^ 2 ≤ (q : ℤ) ^ 2 * ∑ c : Fin s,
          ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq2 : 2 ≤ q := hq.1
  have hq1 : 1 < q := by omega
  have hqz : (4 : ℤ) ≤ q := by exact_mod_cast (show 4 ≤ q by omega)
  have haz : (0 : ℤ) ≤ aU s := by positivity
  have hqaz : 5 * (aU s : ℤ) + 4 ≤ q := by exact_mod_cast hqa
  have h2k : 2 * k ≤ s * k := Nat.mul_le_mul_right k (by omega)
  have hsk : k + 1 ≤ s * k := by omega
  set M := s * k - k with hM
  have hM1 : 1 ≤ M := by omega
  set u : ℤ := (q : ℤ) ^ (M - 1) with hu_def
  have hu : 0 < u := by positivity
  have hpow : (q : ℤ) ^ M = u * q := by rw [hu_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * k) : ℕ) : ℤ) = (q : ℤ) ^ M * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hX : ∀ c, (Upoint s q k w c : ℤ) - Upoint s q k v c =
      (q : ℤ) ^ M * ((cellN s q k w c : ℤ) - cellN s q k v c) +
      (u * ((o0 s q k w c : ℤ) - o0 s q k v c) + ((tl s q k w c : ℤ) - tl s q k v c)) := by
    intro c; rw [X_decomp s q k hsk, X_decomp s q k hsk]; ring
  have htl : ∀ c, |(tl s q k w c : ℤ) - tl s q k v c| < u := by
    intro c
    have h1 := tail_lt s q k hsk (Dg s q k c w); have h2 := tail_lt s q k hsk (Dg s q k c v)
    have h1' : ((tl s q k w c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h1
    have h2' : ((tl s q k v c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hK : ((q : ℤ) - aU s) ^ 2 ≤ (q : ℤ) ^ 2 := by nlinarith
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  have hu2 : (q : ℤ) ^ (2 * M) = (q : ℤ) ^ 2 * u ^ 2 := by
    rw [hu_def, ← pow_mul, ← pow_add]; congr 1; omega
  by_cases hfar : ∃ c, Far s q k v w c
  · obtain ⟨c, hc⟩ := hfar
    have ho0 := o_bound s q k v w c
    have hR : |u * ((o0 s q k w c : ℤ) - o0 s q k v c) + ((tl s q k w c : ℤ) - tl s q k v c)| <
        (q : ℤ) ^ M := by
      have a2 := abs_add_le (u * ((o0 s q k w c : ℤ) - o0 s q k v c)) ((tl s q k w c : ℤ) - tl s q k v c)
      rw [abs_mul, abs_of_pos hu] at a2
      have := htl c
      have b1 : |(o0 s q k w c : ℤ) - o0 s q k v c| ≤ q - 1 := by omega
      rw [hpow]; nlinarith
    have hf := far_gen (q ^ (s * k)) ((q : ℤ) ^ M) ((q : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : ((q : ℤ) ^ M) ^ 2 ≤
        ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc (q : ℤ) ^ (2 * M) * ((q : ℤ) - aU s) ^ 2 ≤ (q : ℤ) ^ (2 * M) * (q : ℤ) ^ 2 := by gcongr
      _ = (q : ℤ) ^ 2 * ((q : ℤ) ^ M) ^ 2 := by rw [← pow_mul]; ring
      _ ≤ _ := by gcongr; exact hsq.trans hsingle
  · push_neg at hfar
    choose e J he hJs hJk hstep hz he0 using fun c => axis_classify s q hq2 k hk v w c (hfar c)
    by_cases hall : ∀ c, e c = 0
    · exact absurd (eq_of_cellN s q hq1 k v w (fun d => he0 d (hall d))).symm hvw
    push_neg at hall
    have r0 : Fin (s * k - k) := ⟨0, by omega⟩
    have hσ : ∀ c, ((o0 s q k w c : ℤ) - o0 s q k v c) ≡ ∑ d, e d * PJ s c d (J d) [ZMOD q] := by
      intro c
      have h := Dg_off_sub s q hs hq k hk c v w e J hJk hJs hstep ⟨0, by omega⟩ rfl
      rw [← o0_cast s q k w c ⟨0, by omega⟩ rfl, ← o0_cast s q k v c ⟨0, by omega⟩ rfl] at h
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast at h ⊢
      exact h
    set V : Fin s → ℤ := fun c => e c * q + ((o0 s q k w c : ℤ) - o0 s q k v c) with hV
    have hVb : ∀ c, |V c| ≤ 2 * (q : ℤ) - 1 := by
      intro c
      have ho := o_bound s q k v w c
      have b1 : |(o0 s q k w c : ℤ) - o0 s q k v c| ≤ q - 1 := by omega
      have b0 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
      have := abs_add_le (e c * q) ((o0 s q k w c : ℤ) - o0 s q k v c)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q)] at this
      simp only [hV]
      nlinarith
    have hXV : ∀ c, ∃ z : ℤ, (Upoint s q k w c : ℤ) - Upoint s q k v c =
        u * V c + ((tl s q k w c : ℤ) - tl s q k v c) + z * ((q ^ (s * k) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hz c
      refine ⟨z, ?_⟩
      rw [hX c, hzc, hN, hpow]; simp only [hV]; ring
    have hqk : (4 : ℤ) ≤ (q : ℤ) ^ k := by
      calc (4 : ℤ) ≤ q := hqz
        _ = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ k := pow_le_pow_right₀ (by omega) (by omega)
    set x : Fin s → ℤ := fun c =>
      ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) / u with hx_def
    have hnear : ∀ c, 0 ≤ x c ∧ |V c| - 1 ≤ x c ∧
        ((tl s q k w c : ℤ) - tl s q k v c = 0 → |V c| ≤ x c) ∧
        u * x c ≤ ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hXV c
      simp only [hx_def]
      rw [hzc]
      refine near_gen (q ^ (s * k)) u (V c) _ z hu (htl c) ?_
      rw [hN, hpow]
      have := abs_add_le (u * V c) ((tl s q k w c : ℤ) - tl s q k v c)
      rw [abs_mul, abs_of_pos hu] at this
      have := hVb c; have := htl c
      have h4 : 4 * (u * q) ≤ u * q * (q : ℤ) ^ k := by
        have : 0 < u * q := by positivity
        nlinarith
      nlinarith
    have hkey := key_sym s (q : ℤ) (aU s : ℤ) haz hqaz e he hall
      (fun c => ∑ d, e d * PJ s c d (J d)) (fun c => (o0 s q k w c : ℤ) - o0 s q k v c) x
      (fun i hi => sigma_moving s i e he J hJs hi)
      (fun i hi hoth => sigma_own s i e he J hi hoth)
      (fun c => ⟨hσ c, o_bound s q k v w c⟩) (fun c => (hnear c).1) (by
        intro c
        split_ifs with honly
        · apply (hnear c).2.2.1
          have := tl_eq_of_only s q hq1 k c v w (fun d hd => he0 d (honly.2 d hd))
          rw [this]; ring
        · exact (hnear c).2.1)
    have hsq : ∀ c, (u * x c) ^ 2 ≤
        ((cres (q ^ (s * k)) ((Upoint s q k w c : ℤ) - (Upoint s q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      fun c => pow_le_pow_left₀ (mul_nonneg hu.le (hnear c).1) (hnear c).2.2.2 2
    calc (q : ℤ) ^ (2 * M) * ((q : ℤ) - aU s) ^ 2 ≤ (q : ℤ) ^ (2 * M) * ∑ c, x c ^ 2 := by
          gcongr
      _ = (q : ℤ) ^ 2 * ∑ c, (u * x c) ^ 2 := by
          rw [hu2, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun c _ => hsq c

end

/-- **Theorem U(2), exact integer form.** -/
theorem U_sep (s q k : ℕ) (hs : 3 ≤ s) (hq : Admissible s q) (hqa : 5 * aU s + 4 ≤ q)
    (hk : 2 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aU s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (Upoint s q k v) (Upoint s q k w) : ℤ) := by
  haveI : NeZero q := ⟨by have := hq.1; omega⟩
  have h := main_bound s q hs hq hqa k hk w v (Ne.symm hvw)
  unfold torusDist2
  push_cast
  exact h

end Z3NetU.Proofs
