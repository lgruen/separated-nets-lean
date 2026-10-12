/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DeficitDefs
public import Z3Net.FRemK
public import Z3Net.FDsep

@[expose] public section

/-!
# V14 stage S2: the first-order deficit (`def:K`), the tail certificate (`prop:Dprime`) and one
cell level (`prop:k1` (1), (2))

* `def:K` against `rem:K`: `K(F) < ∞` iff every own partial sum is `≤ 0` and every multi-axis
  configuration has a backward coordinate (`Kdef_ne_top_iff_core`), and then `K(F)` is the
  constant `Kexp` of `rem:K` (`Kdef_eq_Kexp_core`), so `LB = 1 - K(F)/q + O(q⁻²)`.
* `prop:Dprime` (`Dprime_LB_core`): for `q ≥ Q_D`, `(q - K)²` bounds `q²` and `∑ b_i²` for every
  configuration of `F` or of any truncation; the real form `1 - K/q ≤ LB`; and its application to
  `𝒫^F_{k,q}` for every `k ≥ 1` (`Dprime_sep_core`).
* `prop:k1`: (1) `δ N^{1/s} ≥ LB₁(q)` for a graph form with depths `(1, …, 1)` (`lem:Ss` at
  `k = L = 1`, toroidal, hence Euclidean), and `LB₁(q) ≥ 1 - K₁/q` for `q ≥ Q_D(K₁, S₁)`;
  (2) `LB₁(q)` is at least the relaxation of `F` with any number of levels at the same `q`, and
  every lower bound proved through `lem:Ss` for the design `F` holds for `𝒫^F_{1,q}`.
-/

namespace Z3NetF.Proofs.Deficit

open Finset Z3NetF Z3NetF.Proofs.RemK

/-! ## Capped carry classes -/

/-- The carry classes capped at `L - 1`. -/
def cap {s : ℕ} (L : ℕ) (j : Fin s → ℕ) : Fin s → ℕ := fun d => min (j d) (L - 1)

lemma sigma_cap {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) {L L' : ℕ} (h : L' ≤ L) (e : Fin s → ℤ)
    (j : Fin s → ℕ) (i : Fin s) : sigma F L' e j i = sigma F L e (cap L' j) i := by
  unfold sigma cap
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show min (min (j d) (L' - 1)) (L - 1) = min (j d) (L' - 1) by omega]

lemma bval_congr {s : ℕ} (q : ℕ) (F F' : ℕ → Fin s → Fin s → ℤ) (L L' : ℕ) (e : Fin s → ℤ)
    (j j' : Fin s → ℕ) (i : Fin s) (h : sigma F L e j i = sigma F' L' e j' i) :
    bval q F L e j i = bval q F' L' e j' i := by
  unfold bval; rw [h]

lemma bwd_congr {s : ℕ} (F F' : ℕ → Fin s → Fin s → ℤ) (L L' : ℕ) (e : Fin s → ℤ)
    (j j' : Fin s → ℕ) (h : ∀ i, sigma F L e j i = sigma F' L' e j' i) :
    bwd F L e j = bwd F' L' e j' := by
  ext i; simp [bwd, h i]

lemma cap_mem {s k L L' : ℕ} (hL' : 1 ≤ L') (hL'L : L' ≤ L) {e : Fin s → ℤ} {j : Fin s → ℕ}
    (hc : IsConfig k e j) : (e, cap L' j) ∈ cfgs s L :=
  (mem_cfgs _ _).2 ⟨hc.1, hc.2.1, fun d => by simp only [cap]; omega⟩

lemma cfgs_isConfig {s k L : ℕ} (hLk : L ≤ k) {ej : (Fin s → ℤ) × (Fin s → ℕ)}
    (h : ej ∈ cfgs s L) : IsConfig k ej.1 ej.2 := by
  obtain ⟨h1, h2, h3⟩ := (mem_cfgs ej.1 ej.2).1 h
  exact ⟨h1, h2, fun d => lt_of_lt_of_le (h3 d) hLk⟩

lemma cap_self {s L : ℕ} {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s L) :
    cap L ej.2 = ej.2 := by
  obtain ⟨_, _, h3⟩ := (mem_cfgs ej.1 ej.2).1 h
  funext d; simp only [cap]; have := h3 d; omega

/-! ## `b_i` of a backward coordinate for `|σ_i| < q` -/

lemma jit_cast {s : ℕ} (e : Fin s → ℤ) (i : Fin s) :
    ((jit e i : ℕ) : ℤ) = if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1 := by
  unfold jit; split_ifs <;> simp

lemma jit_le {s : ℕ} (e : Fin s → ℤ) (i : Fin s) : jit e i ≤ 1 := by
  unfold jit; split_ifs <;> simp

/-- A backward coordinate with `|σ_i| < q` has `b_i = q - |σ_i| - jit_i` (the proof of
`prop:Dprime`). -/
lemma bv_back1 {s : ℕ} (q : ℕ) (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ)
    (j : Fin s → ℕ) (i : Fin s) (he : -1 ≤ e i ∧ e i ≤ 1) (hq : |sigma F L e j i| < q)
    (hb : e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0) :
    bval q F L e j i = q - |sigma F L e j i| - (jit e i : ℤ) := by
  rw [jit_cast]
  set σ := sigma F L e j i with hσ
  unfold bval
  simp only [← hσ]
  generalize hjit : (if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then (0 : ℤ) else 1) = jt
  have hj : jt = 0 ∨ jt = 1 := by rw [← hjit]; split_ifs <;> simp
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

/-! ## Costs and `K(F)` -/

lemma cost_le_Kdef {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s L) : cost F L ej.1 ej.2 ≤ Kdef F L :=
  Finset.le_sup (f := fun ej : (Fin s → ℤ) × (Fin s → ℕ) => cost F L ej.1 ej.2) h

lemma Sdef_eq {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) : Sdef F L = Smax F L L := rfl

lemma sig_le_S {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) {ej : (Fin s → ℤ) × (Fin s → ℕ)}
    (h : ej ∈ cfgs s L) (i : Fin s) : |sigma F L ej.1 ej.2 i| ≤ (Sdef F L : ℤ) := by
  rw [Sdef_eq]; exact sig_le F L L h i

/-- A configuration of a design with finite `K(F) = K` has a backward coordinate, and if it has
exactly one, `b`, then `|σ_b| + jit_b ≤ K`. -/
lemma cfg_of_K {s K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hK : Kdef F L = (K : WithTop ℕ))
    {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s L) :
    (bwd F L ej.1 ej.2).card ≠ 0 ∧
      ∀ b, bwd F L ej.1 ej.2 = {b} → (sigma F L ej.1 ej.2 b).natAbs + jit ej.1 b ≤ K := by
  have hc := cost_le_Kdef F L h
  rw [hK] at hc
  constructor
  · intro h0
    simp only [cost, h0, if_true] at hc
    exact absurd hc (by simp)
  · intro b hb
    have h1 : (bwd F L ej.1 ej.2).card = 1 := by rw [hb]; rfl
    simp only [cost, h1, if_pos, one_ne_zero, if_false] at hc
    rw [hb, sum_singleton] at hc
    exact_mod_cast hc

lemma K_le_S {s K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hK : Kdef F L = (K : WithTop ℕ)) :
    K ≤ Sdef F L + 1 := by
  have : Kdef F L ≤ ((Sdef F L + 1 : ℕ) : WithTop ℕ) := by
    refine Finset.sup_le fun ej h => ?_
    obtain ⟨h0, h1⟩ := cfg_of_K F L hK h
    unfold cost
    rw [if_neg h0]
    split_ifs with hc
    · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc
      rw [hb, sum_singleton]
      have s1 := sig_le_S F L h b
      have j1 := jit_le ej.1 b
      have : (sigma F L ej.1 ej.2 b).natAbs ≤ Sdef F L := by
        have := s1; rw [abs_le_natAbs] at this; exact_mod_cast this
      exact_mod_cast (by omega : (sigma F L ej.1 ej.2 b).natAbs + jit ej.1 b ≤ Sdef F L + 1)
    · exact bot_le
  rw [hK] at this
  exact_mod_cast this

/-! ## `prop:Dprime` -/

/-- **`prop:Dprime`**, integer form: for `q ≥ Q_D(K, S)`, `B = (q - K)²` bounds `q²` and
`∑_i b_i²` for every configuration of the truncation `(F_0, …, F_{L'-1})` (any number `k` of cell
levels; `L' = L` is `F` itself). -/
theorem Dprime_LB_core {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L')
    (hL'L : L' ≤ L) (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 ∧
      ∀ e j, IsConfig k e j → ((q : ℤ) - K) ^ 2 ≤ ∑ i, bval q F L' e j i ^ 2 := by
  set S := Sdef F L with hSdef
  have hS1 : S + 1 ≤ q := le_trans (le_max_left _ _) hq
  have hKS := K_le_S F L hK
  have hKq : (K : ℤ) ≤ q := by omega
  have hK0 : (0 : ℤ) ≤ K := by positivity
  refine ⟨by nlinarith, fun e j hc => ?_⟩
  -- the second condition on `Q_D`: `√2 (q - S - 1) ≥ q - K`
  have hpair : ((q : ℤ) - K) ^ 2 ≤ 2 * ((q : ℤ) - S - 1) ^ 2 := by
    have h2 : (Real.sqrt 2 * ((S : ℝ) + 1) - K) / (Real.sqrt 2 - 1) ≤ q :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hq)
    have hs2 : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_le_iff₀ (by linarith)] at h2
    have hqK : (0 : ℝ) ≤ (q : ℝ) - K := by exact_mod_cast (by omega : (0 : ℤ) ≤ (q : ℤ) - K)
    have hle : (q : ℝ) - K ≤ Real.sqrt 2 * ((q : ℝ) - S - 1) := by nlinarith
    have hR : ((q : ℝ) - K) ^ 2 ≤ 2 * ((q : ℝ) - S - 1) ^ 2 := by
      calc ((q : ℝ) - K) ^ 2 ≤ (Real.sqrt 2 * ((q : ℝ) - S - 1)) ^ 2 :=
            pow_le_pow_left₀ hqK hle 2
        _ = 2 * ((q : ℝ) - S - 1) ^ 2 := by rw [mul_pow, sq, hss]
    exact_mod_cast hR
  -- capped configuration of `F`
  set j' := cap L' j with hj'
  have hmem : (e, j') ∈ cfgs s L := cap_mem hL' hL'L hc
  have hsig : ∀ i, sigma F L' e j i = sigma F L e j' i := fun i => sigma_cap F hL'L e j i
  have hsum : ∑ i, bval q F L' e j i ^ 2 = ∑ i, bval q F L e j' i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [bval_congr q F F L' L e j j' i (hsig i)]
  rw [hsum]
  have hsq : ∀ i, bval q F L e j' i ^ 2 ≤ ∑ i, bval q F L e j' i ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => bval q F L e j' i ^ 2) (fun i _ => sq_nonneg _) (mem_univ i)
  have hback : ∀ i ∈ bwd F L e j', bval q F L e j' i = q - |sigma F L e j' i| - (jit e i : ℤ) := by
    intro i hi
    have h' : |sigma F L e j' i| ≤ (S : ℤ) := sig_le_S F L hmem i
    exact bv_back1 q F L e j' i (hc.1 i) (by omega)
      ((mem_bwd F L e j' i).1 hi)
  obtain ⟨hne, hone⟩ := cfg_of_K F L hK hmem
  dsimp only at hne hone
  by_cases h1 : (bwd F L e j').card = 1
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
    have hbK := hone b hb
    have hbv := hback b (by rw [hb]; exact mem_singleton_self b)
    have hbK' : |sigma F L e j' b| + (jit e b : ℤ) ≤ K := by
      rw [abs_le_natAbs]; exact_mod_cast hbK
    have hpos : 0 ≤ (q : ℤ) - K := by omega
    exact (pow_le_pow_left₀ hpos (by rw [hbv]; linarith) 2).trans (hsq b)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (bwd F L e j').card)
    have va := hback a ha
    have vb := hback b hb
    have sa := sig_le_S F L hmem a
    have sb := sig_le_S F L hmem b
    have ja := jit_le e a
    have jb := jit_le e b
    have hp : bval q F L e j' a ^ 2 + bval q F L e j' b ^ 2 ≤ ∑ i, bval q F L e j' i ^ 2 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => bval q F L e j' i ^ 2)
        (subset_univ {a, b}) (fun _ _ _ => sq_nonneg _)
      rwa [Finset.sum_pair hab] at this
    simp only at sa sb
    have hA : (q : ℤ) - S - 1 ≤ bval q F L e j' a := by
      rw [va]; have : ((jit e a : ℕ) : ℤ) ≤ 1 := by exact_mod_cast ja
      linarith
    have hB : (q : ℤ) - S - 1 ≤ bval q F L e j' b := by
      rw [vb]; have : ((jit e b : ℕ) : ℤ) ≤ 1 := by exact_mod_cast jb
      linarith
    have hpos : 0 ≤ (q : ℤ) - S - 1 := by omega
    have e1' := pow_le_pow_left₀ hpos hA 2
    have e2' := pow_le_pow_left₀ hpos hB 2
    linarith

/-- `LB ≥ 1 - K/q` from the integer form. -/
lemma LBval_ge {s q L k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hq : 0 < q) (hKq : K ≤ q)
    (hB : ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 ∧
      ∀ e j, IsConfig k e j → ((q : ℤ) - K) ^ 2 ≤ ∑ i, bval q F L e j i ^ 2) :
    1 - (K : ℝ) / q ≤ LBval q F L k := by
  have hBlow : ((q : ℤ) - K) ^ 2 ≤ Bmin q F L k :=
    (Finset.le_fold_min _).2 ⟨hB.1, fun ej h => hB.2 ej.1 ej.2 ((mem_cfgs ej.1 ej.2).1 h)⟩
  have hBlowR : ((q : ℝ) - K) ^ 2 ≤ (Bmin q F L k : ℝ) := by exact_mod_cast hBlow
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) ≤ (q : ℝ) - K := by
    have : (K : ℝ) ≤ q := by exact_mod_cast hKq
    linarith
  have hs : (q : ℝ) - K ≤ Real.sqrt (Bmin q F L k) := by
    rw [← Real.sqrt_sq hpos]; exact Real.sqrt_le_sqrt hBlowR
  unfold LBval
  rw [show 1 - (K : ℝ) / q = ((q : ℝ) - K) / q by field_simp]
  exact div_le_div_of_nonneg_right hs hqR.le

/-- **`prop:Dprime`**: `LB ≥ 1 - K/q` for `q ≥ Q_D`, for `F` or any truncation. -/
theorem Dprime_core {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L')
    (hL'L : L' ≤ L) (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    1 - (K : ℝ) / q ≤ LBval q F L' k := by
  have hS1 : Sdef F L + 1 ≤ q := le_trans (le_max_left _ _) hq
  have hKS := K_le_S F L hK
  exact LBval_ge F (by omega) (by omega) (Dprime_LB_core (k := k) F hL' hL'L hK hq)

/-- **`prop:Dprime`** applied to `𝒫^F_{k,q}` (every `k ≥ 1`, without dominance): for a design
reachable by the frame (`prop:Gs`, `def:Ns`; `s - 1` levels) with `K(F) = K < ∞` and
`q ≥ Q_D(K, S(F))`, `q^(2(sk-k)) (q - K)² ≤ q² D²`, i.e. `δ ≥ (1 - K/q) q^(-k)`. -/
theorem Dprime_sep_core {R : Type*} [CommRing R] {s q K : ℕ} [NeZero q] (hs : 2 ≤ s)
    (ψ : R →+* ZMod q) (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (hK : Kdef F (s - 1) = (K : WithTop ℕ)) (hq : QD K (Sdef F (s - 1)) ≤ q) (hq3 : 3 ≤ q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  rw [PGen_map_eq]
  obtain ⟨h1, h2⟩ := PGen_H1H2 ψ k inf x hx F lam Ur β hres hβ
  have hL : 1 ≤ min k (s - 1) := by omega
  obtain ⟨hBq, hB⟩ := Dprime_LB_core (k := k) F hL (min_le_right _ _) hK hq
  exact Ss_sep_core s q k _ F _ hs hq3 hk hL (min_le_left _ _) h1 h2 _ hBq hB v w hvw

/-! ## `def:K` against `rem:K` -/

lemma one_axis {s : ℕ} {e : Fin s → ℤ} (h1 : (moving e).card = 1) :
    ∃ a, e a ≠ 0 ∧ ∀ d, d ≠ a → e d = 0 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
  refine ⟨a, ?_, fun d hd => ?_⟩
  · have : a ∈ moving e := by rw [ha]; exact mem_singleton_self a
    simpa [moving] using this
  · by_contra hc
    have : d ∈ moving e := by simp [moving, hc]
    rw [ha] at this; exact hd (mem_singleton.1 this)

lemma moving_pos {s L : ℕ} {ej : (Fin s → ℤ) × (Fin s → ℕ)} (h : ej ∈ cfgs s L) :
    1 ≤ (moving ej.1).card := by
  obtain ⟨_, ⟨d, hd⟩, _⟩ := (mem_cfgs ej.1 ej.2).1 h
  exact Finset.card_pos.2 ⟨d, by simp [moving, hd]⟩

lemma sq_one {x : ℤ} (h1 : -1 ≤ x ∧ x ≤ 1) (h0 : x ≠ 0) : x * x = 1 ∧ |x| = 1 := by
  rcases (show x = 1 ∨ x = -1 by omega) with h | h <;> subst h <;> norm_num

lemma bwd_sub_moving {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ)
    (j : Fin s → ℕ) : bwd F L e j ⊆ moving e := by
  intro i hi; simp only [bwd, moving, mem_filter, mem_univ, true_and] at hi ⊢; exact hi.1

/-- **`def:K`** vs `rem:K`: `K(F) < ∞` iff every own partial sum `M^(j)[a][a]` (`j < L`) is
`≤ 0` and every multi-axis configuration has a backward coordinate. -/
theorem Kdef_ne_top_iff_core {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    Kdef F L ≠ ⊤ ↔ (∀ a, ∀ j < L, Msum F j a a ≤ 0) ∧
      ∀ e j, IsConfig k e j → 2 ≤ (moving e).card → ∃ i, e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0 := by
  have hsup : Kdef F L ≠ ⊤ ↔ ∀ ej ∈ cfgs s L, cost F L ej.1 ej.2 ≠ ⊤ := by
    rw [← lt_top_iff_ne_top, Kdef, Finset.sup_lt_iff (WithTop.coe_lt_top 0)]
    simp only [lt_top_iff_ne_top]
  have hcost : ∀ e j, cost F L e j ≠ ⊤ ↔ (bwd F L e j).card ≠ 0 := by
    intro e j
    unfold cost
    by_cases h0 : (bwd F L e j).card = 0
    · simp [h0]
    · rw [if_neg h0]; split_ifs <;> simp [h0]
  rw [hsup]
  constructor
  · intro h
    refine ⟨fun a j0 hj0 => ?_, fun e j hc h2 => ?_⟩
    · have hm := e1_mem (k := L) a j0 hj0
      have hne := (hcost _ _).1 (h _ hm)
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
      have hi' := (mem_bwd F L _ _ i).1 hi
      have hia : i = a := by by_contra hia; exact hi'.1 (by simp [e1, hia])
      subst hia
      rw [sigma_e1, show min j0 (L - 1) = j0 by omega] at hi'
      simpa [e1] using hi'.2
    · have hm := cap_mem (k := k) hL le_rfl hc
      have hne := (hcost _ _).1 (h _ hm)
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
      rw [← bwd_congr F F L L e j (cap L j) (fun i => sigma_cap F le_rfl e j i)] at hi
      exact ⟨i, (mem_bwd F L e j i).1 hi⟩
  · rintro ⟨hown, hmulti⟩ ej hm
    rw [hcost]
    have hc := cfgs_isConfig (k := k) hLk hm
    by_cases h2 : 2 ≤ (moving ej.1).card
    · obtain ⟨i, hi⟩ := hmulti ej.1 ej.2 hc h2
      exact Finset.card_ne_zero.2 ⟨i, (mem_bwd F L ej.1 ej.2 i).2 hi⟩
    · obtain ⟨a, ha, h0⟩ := one_axis (by have := moving_pos hm; omega : (moving ej.1).card = 1)
      refine Finset.card_ne_zero.2 ⟨a, (mem_bwd F L ej.1 ej.2 a).2 ⟨ha, ?_⟩⟩
      rw [sigma_own F L ej.1 ej.2 a h0, ← mul_assoc, (sq_one (hc.1 a) ha).1, one_mul]
      exact hown a _ (by omega)

/-- **`def:K`** vs `rem:K`: a finite `K(F)` is the constant `Kexp` of `rem:K` (with any number
`k ≥ L` of cell levels). -/
theorem Kdef_eq_Kexp_core {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ)
    (h : Kdef F L ≠ ⊤) : Kdef F L = (Kexp F L k : WithTop ℕ) := by
  obtain ⟨K, hK⟩ := WithTop.ne_top_iff_exists.1 h
  rw [← hK]
  congr 1
  have hK' : Kdef F L = (K : WithTop ℕ) := hK.symm
  apply le_antisymm
  · -- every cost is at most `Kexp`
    have : Kdef F L ≤ (Kexp F L k : WithTop ℕ) := by
      refine Finset.sup_le fun ej hm => ?_
      obtain ⟨hne, _⟩ := cfg_of_K F L hK' hm
      have hc := cfgs_isConfig (k := k) hLk hm
      unfold cost
      rw [if_neg hne]
      split_ifs with h1
      · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
        rw [hb, sum_singleton]
        by_cases h2 : 2 ≤ (moving ej.1).card
        · have := K_multi F L k ((mem_cfgs _ _).2 hc) h2 b hb
          have hj : jit ej.1 b = 1 := by
            have := jit_multi ej.1 h2 b; rw [← jit_cast] at this; exact_mod_cast this
          rw [hj]; exact_mod_cast this
        · obtain ⟨a, ha, h0⟩ := one_axis (by have := moving_pos hm; omega : (moving ej.1).card = 1)
          have hba : b = a := by
            have : b ∈ moving ej.1 := bwd_sub_moving F L ej.1 ej.2 (by rw [hb]; exact mem_singleton_self b)
            by_contra hba; exact (by simpa [moving] using this : ej.1 b ≠ 0) (h0 b hba)
          subst hba
          have hj : jit ej.1 b = 0 := by unfold jit; rw [if_pos ⟨ha, h0⟩]
          have hσ := sigma_own F L ej.1 ej.2 b h0
          have hown := K_own F L k b (min (ej.2 b) (L - 1)) (by omega)
          rw [hj, add_zero, hσ, Int.natAbs_mul,
            show (ej.1 b).natAbs = 1 by
              rcases (show ej.1 b = 1 ∨ ej.1 b = -1 by have := hc.1 b; omega) with h | h <;> simp [h],
            one_mul]
          exact_mod_cast hown
      · exact bot_le
    rw [hK'] at this; exact_mod_cast this
  · -- `Kexp` is attained by a cost
    apply max_le
    · refine Finset.sup_le fun aj hm => ?_
      obtain ⟨a, j0⟩ := aj
      have hj0 : j0 < L := mem_range.1 (mem_product.1 hm).2
      have hm' := e1_mem (k := L) a j0 hj0
      obtain ⟨hne, hone⟩ := cfg_of_K F L hK' hm'
      have hb : bwd F L (e1 a) (fun _ => j0) = {a} := by
        obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        have hsub : bwd F L (e1 a) (fun _ => j0) ⊆ {a} := by
          intro x hx
          have := bwd_sub_moving F L _ _ hx
          have hx0 : e1 a x ≠ 0 := by simpa [moving] using this
          simp only [mem_singleton]; by_contra hxa; exact hx0 (by simp [e1, hxa])
        have hia : i = a := mem_singleton.1 (hsub hi)
        subst hia
        exact Finset.Subset.antisymm hsub (singleton_subset_iff.2 hi)
      have := hone a hb
      simp only at this
      rw [sigma_e1, show min j0 (L - 1) = j0 by omega] at this
      simp only
      omega
    · refine Finset.sup_le fun ej hm => ?_
      obtain ⟨hcf, h2, h1⟩ := mem_filter.1 hm
      obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
      have hcm := cap_mem (k := k) hL le_rfl ((mem_cfgs _ _).1 hcf)
      have hsig := fun i => sigma_cap F (le_refl L) ej.1 ej.2 i
      have hbw := bwd_congr F F L L ej.1 ej.2 (cap L ej.2) hsig
      obtain ⟨_, hone⟩ := cfg_of_K F L hK' hcm
      have := hone b (by simp only; rw [← hbw, hb])
      simp only at this
      rw [← hsig b] at this
      have hj : jit ej.1 b = 1 := by
        have := jit_multi ej.1 h2 b; rw [← jit_cast] at this; exact_mod_cast this
      rw [hb, sum_singleton]
      omega

/-- **`def:K`** with `rem:K`: if `K(F) = K < ∞` then `LB = 1 - K/q + O(q⁻²)`. -/
theorem K_expansion_core {s L k K : ℕ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (hK : Kdef F L = (K : WithTop ℕ)) :
    ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      1 - (K : ℝ) / q ≤ LBval q F L k ∧ LBval q F L k ≤ 1 - (K : ℝ) / q + C / (q : ℝ) ^ 2 := by
  have hne : Kdef F L ≠ ⊤ := by rw [hK]; exact WithTop.coe_ne_top
  obtain ⟨hown, hmulti⟩ := (Kdef_ne_top_iff_core hL hLk F).1 hne
  have hKe := Kdef_eq_Kexp_core hL hLk F hne
  rw [hK] at hKe
  have hKK : K = Kexp F L k := by exact_mod_cast hKe
  rw [hKK]
  exact remK_good_core hs hL hLk F hown hmulti

/-! ## `prop:k1`: one cell level -/

/-- At `k = 1`, (H1) for the design `F` with `L = 1` level is (H1) for the one-level design
`(F_0)`, and the configurations of `F` at one level are those of `(F_0)`. -/
lemma sigma_layer1 {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j j' : Fin s → ℕ)
    (hj : ∀ d, min (j d) (L - 1) = 0) (i : Fin s) :
    sigma (layer1 (F 0)) 1 e j' i = sigma F L e j i := by
  unfold sigma
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hj d, show min (j' d) (1 - 1) = 0 by omega]
  simp [Msum, layer1]

/-- **`prop:k1`(2)**: `LB₁(q)` (the relaxation of the one-level design `(F_0)`, `k = 1`) is at least
the relaxation of `F` with `L` levels at the same `q`, for every number `k ≥ 1` of cell levels. -/
theorem k1_transfer_core {s q L k : ℕ} (hk : 1 ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    Bmin q F L k ≤ Bmin q (layer1 (F 0)) 1 1 := by
  refine (Finset.le_fold_min _).2 ⟨bmin_le_sq q F L k, fun ej hm => ?_⟩
  obtain ⟨he, hne, _⟩ := (mem_cfgs ej.1 ej.2).1 hm
  have hm' : (ej.1, fun _ => 0) ∈ cfgs s k := (mem_cfgs _ _).2 ⟨he, hne, fun _ => hk⟩
  refine (bmin_le_cfg q F L k hm').trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bval_congr q F (layer1 (F 0)) L 1 ej.1 (fun _ => 0) ej.2 i
    (sigma_layer1 F L ej.1 (fun _ => 0) ej.2 (fun _ => by simp) i).symm]

theorem k1_transfer_real_core {s q L k : ℕ} (hk : 1 ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    LBval q F L k ≤ LBval q (layer1 (F 0)) 1 1 := by
  unfold LBval
  have h := k1_transfer_core (q := q) (L := L) hk F
  have hR : (Bmin q F L k : ℝ) ≤ (Bmin q (layer1 (F 0)) 1 1 : ℝ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hR) (by positivity)

/-- **`prop:k1`(2)**: every lower bound proved through `lem:Ss` for the design `F` (with any number
`L ≥ 1` of levels and `k' ≥ 1` cell levels) holds for `𝒫^F_{1,q}`. -/
theorem k1_Ns_sep_core {R : Type*} [CommRing R] {s q L k' : ℕ} [NeZero q] (hs : 2 ≤ s)
    (hq : 3 ≤ q) (ψ : R →+* ZMod q) (hk' : 1 ≤ k') (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, IsConfig k' e j → B ≤ ∑ i, bval q F L e j i ^ 2)
    (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * 1 - 1)) * B ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * 1))
        (digPoint q (s * 1) (fun c => (PGen 1 inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (digPoint q (s * 1) (fun c => (PGen 1 inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  rw [PGen_map_eq]
  obtain ⟨h1, h2⟩ := PGen_H1H2 ψ 1 inf x hx F lam Ur β hres hβ
  rw [show min 1 (s - 1) = 1 by omega] at h1
  refine Ss_sep_core s q 1 _ F 1 hs hq le_rfl le_rfl le_rfl h1 h2 B hBq (fun e j hc => ?_) v w hvw
  have hc' : IsConfig k' e (fun _ => 0) := ⟨hc.1, hc.2.1, fun _ => hk'⟩
  refine (hB e _ hc').trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  have e1 := sigma_layer1 F L e (fun _ => 0) j (fun _ => by simp) i
  have e2 := sigma_layer1 F 1 e j j (fun d => by have := hc.2.2 d; omega) i
  rw [bval_congr q F F L 1 e (fun _ => 0) j i (e1.symm.trans e2)]

/-- `δ N^{1/s} ≥ LB` in real form from the integer form at `k = 1` (`N = q^s`). -/
lemma real_of_int {s q : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q) (B D2 : ℤ) (hB0 : 0 ≤ B)
    (h : (q : ℤ) ^ (2 * (s * 1 - 1)) * B ≤ (q : ℤ) ^ 2 * D2) :
    Real.sqrt B / q * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤ Real.sqrt D2 / (q : ℝ) ^ (s * 1) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (s : ℝ) ≠ 0 := by have : (0 : ℝ) < s := by exact_mod_cast hs
                               exact this.ne'
  have hpow : ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) = (q : ℝ)⁻¹ := by
    rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    rw [show (s : ℝ) * -(1 / (s : ℝ)) = -1 by field_simp]
    exact Real.rpow_neg_one _
  rw [hpow]
  have hR : (q : ℝ) ^ (2 * (s * 1 - 1)) * B ≤ (q : ℝ) ^ 2 * D2 := by exact_mod_cast h
  have hD0 : (0 : ℝ) ≤ D2 := by
    have : (0 : ℝ) ≤ (q : ℝ) ^ (2 * (s * 1 - 1)) * B := by
      have : (0 : ℝ) ≤ B := by exact_mod_cast hB0
      positivity
    have h2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    nlinarith
  -- `q^(s-1) √B ≤ q √D2`
  have hsq : (q : ℝ) ^ (s * 1 - 1) * Real.sqrt B ≤ q * Real.sqrt D2 := by
    have l : ((q : ℝ) ^ (s * 1 - 1) * Real.sqrt B) ^ 2 = (q : ℝ) ^ (2 * (s * 1 - 1)) * B := by
      rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hB0), ← pow_mul, mul_comm (s * 1 - 1) 2]
    have r : ((q : ℝ) * Real.sqrt D2) ^ 2 = (q : ℝ) ^ 2 * D2 := by
      rw [mul_pow, Real.sq_sqrt hD0]
    exact pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero |>.1 (by rw [l, r]; exact hR)
  have hqs : (q : ℝ) ^ (s * 1) = (q : ℝ) ^ (s * 1 - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  have lhs : Real.sqrt B / q * (q : ℝ)⁻¹ = Real.sqrt B / (q * q) := by field_simp
  rw [lhs, hqs, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hsq hqR.le
  calc Real.sqrt B * ((q : ℝ) ^ (s * 1 - 1) * q) = (q : ℝ) ^ (s * 1 - 1) * Real.sqrt B * q := by ring
    _ ≤ q * Real.sqrt D2 * q := this
    _ = Real.sqrt D2 * (q * q) := by ring

/-- `cres N u ≤ |u|` (`N > 0`): the toroidal distance is at most the Euclidean one (as
`Z3NetF.Proofs.AsS11.cres_le_abs`). -/
lemma cres_le_abs (N : ℕ) (hN : 0 < N) (u : ℤ) : (cres N u : ℤ) ≤ |u| := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hm0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have hmN : u % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have hdm := Int.mul_ediv_add_emod u (N : ℤ)
  have ht : (((u % (N : ℤ)).toNat : ℕ) : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg hm0
  have htN : (u % (N : ℤ)).toNat ≤ N := by omega
  unfold cres
  rcases le_or_gt 0 u with hu | hu
  · have hd : 0 ≤ u / (N : ℤ) := Int.ediv_nonneg hu hN'.le
    have : ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) ≤
        (((u % (N : ℤ)).toNat : ℕ) : ℤ) := by exact_mod_cast min_le_left _ _
    rw [abs_of_nonneg hu]
    nlinarith
  · have hd : u / (N : ℤ) < 0 := Int.ediv_neg_of_neg_of_pos hu hN'
    have : ((min (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) : ℕ) : ℤ) ≤
        ((N - (u % (N : ℤ)).toNat : ℕ) : ℤ) := by exact_mod_cast min_le_right _ _
    rw [Nat.cast_sub htN, ht] at this
    rw [abs_of_neg hu]
    nlinarith

lemma sqrt_sum_div {s : ℕ} (N : ℝ) (hN : 0 < N) (a : Fin s → ℝ) :
    Real.sqrt (∑ c, (a c / N) ^ 2) = Real.sqrt (∑ c, a c ^ 2) / N := by
  have : ∑ c, (a c / N) ^ 2 = (∑ c, a c ^ 2) / N ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN.le]

/-- (H1) at `k = L = 1` from the first offset rows. -/
lemma H1_layer1 {s q : ℕ} (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q)) :
    H1 (layer1 F₀) 1 Φ := by
  intro c d r hr j
  rw [Subsingleton.elim j 0, h1 c d r hr]
  simp [layer1]

/-- **`prop:k1`(1)**, the integer form: `q^(2(s-1)) q² LB₁² ≤ q² D²` for any two distinct points. -/
lemma k1_sep_int {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * 1 - 1)) * Bmin q (layer1 F₀) 1 1 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * 1)) (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v)
        (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w) : ℤ) := by
  have hH1 : H1 (layer1 F₀) 1 Φ := H1_layer1 F₀ Φ h1
  have hBq : Bmin q (layer1 F₀) 1 1 ≤ (q : ℤ) ^ 2 := bmin_le_sq q _ 1 1
  have hB : ∀ e j, IsConfig 1 e j → Bmin q (layer1 F₀) 1 1 ≤ ∑ i, bval q (layer1 F₀) 1 e j i ^ 2 :=
    fun e j hc => bmin_le_cfg q (layer1 F₀) 1 1 (ej := (e, j)) ((mem_cfgs e j).2 hc)
  exact Ss_sep_core s q 1 Φ (layer1 F₀) 1 hs hq le_rfl le_rfl le_rfl hH1 h2 _ hBq hB v w hvw

/-- **`prop:k1`(1)**: `δ N^{1/s} ≥ LB₁(q)` for the toroidal distance (`N = q^s`). -/
theorem k1_sep_core {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2) := by
  have h := k1_sep_int hs hq F₀ Φ h1 h2 v w hvw
  have hr := real_of_int (by omega) (by omega) _ _ (bmin_nonneg q _ 1 1) h
  rw [sqrt_sum_div _ (by positivity)]
  unfold LBval
  refine hr.trans (le_of_eq ?_)
  congr 2
  unfold torusDist2
  push_cast
  rfl

/-- **`prop:k1`(1)**, "hence Euclidean": `δ N^{1/s} ≥ LB₁(q)` for the Euclidean distance. -/
theorem k1_sep_eucl_core {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, (((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℝ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℝ)) /
          (q : ℝ) ^ (s * 1)) ^ 2) := by
  refine (k1_sep_core hs hq F₀ Φ h1 h2 v w hvw).trans (Real.sqrt_le_sqrt ?_)
  refine Finset.sum_le_sum fun c _ => ?_
  have hN : (0 : ℝ) < (q : ℝ) ^ (s * 1) := by have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
                                              positivity
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set X := digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ)
  have hc := cres_le_abs (q ^ (s * 1)) (pow_pos (by omega) _) ((X v c : ℤ) - (X w c : ℤ))
  have hc0 : (0 : ℤ) ≤ (cres (q ^ (s * 1)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) := by positivity
  have hsq : ((cres (q ^ (s * 1)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ)) ^ 2 ≤ ((X v c : ℤ) - (X w c : ℤ)) ^ 2 := by
    rw [← sq_abs ((X v c : ℤ) - _)]; exact pow_le_pow_left₀ hc0 hc 2
  have : (((cres (q ^ (s * 1)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ)) ^ 2 ≤ ((X v c : ℝ) - (X w c : ℝ)) ^ 2 := by
    exact_mod_cast hsq
  exact this

/-- **`prop:k1`(1)**, the tail: `LB₁(q) ≥ 1 - K₁/q` for `q ≥ Q_D(K₁, S₁)`. -/
theorem k1_tail_core {s q K₁ : ℕ} (F₀ : Fin s → Fin s → ℤ)
    (hK : Kdef (layer1 F₀) 1 = (K₁ : WithTop ℕ)) (hq : QD K₁ (Sdef (layer1 F₀) 1) ≤ q) :
    1 - (K₁ : ℝ) / q ≤ LBval q (layer1 F₀) 1 1 :=
  Dprime_core (layer1 F₀) le_rfl le_rfl hK hq

end Z3NetF.Proofs.Deficit
