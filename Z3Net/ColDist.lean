/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColNet2

@[expose] public section

/-!
# V14 stage S9′: the minimum distance of `𝒞_q` (`thm:col`(2), (3)) and `lem:drift`(3), (4)

* `colmin_cases`: the case analysis of the proof of `thm:colmin`, keeping the pair: either
  `3d² ≥ 6q⁴`, or the pair lies in neighbouring columns `[a]`, `[a + e_i]` (in one of the two
  orders), with `3d² = 2q⁴ + (3Δ_i([a]) - 2q² + 3q²K)²` and the difference `q²(e_i + k𝟏) + Δ_i`.
* `col_closest`: the closest pairs of `𝒞_q` are exactly the pairs whose difference is `±D` modulo
  `q³` (the step along `e_y` resp. `e_z` without a wrap of the third digit).
* `col_pair`: the pair `𝟏`, `e_y` (resp. `e_z`) attains `d`, also in the Euclidean distance.
* `cCol`: monotone within each residue class, the values at `q = 5, 7, 37, 41`, the expansions with
  explicit `O(q⁻³)` constants (`2` resp. `1`), and `cCol → 1`.
* `drift_eta` (`lem:drift`(3)), `drift_net` (`lem:drift`(4)).
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ## The case analysis of `thm:colmin`, keeping the pair -/

lemma colmin_cases (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    6 * (q : ℤ) ^ 4 ≤ 3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) ∨
    ∃ (a b : Fin 3 → ZMod q) (i : Fin 3) (kk : ℤ) (m : Fin 3 → ℤ),
      ((a = n ∧ b = n') ∨ (a = n' ∧ b = n)) ∧
      3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) =
        2 * (q : ℤ) ^ 4 + (3 * colStep q φ i a - 2 * q ^ 2 + 3 * q ^ 2 * (kk + 1)) ^ 2 ∧
      ∀ c, ((colPt q φ b c : ℕ) : ℤ) - (colPt q φ a c : ℕ) =
        (q : ℤ) ^ 2 * ((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c + kk) + colStep q φ i a +
          (q : ℤ) ^ 3 * m c := by
  have hq0 : 0 < q := by omega
  obtain ⟨k, hk⟩ := torus_exists (q ^ 3) (by positivity) (colPt q φ n) (colPt q φ n')
  obtain ⟨E, hEdef⟩ : ∃ E : Fin 3 → ℤ, E = fun c => ((n' c).val : ℤ) - (n c).val + q * k c :=
    ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℤ, Δ = (φ n' : ℤ) - φ n := ⟨_, rfl⟩
  have hD : ∀ c, ((colPt q φ n' c : ℕ) : ℤ) - (colPt q φ n c : ℕ) + ((q ^ 3 : ℕ) : ℤ) * k c =
      (q : ℤ) ^ 2 * E c + Δ := by
    intro c; rw [hEdef, hΔ]; simp only [colPt]; push_cast; ring
  have hT : 3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) =
      ((q : ℤ) ^ 2) ^ 2 * ((E 0 - E 1) ^ 2 + (E 1 - E 2) ^ 2 + (E 2 - E 0) ^ 2) +
        ((q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ) ^ 2 := by
    rw [hk, ← core_id]; congr 1; exact Finset.sum_congr rfl fun c _ => by rw [hD c]
  have hcast : ∀ c, ((E c : ℤ) : ZMod q) = n' c - n c := by
    intro c; rw [hEdef]; simp
  have hQ : (0 : ℤ) ≤ ((q : ℤ) ^ 2) ^ 2 := by positivity
  rw [hT, show (q : ℤ) ^ 4 = ((q : ℤ) ^ 2) ^ 2 by ring]
  rcases E_cases E with ⟨h0, h1⟩ | h6 | ⟨h2, i, kk, hpm | hpm⟩
  · left
    have hc' : ∀ c, E c = E 2 := by intro c; fin_cases c <;> simp [h0, h1]
    have hn' : n' = n + fun _ => ((E 2 : ℤ) : ZMod q) := by
      funext c; have h := hcast c; rw [hc' c] at h; simp only [Pi.add_apply]; rw [h]; ring
    have hΔ0 : Δ = 0 := by
      rw [hΔ, hn', height_const hφ.2]; ring
    have hE2 : E 2 ≠ 0 := by
      intro h; apply hne; rw [hn', h]; funext c; simp
    have : 1 ≤ E 2 ^ 2 := by
      have : 0 < E 2 ^ 2 := by positivity
      omega
    rw [h0, h1, hΔ0]
    have e : ((q : ℤ) ^ 2) ^ 2 * ((E 2 - E 2) ^ 2 + (E 2 - E 2) ^ 2 + (E 2 - E 2) ^ 2) +
        ((q : ℤ) ^ 2 * (E 2 + E 2 + E 2) + 3 * 0) ^ 2 = 9 * ((q : ℤ) ^ 2) ^ 2 * E 2 ^ 2 := by ring
    rw [e]; nlinarith
  · left
    have := mul_le_mul_of_nonneg_left h6 hQ
    nlinarith [sq_nonneg ((q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ)]
  · right
    have hs : ∀ c, (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c : ℤ) : ZMod q) =
        (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c := by
      intro c; rcases eq_or_ne c i with rfl | hci <;> simp [*]
    have hn' : n' = n + Pi.single i 1 + fun _ => ((kk : ℤ) : ZMod q) := by
      funext c; have h := hcast c; rw [hpm c] at h; push_cast at h; rw [hs] at h
      have : n' c = n c + (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c + kk := by
        linear_combination -h
      simp [this]
    have hΔ' : Δ = colStep q φ i n := by
      rw [hΔ, colStep, hn', height_const hφ.2]
    have hσ : E 0 + E 1 + E 2 = 1 + 3 * kk := by
      rw [hpm 0, hpm 1, hpm 2]; fin_cases i <;> simp <;> ring
    refine ⟨n, n', i, kk, fun c => -k c, Or.inl ⟨rfl, rfl⟩, ?_, fun c => ?_⟩
    · rw [h2, hσ, hΔ']; ring
    · have := hD c
      rw [hpm c, hΔ'] at this
      push_cast at this
      linear_combination this
  · right
    have hs : ∀ c, (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c : ℤ) : ZMod q) =
        (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c := by
      intro c; rcases eq_or_ne c i with rfl | hci <;> simp [*]
    have hn : n = n' + Pi.single i 1 + fun _ => ((-kk : ℤ) : ZMod q) := by
      funext c; have h := hcast c; rw [hpm c] at h; push_cast at h; rw [hs] at h
      have : n c = n' c + (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c + -kk := by
        linear_combination h
      simp [this]
    have hΔ' : Δ = -colStep q φ i n' := by
      have : φ n = φ (n' + Pi.single i 1) := by
        conv_lhs => rw [hn]
        exact height_const hφ.2 _ _
      rw [hΔ, colStep, this]; ring
    have hσ : E 0 + E 1 + E 2 = 3 * kk - 1 := by
      rw [hpm 0, hpm 1, hpm 2]; fin_cases i <;> simp <;> ring
    refine ⟨n', n, i, -kk, fun c => k c, Or.inr ⟨rfl, rfl⟩, ?_, fun c => ?_⟩
    · rw [h2, hσ, hΔ']; ring
    · have := hD c
      rw [hpm c, hΔ'] at this
      push_cast at this
      linear_combination -this

/-! ## `𝒞_q` -/

/-- The heights of `𝒞_q`. -/
abbrev phiC (q : ℕ) : (Fin 3 → ZMod q) → ℕ := colPhi q (wCol q) ellCol

lemma isHeight_phiC (h6 : Nat.Coprime q 6) : IsHeight q (phiC q) := by
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  exact isHeight_colPhi q _ _ hw0 hw3 (by simp [ellCol, Fin.sum_univ_three])

lemma digPoint_colGen (n : Fin 3 → ZMod q) : digPoint q 3 (colGen q) n = colPt q (phiC q) n :=
  digPoint_colGenW q _ _ n

lemma tau_lt (hq : 5 ≤ q) : 0 < tauCol q ∧ tauCol q < (q : ℤ) ^ 2 := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  unfold tauCol; split_ifs <;> constructor <;> nlinarith

/-- `𝒞_q`: `2q⁴ + τ² ≤ 3d²` for every pair. -/
lemma col_lower (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
      3 * (torusDist2 (q ^ 3) (colPt q (phiC q) n) (colPt q (phiC q) n') : ℤ) := by
  have h := colmin_lower (by omega) (phiC q) (isHeight_phiC h6) n n' hne
  rwa [col_gap h6 hq] at h

lemma DCol_vals1 (h : q % 3 = 1) : ∃ A B : ℤ, 2 * (q : ℤ) ^ 2 - 2 * q = 3 * A ∧
    (q : ℤ) ^ 2 + 2 * q = 3 * B ∧ DCol q = ![-A, -A, B] := by
  obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have hA : 2 * (q : ℤ) ^ 2 - 2 * q = 3 * (6 * t ^ 2 + 2 * t) := by rw [ht]; push_cast; ring
  have hB : (q : ℤ) ^ 2 + 2 * q = 3 * (3 * t ^ 2 + 4 * t + 1) := by rw [ht]; push_cast; ring
  refine ⟨_, _, hA, hB, ?_⟩
  simp only [DCol, show q % 3 ≠ 2 by omega, if_false, hA, hB]
  simp

lemma DCol_vals2 (h : q % 3 = 2) : ∃ A B : ℤ, 2 * (q : ℤ) ^ 2 - q - 3 = 3 * A ∧
    (q : ℤ) ^ 2 + q + 3 = 3 * B ∧ DCol q = ![-A, B, -A] := by
  obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  have hA : 2 * (q : ℤ) ^ 2 - q - 3 = 3 * (6 * t ^ 2 + 7 * t + 1) := by rw [ht]; push_cast; ring
  have hB : (q : ℤ) ^ 2 + q + 3 = 3 * (3 * t ^ 2 + 5 * t + 3) := by rw [ht]; push_cast; ring
  refine ⟨_, _, hA, hB, ?_⟩
  simp only [DCol, h, if_true, hA, hB]
  simp

/-- The closest difference: `3|D|² = 2q⁴ + τ²`. -/
lemma DCol_norm (h6 : Nat.Coprime q 6) :
    3 * ∑ c, DCol q c ^ 2 = 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  rcases q_mod3 h6 with h | h
  · obtain ⟨A, B, hA, hB, hD⟩ := DCol_vals1 h
    have ht : tauCol q = (q : ℤ) ^ 2 - 2 * q := by simp [tauCol, show q % 3 ≠ 2 by omega]
    rw [hD, ht]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : (9 : ℤ) * (3 * ((-A) ^ 2 + (-A) ^ 2 + B ^ 2)) =
        9 * (2 * (q : ℤ) ^ 4 + ((q : ℤ) ^ 2 - 2 * q) ^ 2) := by
      have e : (9 : ℤ) * (3 * ((-A) ^ 2 + (-A) ^ 2 + B ^ 2)) = 3 * (2 * (3 * A) ^ 2 + (3 * B) ^ 2) := by
        ring
      rw [e, ← hA, ← hB]; ring
    exact mul_left_cancel₀ (by norm_num) this
  · obtain ⟨A, B, hA, hB, hD⟩ := DCol_vals2 h
    have ht : tauCol q = (q : ℤ) ^ 2 - q - 3 := by simp [tauCol, h]
    rw [hD, ht]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have : (9 : ℤ) * (3 * ((-A) ^ 2 + B ^ 2 + (-A) ^ 2)) =
        9 * (2 * (q : ℤ) ^ 4 + ((q : ℤ) ^ 2 - q - 3) ^ 2) := by
      have e : (9 : ℤ) * (3 * ((-A) ^ 2 + B ^ 2 + (-A) ^ 2)) = 3 * (2 * (3 * A) ^ 2 + (3 * B) ^ 2) := by
        ring
      rw [e, ← hA, ← hB]; ring
    exact mul_left_cancel₀ (by norm_num) this

/-- The direction of the closest step: `e_y` for `q ≡ 2`, `e_z` for `q ≡ 1 (mod 3)`. -/
def iStar (q : ℕ) : Fin 3 := if q % 3 = 2 then 1 else 2

/-- `D = q² e_{i*} + (q a_{i*} + r_{i*} - q²) 𝟏`. -/
lemma DCol_eq (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (c : Fin 3) :
    DCol q c = (q : ℤ) ^ 2 * (Pi.single (iStar q) (1 : ℤ) : Fin 3 → ℤ) c +
      (q * colA q (wCol q) (iStar q) + (((ellCol (iStar q) : ℤ) : ZMod q)).val - (q : ℤ) ^ 2) := by
  have h1 : ((((1 : ℤ) : ZMod q)).val : ℤ) = 1 := val_intCast_of 1 (by norm_num) (by omega)
  rcases q_mod3 h6 with h | h
  · have hi : iStar q = 2 := by simp [iStar, show q % 3 ≠ 2 by omega]
    have ha : 3 * colA q (wCol q) 2 = q + 2 := by
      simp only [colA, wCol, show q % 3 ≠ 2 by omega, if_false]
      simp; omega
    have hqa : 3 * ((q : ℤ) * colA q (wCol q) 2) = (q : ℤ) ^ 2 + 2 * q := by
      rw [show 3 * ((q : ℤ) * colA q (wCol q) 2) = q * (3 * colA q (wCol q) 2) by ring, ha]; ring
    rw [hi]
    have e2 : ((((ellCol 2 : ℤ) : ZMod q)).val : ℤ) = 0 := by
      show ((((0 : ℤ) : ZMod q)).val : ℤ) = 0
      simp
    rw [e2]
    obtain ⟨A, B, hA, hB, hD⟩ := DCol_vals1 h
    rw [hD]
    rcases fin3_cases c with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.single_apply] <;> norm_num <;> linarith
  · have hi : iStar q = 1 := by simp [iStar, h]
    have ha : 3 * colA q (wCol q) 1 = q + 1 := by
      simp only [colA, wCol, h, if_true]
      simp; omega
    have hqa : 3 * ((q : ℤ) * colA q (wCol q) 1) = (q : ℤ) ^ 2 + q := by
      rw [show 3 * ((q : ℤ) * colA q (wCol q) 1) = q * (3 * colA q (wCol q) 1) by ring, ha]; ring
    rw [hi]
    have e1 : ((((ellCol 1 : ℤ) : ZMod q)).val : ℤ) = 1 := h1
    rw [e1]
    obtain ⟨A, B, hA, hB, hD⟩ := DCol_vals2 h
    rw [hD]
    rcases fin3_cases c with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.single_apply] <;> norm_num <;> linarith

/-! ## The closest pairs of `𝒞_q` -/

lemma closest_arith (e M Q K : ℤ) (hQ : 0 < Q) (h1 : e ≤ M) (h2 : M ≤ Q) (h3 : 0 ≤ M)
    (h4 : 0 < e + Q + M) (hY : (e - Q + 3 * Q * K) ^ 2 = (Q - M) ^ 2) : K = 0 ∧ e = M := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · exfalso
    have hK' : K ≤ -1 := by omega
    have : e - Q + 3 * Q * K ≤ e - 4 * Q := by nlinarith
    have hlt : e - Q + 3 * Q * K < -(Q - M) := by linarith
    have : (Q - M) ^ 2 < (e - Q + 3 * Q * K) ^ 2 := by nlinarith
    linarith
  · refine ⟨rfl, ?_⟩
    simp only [mul_zero, add_zero] at hY
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hY with h' | h' <;> linarith
  · exfalso
    have hK' : 1 ≤ K := by omega
    have : e + 2 * Q ≤ e - Q + 3 * Q * K := by nlinarith
    have : Q - M < e - Q + 3 * Q * K := by linarith
    have : (Q - M) ^ 2 < (e - Q + 3 * Q * K) ^ 2 := by nlinarith
    linarith

/-- The values `ε_i` of `𝒞_q`, the maximum `M = q² - τ`, its unique direction `i*`. -/
lemma col_eps (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    ∃ M : ℤ, tauCol q = (q : ℤ) ^ 2 - M ∧ 0 ≤ M ∧ M ≤ 2 * q ∧
      (q : ℤ) * wCol q (iStar q) + 3 * (((ellCol (iStar q) : ℤ) : ZMod q)).val = M ∧
      ∀ i, ((q : ℤ) * wCol q i + 3 * (((ellCol i : ℤ) : ZMod q)).val ≤ M ∧
        -(q : ℤ) ≤ (q : ℤ) * wCol q i + 3 * (((ellCol i : ℤ) : ZMod q)).val ∧
        ((q : ℤ) * wCol q i + 3 * (((ellCol i : ℤ) : ZMod q)).val = M → i = iStar q)) := by
  obtain ⟨-, h2v, h1v⟩ := col_vals h6 hq
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  rcases q_mod3 h6 with h | h
  · obtain ⟨e0, e1, e2⟩ := h1v h
    have hi : iStar q = 2 := by simp [iStar, show q % 3 ≠ 2 by omega]
    refine ⟨2 * q, by simp [tauCol, show q % 3 ≠ 2 by omega], by omega, le_refl _, by rw [hi, e2],
      fun i => ?_⟩
    rw [hi]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [e0]; refine ⟨by omega, by omega, fun h => by omega⟩
    · rw [e1]; refine ⟨by omega, by omega, fun h => by omega⟩
    · rw [e2]; exact ⟨le_refl _, by omega, fun _ => rfl⟩
  · obtain ⟨e0, e1, e2⟩ := h2v h
    have hi : iStar q = 1 := by simp [iStar, h]
    refine ⟨q + 3, by simp [tauCol, h]; ring, by omega, by omega, by rw [hi, e1], fun i => ?_⟩
    rw [hi]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [e0]; refine ⟨by omega, by omega, fun h => by omega⟩
    · rw [e1]; exact ⟨le_refl _, by omega, fun _ => rfl⟩
    · rw [e2]; refine ⟨by omega, by omega, fun h => by omega⟩

/-- **`thm:col`(2)**, closest pairs: two points of `𝒞_q` are closest if and only if their difference
is `±D` modulo `q³`. -/
lemma col_closest (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    3 * (torusDist2 (q ^ 3) (colPt q (phiC q) n) (colPt q (phiC q) n') : ℤ) =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ↔
      (∀ c, ((colPt q (phiC q) n' c : ℕ) : ℤ) ≡ (colPt q (phiC q) n c : ℕ) + DCol q c
        [ZMOD (q : ℤ) ^ 3]) ∨
      (∀ c, ((colPt q (phiC q) n' c : ℕ) : ℤ) ≡ (colPt q (phiC q) n c : ℕ) - DCol q c
        [ZMOD (q : ℤ) ^ 3]) := by
  have hq0 : 0 < q := by omega
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hQ : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  constructor
  · intro heq
    obtain ⟨τp, τl⟩ := tau_lt hq
    rcases colmin_cases (by omega) (phiC q) (isHeight_phiC h6) n n' hne with h | h
    · exfalso
      have : tauCol q ^ 2 < ((q : ℤ) ^ 2) ^ 2 := by nlinarith
      nlinarith
    obtain ⟨a, b, i, kk, m, hab, hT, hdiff⟩ := h
    obtain ⟨hval, -, -⟩ := col_vals h6 hq
    obtain ⟨-, hw3, -, -⟩ := wCol_props (q := q) h6
    obtain ⟨M, hτ, hM0, hM2, hMi, hMall⟩ := col_eps h6 hq
    obtain ⟨κ, hκ⟩ : ∃ x, x = wrapI q (colH q (wCol q) a).val (((colA q (wCol q) i : ℤ) : ZMod q)).val :=
      ⟨_, rfl⟩
    obtain ⟨κ', hκ'⟩ : ∃ x, x = wrapI q (colJ q ellCol a).val (((ellCol i : ℤ) : ZMod q)).val :=
      ⟨_, rfl⟩
    obtain ⟨ε, hε⟩ : ∃ x, x = (q : ℤ) * wCol q i + 3 * (((ellCol i : ℤ) : ZMod q)).val := ⟨_, rfl⟩
    have hS : 3 * colStep q (phiC q) i a - 2 * (q : ℤ) ^ 2 =
        (ε - 3 * q * κ') - (q : ℤ) ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (-κ) := by
      rw [hε, hκ', hκ]; exact step3 (wCol q) ellCol hw3 i (hval i) a
    have hSf : colStep q (phiC q) i a = q * colA q (wCol q) i + (((ellCol i : ℤ) : ZMod q)).val
        - (q : ℤ) ^ 2 * κ - q * κ' := by
      have := step_formula (wCol q) ellCol i a
      rw [hval i, ← hκ, ← hκ'] at this
      exact this
    have hY : ((ε - 3 * q * κ') - (q : ℤ) ^ 2 + 3 * (q : ℤ) ^ 2 * (kk + 1 - κ)) ^ 2 =
        ((q : ℤ) ^ 2 - M) ^ 2 := by
      have e1 : 3 * colStep q (phiC q) i a - 2 * (q : ℤ) ^ 2 + 3 * (q : ℤ) ^ 2 * (kk + 1) =
          (ε - 3 * q * κ') - (q : ℤ) ^ 2 + 3 * (q : ℤ) ^ 2 * (kk + 1 - κ) := by
        rw [hS]; push_cast; ring
      rw [← e1, ← hτ]
      linarith
    have hκ01 : κ' = 0 ∨ κ' = 1 := by rw [hκ']; exact wrapI_cases _ _
    obtain ⟨hεM, hεl, hεu⟩ := hMall i
    rw [← hε] at hεM hεl hεu
    have hq0' : (0 : ℤ) ≤ q := by positivity
    have hcl := closest_arith (ε - 3 * q * κ') M ((q : ℤ) ^ 2) (kk + 1 - κ) hQ
      (by rcases hκ01 with h | h <;> rw [h] <;> linarith)
      (by nlinarith) hM0
      (by rcases hκ01 with h | h <;> rw [h] <;> nlinarith) hY
    obtain ⟨hK, he⟩ := hcl
    have hκ'0 : κ' = 0 := by
      rcases hκ01 with h | h
      · exact h
      · rw [h] at he; linarith
    have hεeq : ε = M := by rw [hκ'0] at he; linarith
    have hi : i = iStar q := hεu hεeq
    have hkk : kk = κ - 1 := by linarith
    have hX : ∀ c, ((colPt q (phiC q) b c : ℕ) : ℤ) = (colPt q (phiC q) a c : ℕ) + DCol q c +
        (q : ℤ) ^ 3 * m c := by
      intro c
      have h1 := hdiff c
      have h2 := DCol_eq h6 hq c
      rw [← hi] at h2
      linear_combination h1 - h2 + hSf + (q : ℤ) ^ 2 * hkk - (q : ℤ) * hκ'0
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; intro c
      rw [hX c]
      exact (Int.modEq_iff_dvd.2 ⟨m c, by ring⟩).symm
    · right; intro c
      have := hX c
      rw [show ((colPt q (phiC q) a c : ℕ) : ℤ) = (colPt q (phiC q) b c : ℕ) - DCol q c -
        (q : ℤ) ^ 3 * m c by linarith]
      exact (Int.modEq_iff_dvd.2 ⟨-m c, by ring⟩).symm
  · intro h
    have hlow := col_lower h6 hq n n' hne
    have hup : 3 * (torusDist2 (q ^ 3) (colPt q (phiC q) n) (colPt q (phiC q) n') : ℤ) ≤
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
      rw [← DCol_norm h6]
      rcases h with h | h
      · have hm : ∀ c, ∃ m : ℤ, ((colPt q (phiC q) n' c : ℕ) : ℤ) - (colPt q (phiC q) n c : ℕ) =
            DCol q c + (q : ℤ) ^ 3 * m := by
          intro c
          obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.1 (h c).symm
          exact ⟨m, by linarith⟩
        choose m hm using hm
        have := torus_le (q ^ 3) (by positivity) (colPt q (phiC q) n) (colPt q (phiC q) n')
          (fun c => -m c)
        beta_reduce at this
        have e : ∑ c, (((colPt q (phiC q) n' c : ℕ) : ℤ) - (colPt q (phiC q) n c : ℕ) +
            ((q ^ 3 : ℕ) : ℤ) * (-m c)) ^ 2 = ∑ c, DCol q c ^ 2 := by
          apply Finset.sum_congr rfl; intro c _; rw [hm c]; push_cast; ring
        linarith
      · have hm : ∀ c, ∃ m : ℤ, ((colPt q (phiC q) n' c : ℕ) : ℤ) - (colPt q (phiC q) n c : ℕ) =
            -DCol q c + (q : ℤ) ^ 3 * m := by
          intro c
          obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.1 (h c).symm
          exact ⟨m, by linarith⟩
        choose m hm using hm
        have := torus_le (q ^ 3) (by positivity) (colPt q (phiC q) n) (colPt q (phiC q) n')
          (fun c => -m c)
        beta_reduce at this
        have e : ∑ c, (((colPt q (phiC q) n' c : ℕ) : ℤ) - (colPt q (phiC q) n c : ℕ) +
            ((q ^ 3 : ℕ) : ℤ) * (-m c)) ^ 2 = ∑ c, DCol q c ^ 2 := by
          apply Finset.sum_congr rfl; intro c _; rw [hm c]; push_cast; ring
        linarith
    linarith

/-- **`thm:col`(2)**, a closest pair without a wrap: the cells `𝟏` and `e_{i*}` (Euclidean
difference exactly `D`). -/
lemma col_pair (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (1 : Fin 3 → ZMod q) ≠ Pi.single (iStar q) 1 ∧
    ∀ c, ((colPt q (phiC q) (Pi.single (iStar q) 1) c : ℕ) : ℤ) - (colPt q (phiC q) 1 c : ℕ) =
      DCol q c := by
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  obtain ⟨hval, -, -⟩ := col_vals h6 hq
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  refine ⟨fun h => ?_, fun c => ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ iStar q := ⟨iStar q + 1, by simp⟩
    have := congrFun h j
    simp [Pi.single_eq_of_ne hj] at this
  · have hH1 : colH q (wCol q) 1 = 0 := by
      have : ∑ d, colA q (wCol q) d = q := sum_colA q _ hw0 hw3
      simp only [colH, Pi.one_apply, mul_one]
      rw [← Int.cast_sum, this]; simp
    have hJ1 : colJ q ellCol 1 = 0 := by
      simp [colJ, ellCol, Fin.sum_univ_three]
    have hHi : colH q (wCol q) (Pi.single (iStar q) 1) = ((colA q (wCol q) (iStar q) : ℤ) : ZMod q) := by
      have := colH_add_single (wCol q) (0 : Fin 3 → ZMod q) (iStar q) 1
      simpa [colH] using this
    have hJi : colJ q ellCol (Pi.single (iStar q) 1) = ((ellCol (iStar q) : ℤ) : ZMod q) := by
      have := colJ_add_single ellCol (0 : Fin 3 → ZMod q) (iStar q) 1
      simpa [colJ] using this
    simp only [colPt, phiC, colPhi, hH1, hJ1, hHi, hJi, ZMod.val_zero, mul_zero, add_zero]
    rw [DCol_eq h6 hq c]
    push_cast
    rw [hval]
    rcases eq_or_ne c (iStar q) with rfl | hc
    · simp [ZMod.val_one]; try ring
    · simp [Pi.single_eq_of_ne hc, ZMod.val_one]; try ring

end Z3NetC.Proofs
