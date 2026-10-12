/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColBasic

@[expose] public section

/-!
# V14 stage S9′: `thm:colmin` (minimum distance of column point sets) and `cor:colceil`

The printed proof: a representative of the difference of the points of the cells `n`, `n'` is
`D = q²E + Δ𝟏` with `E ≡ n' - n (mod q)`, and
`3|q²E + Δ𝟏|² = q⁴((E_x-E_y)² + (E_y-E_z)² + (E_z-E_x)²) + (q²σ_E + 3Δ)²` (`core_id`). If the three
differences vanish the pair is in one column (`|D|² ≥ 3q⁴`); if one of them is at least `2` in
absolute value, `|D|² ≥ 2q⁴`; otherwise `E = ±e_i + k𝟏` and `q²σ_E + 3Δ ≡ ±(3Δ_i - 2q²)` modulo
`3q²`. The least value is attained at a pair in neighbouring columns.

`cor:colceil`: if every step had distance more than `⅓q²` from `⅔q² + q²ℤ`, the residues modulo `q²`
of the three steps around the triangle `[n] → [n+e_x] → [n+e_x+e_y] → [n]` would lie in `(0, ⅓q²)`
and sum to a multiple of `q²`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

/-! ## Arithmetic -/

lemma core_id (Q Δ : ℤ) (E : Fin 3 → ℤ) :
    3 * ∑ c, (Q * E c + Δ) ^ 2 =
      Q ^ 2 * ((E 0 - E 1) ^ 2 + (E 1 - E 2) ^ 2 + (E 2 - E 0) ^ 2) +
        (Q * (E 0 + E 1 + E 2) + 3 * Δ) ^ 2 := by
  simp only [Fin.sum_univ_three]; ring

/-- The three cases of the proof of `thm:colmin` for an integer vector `E`. -/
lemma E_cases (E : Fin 3 → ℤ) :
    (E 0 = E 2 ∧ E 1 = E 2) ∨
      6 ≤ (E 0 - E 1) ^ 2 + (E 1 - E 2) ^ 2 + (E 2 - E 0) ^ 2 ∨
      ((E 0 - E 1) ^ 2 + (E 1 - E 2) ^ 2 + (E 2 - E 0) ^ 2 = 2 ∧
        ∃ (i : Fin 3) (k : ℤ), (∀ c, E c = (Pi.single i (1 : ℤ) : Fin 3 → ℤ) c + k) ∨
          (∀ c, E c = -(Pi.single i (1 : ℤ) : Fin 3 → ℤ) c + k)) := by
  have hc : E 2 - E 0 = -((E 0 - E 1) + (E 1 - E 2)) := by ring
  rw [hc]
  generalize ha : E 0 - E 1 = a
  generalize hb : E 1 - E 2 = b
  by_cases hA : a = 0 ∧ b = 0
  · left; constructor <;> omega
  right
  by_cases hB : 2 ≤ |a| ∨ 2 ≤ |b| ∨ 2 ≤ |a + b|
  · left
    rcases hB with h | h | h
    · have : 4 ≤ a ^ 2 := by nlinarith [sq_abs a]
      nlinarith [sq_nonneg (a + 2 * b)]
    · have : 4 ≤ b ^ 2 := by nlinarith [sq_abs b]
      nlinarith [sq_nonneg (2 * a + b)]
    · have : 4 ≤ (a + b) ^ 2 := by nlinarith [sq_abs (a + b)]
      nlinarith [sq_nonneg (a - b)]
  right
  push Not at hB
  obtain ⟨h1, h2, h3⟩ := hB
  have ha1 := abs_lt.1 h1
  have hb1 := abs_lt.1 h2
  have hab1 := abs_lt.1 h3
  rcases (show (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) ∨
      (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) by omega) with h | h | h | h | h | h <;>
    obtain ⟨rfl, rfl⟩ := h <;> refine ⟨by norm_num, ?_⟩
  · exact ⟨0, E 2, Or.inl fun c => by fin_cases c <;> simp <;> omega⟩
  · exact ⟨0, E 2, Or.inr fun c => by fin_cases c <;> simp <;> omega⟩
  · exact ⟨2, E 2 + 1, Or.inr fun c => by fin_cases c <;> simp <;> omega⟩
  · exact ⟨2, E 2 - 1, Or.inl fun c => by fin_cases c <;> simp <;> omega⟩
  · exact ⟨1, E 2, Or.inr fun c => by fin_cases c <;> simp <;> omega⟩
  · exact ⟨1, E 2, Or.inl fun c => by fin_cases c <;> simp <;> omega⟩

/-- A difference of `ZMod q` values congruent to an integer. -/
lemma val_sub_eq {q : ℕ} [NeZero q] (x y : ZMod q) (e : ℤ) (h : x - y = (e : ZMod q)) :
    ∃ m : ℤ, (x.val : ℤ) - y.val = e + q * m := by
  have h0 : (((x.val : ℤ) - y.val - e : ℤ) : ZMod q) = 0 := by
    push_cast; simp [h]
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  exact ⟨m, by linarith⟩

/-! ## `thm:colmin` -/

variable {q : ℕ} [NeZero q]

/-- `colGap` is at most each step's distance. -/
lemma colGap_le (φ : (Fin 3 → ZMod q) → ℕ) (i : Fin 3) (n : Fin 3 → ZMod q) :
    colGap q φ ≤ cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) :=
  Finset.inf'_le _ (Finset.mem_univ (i, n))

lemma colGap_two_le (hq : 0 < q) (φ : (Fin 3 → ZMod q) → ℕ) :
    2 * (colGap q φ : ℤ) ≤ 3 * q ^ 2 := by
  have h := two_cres_le (3 * q ^ 2) (by positivity) (3 * colStep q φ 0 0 - 2 * q ^ 2)
  have h2 : (colGap q φ : ℤ) ≤ cres (3 * q ^ 2) (3 * colStep q φ 0 0 - 2 * q ^ 2) := by
    exact_mod_cast colGap_le φ 0 0
  push_cast at h; linarith

lemma final_arith (Q G P X : ℤ) (hG0 : 0 ≤ G) (hG2 : 2 * G ≤ 3 * Q)
    (h : 6 ≤ P ∨ (P = 2 ∧ G ^ 2 ≤ X ^ 2) ∨ (P = 0 ∧ 9 * Q ^ 2 ≤ X ^ 2)) :
    2 * Q ^ 2 + G ^ 2 ≤ Q ^ 2 * P + X ^ 2 := by
  have hG4 : 4 * G ^ 2 ≤ 9 * Q ^ 2 := by nlinarith
  rcases h with h | ⟨h, h'⟩ | ⟨h, h'⟩
  · have := mul_le_mul_of_nonneg_left h (sq_nonneg Q)
    nlinarith [sq_nonneg X, sq_nonneg Q]
  · subst h; linarith
  · subst h; nlinarith [sq_nonneg Q]

/-- The lower bound of `thm:colmin`, in `ℤ`. -/
lemma colmin_lower (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    2 * (q : ℤ) ^ 4 + (colGap q φ : ℤ) ^ 2 ≤
      3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) := by
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
  have hG2 := colGap_two_le hq0 φ
  have hG0 : (0 : ℤ) ≤ colGap q φ := by positivity
  rw [hT, show (q : ℤ) ^ 4 = ((q : ℤ) ^ 2) ^ 2 by ring]
  apply final_arith _ _ _ _ hG0 hG2
  rcases E_cases E with ⟨h0, h1⟩ | h6 | ⟨h2, i, kk, hpm | hpm⟩
  · -- one column
    right; right
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
    refine ⟨by ring, ?_⟩
    have e : ((q : ℤ) ^ 2 * (E 2 + E 2 + E 2) + 3 * 0) ^ 2 = 9 * ((q : ℤ) ^ 2) ^ 2 * E 2 ^ 2 := by
      ring
    rw [e]
    have := sq_nonneg ((q : ℤ) ^ 2)
    nlinarith
  · left; exact h6
  · -- `E = e_i + kk 𝟏`
    right; left
    refine ⟨h2, ?_⟩
    have hn' : n' = n + Pi.single i 1 + fun _ => ((kk : ℤ) : ZMod q) := by
      funext c; have h := hcast c; rw [hpm c] at h; push_cast at h
      have hs : (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c : ℤ) : ZMod q) =
          (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c := by
        rcases eq_or_ne c i with rfl | hci <;> simp [*]
      rw [hs] at h
      have : n' c = n c + (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c + kk := by
        linear_combination -h
      simp [this]
    have hΔ' : Δ = colStep q φ i n := by
      rw [hΔ, colStep, hn', height_const hφ.2]
    have hσ : E 0 + E 1 + E 2 = 1 + 3 * kk := by
      rw [hpm 0, hpm 1, hpm 2]; fin_cases i <;> simp <;> ring
    have hle : (colGap q φ : ℤ) ≤ |(q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ| := by
      calc (colGap q φ : ℤ) ≤ cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) := by
            exact_mod_cast colGap_le φ i n
        _ ≤ |3 * colStep q φ i n - 2 * q ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (kk + 1)| :=
            cres_le _ (by positivity) _ _
        _ = |(q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ| := by
            rw [hσ, hΔ']; push_cast; ring_nf
    rw [← sq_abs ((q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ)]
    exact pow_le_pow_left₀ hG0 hle 2
  · -- `E = -e_i + kk 𝟏`
    right; left
    refine ⟨h2, ?_⟩
    have hn : n = n' + Pi.single i 1 + fun _ => ((-kk : ℤ) : ZMod q) := by
      funext c; have h := hcast c; rw [hpm c] at h; push_cast at h
      have hs : (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c : ℤ) : ZMod q) =
          (Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c := by
        rcases eq_or_ne c i with rfl | hci <;> simp [*]
      rw [hs] at h
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
    have hle : (colGap q φ : ℤ) ≤ |(q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ| := by
      calc (colGap q φ : ℤ) ≤ cres (3 * q ^ 2) (3 * colStep q φ i n' - 2 * q ^ 2) := by
            exact_mod_cast colGap_le φ i n'
        _ ≤ |3 * colStep q φ i n' - 2 * q ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (1 - kk)| :=
            cres_le _ (by positivity) _ _
        _ = |(q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ| := by
            rw [hσ, hΔ', ← abs_neg]; push_cast; ring_nf
    rw [← sq_abs ((q : ℤ) ^ 2 * (E 0 + E 1 + E 2) + 3 * Δ)]
    exact pow_le_pow_left₀ hG0 hle 2

lemma ne_shift (hq : 2 ≤ q) (n : Fin 3 → ZMod q) (i : Fin 3) (t : ZMod q) :
    n + Pi.single i 1 + (fun _ => t) ≠ n := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by simp⟩
  have h1 := congrFun h i
  have h2 := congrFun h j
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj] at h1 h2
  have h3 : (1 : ZMod q) = 0 := by linear_combination h1 - h2
  have : Fact (1 < q) := ⟨by omega⟩
  exact one_ne_zero h3

/-- The neighbouring pair of `thm:colmin`: for the cell `n`, the direction `i` and an integer `k`,
the pair `n`, `n + e_i + (k-1)𝟏` has `3 d² ≤ 2q⁴ + (3Δ_i([n]) - 2q² + 3q²k)²`. -/
lemma colmin_pair (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) (i : Fin 3)
    (n : Fin 3 → ZMod q) (k : ℤ) :
    3 * (torusDist2 (q ^ 3) (colPt q φ n)
        (colPt q φ (n + Pi.single i 1 + fun _ => (((k - 1 : ℤ)) : ZMod q))) : ℤ) ≤
      2 * (q : ℤ) ^ 4 + (3 * colStep q φ i n - 2 * q ^ 2 + 3 * q ^ 2 * k) ^ 2 := by
  have hq0 : 0 < q := by omega
  set n' := n + Pi.single i 1 + fun _ => (((k - 1 : ℤ)) : ZMod q) with hn'
  have hφn' : φ n' = φ (n + Pi.single i 1) := height_const hφ.2 _ _
  have hm : ∀ c, ∃ m : ℤ, ((n' c).val : ℤ) - (n c).val =
      ((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c + (k - 1)) + q * m := by
    intro c
    apply val_sub_eq
    simp only [hn', Pi.add_apply]
    rcases eq_or_ne c i with rfl | hci <;> simp [*]
  choose m hm using hm
  have hle := torus_le (q ^ 3) (by positivity) (colPt q φ n) (colPt q φ n') (fun c => -m c)
  have hD : ∀ c, ((colPt q φ n' c : ℕ) : ℤ) - (colPt q φ n c : ℕ) + ((q ^ 3 : ℕ) : ℤ) * (-m c) =
      (q : ℤ) ^ 2 * ((Pi.single i (1 : ℤ) : Fin 3 → ℤ) c + (k - 1)) + colStep q φ i n := by
    intro c
    simp only [colPt, colStep, hφn']
    push_cast
    have := hm c
    linear_combination (q : ℤ) ^ 2 * this
  have hsum : 3 * ∑ c, ((colPt q φ n' c : ℕ) - (colPt q φ n c : ℕ) + ((q ^ 3 : ℕ) : ℤ) * (-m c)) ^ 2 =
      2 * (q : ℤ) ^ 4 + (3 * colStep q φ i n - 2 * q ^ 2 + 3 * q ^ 2 * k) ^ 2 := by
    rw [Finset.sum_congr rfl fun c _ => by rw [hD c]]
    rw [core_id]
    fin_cases i <;> simp [Pi.single_apply] <;> ring
  linarith

lemma colmin_attained (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    ∃ (i : Fin 3) (n : Fin 3 → ZMod q) (t : ZMod q),
      n + Pi.single i 1 + (fun _ => t) ≠ n ∧
      3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ (n + Pi.single i 1 + fun _ => t)) =
        2 * q ^ 4 + colGap q φ ^ 2 := by
  have hq0 : 0 < q := by omega
  obtain ⟨⟨i, n⟩, -, hmin⟩ := Finset.exists_mem_eq_inf' (s := (univ : Finset (Fin 3 × (Fin 3 → ZMod q))))
    univ_nonempty (fun x => cres (3 * q ^ 2) (3 * colStep q φ x.1 x.2 - 2 * q ^ 2))
  have hG : colGap q φ = cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) := hmin
  obtain ⟨k, hk⟩ := cres_exists (3 * q ^ 2) (by positivity) (3 * colStep q φ i n - 2 * q ^ 2)
  refine ⟨i, n, ((k - 1 : ℤ) : ZMod q), ne_shift hq n i _, ?_⟩
  · have hup := colmin_pair hq φ hφ i n k
    have hlow := colmin_lower hq φ hφ n (n + Pi.single i 1 + fun _ => ((k - 1 : ℤ) : ZMod q))
      (ne_shift hq n i _).symm
    have e : (3 * colStep q φ i n - 2 * q ^ 2 + 3 * q ^ 2 * k) ^ 2 = (colGap q φ : ℤ) ^ 2 := by
      rw [hG, hk, sq_abs]; push_cast; ring
    rw [e] at hup
    have h := le_antisymm hup hlow
    exact_mod_cast h

/-! ## `cor:colceil` -/

/-- Every step has a residue modulo `q²` in `(0, ⅓q²)` when its distance exceeds `q²`. -/
lemma step_res (hq : 0 < q) (Δ : ℤ) (hG : (q : ℤ) ^ 2 < cres (3 * q ^ 2) (3 * Δ - 2 * q ^ 2)) :
    0 < Δ % ((q : ℤ) ^ 2) ∧ 3 * (Δ % ((q : ℤ) ^ 2)) < (q : ℤ) ^ 2 := by
  have hq2 : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  have h0 : 0 ≤ Δ % ((q : ℤ) ^ 2) := Int.emod_nonneg _ hq2.ne'
  have h1 : Δ % ((q : ℤ) ^ 2) < (q : ℤ) ^ 2 := Int.emod_lt_of_pos _ hq2
  have hΔ := Int.emod_add_mul_ediv Δ ((q : ℤ) ^ 2)
  have c0 := lt_of_lt_of_le hG (cres_le (3 * q ^ 2) (by positivity) (3 * Δ - 2 * q ^ 2)
    (-(Δ / (q : ℤ) ^ 2)))
  have c1 := lt_of_lt_of_le hG (cres_le (3 * q ^ 2) (by positivity) (3 * Δ - 2 * q ^ 2)
    (1 - Δ / (q : ℤ) ^ 2))
  have e0 : 3 * Δ - 2 * (q : ℤ) ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (-(Δ / (q : ℤ) ^ 2)) =
      3 * (Δ % (q : ℤ) ^ 2) - 2 * (q : ℤ) ^ 2 := by push_cast; linear_combination (-3) * hΔ
  have e1 : 3 * Δ - 2 * (q : ℤ) ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (1 - Δ / (q : ℤ) ^ 2) =
      3 * (Δ % (q : ℤ) ^ 2) + (q : ℤ) ^ 2 := by push_cast; linear_combination (-3) * hΔ
  rw [e0] at c0
  rw [e1] at c1
  constructor
  · rcases lt_abs.1 c1 with h | h <;> linarith
  · rcases lt_abs.1 c0 with h | h <;> linarith

lemma colceil_gap (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    colGap q φ ≤ q ^ 2 := by
  have hq0 : 0 < q := by omega
  by_contra hlt
  push Not at hlt
  have hstep : ∀ i n, 0 < colStep q φ i n % ((q : ℤ) ^ 2) ∧
      3 * (colStep q φ i n % ((q : ℤ) ^ 2)) < (q : ℤ) ^ 2 := by
    intro i n
    apply step_res hq0
    have := colGap_le φ i n
    have h2 : (q : ℤ) ^ 2 < colGap q φ := by exact_mod_cast hlt
    linarith [show (colGap q φ : ℤ) ≤ cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) by
      exact_mod_cast this]
  -- the triangle `[0] → [e_0] → [e_0 + e_1] → [𝟏] = [0]`
  have tri : colStep q φ 0 0 + colStep q φ 1 (Pi.single 0 1) +
      colStep q φ 2 (Pi.single 0 1 + Pi.single 1 1) = 0 := by
    have e : ((Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 : Fin 3 → ZMod q)) = 0 + 1 := by
      funext c; fin_cases c <;> simp
    simp only [colStep, zero_add]
    rw [e, hφ.2]; simp
  have hq2 : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  obtain ⟨a0, a1⟩ := hstep 0 0
  obtain ⟨b0, b1⟩ := hstep 1 (Pi.single 0 1)
  obtain ⟨c0, c1⟩ := hstep 2 (Pi.single 0 1 + Pi.single 1 1)
  have hdvd : (q : ℤ) ^ 2 ∣ colStep q φ 0 0 % ((q : ℤ) ^ 2) + colStep q φ 1 (Pi.single 0 1) %
      ((q : ℤ) ^ 2) + colStep q φ 2 (Pi.single 0 1 + Pi.single 1 1) % ((q : ℤ) ^ 2) := by
    have e : ∀ a b c : ℤ, a % ((q : ℤ) ^ 2) + b % ((q : ℤ) ^ 2) + c % ((q : ℤ) ^ 2) =
        (a + b + c) - (q : ℤ) ^ 2 * (a / (q : ℤ) ^ 2 + b / (q : ℤ) ^ 2 + c / (q : ℤ) ^ 2) := by
      intro a b c; simp only [Int.emod_def]; ring
    rw [e, tri, zero_sub]
    exact (Dvd.intro _ rfl).neg_right
  obtain ⟨t, ht⟩ := hdvd
  have : 0 < t := by nlinarith
  have : t < 1 := by nlinarith
  omega

lemma colceil_pair (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    ∃ n n' : Fin 3 → ZMod q, n ≠ n' ∧ torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') ≤ q ^ 4 := by
  obtain ⟨i, n, t, hne, h⟩ := colmin_attained hq φ hφ
  refine ⟨n, _, hne.symm, ?_⟩
  have hG := colceil_gap hq φ hφ
  have : colGap q φ ^ 2 ≤ q ^ 4 := by
    calc colGap q φ ^ 2 ≤ (q ^ 2) ^ 2 := Nat.pow_le_pow_left hG 2
      _ = q ^ 4 := by ring
  omega

end Z3NetC.Proofs
