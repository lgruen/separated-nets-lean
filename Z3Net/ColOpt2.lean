/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColOpt
public import Z3Net.ColConst

@[expose] public section

/-!
# V14 stage S9′: `thm:O`(3) — the optimum among column nets

The printed proof, in units of thirds (`E = 3η = q² - 3g`, `3g = colGap`): suppose `E < q² - τ`.
* `E ≢ 1 (mod 3)` and `4E < q²` (the threshold step, with `q = 5, 7` by the residue argument).
* Windows: every step value has a unique representative `x` modulo `q²` with `-E ≤ 3x ≤ q² + E`
  (`xr`, `xr_props`). Triangles `[n] → [n+e_i] → [n+e_i+e_{i'}] → [n]` have representative sums
  `0` or `q²`; the two cases put `3x` into the disjoint ranges `≤ 2E` and `≥ q² - 2E`; triangles
  that share a step have the same sum, and all steps are connected (`high_const`).
* Sum `q²` (the reflected cube, `branchH`): the periods of the `3q` cycles (here: of all `q³`
  cycles through the cells, each cycle counted `q` times) sum to `0`; for `q ≡ 1` some period is at
  least `⅔q²` (thirds: `2q²`), so `E ≥ 2q`; for `q ≡ 2` every excess is `q/3` or `-2q/3` (thirds:
  `q`, `-2q`), so `φ` is constant modulo `q`, against (1).
* Sum `0` (the cube, `branchZ`): a nonzero cycle sum forces `E ≥ 3q`; otherwise the closed walk of
  one cycle has range `R ≥ (q-1)²` (`φ` meets all `q` blocks by (1)), and a closed walk with
  up-steps `≤ ⅔E` and down-steps `≥ -⅓E` has `9R ≤ 2Eq`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ## Representatives in the window -/

/-- The representative of `Δ` modulo `q²` in the window `[-E/3, (q² + E)/3]`. -/
def xr (q : ℕ) (E Δ : ℤ) : ℤ :=
  if 3 * (Δ % ((q : ℤ) ^ 2)) ≤ (q : ℤ) ^ 2 + E then Δ % ((q : ℤ) ^ 2) else Δ % ((q : ℤ) ^ 2) - (q : ℤ) ^ 2

lemma xr_props (E Δ : ℤ) (hE : 0 ≤ E) (hG : (q : ℤ) ^ 2 - E ≤ cres (3 * q ^ 2) (3 * Δ - 2 * q ^ 2)) :
    (q : ℤ) ^ 2 ∣ Δ - xr q E Δ ∧ -E ≤ 3 * xr q E Δ ∧ 3 * xr q E Δ ≤ (q : ℤ) ^ 2 + E := by
  have hq : (0 : ℤ) < (q : ℤ) ^ 2 := by
    have : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  have h0 : 0 ≤ Δ % ((q : ℤ) ^ 2) := Int.emod_nonneg _ hq.ne'
  have h1 : Δ % ((q : ℤ) ^ 2) < (q : ℤ) ^ 2 := Int.emod_lt_of_pos _ hq
  have hΔ := Int.emod_add_mul_ediv Δ ((q : ℤ) ^ 2)
  unfold xr
  split_ifs with h
  · refine ⟨⟨Δ / (q : ℤ) ^ 2, by linarith⟩, by linarith, h⟩
  · push Not at h
    -- `3r ≥ 3q² - E`
    have hc := lt_of_lt_of_le (show (q : ℤ) ^ 2 - E - 1 < (q : ℤ) ^ 2 - E by linarith) hG
    have hle := cres_le (3 * q ^ 2) (by have := Nat.pos_of_ne_zero (NeZero.ne q); positivity)
      (3 * Δ - 2 * q ^ 2) (-(Δ / (q : ℤ) ^ 2))
    have e : 3 * Δ - 2 * (q : ℤ) ^ 2 + ((3 * q ^ 2 : ℕ) : ℤ) * (-(Δ / (q : ℤ) ^ 2)) =
        3 * (Δ % (q : ℤ) ^ 2) - 2 * (q : ℤ) ^ 2 := by push_cast; linear_combination (-3) * hΔ
    rw [e] at hle
    have h3 : 3 * (q : ℤ) ^ 2 - E ≤ 3 * (Δ % (q : ℤ) ^ 2) := by
      by_contra hc'
      push Not at hc'
      have : |3 * (Δ % (q : ℤ) ^ 2) - 2 * (q : ℤ) ^ 2| < (q : ℤ) ^ 2 - E := by
        rw [abs_lt]; constructor <;> linarith
      linarith
    refine ⟨⟨Δ / (q : ℤ) ^ 2 + 1, by linarith⟩, by linarith, by linarith⟩

/-! ## Steps, triangles, cycles -/

lemma single_three (i i' j : Fin 3) (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i' ≠ j) :
    (Pi.single i (1 : ZMod q) + Pi.single i' 1 + Pi.single j 1 : Fin 3 → ZMod q) = 1 := by
  funext c
  rcases fin3_cover i i' j c h1 h2 h3 with rfl | rfl | rfl <;>
    simp [Pi.single_apply, h1, h2, h3, h1.symm, h2.symm, h3.symm]

lemma tri_step (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) (i i' j : Fin 3) (h1 : i ≠ i')
    (h2 : i ≠ j) (h3 : i' ≠ j) (n : Fin 3 → ZMod q) :
    colStep q φ i n + colStep q φ i' (n + Pi.single i 1) +
      colStep q φ j (n + Pi.single i 1 + Pi.single i' 1) = 0 := by
  have e : n + Pi.single i 1 + Pi.single i' 1 + Pi.single j 1 = n + 1 := by
    rw [add_assoc, add_assoc, ← add_assoc (Pi.single i 1), single_three i i' j h1 h2 h3]
  simp only [colStep]
  rw [e, hφ.2]; ring

lemma step_col (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) (i : Fin 3) (n : Fin 3 → ZMod q)
    (t : ZMod q) : colStep q φ i (n + fun _ => t) = colStep q φ i n := by
  simp only [colStep]
  rw [add_right_comm, height_const hφ.2, height_const hφ.2]

lemma cyc_step (φ : (Fin 3 → ZMod q) → ℕ) (i : Fin 3) (n : Fin 3 → ZMod q) :
    ∑ t : ZMod q, colStep q φ i (n + Pi.single i t) = 0 := by
  have e : ∀ t : ZMod q, colStep q φ i (n + Pi.single i t) =
      (φ (n + Pi.single i (t + 1)) : ℤ) - φ (n + Pi.single i t) := by
    intro t; simp only [colStep]; rw [Pi.single_add, add_assoc]
  simp only [e, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

lemma sum_translate (f : (Fin 3 → ZMod q) → ℤ) (u : Fin 3 → ZMod q) :
    ∑ n, f (n + u) = ∑ n, f n :=
  Fintype.sum_equiv (Equiv.addRight u) _ _ (fun _ => rfl)

lemma sum_cycles (g : (Fin 3 → ZMod q) → ℤ) (i : Fin 3) :
    ∑ n, ∑ t : ZMod q, g (n + (Pi.single i t : Fin 3 → ZMod q)) = q * ∑ n, g n := by
  rw [Finset.sum_comm]
  simp only [sum_translate]
  simp [ZMod.card]

/-! ## Triangles in the window -/

section window

variable (φ : (Fin 3 → ZMod q) → ℕ) (E : ℤ)

/-- The representative of the step `(n, i)`. -/
def xs (i : Fin 3) (n : Fin 3 → ZMod q) : ℤ := xr q E (colStep q φ i n)

/-- The window property of all steps. -/
def Win : Prop := ∀ i n, (q : ℤ) ^ 2 ∣ colStep q φ i n - xs φ E i n ∧ -E ≤ 3 * xs φ E i n ∧
  3 * xs φ E i n ≤ (q : ℤ) ^ 2 + E

/-- A step is *high* if its representative is near `⅓q²` (the triangle sum is `q²`). -/
def High (i : Fin 3) (n : Fin 3 → ZMod q) : Prop := (q : ℤ) ^ 2 - 2 * E ≤ 3 * xs φ E i n

variable {φ E}

lemma xs_col (hφ : IsHeight q φ) (i : Fin 3) (n : Fin 3 → ZMod q) (t : ZMod q) :
    xs φ E i (n + fun _ => t) = xs φ E i n := by
  simp only [xs, step_col φ hφ]

lemma tri_x (hφ : IsHeight q φ) (hw : Win φ E) (hE : 0 ≤ E) (h4 : 4 * E < (q : ℤ) ^ 2)
    (i i' j : Fin 3) (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i' ≠ j) (n : Fin 3 → ZMod q) :
    (xs φ E i n + xs φ E i' (n + Pi.single i 1) + xs φ E j (n + Pi.single i 1 + Pi.single i' 1) = 0 ∧
      ¬ High φ E i n ∧ ¬ High φ E i' (n + Pi.single i 1) ∧
      ¬ High φ E j (n + Pi.single i 1 + Pi.single i' 1)) ∨
    (xs φ E i n + xs φ E i' (n + Pi.single i 1) + xs φ E j (n + Pi.single i 1 + Pi.single i' 1) =
        (q : ℤ) ^ 2 ∧
      High φ E i n ∧ High φ E i' (n + Pi.single i 1) ∧ High φ E j (n + Pi.single i 1 + Pi.single i' 1)) := by
  set a := xs φ E i n
  set b := xs φ E i' (n + Pi.single i 1)
  set c := xs φ E j (n + Pi.single i 1 + Pi.single i' 1)
  obtain ⟨da, a1, a2⟩ := hw i n
  obtain ⟨db, b1, b2⟩ := hw i' (n + Pi.single i 1)
  obtain ⟨dc, c1, c2⟩ := hw j (n + Pi.single i 1 + Pi.single i' 1)
  have hs := tri_step φ hφ i i' j h1 h2 h3 n
  have hd : (q : ℤ) ^ 2 ∣ a + b + c := by
    have := dvd_add (dvd_add da db) dc
    have e : colStep q φ i n - a + (colStep q φ i' (n + Pi.single i 1) - b) +
        (colStep q φ j (n + Pi.single i 1 + Pi.single i' 1) - c) = -(a + b + c) := by
      linear_combination hs
    rw [e] at this; exact (dvd_neg).1 this
  obtain ⟨m, hm⟩ := hd
  have hQ : (0 : ℤ) < (q : ℤ) ^ 2 := by
    have : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  have hm0 : 0 ≤ m := by
    by_contra h; push Not at h
    have : (q : ℤ) ^ 2 * m ≤ -(q : ℤ) ^ 2 := by nlinarith
    linarith
  have hm1 : m ≤ 1 := by
    by_contra h; push Not at h
    have : 2 * (q : ℤ) ^ 2 ≤ (q : ℤ) ^ 2 * m := by nlinarith
    linarith
  unfold High
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · left; refine ⟨by linarith, ?_, ?_, ?_⟩ <;> intro h <;> linarith
  · right; refine ⟨by linarith, ?_, ?_, ?_⟩ <;> linarith

lemma fin3_others (i : Fin 3) : i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by
  fin_cases i <;> decide

lemma high_shift (hφ : IsHeight q φ) (hw : Win φ E) (hE : 0 ≤ E) (h4 : 4 * E < (q : ℤ) ^ 2)
    (i i' j : Fin 3) (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i' ≠ j) (n : Fin 3 → ZMod q) :
    High φ E i (n + Pi.single j 1) ↔ High φ E i n := by
  have t1 := tri_x hφ hw hE h4 i i' j h1 h2 h3 (n + Pi.single j 1)
  have t2 := tri_x hφ hw hE h4 i' i j h1.symm h3 h2 (n + Pi.single j 1 + Pi.single i 1)
  have e : n + Pi.single j 1 + Pi.single i 1 + Pi.single i' 1 = n + fun _ => (1 : ZMod q) := by
    have := single_three (q := q) i i' j h1 h2 h3
    rw [show (fun _ => (1 : ZMod q)) = (1 : Fin 3 → ZMod q) from rfl, ← this]; abel
  have hx : xs φ E i (n + Pi.single j 1 + Pi.single i 1 + Pi.single i' 1) = xs φ E i n := by
    rw [e, xs_col hφ]
  have hH : High φ E i (n + Pi.single j 1 + Pi.single i 1 + Pi.single i' 1) ↔ High φ E i n := by
    unfold High; rw [hx]
  rcases t1 with ⟨-, a1, a2, -⟩ | ⟨-, a1, a2, -⟩ <;> rcases t2 with ⟨-, b1, b2, -⟩ | ⟨-, b1, b2, -⟩
  · rw [← hH]; exact ⟨fun h => absurd h a1, fun h => absurd h b2⟩
  · exact absurd b1 a2
  · exact absurd a2 b1
  · rw [← hH]; exact ⟨fun _ => b2, fun _ => a1⟩

lemma high_single (hφ : IsHeight q φ) (hw : Win φ E) (hE : 0 ≤ E) (h4 : 4 * E < (q : ℤ) ^ 2)
    (i i' j : Fin 3) (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i' ≠ j) (n : Fin 3 → ZMod q) (t : ZMod q) :
    High φ E i (n + Pi.single j t) ↔ High φ E i n := by
  have key : ∀ k : ℕ, High φ E i (n + Pi.single j (k : ZMod q)) ↔ High φ E i n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : n + Pi.single j ((k + 1 : ℕ) : ZMod q) = (n + Pi.single j (k : ZMod q)) + Pi.single j 1 := by
        push_cast; rw [Pi.single_add]; abel
      rw [e, high_shift hφ hw hE h4 i i' j h1 h2 h3, ih]
  have := key t.val
  rwa [ZMod.natCast_zmod_val] at this

lemma high_const (hq : 2 ≤ q) (hφ : IsHeight q φ) (hw : Win φ E) (hE : 0 ≤ E)
    (h4 : 4 * E < (q : ℤ) ^ 2) (i : Fin 3) (n : Fin 3 → ZMod q) :
    High φ E i n ↔ High φ E 0 0 := by
  have hdir : ∀ i (n : Fin 3 → ZMod q), High φ E i n ↔ High φ E i 0 := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := fin3_others i
    have e : n = ((fun _ => n i) + Pi.single (i + 1) (n (i + 1) - n i)) +
        Pi.single (i + 2) (n (i + 2) - n i) := by
      funext c
      rcases fin3_cover i (i + 1) (i + 2) c d1 d2 d3 with rfl | rfl | rfl
      · simp [Pi.single_eq_of_ne d1, Pi.single_eq_of_ne d2]
      · simp [Pi.single_eq_of_ne d3]
      · simp [Pi.single_eq_of_ne d3.symm]
    rw [e, high_single hφ hw hE h4 i (i + 1) (i + 2) d1 d2 d3,
      high_single hφ hw hE h4 i (i + 2) (i + 1) d2 d1 d3.symm]
    have : (fun _ => n i : Fin 3 → ZMod q) = 0 + fun _ => n i := by simp
    unfold High; rw [this, xs_col hφ]
  rw [hdir i n]
  -- `High i 0 ↔ High (i+1) e_i`, constant in the cell
  obtain ⟨d1, d2, d3⟩ := fin3_others i
  have hi : ∀ i : Fin 3, High φ E i 0 ↔ High φ E (i + 1) 0 := by
    intro i
    obtain ⟨d1, d2, d3⟩ := fin3_others i
    have t := tri_x hφ hw hE h4 i (i + 1) (i + 2) d1 d2 d3 0
    rw [← hdir (i + 1) (0 + Pi.single i 1)]
    rcases t with ⟨-, a1, a2, -⟩ | ⟨-, a1, a2, -⟩
    · exact ⟨fun h => absurd h a1, fun h => absurd h a2⟩
    · exact ⟨fun _ => a2, fun _ => a1⟩
  have h01 := hi 0
  have h12 := hi 1
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at h01
  rw [show (1 : Fin 3) + 1 = 2 from rfl] at h12
  fin_cases i
  · rfl
  · exact h01.symm
  · exact h12.symm.trans h01.symm

end window

/-! ## Common facts -/

section branches

variable {φ : (Fin 3 → ZMod q) → ℕ} {E : ℤ}

lemma cyc_dvd (hw : Win φ E) (i : Fin 3) (n : Fin 3 → ZMod q) :
    (q : ℤ) ^ 2 ∣ ∑ t : ZMod q, xs φ E i (n + Pi.single i t) := by
  have h1 := cyc_step φ i n
  have h2 : (q : ℤ) ^ 2 ∣ ∑ t : ZMod q, (colStep q φ i (n + Pi.single i t) - xs φ E i (n + Pi.single i t)) :=
    Finset.dvd_sum fun t _ => (hw i _).1
  rw [Finset.sum_sub_distrib, h1, zero_sub] at h2
  exact (dvd_neg).1 h2

/-- `φ` constant modulo `q` from steps divisible by `q`. -/
lemma phi_const_mod (hφ : IsHeight q φ) (h : ∀ i n, (q : ℤ) ∣ colStep q φ i n) (n : Fin 3 → ZMod q) :
    (q : ℤ) ∣ (φ n : ℤ) - φ 0 := by
  have hstep : ∀ i (m : Fin 3 → ZMod q) (t : ZMod q), (q : ℤ) ∣ (φ (m + Pi.single i t) : ℤ) - φ m := by
    intro i m t
    have key : ∀ k : ℕ, (q : ℤ) ∣ (φ (m + Pi.single i (k : ZMod q)) : ℤ) - φ m := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : m + Pi.single i ((k + 1 : ℕ) : ZMod q) = (m + Pi.single i (k : ZMod q)) + Pi.single i 1 := by
          push_cast; rw [Pi.single_add]; abel
        have := h i (m + Pi.single i (k : ZMod q))
        simp only [colStep] at this
        rw [e]
        have := dvd_add this ih
        rwa [show (φ (m + Pi.single i (k : ZMod q) + Pi.single i 1) : ℤ) - φ (m + Pi.single i (k : ZMod q)) +
          ((φ (m + Pi.single i (k : ZMod q)) : ℤ) - φ m) =
          (φ (m + Pi.single i (k : ZMod q) + Pi.single i 1) : ℤ) - φ m by ring] at this
    have := key t.val
    rwa [ZMod.natCast_zmod_val] at this
  have e : n = ((0 + Pi.single 0 (n 0)) + Pi.single 1 (n 1)) + Pi.single 2 (n 2) := by
    funext c; fin_cases c <;> simp
  rw [e]
  have h1 := hstep 0 0 (n 0)
  have h2 := hstep 1 (0 + Pi.single 0 (n 0)) (n 1)
  have h3 := hstep 2 (0 + Pi.single 0 (n 0) + Pi.single 1 (n 1)) (n 2)
  have := dvd_add (dvd_add h3 h2) h1
  convert this using 1; ring

lemma tri_low (hw : Win φ E) (a b c : ℤ) (i : Fin 3) (n : Fin 3 → ZMod q) (i' : Fin 3)
    (n' : Fin 3 → ZMod q) (j : Fin 3) (n'' : Fin 3 → ZMod q)
    (ha : a = xs φ E i n) (hb : b = xs φ E i' n') (hc : c = xs φ E j n'') (hs : a + b + c = 0) :
    3 * a ≤ 2 * E := by
  have := (hw i' n').2.1; have := (hw j n'').2.1
  rw [← hb] at *; rw [← hc] at *; linarith

/-! ## The branch "sum `q²`" (the reflected cube) -/

lemma branchH (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (hφ : IsHeight q φ)
    (hbij : ∀ y, y < q ^ 2 → ∃ n, φ n = y) (hw : Win φ E) (hE : 0 ≤ E) (h4 : 4 * E < (q : ℤ) ^ 2)
    (hlt : E < (q : ℤ) ^ 2 - tauCol q) (hall : ∀ i n, High φ E i n) : False := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by omega
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (q : ℤ) ^ 2 := ⟨_, rfl⟩
  -- every triangle has sum `q²`
  have htri : ∀ i n, xs φ E i n + xs φ E (i + 1) (n + Pi.single i 1) +
      xs φ E (i + 2) (n + Pi.single i 1 + Pi.single (i + 1) 1) = Q := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := fin3_others i
    rcases tri_x hφ hw hE h4 i (i + 1) (i + 2) d1 d2 d3 n with ⟨-, h, -, -⟩ | ⟨h, -⟩
    · exact absurd (hall i n) h
    · rw [hQ]; exact h
  -- the excess (thirds) `e = 3x - q²`
  obtain ⟨e, he⟩ : ∃ e : Fin 3 → (Fin 3 → ZMod q) → ℤ, e = fun i n => 3 * xs φ E i n - Q :=
    ⟨_, rfl⟩
  have heE : ∀ i n, e i n ≤ E := fun i n => by rw [he]; beta_reduce; rw [hQ]; linarith [(hw i n).2.2]
  have hetri : ∀ i n, e i n = -(e (i + 1) (n + Pi.single i 1) +
      e (i + 2) (n + Pi.single i 1 + Pi.single (i + 1) 1)) := by
    intro i n; rw [he]; beta_reduce; have := htri i n; linarith
  -- the excesses of all steps sum to `0`
  have hsumE : ∑ n, (e 0 n + e 1 n + e 2 n) = 0 := by
    obtain ⟨u0, hu0⟩ : ∃ u : Fin 3 → ZMod q, u = Pi.single 0 1 := ⟨_, rfl⟩
    obtain ⟨u1, hu1⟩ : ∃ u : Fin 3 → ZMod q, u = Pi.single 1 1 := ⟨_, rfl⟩
    have h1 : ∑ n, e 1 n = ∑ n, e 1 (n + u0) := (sum_translate (fun n => e 1 n) u0).symm
    have h2 : ∑ n, e 2 n = ∑ n, e 2 (n + u0 + u1) := by
      rw [← sum_translate (fun n => e 2 n) (u0 + u1)]
      simp only [add_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro n _
    have := htri 0 n
    rw [he]; beta_reduce
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, ← hu0, ← hu1] at this
    linarith
  -- periods
  obtain ⟨P, hP⟩ : ∃ P : Fin 3 → (Fin 3 → ZMod q) → ℤ,
      P = fun i n => ∑ t : ZMod q, e i (n + Pi.single i t) := ⟨_, rfl⟩
  have hPK : ∀ i n, ∃ K, P i n = Q * (3 * K - q) := by
    intro i n
    obtain ⟨K, hK⟩ := cyc_dvd hw i n
    rw [← hQ] at hK
    refine ⟨K, ?_⟩
    rw [hP, he]; beta_reduce
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hK]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring
  have hPsum : ∑ n, (P 0 n + P 1 n + P 2 n) = 0 := by
    rw [hP]; beta_reduce
    simp only [Finset.sum_add_distrib]
    rw [sum_cycles (fun n => e 0 n) 0, sum_cycles (fun n => e 1 n) 1, sum_cycles (fun n => e 2 n) 2,
      ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, hsumE, mul_zero]
  have hPle : ∀ i n, P i n ≤ q * E := by
    intro i n
    calc P i n ≤ ∑ _t : ZMod q, E := by rw [hP]; exact Finset.sum_le_sum fun t _ => heE i _
      _ = q * E := by simp [ZMod.card]
  rcases q_mod3 h6 with h | h
  · -- `q ≡ 1`: some period is at least `2q²`
    have ht : tauCol q = Q - 2 * q := by simp [tauCol, show q % 3 ≠ 2 by omega, hQ]
    rw [ht] at hlt
    have hex : ∃ i n, 0 ≤ P i n := by
      by_contra hc; push Not at hc
      have : ∑ n, (P 0 n + P 1 n + P 2 n) < 0 :=
        Finset.sum_neg (fun n _ => by linarith [hc 0 n, hc 1 n, hc 2 n]) univ_nonempty
      linarith
    obtain ⟨i, n, hn⟩ := hex
    obtain ⟨K, hK⟩ := hPK i n
    have hQ0 : 0 < Q := by rw [hQ]; positivity
    have hK0 : 0 ≤ 3 * K - q := by
      by_contra hc; push Not at hc
      have : Q * (3 * K - q) < 0 := mul_neg_of_pos_of_neg hQ0 hc
      linarith
    have hK2 : 2 ≤ 3 * K - q := by omega
    have := hPle i n
    rw [hK] at this
    nlinarith
  · -- `q ≡ 2`: every excess is `q` or `-2q`
    have ht : tauCol q = Q - q - 3 := by simp [tauCol, h, hQ]
    rw [ht] at hlt
    have hQ3 : Q % 3 = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
      rw [hQ, hk]; push_cast; ring_nf; omega
    have heq : ∀ i n, e i n ≤ q := by
      intro i n
      have h1 := heE i n
      have h2 : e i n % 3 = 2 := by rw [he]; beta_reduce; omega
      omega
    have hge : ∀ i n, -2 * q ≤ e i n := by
      intro i n; rw [hetri i n]; linarith [heq (i + 1) (n + Pi.single i 1),
        heq (i + 2) (n + Pi.single i 1 + Pi.single (i + 1) 1)]
    have hvals : ∀ i n, e i n = q ∨ e i n = -2 * q := by
      intro i n
      obtain ⟨K, hK⟩ := hPK i n
      have hlo : -2 * q * q ≤ P i n := by
        calc -2 * q * q = ∑ _t : ZMod q, (-2 * (q : ℤ)) := by simp [ZMod.card]; ring
          _ ≤ P i n := by rw [hP]; exact Finset.sum_le_sum fun t _ => hge i _
      have hhi : P i n ≤ q * q := by
        calc P i n ≤ ∑ _t : ZMod q, (q : ℤ) := by rw [hP]; exact Finset.sum_le_sum fun t _ => heq i _
          _ = q * q := by simp [ZMod.card]
      have hQ0 : 0 < Q := by rw [hQ]; positivity
      have hr1 : -2 ≤ 3 * K - q := by
        by_contra hc; push Not at hc
        have : Q * (3 * K - q) < Q * (-2) := mul_lt_mul_of_pos_left hc hQ0
        rw [hQ] at this hK; nlinarith
      have hr2 : 3 * K - q ≤ 1 := by
        by_contra hc; push Not at hc
        have : Q * 2 ≤ Q * (3 * K - q) := mul_le_mul_of_nonneg_left (by omega) hQ0.le
        rw [hQ] at this hK; nlinarith
      have hr : 3 * K - q = 1 ∨ 3 * K - q = -2 := by omega
      have h0 : n + Pi.single i (0 : ZMod q) = n := by simp
      rcases hr with hr | hr
      · left
        have hs : ∑ t : ZMod q, ((q : ℤ) - e i (n + Pi.single i t)) = 0 := by
          rw [Finset.sum_sub_distrib]
          have : ∑ t : ZMod q, e i (n + Pi.single i t) = Q := by
            have := hK; rw [hP] at this; beta_reduce at this; rw [this, hr, mul_one]
          rw [this]; simp [ZMod.card, hQ]; ring
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => by linarith [heq i (n + Pi.single i t)])).1 hs
          0 (mem_univ _)
        rw [h0] at this; linarith
      · right
        have hs : ∑ t : ZMod q, (e i (n + Pi.single i t) + 2 * q) = 0 := by
          rw [Finset.sum_add_distrib]
          have : ∑ t : ZMod q, e i (n + Pi.single i t) = -2 * Q := by
            have := hK; rw [hP] at this; beta_reduce at this; rw [this, hr]; ring
          rw [this]; simp [ZMod.card, hQ]; ring
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => by linarith [hge i (n + Pi.single i t)])).1 hs
          0 (mem_univ _)
        rw [h0] at this; linarith
    -- every step is divisible by `q`
    have hdivS : ∀ i n, (q : ℤ) ∣ colStep q φ i n := by
      intro i n
      have h3x : (q : ℤ) ∣ 3 * xs φ E i n := by
        rcases hvals i n with h' | h' <;> rw [he] at h' <;> beta_reduce at h'
        · exact ⟨q + 1, by rw [hQ] at h'; linarith⟩
        · exact ⟨q - 2, by rw [hQ] at h'; linarith⟩
      have hx : (q : ℤ) ∣ xs φ E i n := by
        apply Int.dvd_of_dvd_mul_right_of_gcd_one h3x
        have h3 : Nat.Coprime q 3 := Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h6
        simpa [Int.gcd] using h3
      have := (hw i n).1
      have hqq : (q : ℤ) ∣ (q : ℤ) ^ 2 := dvd_pow_self _ (by norm_num)
      have := dvd_add (dvd_trans hqq this) hx
      simpa using this
    have hc := phi_const_mod hφ hdivS
    obtain ⟨n0, hn0⟩ := hbij 0 (by positivity)
    obtain ⟨n1, hn1⟩ := hbij 1 (by nlinarith)
    have := dvd_sub (hc n1) (hc n0)
    rw [hn0, hn1] at this
    simp at this
    have := Int.le_of_dvd (by norm_num) this
    omega

end branches

/-! ## The branch "sum `0`" (the cube) -/

lemma sum_zmod_range (g : ZMod q → ℤ) : ∑ t : ZMod q, g t = ∑ t ∈ range q, g (t : ZMod q) := by
  have hb : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j h => Fin.ext ?_, by simp [ZMod.card]⟩
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at this
    exact this
  rw [← Fintype.sum_bijective _ hb (fun i : Fin q => g ((i : ℕ) : ZMod q)) g (fun _ => rfl),
    Fin.sum_univ_eq_sum_range (fun i => g (i : ZMod q)) q]

lemma div_emod_sq (V : ℤ) (q : ℤ) (hq : 0 < q) : (V % (q * q)) / q = (V / q) % q := by
  have hV := Int.emod_add_mul_ediv V (q * q)
  set r := V % (q * q)
  set a := V / (q * q)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by positivity)
  have hr1 : r < q * q := Int.emod_lt_of_pos _ (by positivity)
  have h1 : V / q = r / q + q * a := by
    rw [← hV, show r + q * q * a = r + q * (q * a) by ring, Int.add_mul_ediv_left _ _ hq.ne']
  rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.ediv_nonneg hr0 hq.le)]
  rw [Int.ediv_lt_iff_lt_mul hq]; exact hr1

section branchZsec

variable {φ : (Fin 3 → ZMod q) → ℕ} {E : ℤ}

lemma branchZ (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (hφ : IsHeight q φ)
    (hline : ∀ (c : Fin 3) n (t : ZMod q), φ (n + Pi.single c t) / q = φ n / q → t = 0)
    (hw : Win φ E) (hE : 0 ≤ E) (h4 : 4 * E < (q : ℤ) ^ 2)
    (hlt : E < (q : ℤ) ^ 2 - tauCol q) (hnone : ∀ i n, ¬ High φ E i n) : False := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by omega
  have hM : E < 2 * q := by
    rcases q_mod3 h6 with h | h
    · have : tauCol q = (q : ℤ) ^ 2 - 2 * q := by simp [tauCol, show q % 3 ≠ 2 by omega]
      rw [this] at hlt; linarith
    · have : tauCol q = (q : ℤ) ^ 2 - q - 3 := by simp [tauCol, h]
      rw [this] at hlt; linarith
  -- every triangle has sum `0`
  have htri : ∀ i n, xs φ E i n + xs φ E (i + 1) (n + Pi.single i 1) +
      xs φ E (i + 2) (n + Pi.single i 1 + Pi.single (i + 1) 1) = 0 := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := fin3_others i
    rcases tri_x hφ hw hE h4 i (i + 1) (i + 2) d1 d2 d3 n with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd h (hnone i n)
  have hup : ∀ i n, 3 * xs φ E i n ≤ 2 * E := fun i n =>
    tri_low hw _ _ _ i n (i + 1) _ (i + 2) _ rfl rfl rfl (htri i n)
  have hlo : ∀ i n, -E ≤ 3 * xs φ E i n := fun i n => (hw i n).2.1
  -- cycle sums
  obtain ⟨C, hC⟩ : ∃ C : Fin 3 → (Fin 3 → ZMod q) → ℤ,
      C = fun i n => ∑ t : ZMod q, xs φ E i (n + Pi.single i t) := ⟨_, rfl⟩
  have hCdvd : ∀ i n, (q : ℤ) ^ 2 ∣ C i n := fun i n => by rw [hC]; exact cyc_dvd hw i n
  have hxsum : ∑ n, (xs φ E 0 n + xs φ E 1 n + xs φ E 2 n) = 0 := by
    obtain ⟨u0, hu0⟩ : ∃ u : Fin 3 → ZMod q, u = Pi.single 0 1 := ⟨_, rfl⟩
    obtain ⟨u1, hu1⟩ : ∃ u : Fin 3 → ZMod q, u = Pi.single 1 1 := ⟨_, rfl⟩
    have h1 : ∑ n, xs φ E 1 n = ∑ n, xs φ E 1 (n + u0) :=
      (sum_translate (fun n => xs φ E 1 n) u0).symm
    have h2 : ∑ n, xs φ E 2 n = ∑ n, xs φ E 2 (n + u0 + u1) := by
      rw [← sum_translate (fun n => xs φ E 2 n) (u0 + u1)]
      simp only [add_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro n _
    have := htri 0 n
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, ← hu0, ← hu1] at this
    exact this
  have hCsum : ∑ n, (C 0 n + C 1 n + C 2 n) = 0 := by
    rw [hC]; beta_reduce
    simp only [Finset.sum_add_distrib]
    rw [sum_cycles (fun n => xs φ E 0 n) 0, sum_cycles (fun n => xs φ E 1 n) 1,
      sum_cycles (fun n => xs φ E 2 n) 2, ← mul_add, ← mul_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, hxsum, mul_zero]
  have hClow : ∀ i n, -((q : ℤ) * E) ≤ 3 * C i n := by
    intro i n
    rw [hC]; beta_reduce
    rw [Finset.mul_sum]
    calc -((q : ℤ) * E) = ∑ _t : ZMod q, -E := by simp [ZMod.card]
      _ ≤ _ := Finset.sum_le_sum fun t _ => hlo i _
  -- every cycle closes
  have hC0 : ∀ i n, C i n = 0 := by
    by_contra hc
    push Not at hc
    have hneg : ∃ i n, C i n < 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨i, n, hn⟩ := hc
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => by
        linarith [hpos 0 n, hpos 1 n, hpos 2 n])).1 hCsum n (mem_univ n)
      have h0 := hpos 0 n; have h1 := hpos 1 n; have h2 := hpos 2 n
      have : C 0 n = 0 ∧ C 1 n = 0 ∧ C 2 n = 0 := ⟨by linarith, by linarith, by linarith⟩
      rcases fin3_cover 0 1 2 i (by decide) (by decide) (by decide) with rfl | rfl | rfl
      · exact hn this.1
      · exact hn this.2.1
      · exact hn this.2.2
    obtain ⟨i, n, hn⟩ := hneg
    obtain ⟨K, hK⟩ := hCdvd i n
    have hK1 : K ≤ -1 := by
      by_contra h; push Not at h
      have : 0 ≤ (q : ℤ) ^ 2 * K := mul_nonneg (by positivity) (by omega)
      linarith
    have hCQ : C i n ≤ -(q : ℤ) ^ 2 := by rw [hK]; nlinarith
    have := hClow i n
    nlinarith
  -- the walk along the cycle of the cell `0` in the direction `e_0`
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℤ, y = fun t : ℕ => xs φ E 0 (Pi.single 0 (t : ZMod q)) := ⟨_, rfl⟩
  have hysum : ∑ t ∈ range q, y t = 0 := by
    have := hC0 0 0
    rw [hC] at this; beta_reduce at this
    rw [sum_zmod_range] at this
    rw [hy]; simpa using this
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℤ, V = fun t : ℕ => (φ 0 : ℤ) + ∑ s ∈ range t, y s := ⟨_, rfl⟩
  have hV1 : ∀ t : ℕ, (q : ℤ) ^ 2 ∣ V t - φ (Pi.single 0 (t : ZMod q)) := by
    intro t
    induction t with
    | zero => rw [hV]; simp
    | succ t ih =>
      have e : (Pi.single 0 ((t + 1 : ℕ) : ZMod q) : Fin 3 → ZMod q) =
          Pi.single 0 (t : ZMod q) + Pi.single 0 1 := by push_cast; rw [Pi.single_add]
      have hd := (hw 0 (Pi.single 0 (t : ZMod q))).1
      have : V (t + 1) - φ (Pi.single 0 ((t + 1 : ℕ) : ZMod q)) =
          (V t - φ (Pi.single 0 (t : ZMod q))) -
            (colStep q φ 0 (Pi.single 0 (t : ZMod q)) - xs φ E 0 (Pi.single 0 (t : ZMod q))) := by
        rw [hV, e]; beta_reduce
        rw [Finset.sum_range_succ, hy]; simp only [colStep]; ring
      rw [this]; exact dvd_sub ih hd
  have hV2 : ∀ t : ℕ, ((φ (Pi.single 0 (t : ZMod q)) / q : ℕ) : ℤ) = (V t / q) % q := by
    intro t
    obtain ⟨k, hk⟩ := hV1 t
    have hφl : (φ (Pi.single 0 (t : ZMod q)) : ℤ) < (q : ℤ) ^ 2 := by exact_mod_cast hφ.1 _
    have hm : V t % ((q : ℤ) * q) = φ (Pi.single 0 (t : ZMod q)) := by
      rw [show V t = φ (Pi.single 0 (t : ZMod q)) + (q : ℤ) * q * k by rw [← sq]; linarith,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by rw [← sq]; exact hφl)]
    rw [← div_emod_sq _ _ hq0, hm, Int.natCast_ediv]
  have hV3 : ∀ t t' : ℕ, t < q → t' < q → V t / q = V t' / q → t = t' := by
    intro t t' ht ht' h
    have h' : φ (Pi.single 0 (t' : ZMod q)) / q = φ (Pi.single 0 (t : ZMod q)) / q := by
      have := (hV2 t').trans ((congrArg (· % (q : ℤ)) h).symm.trans (hV2 t).symm)
      exact_mod_cast this
    have e : (Pi.single 0 (t' : ZMod q) : Fin 3 → ZMod q) =
        Pi.single 0 (t : ZMod q) + Pi.single 0 ((t' : ZMod q) - t) := by
      rw [← Pi.single_add]; congr 1; ring
    rw [e] at h'
    have := hline 0 _ _ h'
    have h2 : ((t : ℕ) : ZMod q) = (t' : ZMod q) := (sub_eq_zero.1 this).symm
    have := congrArg ZMod.val h2
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at this
  -- the range of the walk
  have hne : (range q).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image (range q) V hne
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (range q) V hne
  have hR : (q : ℤ) ^ 2 - 2 * q + 1 ≤ V b - V a := by
    have hcard : ((range q).image (fun t => V t / q)).card = q := by
      rw [Finset.card_image_of_injOn (fun t ht t' ht' h => hV3 t t' (by simpa using ht)
        (by simpa using ht') h), Finset.card_range]
    have hsub : (range q).image (fun t => V t / q) ⊆ Finset.Icc (V a / q) (V b / q) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_Icc.2 ⟨Int.ediv_le_ediv hq0 (hamin t ht), Int.ediv_le_ediv hq0 (hbmax t ht)⟩
    have := Finset.card_le_card hsub
    rw [hcard, Int.card_Icc] at this
    have h1 : (q : ℤ) ≤ V b / q + 1 - V a / q := by omega
    have h2 := Int.ediv_mul_le (V b) hq0.ne'
    have h3 := Int.lt_ediv_add_one_mul_self (V a) hq0
    nlinarith
  -- the closed walk: `R ≤ ∑ max(y, 0) = ∑ max(-y, 0)`
  have hPM : ∑ t ∈ range q, max (y t) 0 = ∑ t ∈ range q, max (-y t) 0 := by
    have : ∑ t ∈ range q, (max (y t) 0 - max (-y t) 0) = ∑ t ∈ range q, y t := by
      apply Finset.sum_congr rfl; intro t _
      rcases le_total 0 (y t) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [hysum, Finset.sum_sub_distrib] at this; linarith
  have hRP : V b - V a ≤ ∑ t ∈ range q, max (y t) 0 := by
    have hbq : b < q := by simpa using hb
    have haq : a < q := by simpa using ha
    rcases le_total a b with hab | hab
    · have e : V b - V a = ∑ t ∈ Finset.Ico a b, y t := by
        rw [Finset.sum_Ico_eq_sub _ hab, hV]
        beta_reduce; ring
      rw [e]
      calc ∑ t ∈ Finset.Ico a b, y t ≤ ∑ t ∈ Finset.Ico a b, max (y t) 0 :=
            Finset.sum_le_sum fun t _ => le_max_left _ _
        _ ≤ ∑ t ∈ range q, max (y t) 0 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht; simp only [Finset.mem_Ico] at ht; simp; omega
            · intro t _ _; exact le_max_right _ _
    · have e : V b - V a = -∑ t ∈ Finset.Ico b a, y t := by
        rw [Finset.sum_Ico_eq_sub _ hab, hV]
        beta_reduce; ring
      rw [e, hPM, ← Finset.sum_neg_distrib]
      calc ∑ t ∈ Finset.Ico b a, -y t ≤ ∑ t ∈ Finset.Ico b a, max (-y t) 0 :=
            Finset.sum_le_sum fun t _ => le_max_left _ _
        _ ≤ ∑ t ∈ range q, max (-y t) 0 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht; simp only [Finset.mem_Ico] at ht; simp; omega
            · intro t _ _; exact le_max_right _ _
  have hPQ : 9 * ∑ t ∈ range q, max (y t) 0 ≤ 2 * E * q := by
    have hterm : ∀ t : ℕ, 3 * max (y t) 0 + 6 * max (-y t) 0 ≤ 2 * E := by
      intro t
      have h1 := hup 0 (Pi.single 0 (t : ZMod q))
      have h2 := hlo 0 (Pi.single 0 (t : ZMod q))
      rw [show xs φ E 0 (Pi.single 0 (t : ZMod q)) = y t by rw [hy]] at h1 h2
      rcases le_total 0 (y t) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; linarith
      · rw [max_eq_right h, max_eq_left (by linarith)]; linarith
    have := Finset.sum_le_sum (s := range q) fun t _ => hterm t
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hPM] at this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  nlinarith

end branchZsec

/-! ## `thm:O`(3) -/

lemma colO_opt (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ)
    (hnet : IsNet0 3 q 3 (colPt q φ)) : (colGap q φ : ℤ) ≤ tauCol q := by
  by_contra hlt
  push Not at hlt
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  obtain ⟨⟨hbij, -⟩, hline⟩ := (colPt_net_iff (by omega) φ hφ).1 hnet
  obtain ⟨E, hEdef⟩ : ∃ E : ℤ, E = (q : ℤ) ^ 2 - colGap q φ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    have := colceil_gap (by omega) φ hφ
    rw [hEdef]; have : (colGap q φ : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast this
    linarith
  have hEM : E < (q : ℤ) ^ 2 - tauCol q := by rw [hEdef]; linarith
  -- `E ≢ 1 (mod 3)`
  have hQ3 : ((q : ℤ) ^ 2) % 3 = 1 := by
    rcases q_mod3 h6 with h | h
    · obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
      rw [hk]; push_cast; ring_nf; omega
    · obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
      rw [hk]; push_cast; ring_nf; omega
  have hG3 : (colGap q φ : ℤ) % 3 ≠ 0 := by
    obtain ⟨⟨i, n⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (univ : Finset (Fin 3 × (Fin 3 → ZMod q)))) univ_nonempty
      (fun x => cres (3 * q ^ 2) (3 * colStep q φ x.1 x.2 - 2 * q ^ 2))
    have hG : colGap q φ = cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) := hmin
    obtain ⟨k, hk⟩ := cres_exists (3 * q ^ 2) (by positivity) (3 * colStep q φ i n - 2 * q ^ 2)
    have hG' : (colGap q φ : ℤ) = |3 * colStep q φ i n - 2 * (q : ℤ) ^ 2 + 3 * ((q : ℤ) ^ 2 * k)| := by
      rw [hG, hk]; push_cast; ring_nf
    rw [hG']
    generalize colStep q φ i n = m at *
    generalize (q : ℤ) ^ 2 * k = P at *
    generalize (q : ℤ) ^ 2 = Q at *
    rcases abs_cases (3 * m - 2 * Q + 3 * P) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  have hE3 : E % 3 ≠ 1 := by rw [hEdef]; omega
  -- `4E < q²`
  have h4 : 4 * E < (q : ℤ) ^ 2 := by
    rcases coprime6_ge q h6 hq with ⟨h, h'⟩ | ⟨h, h'⟩
    · have ht : tauCol q = (q : ℤ) ^ 2 - q - 3 := by simp [tauCol, h]
      rw [ht] at hEM
      rcases (show q = 5 ∨ 6 ≤ q by omega) with rfl | h6'
      · norm_num at hEM ⊢; omega
      · have : (6 : ℤ) ≤ q := by exact_mod_cast h6'
        nlinarith
    · have ht : tauCol q = (q : ℤ) ^ 2 - 2 * q := by simp [tauCol, show q % 3 ≠ 2 by omega]
      rw [ht] at hEM
      rcases (show q = 7 ∨ 8 ≤ q by omega) with rfl | h8
      · norm_num at hEM ⊢; omega
      · have : (8 : ℤ) ≤ q := by exact_mod_cast h8
        nlinarith
  -- the windows
  have hw : Win φ E := by
    intro i n
    have hG := colGap_le φ i n
    have := xr_props (q := q) E (colStep q φ i n) hE0 (by
      rw [hEdef]; have : (colGap q φ : ℤ) ≤ cres (3 * q ^ 2) (3 * colStep q φ i n - 2 * q ^ 2) := by
        exact_mod_cast hG
      linarith)
    exact this
  by_cases hH : High φ E 0 0
  · exact branchH h6 hq hφ hbij hw hE0 h4 hEM fun i n =>
      (high_const (by omega) hφ hw hE0 h4 i n).2 hH
  · exact branchZ h6 hq hφ hline hw hE0 h4 hEM fun i n h =>
      hH ((high_const (by omega) hφ hw hE0 h4 i n).1 h)

end Z3NetC.Proofs
