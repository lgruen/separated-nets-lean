/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColShared
public import Z3Net.ColNet

@[expose] public section

/-!
# V14 stage S9′: `thm:O`(1), (2) — which column point sets are nets

(1) The point of the cell `n` has the digits `n_c`, `⌊φ/q⌋`, `φ mod q`. The box of shape `(1,1,1)`
holds one point per cell; a box with depth `3` on `c` prescribes `n_c` and `φ`, and the cells with a
given `n_c` meet every column once, so these boxes hold one point each iff `φ` is a bijection
`T → {0, …, q²-1}`; a box with depth `2` on `c`, `1` on `c'`, `0` on `c''` prescribes `n_c`, `n_{c'}`,
`⌊φ/q⌋`, and the cells with given `n_c`, `n_{c'}` form a line in the direction `e_{c''}`
(`colPt_net_iff`; the converse direction through `net_of_inj`, injectivity of every box map).

(2) For even `q`: a level set of `⌊φ/q⌋` among the cells `(x, y, 0)` is the graph of a permutation
`π` (once in every row and column) with `y ↦ π(y) - y` a permutation too (once on every line of
slope `1`, through the columns), so `∑_y (π(y) - y) = 0` and `= ∑ ℤ/qℤ = q/2 ≠ 0`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-- The net property from the injectivity of every box map. -/
lemma net_of_inj {s m : ℕ} (X : (Fin m → ZMod q) → Fin s → ℕ) (hlt : ∀ v c, X v c < q ^ m)
    (hinj : ∀ d : Fin s → ℕ, ∑ c, d c = m →
      ∀ v w, (∀ c, X v c / q ^ (m - d c) = X w c / q ^ (m - d c)) → v = w) :
    IsNet0 s q m X := by
  intro d hd A hA
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdle : ∀ c, d c ≤ m := fun c => by
    rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  let f : (Fin m → ZMod q) → ((c : Fin s) → Fin (q ^ d c)) := fun v c =>
    ⟨X v c / q ^ (m - d c), by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' (hdle c)]
      exact hlt v c⟩
  have hfi : Function.Injective f := by
    intro v w h
    exact hinj d hd v w fun c => congrArg Fin.val (congrFun h c)
  have hcard : Fintype.card (Fin m → ZMod q) = Fintype.card ((c : Fin s) → Fin (q ^ d c)) := by
    simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, Finset.card_univ]
    rw [Finset.prod_pow_eq_pow_sum, hd]
  obtain ⟨v, hv⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, hcard⟩).2
    (fun c => ⟨A c, hA c⟩)
  refine ⟨v, fun c => congrArg Fin.val (congrFun hv c), fun w hw => hfi ?_⟩
  rw [hv]; funext c; exact Fin.ext (hw c)

lemma colPt_lt (φ : (Fin 3 → ZMod q) → ℕ) (hφ : ∀ n, φ n < q ^ 2) (n : Fin 3 → ZMod q) (c : Fin 3) :
    colPt q φ n c < q ^ 3 := by
  have h1 := ZMod.val_lt (n c)
  have h2 := hφ n
  unfold colPt
  calc q ^ 2 * (n c).val + φ n < q ^ 2 * (n c).val + q ^ 2 := by omega
    _ = q ^ 2 * ((n c).val + 1) := by ring
    _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ h1
    _ = q ^ 3 := by ring

lemma colPt_div (φ : (Fin 3 → ZMod q) → ℕ) (hφ : ∀ n, φ n < q ^ 2) (n : Fin 3 → ZMod q)
    (c : Fin 3) :
    colPt q φ n c / q ^ 3 = 0 ∧ colPt q φ n c / q ^ 2 = (n c).val ∧
      colPt q φ n c / q = q * (n c).val + φ n / q ∧ colPt q φ n c / q ^ 0 = colPt q φ n c := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine ⟨Nat.div_eq_of_lt (colPt_lt φ hφ n c), ?_, ?_, by simp⟩
  · unfold colPt
    rw [add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (hφ n), zero_add]
  · unfold colPt
    rw [show q ^ 2 * (n c).val + φ n = φ n + q * (q * (n c).val) by ring,
      Nat.add_mul_div_left _ _ hq]
    ring

lemma fin3_cover (x y z d : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d = x ∨ d = y ∨ d = z := by
  rcases x with ⟨x, hx⟩; rcases y with ⟨y, hy⟩; rcases z with ⟨z, hz⟩; rcases d with ⟨d, hd⟩
  simp only [ne_eq, Fin.mk.injEq] at *
  omega

/-- The lines of `T`: the cells `n + t e_c`. -/
lemma single_diff (n n' : Fin 3 → ZMod q) (c : Fin 3) (h : ∀ d, d ≠ c → n d = n' d) :
    n' = n + Pi.single c (n' c - n c) := by
  funext d
  by_cases hd : d = c
  · subst hd; simp
  · simp [Pi.single_eq_of_ne hd, h d hd]

/-- **`thm:O`(1)**. -/
lemma colPt_net_iff (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    IsNet0 3 q 3 (colPt q φ) ↔
      ((∀ y, y < q ^ 2 → ∃ n, φ n = y) ∧
        (∀ n n', φ n = φ n' → ∃ t : ZMod q, n' = n + fun _ => t)) ∧
      (∀ (c : Fin 3) n (t : ZMod q), φ (n + Pi.single c t) / q = φ n / q → t = 0) := by
  have hq0 : 0 < q := by omega
  have hdiv := colPt_div φ hφ.1
  constructor
  · intro hnet
    -- boxes with depth `3` on coordinate `0`
    have hbox3 : ∀ y : ℕ, y < q ^ 3 → ∃! v, colPt q φ v 0 = y := by
      intro y hy
      obtain ⟨v, hv, hu⟩ := hnet ![3, 0, 0] (by simp [Fin.sum_univ_three]) ![y, 0, 0]
        (by intro c; fin_cases c <;> simp [hy])
      refine ⟨v, by simpa using hv 0, fun w hw => hu w fun c => ?_⟩
      fin_cases c
      · simpa using hw
      · simpa using (hdiv w 1).1
      · simpa using (hdiv w 2).1
    refine ⟨⟨fun y hy => ?_, fun n n' h => ?_⟩, fun c n t h => ?_⟩
    · obtain ⟨v, hv, -⟩ := hbox3 y (by
        calc y < q ^ 2 := hy
          _ ≤ q ^ 3 := Nat.pow_le_pow_right hq0 (by norm_num))
      refine ⟨v, ?_⟩
      have h1 := hφ.1 v
      unfold colPt at hv
      have : (v 0).val = 0 := by
        by_contra h0
        have : q ^ 2 ≤ q ^ 2 * (v 0).val := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
        omega
      rw [this] at hv; simpa using hv
    · refine ⟨n' 0 - n 0, ?_⟩
      have hm : φ (n + fun _ => n' 0 - n 0) = φ n' := by rw [height_const hφ.2, h]
      obtain ⟨v, -, hu⟩ := hbox3 (colPt q φ n' 0) (colPt_lt φ hφ.1 n' 0)
      have e1 := hu n' rfl
      have e2 := hu (n + fun _ => n' 0 - n 0) (by
        show colPt q φ (n + fun _ => n' 0 - n 0) 0 = colPt q φ n' 0
        unfold colPt; rw [hm]; simp)
      exact e1.trans e2.symm
    · -- the box with depth `2` on `c + 1`, `1` on `c + 2`, `0` on `c`
      set c1 := c + 1 with hc1
      set c2 := c + 2 with hc2
      have h01 : c ≠ c1 := by rw [hc1]; simp
      have h02 : c ≠ c2 := by rw [hc2]; fin_cases c <;> decide
      have h12 : c1 ≠ c2 := by rw [hc1, hc2]; fin_cases c <;> decide
      set d : Fin 3 → ℕ := Pi.single c1 2 + Pi.single c2 1 with hd
      have hd1 : d c1 = 2 := by simp [hd, Pi.single_eq_of_ne h12]
      have hd2 : d c2 = 1 := by simp [hd, Pi.single_eq_of_ne h12.symm]
      have hd0 : d c = 0 := by simp [hd, Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h02]
      have hds : ∑ c', d c' = 3 := by
        simp only [hd, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']; simp
      have hm : ∀ c' : Fin 3, c' = c ∨ c' = c1 ∨ c' = c2 := fun c' => by
        rw [hc1, hc2]; fin_cases c <;> fin_cases c' <;> simp
      obtain ⟨v, hv, hu⟩ := hnet d hds (fun c' => colPt q φ n c' / q ^ (3 - d c')) (by
        intro c'
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
        have : d c' ≤ 3 := by
          rw [← hds]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c')
        rw [Nat.add_sub_cancel' this]
        exact colPt_lt φ hφ.1 n c')
      have e1 := hu n (fun _ => rfl)
      have e2 := hu (n + Pi.single c t) (by
        intro c'
        rcases hm c' with rfl | rfl | rfl
        · rw [hd0]; simp only [Nat.sub_zero]; rw [(hdiv _ _).1, (hdiv _ _).1]
        · rw [hd1]; simp only [show 3 - 2 = 1 by rfl, pow_one]
          rw [(hdiv _ _).2.2.1, (hdiv _ _).2.2.1, h]
          simp [Pi.single_eq_of_ne h01.symm]
        · rw [hd2]; simp only [show 3 - 1 = 2 by rfl]
          rw [(hdiv _ _).2.1, (hdiv _ _).2.1]
          simp [Pi.single_eq_of_ne h02.symm])
      have := congrFun (e2.trans e1.symm) c
      simpa using this
  · rintro ⟨⟨-, hcol⟩, hline⟩
    have hq2 : 0 < q ^ 2 := by positivity
    have inj3 : ∀ c v w, colPt q φ v c = colPt q φ w c → v = w := by
      intro c v w h
      unfold colPt at h
      have h1 : (v c).val = (w c).val := by
        have := congrArg (fun x => x / q ^ 2) h
        rwa [add_comm, Nat.add_mul_div_left _ _ hq2, Nat.div_eq_of_lt (hφ.1 v), zero_add,
          add_comm, Nat.add_mul_div_left _ _ hq2, Nat.div_eq_of_lt (hφ.1 w), zero_add] at this
      have h2 : φ v = φ w := by rw [h1] at h; omega
      obtain ⟨t, ht⟩ := hcol v w h2
      have hvc : v c = w c := ZMod.val_injective _ h1
      have : t = 0 := by
        have := congrFun ht c; simp only [Pi.add_apply] at this
        rw [← hvc] at this; simpa using this.symm
      rw [ht, this]; funext c; simp
    have inj21 : ∀ c1 c2 c3 : Fin 3, c1 ≠ c2 → c1 ≠ c3 → c2 ≠ c3 → ∀ v w,
        colPt q φ v c1 / q = colPt q φ w c1 / q → colPt q φ v c2 / q ^ 2 = colPt q φ w c2 / q ^ 2 →
        v = w := by
      intro c1 c2 c3 h12 h13 h23 v w e1 e2
      rw [(hdiv v c1).2.2.1, (hdiv w c1).2.2.1] at e1
      rw [(hdiv v c2).2.1, (hdiv w c2).2.1] at e2
      have hb1 : φ v / q < q := by
        rw [Nat.div_lt_iff_lt_mul hq0]; have := hφ.1 v; nlinarith
      have hb2 : φ w / q < q := by
        rw [Nat.div_lt_iff_lt_mul hq0]; have := hφ.1 w; nlinarith
      have hv1 : (v c1).val = (w c1).val := by
        have := congrArg (fun x => x / q) e1
        rwa [add_comm, Nat.add_mul_div_left _ _ hq0, Nat.div_eq_of_lt hb1, zero_add, add_comm,
          Nat.add_mul_div_left _ _ hq0, Nat.div_eq_of_lt hb2, zero_add] at this
      have hφq : φ v / q = φ w / q := by rw [hv1] at e1; omega
      have hagree : ∀ d, d ≠ c3 → v d = w d := by
        intro d hd
        have hm : d = c1 ∨ d = c2 := by
          rcases fin3_cover c1 c2 c3 d h12 h13 h23 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hd
        rcases hm with rfl | rfl
        · exact ZMod.val_injective _ hv1
        · exact ZMod.val_injective _ e2
      have hw := single_diff v w c3 hagree
      have ht := hline c3 v (w c3 - v c3) (by rw [← hw]; exact hφq.symm)
      rw [hw, ht]; simp
    apply net_of_inj _ (colPt_lt φ hφ.1)
    intro d hd v w hvw
    rcases sum_three_cases d hd with h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact inj3 0 v w (by simpa using hvw 0)
    · exact inj3 1 v w (by simpa using hvw 1)
    · exact inj3 2 v w (by simpa using hvw 2)
    · exact inj21 0 1 2 (by decide) (by decide) (by decide) v w (by simpa using hvw 0) (by simpa using hvw 1)
    · exact inj21 0 2 1 (by decide) (by decide) (by decide) v w (by simpa using hvw 0) (by simpa using hvw 2)
    · exact inj21 1 0 2 (by decide) (by decide) (by decide) v w (by simpa using hvw 1) (by simpa using hvw 0)
    · exact inj21 1 2 0 (by decide) (by decide) (by decide) v w (by simpa using hvw 1) (by simpa using hvw 2)
    · exact inj21 2 0 1 (by decide) (by decide) (by decide) v w (by simpa using hvw 2) (by simpa using hvw 0)
    · exact inj21 2 1 0 (by decide) (by decide) (by decide) v w (by simpa using hvw 2) (by simpa using hvw 1)
    · funext c
      apply ZMod.val_injective
      have := hvw c
      fin_cases c <;> simpa [(hdiv v _).2.1, (hdiv w _).2.1] using this

/-! ## `thm:O`(2): even `q` -/

lemma sum_zmod (q : ℕ) [NeZero q] : ∑ x : ZMod q, x = ((∑ i ∈ range q, i : ℕ) : ZMod q) := by
  have hb : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j h => Fin.ext ?_, by simp [ZMod.card]⟩
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at this
    exact this
  rw [← Fintype.sum_bijective _ hb (fun i : Fin q => ((i : ℕ) : ZMod q)) (fun x => x) (fun _ => rfl),
    ← Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun i => i) q]

lemma even_sum_ne (hq : 2 ≤ q) (he : Even q) : ∑ x : ZMod q, x ≠ 0 := by
  rw [sum_zmod]
  intro h
  obtain ⟨r, hr⟩ := he
  have hS := Finset.sum_range_id_mul_two q
  have hd := (ZMod.natCast_eq_zero_iff _ q).1 h
  set S := ∑ i ∈ range q, i
  have hS' : S = r * (2 * r - 1) := by
    have : S * 2 = 2 * r * (2 * r - 1) := by rw [hS, hr]; ring_nf
    have h2 : S * 2 = r * (2 * r - 1) * 2 := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  rw [hS', hr, show r + r = r * 2 by ring] at hd
  have hr0 : 0 < r := by omega
  have := Nat.dvd_of_mul_dvd_mul_left hr0 hd
  omega

/-- **`thm:O`(2)**: for even `q` no column point set is a `(0,3,3)`-net. -/
lemma colPt_not_net_even (hq : 2 ≤ q) (he : Even q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    ¬ IsNet0 3 q 3 (colPt q φ) := by
  intro hnet
  have hq0 : 0 < q := by omega
  obtain ⟨⟨-, -⟩, hline⟩ := (colPt_net_iff hq φ hφ).1 hnet
  let cell : ZMod q → ZMod q → ZMod q → (Fin 3 → ZMod q) := fun x y z => ![x, y, z]
  have hlt : ∀ n, φ n / q < q := fun n => by
    rw [Nat.div_lt_iff_lt_mul hq0]; have := hφ.1 n; nlinarith
  -- in every row a unique `x` with `⌊φ/q⌋ = 0`
  have hrow : ∀ y : ZMod q, ∃ x, φ (cell x y 0) / q = 0 := by
    intro y
    let f : ZMod q → Fin q := fun x => ⟨φ (cell x y 0) / q, hlt _⟩
    have hfi : Function.Injective f := by
      intro x x' h
      have h' : φ (cell x y 0 + Pi.single 0 (x' - x)) / q = φ (cell x y 0) / q := by
        have e : cell x y 0 + Pi.single 0 (x' - x) = cell x' y 0 := by
          funext c; fin_cases c <;> simp [cell]
        rw [e]; exact (congrArg Fin.val h).symm
      have := hline 0 _ _ h'
      exact (sub_eq_zero.1 this).symm
    have hcard : Fintype.card (ZMod q) = Fintype.card (Fin q) := by simp [ZMod.card]
    obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, hcard⟩).2 ⟨0, hq0⟩
    exact ⟨x, congrArg Fin.val hx⟩
  choose π hπ using hrow
  have hπi : Function.Injective π := by
    intro y y' h
    have h' : φ (cell (π y) y 0 + Pi.single 1 (y' - y)) / q = φ (cell (π y) y 0) / q := by
      have e : cell (π y) y 0 + Pi.single 1 (y' - y) = cell (π y') y' 0 := by
        funext c; fin_cases c <;> simp [cell, h]
      rw [e, hπ, hπ]
    exact (sub_eq_zero.1 (hline 1 _ _ h')).symm
  have hcol : ∀ y, φ (cell (π y - y) 0 (-y)) / q = 0 := by
    intro y
    have e : cell (π y - y) 0 (-y) = cell (π y) y 0 + fun _ => -y := by
      funext c; fin_cases c <;> simp [cell]; ring
    rw [e, height_const hφ.2]; exact hπ y
  have hgi : Function.Injective (fun y => π y - y) := by
    intro y y' h
    simp only at h
    have h' : φ (cell (π y - y) 0 (-y) + Pi.single 2 (y - y')) / q = φ (cell (π y - y) 0 (-y)) / q := by
      have e : cell (π y - y) 0 (-y) + Pi.single 2 (y - y') = cell (π y' - y') 0 (-y') := by
        funext c; fin_cases c <;> simp [cell, h]; ring
      rw [e, hcol, hcol]
    exact sub_eq_zero.1 (hline 2 _ _ h')
  have hπb : Function.Bijective π := (Finite.injective_iff_bijective).1 hπi
  have hgb : Function.Bijective (fun y => π y - y) := (Finite.injective_iff_bijective).1 hgi
  have s1 : ∑ y : ZMod q, π y = ∑ y : ZMod q, y :=
    Fintype.sum_bijective π hπb _ _ (fun _ => rfl)
  have s2 : ∑ y : ZMod q, (π y - y) = ∑ y : ZMod q, y :=
    Fintype.sum_bijective _ hgb _ _ (fun _ => rfl)
  rw [Finset.sum_sub_distrib, s1, sub_self] at s2
  exact even_sum_ne hq he s2.symm

end Z3NetC.Proofs
