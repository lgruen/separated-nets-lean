/-
Entry WhyLat: `prop:cube` (one point per cube) of `paper/core.tex`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.WLDefs

@[expose] public section

/-!
# `prop:cube`: one point per cube

(i)–(iii) are reductions to Hajós's theorem resp. Keller's property (explicit hypotheses
`HajosProp s`, `KellerProp s`); (iv) is proved in full (the packing bounds for `s = 2, 3`, which
the paper takes from Thue / Hales, enter as the explicit hypothesis `μ(S) ≤ bound`).
-/

namespace Z3NetF

open Matrix

namespace CubeAux

open Filter Topology

/-- Exactly one point of `S` in the half-open cube `x + [0,1)^s`. -/
def PC {s : ℕ} (S : Set (Fin s → ℝ)) (x : Fin s → ℝ) : Prop :=
  ∃! σ : Fin s → ℝ, σ ∈ S ∧ ∀ c, x c ≤ σ c ∧ σ c < x c + 1

theorem PC_of_iff {s : ℕ} {S : Set (Fin s → ℝ)} {x y : Fin s → ℝ}
    (h : ∀ σ ∈ S, (∀ c, y c ≤ σ c ∧ σ c < y c + 1) ↔ (∀ c, x c ≤ σ c ∧ σ c < x c + 1))
    (hy : PC S y) : PC S x := by
  obtain ⟨σ, ⟨hσS, hσ⟩, hu⟩ := hy
  exact ⟨σ, ⟨hσS, (h σ hσS).1 hσ⟩, fun τ ⟨hτS, hτ⟩ => hu τ ⟨hτS, (h τ hτS).2 hτ⟩⟩

/-- `P` holds at the points of `ℤ^s + Π`. -/
theorem PC_intPlus {s : ℕ} {S : Set (Fin s → ℝ)} (P : AddSubgroup (Fin s → ℝ))
    (h1 : OnePerCube S) (hper : ∀ σ ∈ S, ∀ π ∈ P, σ + π ∈ S) {y : Fin s → ℝ}
    (hy : y ∈ intPlus (P : Set (Fin s → ℝ))) : PC S y := by
  obtain ⟨n, π, hπ, rfl⟩ := hy
  obtain ⟨σ, ⟨hσS, hσ⟩, hu⟩ := h1 n
  refine ⟨σ + π, ⟨hper σ hσS π hπ, fun c => ?_⟩, fun τ ⟨hτS, hτ⟩ => ?_⟩
  · simp only [Pi.add_apply]; constructor <;> linarith [(hσ c).1, (hσ c).2]
  · have hτ' : τ + -π ∈ S := hper τ hτS (-π) (P.neg_mem hπ)
    have := hu (τ + -π) ⟨hτ', fun c => by
      have := hτ c; simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
      constructor <;> linarith [this.1, this.2]⟩
    rw [← this]; abel

/-- Finiteness of `S` in an integer box. -/
theorem finite_box {s : ℕ} {S : Set (Fin s → ℝ)} (h1 : OnePerCube S) (a b : Fin s → ℤ) :
    {σ | σ ∈ S ∧ ∀ c, (a c : ℝ) ≤ σ c ∧ σ c < b c}.Finite := by
  have hfin : (Set.Icc a b).Finite := Set.finite_Icc a b
  refine Set.Finite.of_finite_image (f := fun σ c => ⌊σ c⌋) (hfin.subset ?_) ?_
  · rintro _ ⟨σ, ⟨_, hσ⟩, rfl⟩
    refine ⟨fun c => ?_, fun c => ?_⟩
    · exact Int.le_floor.2 (hσ c).1
    · have := (hσ c).2
      have : ⌊σ c⌋ < b c := Int.floor_lt.2 this
      exact this.le
  · intro σ ⟨hσS, _⟩ τ ⟨hτS, _⟩ hστ
    obtain ⟨ρ, _, hu⟩ := h1 (fun c => ⌊σ c⌋)
    have e1 := hu σ ⟨hσS, fun c => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩
    have e2 := hu τ ⟨hτS, fun c => by
      have := congrFun hστ c
      simp only at this
      rw [this]; exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩
    rw [e1, e2]

/-- Local constancy of the cube condition from the left. -/
theorem local_const {s : ℕ} {S : Set (Fin s → ℝ)} (h1 : OnePerCube S) (x : Fin s → ℝ) :
    ∃ ε > 0, ∀ y : Fin s → ℝ, (∀ c, x c - ε < y c ∧ y c ≤ x c) → ∀ σ ∈ S,
      (∀ c, y c ≤ σ c ∧ σ c < y c + 1) ↔ (∀ c, x c ≤ σ c ∧ σ c < x c + 1) := by
  set a : Fin s → ℤ := fun c => ⌊x c⌋ - 2
  set b : Fin s → ℤ := fun c => ⌊x c⌋ + 2
  have hF := finite_box h1 a b
  set F := {σ | σ ∈ S ∧ ∀ c, (a c : ℝ) ≤ σ c ∧ σ c < b c} with hFdef
  have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h1' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε using hε.2.le
  have gap : ∀ g : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 < g → ε ≤ g) := by
    intro g
    by_cases hg : 0 < g
    · filter_upwards [Ioo_mem_nhdsGT hg] with ε hε using fun _ => hε.2.le
    · exact Filter.Eventually.of_forall fun ε h => absurd h hg
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ σ ∈ F, ∀ c : Fin s,
      (σ c < x c → σ c ≤ x c - ε) ∧ (σ c < x c + 1 → σ c ≤ x c + 1 - ε) := by
    refine (hF.eventually_all).2 fun σ _ => Filter.eventually_all.2 fun c => ?_
    filter_upwards [gap (x c - σ c), gap (x c + 1 - σ c)] with ε e1 e2
    exact ⟨fun h => by linarith [e1 (by linarith)], fun h => by linarith [e2 (by linarith)]⟩
  obtain ⟨ε, hε0, hε1, hε2⟩ := (h0.and (h1'.and h2)).exists
  have hfl : ∀ c, (⌊x c⌋ : ℝ) ≤ x c ∧ x c < ⌊x c⌋ + 1 :=
    fun c => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hab : ∀ c, (a c : ℝ) = ⌊x c⌋ - 2 ∧ (b c : ℝ) = ⌊x c⌋ + 2 := by
    intro c; simp only [a, b]; push_cast; exact ⟨rfl, rfl⟩
  refine ⟨ε, hε0, fun y hy σ hσS => ?_⟩
  constructor
  · intro hyc
    have hσF : σ ∈ F := ⟨hσS, fun c => by
      have := hyc c; have := hy c; have := hfl c; have := hab c
      constructor <;> linarith⟩
    intro c
    have := hyc c; have := hy c
    refine ⟨?_, by linarith⟩
    by_contra hlt
    push Not at hlt
    have := (hε2 σ hσF c).1 hlt
    linarith
  · intro hxc
    have hσF : σ ∈ F := ⟨hσS, fun c => by
      have := hxc c; have := hfl c; have := hab c
      constructor <;> linarith⟩
    intro c
    have := hxc c; have := hy c
    have := (hε2 σ hσF c).2 (hxc c).2
    constructor <;> linarith

/-- **The cube count is `1` everywhere** when `ℤ^s + Π` is dense. -/
theorem PC_all {s : ℕ} {S : Set (Fin s → ℝ)} (P : AddSubgroup (Fin s → ℝ))
    (h1 : OnePerCube S) (hper : ∀ σ ∈ S, ∀ π ∈ P, σ + π ∈ S)
    (hdense : Dense (intPlus (P : Set (Fin s → ℝ)))) (x : Fin s → ℝ) : PC S x := by
  obtain ⟨ε, hε, hloc⟩ := local_const h1 x
  have hU : IsOpen (Set.pi Set.univ fun c => Set.Ioo (x c - ε) (x c)) :=
    isOpen_set_pi Set.finite_univ fun c _ => isOpen_Ioo
  have hne : (Set.pi Set.univ fun c => Set.Ioo (x c - ε) (x c)).Nonempty :=
    ⟨fun c => x c - ε / 2, fun c _ => ⟨by linarith, by linarith⟩⟩
  obtain ⟨y, hyD, hyU⟩ := hdense.exists_mem_open hU hne
  refine PC_of_iff (y := y) (fun σ hσ => hloc y (fun c => ?_) σ hσ) (PC_intPlus P h1 hper hyD)
  have := hyU c (Set.mem_univ c)
  exact ⟨this.1, this.2.le⟩

/-- Negation turns the cube count into a cube tiling in the standard orientation. -/
theorem tiling_neg {s : ℕ} {S : Set (Fin s → ℝ)} (h : ∀ x, PC S x) :
    IsCubeTiling {τ | -τ ∈ S} := by
  intro x
  obtain ⟨σ, ⟨hσS, hσ⟩, hu⟩ := h (-x)
  refine ⟨-σ, ⟨by simpa using hσS, fun c => ?_⟩, fun τ ⟨hτS, hτ⟩ => ?_⟩
  · have := hσ c; simp only [Pi.neg_apply] at this ⊢; constructor <;> linarith [this.1, this.2]
  · have := hu (-τ) ⟨hτS, fun c => by
      have := hτ c; simp only [Pi.neg_apply]; constructor <;> linarith [this.1, this.2]⟩
    rw [← this, neg_neg]

theorem sum_unitVec_sq {s : ℕ} (c : Fin s) : ∑ c', (unitVec c c') ^ 2 = 1 := by
  rw [Finset.sum_eq_single c]
  · simp [unitVec]
  · intro b _ hb; simp [unitVec, hb]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem minDist_nonneg_set {s : ℕ} (S : Set (Fin s → ℝ)) :
    BddBelow {d : ℝ | ∃ σ ∈ S, ∃ σ' ∈ S, σ ≠ σ' ∧ d = Real.sqrt (∑ c, (σ c - σ' c) ^ 2)} :=
  ⟨0, by rintro d ⟨σ, -, σ', -, -, rfl⟩; exact Real.sqrt_nonneg _⟩

theorem minDist_le_one {s : ℕ} {S : Set (Fin s → ℝ)} {σ : Fin s → ℝ} (hσ : σ ∈ S) (c : Fin s)
    (hσc : σ + unitVec c ∈ S) : minDist S ≤ 1 := by
  apply csInf_le (minDist_nonneg_set S)
  refine ⟨σ + unitVec c, hσc, σ, hσ, fun h => ?_, ?_⟩
  · have := congrFun h c; simp [unitVec] at this
  · simp only [Pi.add_apply, add_sub_cancel_left, sum_unitVec_sq, Real.sqrt_one]

theorem den_mono {D D' : ℕ} (h : D ∣ D') {t : ℝ} (ht : ∃ z : ℤ, (D : ℝ) * t = z) :
    ∃ z : ℤ, (D' : ℝ) * t = z := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨z, hz⟩ := ht
  exact ⟨k * z, by push_cast; rw [← hz]; ring⟩

theorem den_rat (q : ℚ) : ((q.den : ℕ) : ℝ) * (q : ℝ) = (q.num : ℝ) := by
  have h2 : (((q * q.den : ℚ)) : ℝ) = ((q.num : ℚ) : ℝ) := by rw [Rat.mul_den_eq_num]
  push_cast at h2; linarith

theorem exists_den_vec {s : ℕ} (v : Fin s → ℝ) (h : ∀ c, ∃ r : ℚ, v c = r) :
    ∃ D : ℕ, 0 < D ∧ ∀ c, ∃ z : ℤ, (D : ℝ) * v c = z := by
  choose r hr using h
  refine ⟨∏ c, (r c).den, Finset.prod_pos (fun c _ => (r c).den_pos), fun c => ?_⟩
  exact den_mono (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) ⟨(r c).num, by rw [hr c]; exact den_rat _⟩

theorem exists_den_finset {s : ℕ} (x : Fin s → ℝ) (F : Finset (Fin s → ℝ))
    (h : ∀ v ∈ F, ∀ c, ∃ r : ℚ, v c - x c = r) :
    ∃ D : ℕ, 0 < D ∧ ∀ v ∈ F, ∀ c, ∃ z : ℤ, (D : ℝ) * (v c - x c) = z := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a F ha ih =>
    obtain ⟨D, hD, hDF⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    obtain ⟨D', hD', hD'a⟩ := exists_den_vec (fun c => a c - x c) (h a (Finset.mem_insert_self a F))
    refine ⟨D * D', Nat.mul_pos hD hD', fun v hv c => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact den_mono (Dvd.intro_left D rfl) (hD'a c)
    · exact den_mono (Dvd.intro D' rfl) (hDF v hv c)

/-- No rational number `y` with `y^n = m` lies strictly between two consecutive integers. -/
theorem no_rat_root (y : ℝ) (q : ℚ) (hy : y = q) (n : ℕ) (hn : 0 < n) (m : ℤ) (hpow : y ^ n = m)
    (k : ℤ) (hlo : (k : ℝ) < y) (hhi : y < k + 1) : False := by
  have hirr := irrational_nrt_of_notint_nrt n m hpow (by
    rintro ⟨j, rfl⟩
    have h1 : k < j := by exact_mod_cast hlo
    have h2 : j < k + 1 := by exact_mod_cast hhi
    omega) hn
  exact hirr ⟨q, hy.symm⟩

end CubeAux

theorem cube_i' {s : ℕ} (hajos : HajosProp s) (L : AddSubgroup (Fin s → ℝ))
    (h1 : OnePerCube (L : Set (Fin s → ℝ))) (hdense : Dense (intPlus (L : Set (Fin s → ℝ)))) :
    ∃ c, unitVec c ∈ L ∧ minDist (L : Set (Fin s → ℝ)) ≤ 1 := by
  have hper : ∀ σ ∈ (L : Set (Fin s → ℝ)), ∀ π ∈ L, σ + π ∈ (L : Set (Fin s → ℝ)) :=
    fun σ hσ π hπ => L.add_mem hσ hπ
  have ht := CubeAux.tiling_neg (CubeAux.PC_all L h1 hper hdense)
  have hset : {τ | -τ ∈ (L : Set (Fin s → ℝ))} = (L : Set (Fin s → ℝ)) := by ext τ; simp
  rw [hset] at ht
  obtain ⟨c, hc⟩ := hajos L ht
  exact ⟨c, hc, CubeAux.minDist_le_one (S := (L : Set (Fin s → ℝ))) L.zero_mem c
    (by simpa using hc)⟩

theorem cube_ii' {s : ℕ} (hajos : HajosProp s) (L : AddSubgroup (Fin s → ℝ)) (hfg : L.FG)
    (hrat : ∀ ℓ ∈ L, ∀ c, ∃ r : ℚ, ℓ c = r) (h1 : OnePerCube (L : Set (Fin s → ℝ)))
    (hprod : ∀ x : Fin s → ℝ, (∀ c, ∃ ℓ ∈ L, ∃ n : ℤ, x c = ℓ c + n) →
      x ∈ intPlus (L : Set (Fin s → ℝ))) :
    ∃ c, unitVec c ∈ L ∧ minDist (L : Set (Fin s → ℝ)) ≤ 1 := by
  classical
  have hperL : ∀ σ ∈ (L : Set (Fin s → ℝ)), ∀ π ∈ L, σ + π ∈ (L : Set (Fin s → ℝ)) :=
    fun σ hσ π hπ => L.add_mem hσ hπ
  -- Step A: `L ⊆ (1/D) ℤ^s`
  obtain ⟨S0, hF, hfin⟩ := (AddSubgroup.fg_iff L).1 hfg
  have hFL : ∀ v ∈ S0, v ∈ L := fun v hv => hF ▸ AddSubgroup.subset_closure hv
  obtain ⟨D, hD, hDF⟩ := CubeAux.exists_den_finset 0 hfin.toFinset (fun v hv c => by
    simpa using hrat v (hFL v ((Set.Finite.mem_toFinset hfin).1 hv)) c)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let M : AddSubgroup (Fin s → ℝ) :=
    { carrier := {v | ∀ c, ∃ z : ℤ, (D : ℝ) * v c = z}
      add_mem' := fun {a b} ha hb c => by
        obtain ⟨z, hz⟩ := ha c; obtain ⟨w, hw⟩ := hb c
        exact ⟨z + w, by simp only [Pi.add_apply]; push_cast; rw [← hz, ← hw]; ring⟩
      zero_mem' := fun c => ⟨0, by simp⟩
      neg_mem' := fun {a} ha c => by
        obtain ⟨z, hz⟩ := ha c
        exact ⟨-z, by simp only [Pi.neg_apply]; push_cast; rw [← hz]; ring⟩ }
  have hLM : L ≤ M := by
    rw [← hF]
    exact (AddSubgroup.closure_le M).2 (fun v hv c => by
      simpa using hDF v ((Set.Finite.mem_toFinset hfin).2 hv) c)
  -- Step B: `G_c = π_c(L) + ℤ` is cyclic
  let G : Fin s → AddSubgroup ℝ := fun c =>
    L.map (Pi.evalAddMonoidHom (fun _ => ℝ) c) ⊔ AddSubgroup.zmultiples 1
  have hGD : ∀ c, ∀ t ∈ G c, ∃ z : ℤ, (D : ℝ) * t = z := by
    intro c t ht
    obtain ⟨y, hy, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 ht
    obtain ⟨ℓ, hℓ, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
    obtain ⟨z, hz⟩ := hLM hℓ c
    refine ⟨z + D * n, ?_⟩
    simp only [Pi.evalAddMonoidHom_apply, zsmul_eq_mul, mul_one]
    push_cast
    rw [← hz]; ring
  have hone : ∀ c, (1 : ℝ) ∈ G c := fun c =>
    AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples 1)
  have hLG : ∀ c, ∀ σ ∈ L, σ c ∈ G c := fun c σ hσ =>
    AddSubgroup.mem_sup_left (AddSubgroup.mem_map_of_mem _ hσ)
  have hcyc : ∀ c, ∃ g : ℝ, 0 < g ∧ ∀ t, t ∈ G c ↔ ∃ m : ℤ, t = m * g := by
    intro c
    have hnd : ¬ Dense (G c : Set ℝ) := by
      intro hd
      obtain ⟨t, ht, ht0, ht1⟩ := hd.exists_between (show (0 : ℝ) < 1 / D by positivity)
      obtain ⟨z, hz⟩ := hGD c t ht
      have h0 : (0 : ℝ) < z := by rw [← hz]; positivity
      have h1 : (z : ℝ) < 1 := by
        rw [← hz]; rw [lt_div_iff₀ hDR] at ht1; linarith
      have : (0 : ℤ) < z := by exact_mod_cast h0
      have : z < 1 := by exact_mod_cast h1
      omega
    obtain ⟨a, ha⟩ := (AddSubgroup.dense_or_cyclic (G c)).resolve_left hnd
    have hmem : ∀ t, t ∈ G c ↔ ∃ n : ℤ, t = n * a := by
      intro t; rw [ha, AddSubgroup.mem_closure_singleton]
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨n, by rw [zsmul_eq_mul]⟩
      · rintro ⟨n, rfl⟩; exact ⟨n, by rw [zsmul_eq_mul]⟩
    have ha0 : a ≠ 0 := by
      intro h0
      obtain ⟨n, hn⟩ := (hmem 1).1 (hone c)
      rw [h0, mul_zero] at hn; norm_num at hn
    refine ⟨|a|, abs_pos.2 ha0, fun t => ?_⟩
    rw [hmem]
    rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨-n, by push_cast; ring⟩
      · rintro ⟨n, rfl⟩; exact ⟨-n, by push_cast; ring⟩
  choose g hg0 hgm using hcyc
  -- Step C: the cube count is `1` everywhere
  have hint : ∀ (a b : ℤ) (t : ℝ), 0 < t → (a : ℝ) * t < b * t → a < b := by
    intro a b t ht h; exact_mod_cast lt_of_mul_lt_mul_right h ht.le
  have hall : ∀ x : Fin s → ℝ, CubeAux.PC (L : Set (Fin s → ℝ)) x := by
    intro x
    set k : Fin s → ℤ := fun c => ⌈x c / g c⌉
    set y : Fin s → ℝ := fun c => (k c : ℝ) * g c
    have hyG : ∀ c, y c ∈ G c := fun c => (hgm c (y c)).2 ⟨k c, rfl⟩
    have hyI : y ∈ intPlus (L : Set (Fin s → ℝ)) := by
      apply hprod
      intro c
      obtain ⟨u, hu, w, hw, huw⟩ := AddSubgroup.mem_sup.1 (hyG c)
      obtain ⟨ℓ, hℓ, rfl⟩ := AddSubgroup.mem_map.1 hu
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
      exact ⟨ℓ, hℓ, n, by rw [← huw]; simp⟩
    refine CubeAux.PC_of_iff (y := y) (fun σ hσ => forall_congr' fun c => ?_)
      (CubeAux.PC_intPlus L h1 hperL hyI)
    obtain ⟨m, hm⟩ := (hgm c (σ c)).1 (hLG c σ hσ)
    obtain ⟨u, hu⟩ := (hgm c 1).1 (hone c)
    have gp := hg0 c
    have k1 : x c ≤ k c * g c := by
      have := Int.le_ceil (x c / g c); rw [div_le_iff₀ gp] at this; exact this
    have k2 : ((k c : ℝ) - 1) * g c < x c := by
      have := Int.ceil_lt_add_one (x c / g c)
      have h' : ((k c : ℝ) - 1) < x c / g c := by simp only [k]; linarith
      exact (lt_div_iff₀ gp).1 h'
    simp only [y]
    rw [hm]
    constructor
    · rintro ⟨h1', h2'⟩
      refine ⟨k1.trans h1', ?_⟩
      have h3 : (m : ℝ) * g c < ((k c + u : ℤ) : ℝ) * g c := by push_cast; nlinarith
      have h4 := hint _ _ _ gp h3
      have h5 : ((m : ℤ) : ℝ) ≤ ((k c + u - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : m ≤ k c + u - 1)
      push_cast at h5
      nlinarith
    · rintro ⟨h1', h2'⟩
      have h3 : ((k c - 1 : ℤ) : ℝ) * g c < (m : ℝ) * g c := by push_cast; linarith
      have h4 := hint _ _ _ gp h3
      have h5 : ((k c : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : k c ≤ m)
      exact ⟨by nlinarith, by linarith⟩
  have ht := CubeAux.tiling_neg hall
  have hset : {τ | -τ ∈ (L : Set (Fin s → ℝ))} = (L : Set (Fin s → ℝ)) := by ext τ; simp
  rw [hset] at ht
  obtain ⟨c, hc⟩ := hajos L ht
  exact ⟨c, hc, CubeAux.minDist_le_one (S := (L : Set (Fin s → ℝ))) L.zero_mem c
    (by simpa using hc)⟩

theorem cube_iii' {s : ℕ} (_hs : s ≤ 7) (keller : KellerProp s) (S : Set (Fin s → ℝ))
    (P : AddSubgroup (Fin s → ℝ)) (h1 : OnePerCube S) (hper : ∀ σ ∈ S, ∀ π ∈ P, σ + π ∈ S)
    (hdense : Dense (intPlus (P : Set (Fin s → ℝ)))) :
    ∃ σ ∈ S, ∃ c, σ + unitVec c ∈ S ∧ minDist S ≤ 1 := by
  obtain ⟨τ, hτ, c, hτc⟩ := keller _ (CubeAux.tiling_neg (CubeAux.PC_all P h1 hper hdense))
  simp only [Set.mem_ofPred_eq] at hτ hτc
  have e : -(τ + unitVec c) + unitVec c = -τ := by abel
  exact ⟨-(τ + unitVec c), hτc, c, by rw [e]; exact hτ,
    CubeAux.minDist_le_one hτc c (by rw [e]; exact hτ)⟩

theorem cube_iv_rat' {s : ℕ} (S : Set (Fin s → ℝ)) (x : Fin s → ℝ)
    (hrat : ∀ σ ∈ S, ∀ c, ∃ r : ℚ, σ c - x c = r) :
    ∀ σ ∈ S, ∀ σ' ∈ S, ∃ r : ℚ, ∑ c, (σ c - σ' c) ^ 2 = r := by
  intro σ hσ σ' hσ'
  choose r hr using hrat σ hσ
  choose r' hr' using hrat σ' hσ'
  refine ⟨∑ c, (r c - r' c) ^ 2, ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hr c, ← hr' c]; ring

theorem cube_iv_min' {s : ℕ} (hs : 0 < s) (S : Set (Fin s → ℝ)) (P : AddSubgroup (Fin s → ℝ))
    (h1 : OnePerCube S) (hper : ∀ σ ∈ S, ∀ π ∈ P, σ + π ∈ S) (N : ℕ) (hN : 0 < N)
    (hPN : ∀ z : Fin s → ℤ, (fun c => (N : ℝ) * z c) ∈ P) (x : Fin s → ℝ)
    (hrat : ∀ σ ∈ S, ∀ c, ∃ r : ℚ, σ c - x c = r) :
    (∃ σ ∈ S, ∃ σ' ∈ S, σ ≠ σ' ∧ minDist S = Real.sqrt (∑ c, (σ c - σ' c) ^ 2)) ∧
      ∃ r : ℚ, 0 < r ∧ minDist S ^ 2 = r := by
  classical
  have hS0 := CubeAux.finite_box h1 (fun _ => 0) (fun _ => (N : ℤ))
  obtain ⟨D, hD, hDS0⟩ := CubeAux.exists_den_finset x hS0.toFinset (fun v hv c =>
    hrat v ((Set.Finite.mem_toFinset hS0).1 hv).1 c)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  -- every point of `S` has denominator `D` relative to `x`
  have hall : ∀ σ ∈ S, ∀ c, ∃ z : ℤ, (D : ℝ) * (σ c - x c) = z := by
    intro σ hσ c
    set z : Fin s → ℤ := fun c => -⌊σ c / N⌋ with hz
    have hπ := hPN z
    have hσ0 : σ + (fun c => (N : ℝ) * z c) ∈ S := hper σ hσ _ hπ
    have hmem : σ + (fun c => (N : ℝ) * z c) ∈ hS0.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hσ0, fun c => ?_⟩
      have f1 := Int.floor_le (σ c / N)
      have f2 := Int.lt_floor_add_one (σ c / N)
      rw [le_div_iff₀ hNR] at f1
      rw [div_lt_iff₀ hNR] at f2
      simp only [Pi.add_apply, hz]
      push_cast
      constructor <;> nlinarith
    obtain ⟨w, hw⟩ := hDS0 _ hmem c
    refine ⟨w + D * N * ⌊σ c / N⌋, ?_⟩
    simp only [Pi.add_apply, hz] at hw
    push_cast at hw ⊢
    linear_combination hw
  -- squared distances times `D²` are positive naturals
  have key : ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' →
      ∃ k : ℕ, 1 ≤ k ∧ (D : ℝ) ^ 2 * ∑ c, (σ c - σ' c) ^ 2 = k := by
    intro σ hσ σ' hσ' hne
    choose z hz using hall σ hσ
    choose z' hz' using hall σ' hσ'
    have hK : (D : ℝ) ^ 2 * ∑ c, (σ c - σ' c) ^ 2 = ((∑ c, (z c - z' c) ^ 2 : ℤ) : ℝ) := by
      rw [Finset.mul_sum]; push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hz c, ← hz' c]; ring
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
    have hzc : z c ≠ z' c := by
      intro h
      apply hc
      have := hz c; have := hz' c
      have e : (D : ℝ) * (σ c - x c) = (D : ℝ) * (σ' c - x c) := by rw [hz c, hz' c, h]
      have := mul_left_cancel₀ hDR.ne' e
      linarith
    have h1K : 1 ≤ ∑ c, (z c - z' c) ^ 2 := by
      have hpos : 1 ≤ (z c - z' c) ^ 2 := by
        have : z c - z' c ≠ 0 := sub_ne_zero.2 hzc
        rcases lt_or_gt_of_ne this with h | h <;> nlinarith
      exact hpos.trans (Finset.single_le_sum (f := fun c => (z c - z' c) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ c))
    refine ⟨(∑ c, (z c - z' c) ^ 2).toNat, by omega, ?_⟩
    rw [hK]
    exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
  -- a distinct pair exists
  have hex : ∃ k : ℕ, ∃ σ ∈ S, ∃ σ' ∈ S, σ ≠ σ' ∧ (D : ℝ) ^ 2 * ∑ c, (σ c - σ' c) ^ 2 = k := by
    set c0 : Fin s := ⟨0, hs⟩
    obtain ⟨σ, ⟨hσS, hσ⟩, -⟩ := h1 (fun _ => 0)
    obtain ⟨σ', ⟨hσS', hσ'⟩, -⟩ := h1 (fun c => if c = c0 then 1 else 0)
    have hne : σ ≠ σ' := by
      intro h
      have a := (hσ c0).2
      have b := (hσ' c0).1
      rw [h] at a
      simp at a b
      linarith
    obtain ⟨k, -, hk⟩ := key σ hσS σ' hσS' hne
    exact ⟨k, σ, hσS, σ', hσS', hne, hk⟩
  obtain ⟨σ₀, hσ₀, σ₀', hσ₀', hne₀, hk₀⟩ := Nat.find_spec hex
  have hmin : ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' →
      ∑ c, (σ₀ c - σ₀' c) ^ 2 ≤ ∑ c, (σ c - σ' c) ^ 2 := by
    intro σ hσ σ' hσ' hne
    obtain ⟨k, -, hk⟩ := key σ hσ σ' hσ' hne
    have hle : Nat.find hex ≤ k := Nat.find_min' hex ⟨σ, hσ, σ', hσ', hne, hk⟩
    have : (D : ℝ) ^ 2 * ∑ c, (σ₀ c - σ₀' c) ^ 2 ≤ (D : ℝ) ^ 2 * ∑ c, (σ c - σ' c) ^ 2 := by
      rw [hk₀, hk]; exact_mod_cast hle
    exact le_of_mul_le_mul_left this (by positivity)
  have hμ : minDist S = Real.sqrt (∑ c, (σ₀ c - σ₀' c) ^ 2) := by
    apply IsLeast.csInf_eq
    refine ⟨⟨σ₀, hσ₀, σ₀', hσ₀', hne₀, rfl⟩, ?_⟩
    rintro d ⟨σ, hσ, σ', hσ', hne, rfl⟩
    exact Real.sqrt_le_sqrt (hmin σ hσ σ' hσ' hne)
  refine ⟨⟨σ₀, hσ₀, σ₀', hσ₀', hne₀, hμ⟩, ?_⟩
  obtain ⟨k, hk1, hk⟩ := key σ₀ hσ₀ σ₀' hσ₀' hne₀
  refine ⟨(k : ℚ) / (D : ℚ) ^ 2, by positivity, ?_⟩
  rw [hμ, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
  push_cast
  rw [← hk]
  field_simp

theorem cube_iv_vals' {s : ℕ} (hs : 0 < s) (S : Set (Fin s → ℝ)) (P : AddSubgroup (Fin s → ℝ))
    (h1 : OnePerCube S) (hper : ∀ σ ∈ S, ∀ π ∈ P, σ + π ∈ S) (N : ℕ) (hN : 0 < N)
    (hPN : ∀ z : Fin s → ℤ, (fun c => (N : ℝ) * z c) ∈ P) (x : Fin s → ℝ)
    (hrat : ∀ σ ∈ S, ∀ c, ∃ r : ℚ, σ c - x c = r) :
    (s = 2 → minDist S ≠ (4 / 3 : ℝ) ^ ((1 : ℝ) / 4) ∧
      (minDist S ≤ (4 / 3 : ℝ) ^ ((1 : ℝ) / 4) → minDist S < (4 / 3 : ℝ) ^ ((1 : ℝ) / 4))) ∧
    (s = 3 → minDist S ≠ (2 : ℝ) ^ ((1 : ℝ) / 6) ∧
      (minDist S ≤ (2 : ℝ) ^ ((1 : ℝ) / 6) → minDist S < (2 : ℝ) ^ ((1 : ℝ) / 6))) ∧
    (s = 4 → minDist S ^ 2 ≠ Real.sqrt 2) ∧
    (s = 5 → minDist S ^ 2 ≠ (2 : ℝ) ^ ((3 : ℝ) / 5)) ∧
    (s = 6 → minDist S ^ 2 ≠ 2 * (3 : ℝ) ^ (-(1 : ℝ) / 6)) ∧
    (s = 7 → minDist S ^ 2 ≠ (2 : ℝ) ^ ((6 : ℝ) / 7)) := by
  obtain ⟨-, r, hr0, hr⟩ := cube_iv_min' hs S P h1 hper N hN hPN x hrat
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hpow : ∀ n : ℕ, minDist S ^ (2 * n) = (r : ℝ) ^ n := by intro n; rw [pow_mul, hr]
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · have hne : minDist S ≠ (4 / 3 : ℝ) ^ ((1 : ℝ) / 4) := by
      intro he
      have h4 : (r : ℝ) ^ 2 = 4 / 3 := by
        rw [← hpow, he, ← Real.rpow_mul_natCast (by norm_num)]; norm_num
      have hy : (3 * (r : ℝ)) ^ 2 = ((12 : ℤ) : ℝ) := by rw [mul_pow, h4]; norm_num
      have hy0 : (0 : ℝ) ≤ 3 * r := by positivity
      exact CubeAux.no_rat_root (3 * r) (3 * r) (by push_cast; ring) 2 two_pos 12 hy 3
        (lt_of_pow_lt_pow_left₀ 2 hy0 (by rw [hy]; norm_num))
        (lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [hy]; norm_num))
    exact ⟨hne, fun h => lt_of_le_of_ne h hne⟩
  · have hne : minDist S ≠ (2 : ℝ) ^ ((1 : ℝ) / 6) := by
      intro he
      have h4 : (r : ℝ) ^ 3 = ((2 : ℤ) : ℝ) := by
        rw [← hpow, he, ← Real.rpow_mul_natCast (by norm_num)]; norm_num
      exact CubeAux.no_rat_root r r rfl 3 (by norm_num) 2 h4 1
        (lt_of_pow_lt_pow_left₀ 3 hr0'.le (by rw [h4]; norm_num))
        (lt_of_pow_lt_pow_left₀ 3 (by norm_num) (by rw [h4]; norm_num))
    exact ⟨hne, fun h => lt_of_le_of_ne h hne⟩
  · intro he
    have h4 : (r : ℝ) ^ 2 = ((2 : ℤ) : ℝ) := by
      rw [← hr, he, Real.sq_sqrt (by norm_num)]; norm_num
    exact CubeAux.no_rat_root r r rfl 2 two_pos 2 h4 1
      (lt_of_pow_lt_pow_left₀ 2 hr0'.le (by rw [h4]; norm_num))
      (lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h4]; norm_num))
  · intro he
    have h4 : (r : ℝ) ^ 5 = ((8 : ℤ) : ℝ) := by
      rw [← hr, he, ← Real.rpow_mul_natCast (by norm_num)]; norm_num
    exact CubeAux.no_rat_root r r rfl 5 (by norm_num) 8 h4 1
      (lt_of_pow_lt_pow_left₀ 5 hr0'.le (by rw [h4]; norm_num))
      (lt_of_pow_lt_pow_left₀ 5 (by norm_num) (by rw [h4]; norm_num))
  · intro he
    have h3 : ((3 : ℝ) ^ (-(1 : ℝ) / 6)) ^ 6 = 1 / 3 := by
      rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
    have h4 : (3 * (r : ℝ)) ^ 6 = ((15552 : ℤ) : ℝ) := by
      rw [mul_pow, ← hr, he, mul_pow, h3]; norm_num
    have hy0 : (0 : ℝ) ≤ 3 * r := by positivity
    exact CubeAux.no_rat_root (3 * r) (3 * r) (by push_cast; ring) 6 (by norm_num) 15552 h4 4
      (lt_of_pow_lt_pow_left₀ 6 hy0 (by rw [h4]; norm_num))
      (lt_of_pow_lt_pow_left₀ 6 (by norm_num) (by rw [h4]; norm_num))
  · intro he
    have h4 : (r : ℝ) ^ 7 = ((64 : ℤ) : ℝ) := by
      rw [← hr, he, ← Real.rpow_mul_natCast (by norm_num)]; norm_num
    exact CubeAux.no_rat_root r r rfl 7 (by norm_num) 64 h4 1
      (lt_of_pow_lt_pow_left₀ 7 hr0'.le (by rw [h4]; norm_num))
      (lt_of_pow_lt_pow_left₀ 7 (by norm_num) (by rw [h4]; norm_num))

end Z3NetF
