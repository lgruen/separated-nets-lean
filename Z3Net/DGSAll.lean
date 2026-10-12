/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DGS
public import Z3Net.PPShift
public import Z3Net.B23Main

@[expose] public section

/-!
# V14 stage S15′: `rem:dgsfinite` in every prime base, under every digital shift

The abstract's claim "In prime bases these families are well separated in the sense of Dick, Goda and Suzuki, and
they stay so under every digital shift", as one theorem (`dgs_family_all`): for every prime `p` there are digital
`(0,m,3)`-nets over `𝔽_p`, one for every `m ∈ ℕ`, such that for every choice of digital shifts the family is well
separated and toroidally well separated on all of `ℕ` in the sense of [DGS2, Def. 3.8] (`WellSepFamily`,
`WellSepFamilyTor` of `Z3Net/DGSDefs.lean`). The constructions per range:

* `p ∈ {2, 3}`: `thm:base23`(3) (`base23_everyshift_base`) for `m ≥ 1`, through `cor:dgs` Step 2 (`dgs_main`);
* `5 ≤ p ≤ 31`: for `m ≥ 10`, `thm:main` (`m ≡ 0`, `dgs_P`'s integer bound), and the per-prime designs of
  `app:perprime` (`table1` for `m ≡ 1`, `table2` for `m ≡ 2`) with `rem:ppshift` (`Z3Net/PPShift.lean`);
* `p ≥ 37`: `dgs_family` (stage S10′: `𝒞_p`, `thm:main`, `thm:allm`, `thm:S1` at `s = 3`);
* the finitely many remaining `m` (`m = 0` for `p ≤ 3`, `m ≤ 9` for `5 ≤ p ≤ 31`): the frame of the places
  `∞, 0, 1` (`frame3_net`), `m`-separated as a shifted `(0,m,3)`-net on the grid (`dgsfinite_sep`, `lem:shift`).
-/

namespace Z3NetDGS.Proofs

open Finset Matrix

section all

/-- The shifted frame nets are `(0,m,3)`-nets, `m`-separated and toroidally `m`-separated (`rem:dgsfinite`). -/
lemma frame_shift_sep (p m : ℕ) [NeZero p] (hp : 2 ≤ p) (τ : Fin 3 → Fin m → ZMod p) :
    IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m (Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1]) τ)) ∧
      IsKSep p m (ptSet p (Z3NetF.digPointShift p m (Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1]) τ)) ∧
      IsKSepTor p m (ptSet p (Z3NetF.digPointShift p m (Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1]) τ)) := by
  have hXlt := Z3NetF.Proofs.digPointShift_lt (Z3NetF.frameRead (R := ZMod p) m (0 : Fin 3) ![0, 0, 1]) τ
  have hN := isTMSNet_of_isNet0 (by norm_num) _ hXlt (Z3NetF.Proofs.digPointShift_net _ τ (frame3_net p m))
  refine ⟨hN, dgsfinite_sep p m (by norm_num) hp _ ?_ hN⟩
  intro x hx j
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨_, rfl⟩

/-- **Assembly** (`rem:dgsfinite`): a family that is well separated on `{m | M ≤ m}` for every choice of shifts,
completed by the frame nets below `M`, is well separated on all of `ℕ` for every choice of shifts. -/
theorem family_extend (p M : ℕ) [NeZero p] (hp : 2 ≤ p) (C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p))
    (h : ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 {m | M ≤ m} (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 {m | M ≤ m} (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m)))) :
    ∃ C' : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C' m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C' m) (τ m))) := by
  classical
  let C' : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p) := fun m =>
    if M ≤ m then C m else Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1]
  have hhi : ∀ m, M ≤ m → C' m = C m := fun m hm => if_pos hm
  have hlo : ∀ m, ¬ M ≤ m → C' m = Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1] := fun m hm => if_neg hm
  refine ⟨C', fun τ => ?_⟩
  obtain ⟨⟨-, hnet, κ, K, hκ⟩, ⟨-, -, κT, KT, hκT⟩⟩ := h τ
  have hlow : ∀ m : ℕ, ¬ M ≤ m → ∀ K : ℝ, (m : ℝ) ≤ (m : ℝ) / 3 + max K M := by
    intro m hm K
    have h1 : (m : ℝ) ≤ M := by exact_mod_cast (show m ≤ M by omega)
    have h2 : (0 : ℝ) ≤ m := by positivity
    have := le_max_right K (M : ℝ)
    linarith
  have hnet' : ∀ m ∈ (Set.univ : Set ℕ),
      IsTMSNet p 0 m ((fun m => ptSet p (Z3NetF.digPointShift p m (C' m) (τ m))) m) := by
    intro m _
    by_cases hm : M ≤ m
    · simp only [hhi m hm]; exact hnet m hm
    · simp only [hlo m hm]; exact (frame_shift_sep p m hp (τ m)).1
  refine ⟨⟨Set.infinite_univ, hnet', fun m => if M ≤ m then κ m else m, max K M, fun m _ => ?_⟩,
    ⟨Set.infinite_univ, hnet', fun m => if M ≤ m then κT m else m, max KT M, fun m _ => ?_⟩⟩
  · by_cases hm : M ≤ m
    · simp only [if_pos hm, hhi m hm]
      refine ⟨(hκ m hm).1, ?_⟩
      have := (hκ m hm).2; have := le_max_left K (M : ℝ); linarith
    · simp only [if_neg hm, hlo m hm]
      exact ⟨(frame_shift_sep p m hp (τ m)).2.1, hlow m hm K⟩
  · by_cases hm : M ≤ m
    · simp only [if_pos hm, hhi m hm]
      refine ⟨(hκT m hm).1, ?_⟩
      have := (hκT m hm).2; have := le_max_left KT (M : ℝ); linarith
    · simp only [if_neg hm, hlo m hm]
      exact ⟨(frame_shift_sep p m hp (τ m)).2.2, hlow m hm KT⟩

/-- A family of per-level statements `∃ C, ∀ τ, (net, κ_m-separated)` on `{m | M ≤ m}` with `κ_m ≤ m/3 + K` is a
well-separated family there, for every choice of shifts. -/
theorem family_of_levels (p M K : ℕ) [NeZero p] (κ : ℕ → ℕ) (hκ : ∀ m, M ≤ m → κ m ≤ m / 3 + K)
    (h : ∀ m, M ≤ m → ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSep p (κ m) (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSepTor p (κ m) (ptSet p (Z3NetF.digPointShift p m C τ))) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 {m | M ≤ m} (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 {m | M ≤ m} (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  classical
  let C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p) := fun m =>
    if hm : M ≤ m then Classical.choose (h m hm) else 0
  have hC : ∀ m (hm : M ≤ m), C m = Classical.choose (h m hm) := fun m hm => dif_pos hm
  have hinf : ({m | M ≤ m} : Set ℕ).Infinite := Set.infinite_of_not_bddAbove (by
    rintro ⟨B, hB⟩
    have := hB (show M + B + 1 ∈ {m | M ≤ m} by simp only [Set.mem_setOf_eq]; omega)
    omega)
  have hb : ∀ m, M ≤ m → (κ m : ℝ) ≤ (m : ℝ) / 3 + K := by
    intro m hm
    have h1 : ((m / 3 : ℕ) : ℝ) ≤ (m : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self m 3
    have h2 : (κ m : ℝ) ≤ ((m / 3 : ℕ) : ℝ) + K := by exact_mod_cast hκ m hm
    linarith
  refine ⟨C, fun τ => ⟨⟨hinf, fun m hm => ?_, κ, K, fun m hm => ⟨?_, hb m hm⟩⟩,
    ⟨hinf, fun m hm => ?_, κ, K, fun m hm => ⟨?_, hb m hm⟩⟩⟩⟩ <;>
  · simp only [hC m hm]
    have := Classical.choose_spec (h m hm) (τ m)
    first | exact this.1 | exact this.2.1 | exact this.2.2

/-! ## The per-prime range `5 ≤ p ≤ 31` -/

lemma table1_has (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) :
    ∃ T R, (p, T, R) ∈ Z3NetKN.table1 ∧ 1 ≤ T := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact ⟨_, _, by simp [Z3NetKN.table1]; exact ⟨rfl, rfl⟩, by norm_num⟩

lemma table2_has (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) :
    ∃ T R, (p, T, R) ∈ Z3NetKN.table2 ∧ 1 ≤ T := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact ⟨_, _, by simp [Z3NetKN.table2]; exact ⟨rfl, rfl⟩, by norm_num⟩

/-- `Z3NetKN.torusDist2` as a sum of `Z3NetF.cres` squares. -/
lemma kn_torus_eq (N : ℕ) (x y : Fin 3 → ℕ) :
    Z3NetKN.torusDist2 N x y = ∑ c, Z3NetF.cres N ((x c : ℤ) - (y c : ℤ)) ^ 2 := rfl

/-- **`rem:dgsfinite`, the per-prime range**: for every prime `5 ≤ p ≤ 31` and every `m ≥ 10` there are generator
matrices (`thm:main` for `m ≡ 0`, the per-prime designs of `app:perprime` for `m ≡ 1, 2`) such that every digital
shift of the net is a `(0,m,3)`-net in base `p` and `(⌊m/3⌋ + 3)`-separated and toroidally `(⌊m/3⌋ + 3)`-separated. -/
theorem dgs_pp_core (p m : ℕ) [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) (hm : 10 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSep p (m / 3 + 3) (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSepTor p (m / 3 + 3) (ptSet p (Z3NetF.digPointShift p m C τ)) := by
  have hp2 := hp.two_le
  have hpp : 9 ≤ p * p := by nlinarith
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ m = 3 * k + r := ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hdiv : (3 * k + r) / 3 = k := by omega
  rw [hdiv]
  interval_cases r
  · -- `m ≡ 0`: `thm:main`
    refine ⟨PGenZ p k, fun τ => ?_⟩
    refine ⟨isTMSNet_of_isNet0 (by norm_num) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
      (P_shift_net p k (by omega) (by omega) τ), ?_⟩
    apply sep_of_int (k + 3) (by omega) (by omega) _ (Z3NetF.Proofs.digPointShift_lt _ τ)
    intro v w hvw
    obtain ⟨c, hc⟩ := (Z3Net.Sep.P_sep_shift_main p k (by omega) (by omega) τ v w hvw).2
    refine ⟨c, ?_⟩
    have e : 3 * k + 0 - (k + 3) = 2 * k - 3 := by omega
    rw [e]
    have hq3 : (1 : ℤ) ≤ (p : ℤ) - 3 := by have : (5 : ℤ) ≤ p := by exact_mod_cast hp5
                                           linarith
    have hle : (p : ℤ) ^ (2 * k - 3) ≤ (p : ℤ) ^ (2 * k - 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le) (by omega)
    have hpos : (0 : ℤ) ≤ (p : ℤ) ^ (2 * k - 1) := by positivity
    have : ((p ^ (2 * k - 3) : ℕ) : ℤ) ≤ ((Z3NetF.cres (p ^ (3 * k)) ((Z3NetF.digPointShift p (3 * k)
        (PGenZ p k) τ v c : ℤ) - (Z3NetF.digPointShift p (3 * k) (PGenZ p k) τ w c : ℤ)) : ℕ) : ℤ) := by
      push_cast
      refine le_trans hle (le_trans ?_ hc)
      nlinarith
    exact_mod_cast this
  · -- `m ≡ 1`: the per-prime designs of `table1`, `rem:ppshift`
    obtain ⟨T, R, hmem, hT⟩ := table1_has p hp hp5 hp31
    obtain ⟨C, hCR, hnet⟩ := Z3NetKN.Proofs.KN1_net p T R hmem k (by omega)
    refine ⟨C, fun τ => ?_⟩
    have hXlt := Z3NetF.Proofs.digPointShift_lt C τ
    refine ⟨isTMSNet_of_isNet0 (by norm_num) _ hXlt
      ((isNet0_KN _).mp (Z3NetKN.Proofs.D3.isNet0_shift p (3 * k + 1) C hnet τ)), ?_⟩
    apply sep_of_int (k + 3) (by omega) hp2 _ hXlt
    intro v w hvw
    apply pigeon (by norm_num) (fun c => Z3NetF.cres (p ^ (3 * k + 1))
      ((Z3NetF.digPointShift p (3 * k + 1) C τ v c : ℤ) - (Z3NetF.digPointShift p (3 * k + 1) C τ w c : ℤ)))
    have hsep := Z3NetKN.Proofs.KN1_sep_shift_core p T R hmem k (by omega) C hCR τ v w hvw
    rw [kn_torus_eq] at hsep
    refine le_trans ?_ hsep
    have e1 : (p ^ (3 * k + 1 - (k + 3))) ^ 2 * (p * p) = p ^ (4 * k - 2) := by
      rw [← pow_mul, ← pow_two, ← pow_add]; congr 1; omega
    calc 3 * (p ^ (3 * k + 1 - (k + 3))) ^ 2 ≤ (p ^ (3 * k + 1 - (k + 3))) ^ 2 * (p * p) := by nlinarith
      _ = p ^ (4 * k - 2) := e1
      _ ≤ T * p ^ (4 * k - 2) := Nat.le_mul_of_pos_left _ hT
  · -- `m ≡ 2`: the per-prime designs of `table2`, `rem:ppshift`
    obtain ⟨T, R, hmem, hT⟩ := table2_has p hp hp5 hp31
    obtain ⟨C, hCR, hnet⟩ := Z3NetKN.Proofs.KN2_net p T R hmem k (by omega)
    refine ⟨C, fun τ => ?_⟩
    have hXlt := Z3NetF.Proofs.digPointShift_lt C τ
    refine ⟨isTMSNet_of_isNet0 (by norm_num) _ hXlt
      ((isNet0_KN _).mp (Z3NetKN.Proofs.D3.isNet0_shift p (3 * k + 2) C hnet τ)), ?_⟩
    apply sep_of_int (k + 3) (by omega) hp2 _ hXlt
    intro v w hvw
    apply pigeon (by norm_num) (fun c => Z3NetF.cres (p ^ (3 * k + 2))
      ((Z3NetF.digPointShift p (3 * k + 2) C τ v c : ℤ) - (Z3NetF.digPointShift p (3 * k + 2) C τ w c : ℤ)))
    have hsep := Z3NetKN.Proofs.KN2_sep_shift_core p T R hmem k (by omega) C hCR τ v w hvw
    rw [kn_torus_eq] at hsep
    refine le_trans ?_ hsep
    have e1 : (p ^ (3 * k + 2 - (k + 3))) ^ 2 * (p * p) = p ^ (4 * k) := by
      rw [← pow_mul, ← pow_two, ← pow_add]; congr 1; omega
    calc 3 * (p ^ (3 * k + 2 - (k + 3))) ^ 2 ≤ (p ^ (3 * k + 2 - (k + 3))) ^ 2 * (p * p) := by nlinarith
      _ = p ^ (4 * k) := e1
      _ ≤ T * p ^ (4 * k) := Nat.le_mul_of_pos_left _ hT

/-- **`rem:dgsfinite`, `5 ≤ p ≤ 31`**: the family on all of `ℕ`, every choice of digital shifts. -/
theorem dgs_family_pp_core (p : ℕ) [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  obtain ⟨C, hC⟩ := family_of_levels p 10 3 (fun m => m / 3 + 3) (fun m _ => le_refl _)
    (fun m hm => dgs_pp_core p m hp hp5 hp31 hm)
  exact family_extend p 10 hp.two_le C hC

/-! ## The bases two and three -/

lemma rpow_third (b m : ℕ) (hb : 0 < b) :
    ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) = (b : ℝ) ^ (-((m : ℝ) / 3)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; ring

/-- The toroidal distance of two points of `ptSet` in terms of `cres`. -/
lemma torDist2_ptReal {m q : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin 3 → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (v w : Fin m → ZMod q) :
    torDist2 (ptReal q X v) (ptReal q X w) =
      Real.sqrt (∑ c, ((Z3NetF.cres (q ^ m) ((X v c : ℤ) - X w c) : ℝ) / (q : ℝ) ^ m) ^ 2) := by
  unfold torDist2 ptReal
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hqm : 0 < q ^ m := Nat.pos_of_ne_zero (by have := NeZero.ne q; positivity)
  have e : ((q ^ m : ℕ) : ℝ) = (q : ℝ) ^ m := by push_cast; ring
  rw [← e, torCoord_cres (q ^ m) hqm _ _ (hX v c) (hX w c)]

/-- **`rem:dgsfinite`, `b ∈ {2, 3}`**, on `{m | 1 ≤ m}`: the nets of `thm:base23` with every choice of digital shifts,
through `thm:base23`(3) and `cor:dgs` Step 2. -/
theorem dgs_b23_pos (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod b,
      WellSepFamily b 0 3 {m | 1 ≤ m} (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) ∧
      WellSepFamilyTor b 0 3 {m | 1 ≤ m} (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) := by
  classical
  have hb2 : 2 ≤ b := by rcases hb with rfl | rfl <;> norm_num
  haveI : NeZero b := ⟨by omega⟩
  let C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b) := fun m =>
    if hm : 1 ≤ m then Classical.choose (Z3NetB23.Proofs.base23_exists_core b hb m hm) else 0
  have hC : ∀ m (hm : 1 ≤ m), Z3NetB23.IsB23Gen b m (C m) := fun m hm => by
    simp only [C, dif_pos hm]; exact Classical.choose_spec (Z3NetB23.Proofs.base23_exists_core b hb m hm)
  have hinf : ({m | 1 ≤ m} : Set ℕ).Infinite := Set.infinite_of_not_bddAbove (by
    rintro ⟨B, hB⟩
    have := hB (show B + 1 ∈ {m | 1 ≤ m} by simp only [Set.mem_setOf_eq]; omega)
    omega)
  refine ⟨C, fun τ => ?_⟩
  have hmain := dgs_main 3 b (by norm_num) hb2 {m | 1 ≤ m} hinf
    (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) 0.0770 (by norm_num)
    (fun m hm => isTMSNet_of_isNet0 (by norm_num) _ (Z3NetF.Proofs.digPointShift_lt _ _)
      (Z3NetB23.Proofs.base23_net_core b hb (hC m hm) (τ m))) ?_
  · exact ⟨hmain.2.2.1, hmain.2.2.2⟩
  intro m hm x hx y hy hxy
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hy
  have hvw : v ≠ w := fun h => hxy (h ▸ rfl)
  have h := Z3NetB23.Proofs.base23_base_core b hb (hC m hm) (τ m) v w hvw
  rw [torDist2_ptReal _ (Z3NetF.Proofs.digPointShift_lt _ _)]
  push_cast
  rw [← rpow_third b m (by omega)]
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

/-- **`rem:dgsfinite`, `b ∈ {2, 3}`**: the family on all of `ℕ`, every choice of digital shifts. -/
theorem dgs_family_b23_core (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod b,
      WellSepFamily b 0 3 Set.univ (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) ∧
      WellSepFamilyTor b 0 3 Set.univ (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) := by
  have hb2 : 2 ≤ b := by rcases hb with rfl | rfl <;> norm_num
  haveI : NeZero b := ⟨by omega⟩
  obtain ⟨C, hC⟩ := dgs_b23_pos b hb
  exact family_extend b 1 hb2 C hC

/-! ## Every prime base -/

/-- **`rem:dgsfinite`, every prime base, every digital shift** (the abstract's claim): for every prime `p` there are
digital `(0,m,3)`-nets over `𝔽_p`, one for every `m ∈ ℕ`, such that for every choice of digital shifts `τ_m` the
family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is well separated and toroidally well separated on all of `ℕ` in the sense of
[DGS2, Def. 3.8]. -/
theorem dgs_family_all_core (p : ℕ) [NeZero p] (hp : p.Prime) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p ≤ 3
  · exact dgs_family_b23_core p (by have := hp.two_le; interval_cases p <;> simp_all)
  by_cases h31 : p ≤ 31
  · refine dgs_family_pp_core p hp ?_ h31
    by_contra h5
    have : p = 4 := by omega
    subst this; norm_num at hp
  · refine dgs_family p hp ?_
    by_contra h37
    interval_cases p <;> norm_num at hp

end all

end Z3NetDGS.Proofs
