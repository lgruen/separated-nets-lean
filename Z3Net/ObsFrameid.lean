/-
Proof module of entry Obs: `lem:frameid` and `cor:frameid`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsCH
public import Z3Net.SkCompE

@[expose] public section

/-!
# Entry Obs: `lem:frameid`, `cor:frameid`

The moves `Φ_cd = L_c Φ^F_cd U_d` (lower triangular `L_c`, `U_d`) scale the deepest-level entry of
row `0` of every off-diagonal block by `(L_c)_{00} (U_d)_{last,last}`; by the normal form of
`prop:skelcomp`(i) (`skelcomp_normal`, for arbitrary depths `K`) these entries of the frame are
`Q_c w_cd / u_d(0)`. So they form a Cauchy layer `λ_c μ_d w_cd`, which is a Cauchy layer in
homogeneous coordinates (`wN_cauchy`), and `lem:CH`(X) gives the identity.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

namespace ObsFrameid

/-- Deepest-level entry of row `0` of `L A U` for lower-triangular `L`, `U`. -/
lemma ent_LAU {R : Type*} [CommRing R] {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (L : Matrix (Fin p) (Fin p) R) (A : Matrix (Fin p) (Fin n) R) (U : Matrix (Fin n) (Fin n) R)
    (hL : ∀ i j, i < j → L i j = 0) (hU : ∀ i j, i < j → U i j = 0) :
    Z3NetF.ent (L * A * U) 0 (n - 1) =
      L ⟨0, hp⟩ ⟨0, hp⟩ * Z3NetF.ent A 0 (n - 1) * U ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ := by
  unfold Z3NetF.ent
  rw [dif_pos ⟨hp, by omega⟩, dif_pos ⟨hp, by omega⟩, Matrix.mul_apply,
    Finset.sum_eq_single ⟨n - 1, by omega⟩, Matrix.mul_apply, Finset.sum_eq_single ⟨0, hp⟩]
  · intro i _ hi
    rw [hL _ _ (by
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      exact Fin.mk_lt_of_lt_val (by omega)), zero_mul]
  · simp
  · intro l _ hl
    rw [hU _ _ (by
      have : (l : ℕ) ≠ n - 1 := fun h => hl (Fin.ext h)
      have := l.isLt
      exact Fin.lt_def.mpr (by simp only; omega)), mul_zero]
  · simp

variable {𝕜 : Type*} [Field 𝕜] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
  (hK1 : ∀ c, 1 ≤ K c) (inf : Fin s) (x : Fin s → 𝕜) (hx : Z3NetF.PlacesOK inf x)
  (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) 𝕜)
  (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) 𝕜) (hL : ∀ c, Z3NetF.IsLTU (L c))
  (hU : ∀ d, Z3NetF.IsLTU (U d)) (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) 𝕜)
  (hΦ : ∀ c d, c ≠ d → Φ c d = L c * Z3NetF.frameGraphK 𝕜 m K inf x c d * U d)

include hK hK1 hx hL hU hΦ

lemma m_pos (hs : 2 ≤ s) (c : Fin s) : 0 < m - K c := by
  have d : Fin s := if (c : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin s, d ≠ c := by
    by_cases h : (c : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  have := SkComp.two_le_sum K c d (Ne.symm hd)
  have := hK1 d
  omega

/-- The deepest-level layer of the frame orbit is `λ_c μ_d w_cd` with nonzero `λ`, `μ`. -/
lemma layer (hs : 2 ≤ s) :
    ∃ lam mu : Fin s → 𝕜, (∀ c, lam c ≠ 0) ∧ (∀ d, mu d ≠ 0) ∧
      ∀ c d, c ≠ d → Z3NetF.ent (Φ c d) 0 (K d - 1) = lam c * mu d * Z3NetF.wN inf x c d := by
  classical
  have hp : ∀ c, 0 < m - K c := m_pos K hK hK1 inf x hx L U hL hU Φ hΦ hs
  -- the normal form at the deepest level
  have hnorm : ∀ c d, c ≠ d →
      Ring.inverse (Z3NetF.QfK K inf x c) *
        Z3NetF.ent (Z3NetF.frameGraphK 𝕜 m K inf x c d) 0 (K d - 1) *
        (Z3NetF.uNK K inf x d).coeff 0 = Z3NetF.wN inf x c d := by
    intro c d hcd
    have h := skelcomp_normal K hK inf x hx c d hcd ⟨K d - 1, by have := hK1 d; omega⟩
    rw [ent_LAU (hp c) (by have := hK1 d; omega) _ _ _ (fun i j hij => by
        unfold Z3NetF.Lgauge; exact Matrix.diagonal_apply_ne _ (ne_of_lt hij))
      (fun i j hij => by unfold Z3NetF.toep; rw [if_neg (not_le.mpr hij)])] at h
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    rw [← h]
    unfold Z3NetF.Lgauge Z3NetF.toep
    simp
  have hwN : ∀ c d, c ≠ d → Z3NetF.wN inf x c d ≠ 0 := by
    intro c d hcd
    unfold Z3NetF.wN
    split_ifs with h
    · exact one_ne_zero
    · push Not at h
      rw [Ring.inverse_eq_inv']
      exact inv_ne_zero (hx c d h.1 h.2 hcd).ne_zero
  -- pick the factors
  obtain ⟨d0, hd0⟩ : ∃ d : Fin s, ∀ c : Fin s, ∃ e : Fin s, e ≠ c := by
    refine ⟨⟨0, by omega⟩, fun c => ?_⟩
    by_cases h : (c : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  have hQ : ∀ c, Z3NetF.QfK K inf x c ≠ 0 := by
    intro c hQ0
    obtain ⟨d, hd⟩ := hd0 c
    have := hnorm c d (Ne.symm hd)
    rw [hQ0, Ring.inverse_zero, zero_mul, zero_mul] at this
    exact hwN c d (Ne.symm hd) this.symm
  have hu : ∀ d, (Z3NetF.uNK K inf x d).coeff 0 ≠ 0 := by
    intro d hu0
    obtain ⟨c, hc⟩ := hd0 d
    have := hnorm c d hc
    rw [hu0, mul_zero] at this
    exact hwN c d hc this.symm
  refine ⟨fun c => L c ⟨0, hp c⟩ ⟨0, hp c⟩ * Z3NetF.QfK K inf x c,
    fun d => U d ⟨K d - 1, by have := hK1 d; omega⟩ ⟨K d - 1, by have := hK1 d; omega⟩ /
      (Z3NetF.uNK K inf x d).coeff 0, fun c => mul_ne_zero ((hL c).2 _).ne_zero (hQ c),
    fun d => div_ne_zero ((hU d).2 _).ne_zero (hu d), fun c d hcd => ?_⟩
  rw [hΦ c d hcd, ent_LAU (hp c) (by have := hK1 d; omega) _ _ _ (hL c).1 (hU d).1]
  rw [← hnorm c d hcd, Ring.inverse_eq_inv']
  have := hQ c; have := hu d
  field_simp

theorem frameid (zi zj zl d : Fin s) (hij : zi ≠ zj) (hil : zi ≠ zl) (hid : zi ≠ d) (hjl : zj ≠ zl)
    (hjd : zj ≠ d) (hld : zl ≠ d) :
    Z3NetF.ent (Φ zj zi) 0 (K zi - 1) * Z3NetF.ent (Φ zl zj) 0 (K zj - 1) *
        (Z3NetF.ent (Φ zj d) 0 (K d - 1))⁻¹ +
      Z3NetF.ent (Φ zi zj) 0 (K zj - 1) * Z3NetF.ent (Φ zl zi) 0 (K zi - 1) *
        (Z3NetF.ent (Φ zi d) 0 (K d - 1))⁻¹ =
      Z3NetF.ent (Φ zl zi) 0 (K zi - 1) * Z3NetF.ent (Φ zl zj) 0 (K zj - 1) *
        (Z3NetF.ent (Φ zl d) 0 (K d - 1))⁻¹ := by
  have hs : 2 ≤ s := by
    have := zi.isLt; have := zj.isLt
    have : (zi : ℕ) ≠ zj := fun h => hij (Fin.ext h)
    omega
  obtain ⟨lam, mu, hl, hm, hent⟩ := layer K hK hK1 inf x hx L U hL hU Φ hΦ hs
  obtain ⟨hC, hW⟩ := ObsCH.wN_cauchy inf x hx lam mu (fun c => isUnit_iff_ne_zero.mpr (hl c))
    (fun d => isUnit_iff_ne_zero.mpr (hm d))
  set α := fun c => if c = inf then (1 : 𝕜) else x c
  set β := fun c => if c = inf then (0 : 𝕜) else 1
  set mu' := fun d => if d = inf then -mu d else mu d
  have hE : ∀ c e, c ≠ e → Z3NetF.ent (Φ c e) 0 (K e - 1) = Z3NetF.cauchyW α β lam mu' c e :=
    fun c e hce => by rw [hent c e hce, hW c e hce]
  have hX := ObsCH.CH_X α β lam mu' hC zi zj zl d hij hil hid hjl hjd hld
  rw [hE _ _ (Ne.symm hij), hE _ _ (Ne.symm hjl), hE _ _ hjd, hE _ _ hij, hE _ _ (Ne.symm hil),
    hE _ _ hid, hE _ _ hld]
  have nz : ∀ c e, c ≠ e → Z3NetF.cauchyW α β lam mu' c e ≠ 0 :=
    fun c e hce => (ObsCH.W_unit α β lam mu' hC c e hce).ne_zero
  simp only [Ring.inverse_eq_inv'] at hX
  have n1 := nz _ _ (Ne.symm hij); have n2 := nz _ _ (Ne.symm hjl); have n3 := nz _ _ hjd
  have n4 := nz _ _ hij; have n5 := nz _ _ (Ne.symm hil); have n6 := nz _ _ hid
  have n7 := nz _ _ hld
  set W := Z3NetF.cauchyW α β lam mu'
  calc W zj zi * W zl zj * (W zj d)⁻¹ + W zi zj * W zl zi * (W zi d)⁻¹
      = W zl zi * W zl zj * (W zl d)⁻¹ * (W zj zi * W zl d * (W zj d * W zl zi)⁻¹ +
          W zi zj * W zl d * (W zi d * W zl zj)⁻¹) := by
        field_simp
    _ = W zl zi * W zl zj * (W zl d)⁻¹ := by rw [hX, mul_one]

end ObsFrameid

theorem frameid_cor (p : ℕ) [Fact p.Prime] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (hK1 : ∀ c, 1 ≤ K c) (inf : Fin s) (x : Fin s → ZMod p) (hx : Z3NetF.PlacesOK inf x)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) (ZMod p))
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) (ZMod p)) (hL : ∀ c, Z3NetF.IsLTU (L c))
    (hU : ∀ d, Z3NetF.IsLTU (U d)) (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod p))
    (hΦ : ∀ c d, c ≠ d → Φ c d = L c * Z3NetF.frameGraphK (ZMod p) m K inf x c d * U d)
    (z₁ z₂ z₃ d : Fin s) (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h1d : z₁ ≠ d) (h23 : z₂ ≠ z₃)
    (h2d : z₂ ≠ d) (h3d : z₃ ≠ d) (ρ G : ℕ) (hρ : 1 ≤ ρ) (hG : 1 ≤ G) (hGρ : G ^ 2 < ρ)
    (hp : G ^ 2 * (2 * ρ ^ 2 + 1) < p) :
    ¬ (Z3NetF.ent (Φ z₁ d) 0 (K d - 1) = (ρ : ZMod p) ∧
      Z3NetF.ent (Φ z₂ d) 0 (K d - 1) = (ρ : ZMod p) ^ 2 ∧
      Z3NetF.ent (Φ z₃ d) 0 (K d - 1) = (ρ : ZMod p) ^ 3 ∧
      ∀ i j, (i = z₁ ∨ i = z₂ ∨ i = z₃) → (j = z₁ ∨ j = z₂ ∨ j = z₃) → i ≠ j →
        |(Z3NetF.ent (Φ i j) 0 (K j - 1)).valMinAbs| ≤ G) := by
  rintro ⟨e1, e2, e3, hg⟩
  have hs : 2 ≤ s := by
    have := z₁.isLt; have := z₂.isLt
    have : (z₁ : ℕ) ≠ z₂ := fun h => h12 (Fin.ext h)
    omega
  obtain ⟨lam, mu, hl, hm, hent⟩ := ObsFrameid.layer K hK hK1 inf x hx L U hL hU Φ hΦ hs
  have hwN : ∀ c e, c ≠ e → Z3NetF.wN inf x c e ≠ 0 := by
    intro c e hce
    unfold Z3NetF.wN
    split_ifs with h
    · exact one_ne_zero
    · push Not at h
      rw [Ring.inverse_eq_inv']
      exact inv_ne_zero (hx c e h.1 h.2 hce).ne_zero
  have nz : ∀ c e, c ≠ e → Z3NetF.ent (Φ c e) 0 (K e - 1) ≠ 0 := fun c e hce => by
    rw [hent c e hce]; exact mul_ne_zero (mul_ne_zero (hl c) (hm e)) (hwN c e hce)
  have hid := ObsFrameid.frameid K hK hK1 inf x hx L U hL hU Φ hΦ z₁ z₂ z₃ d h12 h13 h1d h23 h2d h3d
  rw [e1, e2, e3] at hid
  have hρ0 : (ρ : ZMod p) ≠ 0 := by rw [← e1]; exact nz _ _ h1d
  -- `g21 g32 ρ + g12 g31 ρ² = g31 g32` in `𝔽_p`
  set g := fun i j => Z3NetF.ent (Φ i j) 0 (K j - 1)
  have key : g z₂ z₁ * g z₃ z₂ * (ρ : ZMod p) + g z₁ z₂ * g z₃ z₁ * (ρ : ZMod p) ^ 2 =
      g z₃ z₁ * g z₃ z₂ := by
    field_simp at hid
    linear_combination hid
  -- the integer version
  set G21 := (g z₂ z₁).valMinAbs
  set G32 := (g z₃ z₂).valMinAbs
  set G12 := (g z₁ z₂).valMinAbs
  set G31 := (g z₃ z₁).valMinAbs
  have S1 : z₁ = z₁ ∨ z₁ = z₂ ∨ z₁ = z₃ := Or.inl rfl
  have S2 : z₂ = z₁ ∨ z₂ = z₂ ∨ z₂ = z₃ := Or.inr (Or.inl rfl)
  have S3 : z₃ = z₁ ∨ z₃ = z₂ ∨ z₃ = z₃ := Or.inr (Or.inr rfl)
  have b21 := hg z₂ z₁ S2 S1 (Ne.symm h12)
  have b32 := hg z₃ z₂ S3 S2 (Ne.symm h23)
  have b12 := hg z₁ z₂ S1 S2 h12
  have b31 := hg z₃ z₁ S3 S1 (Ne.symm h13)
  set Z : ℤ := G21 * G32 * ρ + G12 * G31 * ρ ^ 2 - G31 * G32 with hZ
  have c21 : ((G21 : ℤ) : ZMod p) = g z₂ z₁ := ZMod.coe_valMinAbs _
  have c32 : ((G32 : ℤ) : ZMod p) = g z₃ z₂ := ZMod.coe_valMinAbs _
  have c12 : ((G12 : ℤ) : ZMod p) = g z₁ z₂ := ZMod.coe_valMinAbs _
  have c31 : ((G31 : ℤ) : ZMod p) = g z₃ z₁ := ZMod.coe_valMinAbs _
  have hZp : ((Z : ℤ) : ZMod p) = 0 := by
    rw [hZ]
    push_cast [c21, c32, c12, c31]
    linear_combination key
  have hdvd : (p : ℤ) ∣ Z := (ZMod.intCast_zmod_eq_zero_iff_dvd Z p).mp hZp
  have hGr : (G : ℤ) ^ 2 < ρ := by exact_mod_cast hGρ
  have hpr : (G : ℤ) ^ 2 * (2 * ρ ^ 2 + 1) < p := by exact_mod_cast hp
  have hρ1 : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have habs : ∀ a b : ℤ, |a| ≤ G → |b| ≤ G → |a * b| ≤ (G : ℤ) ^ 2 := by
    intro a b ha hb
    rw [abs_mul, sq]
    exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
  have hZ0 : Z = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    have t1 := habs _ _ b21 b32
    have t2 := habs _ _ b12 b31
    have t3 := habs _ _ b31 b32
    calc |Z| ≤ |G21 * G32 * ρ| + |G12 * G31 * ρ ^ 2| + |G31 * G32| := by
          have := abs_sub (G21 * G32 * ρ + G12 * G31 * ρ ^ 2) (G31 * G32)
          have := abs_add_le (G21 * G32 * ρ) (G12 * G31 * ρ ^ 2)
          rw [hZ]; linarith
      _ = |G21 * G32| * ρ + |G12 * G31| * ρ ^ 2 + |G31 * G32| := by
          rw [abs_mul (G21 * G32), abs_mul (G12 * G31), abs_of_pos (by positivity : (0 : ℤ) < ρ),
            abs_of_pos (by positivity : (0 : ℤ) < ρ ^ 2)]
      _ ≤ (G : ℤ) ^ 2 * ρ + (G : ℤ) ^ 2 * ρ ^ 2 + (G : ℤ) ^ 2 := by
          have : (0 : ℤ) ≤ ρ := by positivity
          nlinarith
      _ < p := by nlinarith
  have hne : G31 * G32 ≠ 0 := by
    apply mul_ne_zero
    · intro h; exact nz _ _ (Ne.symm h13) ((ZMod.valMinAbs_eq_zero _).mp h)
    · intro h; exact nz _ _ (Ne.symm h23) ((ZMod.valMinAbs_eq_zero _).mp h)
  have hdvd2 : (ρ : ℤ) ∣ G31 * G32 := ⟨G21 * G32 + G12 * G31 * ρ, by rw [hZ] at hZ0; linarith⟩
  have : G31 * G32 = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd2
    have := habs _ _ b31 b32
    linarith
  exact hne this

alias frameid := ObsFrameid.frameid

end

end Z3NetF.Proofs
