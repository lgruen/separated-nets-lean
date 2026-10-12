/-
`prop:wfamily` (2): `F(½ − ε, ½ − ε, 2ε) = min(q_a(ε), q_b(ε))` for `0 < ε ≤ 3/100`
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WFamCert
public import QUNetsM3.WDefs

@[expose] public section

/-!
# `prop:wfamily` (2)

As printed: every option has `|δ| < 1` and `|2δ − κ| < 1`, so a step with some `|E_c| ≥ 3` has `|V|² > 4`; for the
other steps `δ = J/2 − Qε` and the finite certificate `famAll` (`WFamCert.lean`) gives `|V|² ≥ q_a(ε)` or
`|V|² ≥ q_b(ε)` on every option; the rows (a) `E = (1,0,−1)`, `(δ, κ) = (½ − 3ε, 1)` and (b) `E = e_z`, `(2ε, 0)`
attain `q_a(ε)` and `q_b(ε)`.
-/

namespace QUNetsM3

/-- `|V|²` in coordinates. -/
theorem optValW_eval (E : Fin 3 → ℤ) (δ : ℝ) (κ : ℤ) :
    optValW E δ κ = ((E 0 : ℝ) + 2 * δ - κ) ^ 2 + ((E 1 : ℝ) + 2 * δ - κ) ^ 2 + ((E 2 : ℝ) + δ) ^ 2 := by
  simp only [optValW, Fin.sum_univ_three, wW, oneOneW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem optValW_nonneg (E : Fin 3 → ℤ) (δ : ℝ) (κ : ℤ) : 0 ≤ optValW E δ κ := by
  rw [optValW_eval]; positivity

/-- The set of option values of `τ`. -/
def optSet (τ : Fin 3 → ℝ) : Set ℝ :=
  {v : ℝ | ∃ E : Fin 3 → ℤ, E ≠ 0 ∧ ∃ δ : ℝ, ∃ κ : ℤ, IsOptW τ E δ κ ∧ v = optValW E δ κ}

theorem Ffam_def (τ : Fin 3 → ℝ) : Ffam τ = sInf (optSet τ) := rfl

theorem optSet_bdd (τ : Fin 3 → ℝ) : BddBelow (optSet τ) :=
  ⟨0, by rintro v ⟨E, -, δ, κ, -, rfl⟩; exact optValW_nonneg E δ κ⟩

theorem sgnR_pos {x : ℝ} (h : 0 < x) : sgnR x = 1 := by simp [sgnR, h]
theorem sgnR_neg {x : ℝ} (h : x < 0) : sgnR x = -1 := by simp [sgnR, h, not_lt.2 h.le]

/-- The wrap of an option: `κ = 1` and `δ > 0`, `κ = −1` and `δ < 0`, or `κ = 0` and `|δ| < ½`. -/
theorem opt_kappa {τ : Fin 3 → ℝ} {E : Fin 3 → ℤ} {δ : ℝ} {κ : ℤ} (h : IsOptW τ E δ κ) :
    (κ = 1 ∧ 0 < δ) ∨ (κ = -1 ∧ δ < 0) ∨ (κ = 0 ∧ -(1 / 2) < δ ∧ δ < 1 / 2) := by
  obtain ⟨-, -, -, hk | ⟨hk, hd⟩⟩ := h
  · unfold sgnR at hk
    split_ifs at hk with h1 h2
    · exact Or.inl ⟨hk, h1⟩
    · exact Or.inr (Or.inl ⟨hk, h2⟩)
    · right; right
      have : δ = 0 := by push Not at h1 h2; linarith
      exact ⟨hk, by linarith, by linarith⟩
  · rw [abs_lt] at hd
    exact Or.inr (Or.inr ⟨hk, hd.1, hd.2⟩)

/-- A long step: some `|E_c| ≥ 3` gives `|V|² > 4`. -/
theorem opt_long {τ : Fin 3 → ℝ} {E : Fin 3 → ℤ} {δ : ℝ} {κ : ℤ} (h : IsOptW τ E δ κ)
    (h3 : 3 ≤ |E 0| ∨ 3 ≤ |E 1| ∨ 3 ≤ |E 2|) : 4 < optValW E δ κ := by
  have hk := opt_kappa h
  obtain ⟨hd1, hd2, -⟩ := h
  have hy : -1 < 2 * δ - κ ∧ 2 * δ - κ < 1 := by
    rcases hk with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h, h'⟩ <;> push_cast <;> constructor <;> linarith
  have key : ∀ (e : ℤ) (y : ℝ), 3 ≤ |e| → -1 < y → y < 1 → 4 < ((e : ℝ) + y) ^ 2 := by
    intro e y he h1 h2
    rcases le_abs'.1 he with h | h
    · have : (e : ℝ) ≤ -3 := by exact_mod_cast h
      nlinarith
    · have : (3 : ℝ) ≤ e := by exact_mod_cast h
      nlinarith
  rw [optValW_eval]
  have q0 := sq_nonneg ((E 0 : ℝ) + 2 * δ - κ)
  have q1 := sq_nonneg ((E 1 : ℝ) + 2 * δ - κ)
  have q2 := sq_nonneg ((E 2 : ℝ) + δ)
  rcases h3 with h | h | h
  · have := key (E 0) (2 * δ - κ) h hy.1 hy.2
    rw [show (E 0 : ℝ) + (2 * δ - κ) = (E 0 : ℝ) + 2 * δ - κ by ring] at this; linarith
  · have := key (E 1) (2 * δ - κ) h hy.1 hy.2
    rw [show (E 1 : ℝ) + (2 * δ - κ) = (E 1 : ℝ) + 2 * δ - κ by ring] at this; linarith
  · have := key (E 2) δ h hd1 hd2; linarith

theorem sum_tauEps (ε : ℝ) (E : Fin 3 → ℤ) :
    ∑ c, tauEps ε c * (E c : ℝ) = ((E 0 : ℝ) + E 1) / 2 - ε * ((E 0 : ℝ) + E 1 - 2 * E 2) := by
  simp only [Fin.sum_univ_three, tauEps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem qaW_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 3 / 100) : qaW ε ≤ 5 / 4 := by unfold qaW; nlinarith

/-- **The lower bound of `prop:wfamily` (2)**: every option of `τ_ε` has `|V|² ≥ min(q_a(ε), q_b(ε))`. -/
theorem wfam_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 3 / 100) (E : Fin 3 → ℤ) (hE : E ≠ 0) (δ : ℝ) (κ : ℤ)
    (hopt : IsOptW (tauEps ε) E δ κ) : min (qaW ε) (qbW ε) ≤ optValW E δ κ := by
  by_cases h3 : 3 ≤ |E 0| ∨ 3 ≤ |E 1| ∨ 3 ≤ |E 2|
  · have := opt_long hopt h3
    have := qaW_le h0.le h1
    exact le_trans (min_le_left _ _) (by linarith)
  push Not at h3
  obtain ⟨hx3, hy3, hz3⟩ := h3
  have hx : -2 ≤ E 0 ∧ E 0 ≤ 2 := by rw [abs_lt] at hx3; omega
  have hy : -2 ≤ E 1 ∧ E 1 ≤ 2 := by rw [abs_lt] at hy3; omega
  have hz : -2 ≤ E 2 ∧ E 2 ≤ 2 := by rw [abs_lt] at hz3; omega
  have hkap := opt_kappa hopt
  obtain ⟨hd1, hd2, ⟨k, hk⟩, -⟩ := hopt
  rw [sum_tauEps] at hk
  set J : ℤ := E 0 + E 1 + 2 * k with hJ
  set Q : ℤ := E 0 + E 1 - 2 * E 2 with hQ
  have hδ : δ = (J : ℝ) / 2 - ε * Q := by rw [hk, hJ, hQ]; push_cast; ring
  have hQb : -8 ≤ Q ∧ Q ≤ 8 := by omega
  have hQR : (-8 : ℝ) ≤ Q ∧ (Q : ℝ) ≤ 8 := by constructor <;> exact_mod_cast (by omega : _)
  have hεQ : -(24 / 100 : ℝ) ≤ ε * Q ∧ ε * (Q : ℝ) ≤ 24 / 100 := by
    constructor <;> nlinarith
  have hJb : -2 ≤ J ∧ J ≤ 2 := by
    have h1' : ((J : ℤ) : ℝ) < 3 := by rw [hδ] at hd2; linarith
    have h2' : (-3 : ℝ) < ((J : ℤ) : ℝ) := by rw [hδ] at hd1; linarith
    constructor
    · have : (-3 : ℤ) < J := by exact_mod_cast h2'
      omega
    · have : J < 3 := by exact_mod_cast h1'
      omega
  have hκb : -1 ≤ κ ∧ κ ≤ 1 := by
    rcases hkap with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hall := famAll_true
  simp only [famAll, List.all_eq_true] at hall
  have hcase := hall (E 0) (mem_LW5 hx.1 hx.2) (E 1) (mem_LW5 hy.1 hy.2) (E 2) (mem_LW5 hz.1 hz.2)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcase
  rcases hcase with ⟨⟨h0', h1'⟩, h2'⟩ | hc
  · exact absurd (funext fun c => by fin_cases c <;> assumption) hE
  set t : ℝ := 100 * ε / 3 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hεt : ε = 3 * t / 100 := by rw [ht]; ring
  have h100 : 100 * δ = 50 * (J : ℝ) - 3 * (Q : ℝ) * t := by rw [hδ, hεt]; ring
  have h100' : 100 * δ = 50 * (J : ℝ) - 3 * ((E 0 : ℝ) + E 1 - 2 * E 2) * t := by
    rw [h100, hQ]; push_cast; ring
  have hok := hc J (mem_LW5 hJb.1 hJb.2) κ (mem_LW3 hκb.1 hκb.2)
  have hsound := famOK_sound (E 0) (E 1) (E 2) J κ k t ht0 ht1 (by rw [hJ]; ring)
    (by push_cast; linarith [h100'])
    (by push_cast; linarith [h100'])
    (by intro h; rcases hkap with ⟨-, hp⟩ | ⟨h', -⟩ | ⟨h', -⟩
        · push_cast; linarith [h100']
        · rw [h] at h'; norm_num at h'
        · rw [h] at h'; norm_num at h')
    (by intro h; rcases hkap with ⟨h', -⟩ | ⟨-, hn⟩ | ⟨h', -⟩
        · rw [h] at h'; norm_num at h'
        · push_cast; linarith [h100']
        · rw [h] at h'; norm_num at h')
    (by intro h; rcases hkap with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, ha, hb⟩
        · rw [h] at h'; norm_num at h'
        · rw [h] at h'; norm_num at h'
        · constructor <;> push_cast <;> linarith [h100'])
    hok
  have hval : 10000 * optValW E δ κ =
      famA0 (E 0) (E 1) (E 2) J κ + famA1 (E 0) (E 1) (E 2) J κ * t + famA2 (E 0) (E 1) (E 2) * t ^ 2 := by
    rw [optValW_eval]
    have : δ = (50 * (J : ℝ) - 3 * (Q : ℝ) * t) / 100 := by linarith
    rw [this, hQ]
    simp only [famA0, famA1, famA2]
    push_cast
    ring
  have hqa : 10000 * qaW ε = 12500 - 2700 * t + 729 * t ^ 2 := by unfold qaW; rw [hεt]; ring
  have hqb : 10000 * qbW ε = 10000 + 1200 * t + 324 * t ^ 2 := by unfold qbW; rw [hεt]; ring
  rcases hsound with h | h
  · exact le_trans (min_le_left _ _) (by linarith)
  · exact le_trans (min_le_right _ _) (by linarith)

/-- Row (a) of `tab:wcontacts`: the option `E = (1, 0, −1)`, `δ = ½ − 3ε`, `κ = 1` of `τ_ε`, value `q_a(ε)`. -/
theorem wfam_rowa {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 3 / 100) :
    qaW ε ∈ optSet (tauEps ε) := by
  refine ⟨![1, 0, -1], by decide, 1 / 2 - 3 * ε, 1, ⟨by linarith, by linarith, ⟨0, ?_⟩, ?_⟩, ?_⟩
  · rw [sum_tauEps]; simp
    ring
  · left; rw [sgnR_pos (by linarith)]
  · rw [optValW_eval]; unfold qaW; simp; ring

/-- Row (b) of `tab:wcontacts`: the option `E = e_z`, `δ = 2ε`, `κ = 0` of `τ_ε`, value `q_b(ε)`. -/
theorem wfam_rowb {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 3 / 100) :
    qbW ε ∈ optSet (tauEps ε) := by
  refine ⟨![0, 0, 1], by decide, 2 * ε, 0, ⟨by linarith, by linarith, ⟨0, ?_⟩, ?_⟩, ?_⟩
  · rw [sum_tauEps]; simp; ring
  · right; refine ⟨rfl, ?_⟩; rw [abs_lt]; constructor <;> linarith
  · rw [optValW_eval]; unfold qbW; simp; ring

/-- **`prop:wfamily` (2)** (proof of `Wfam_two`). -/
theorem wfam_two {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 3 / 100) :
    Ffam (tauEps ε) = min (qaW ε) (qbW ε) := by
  rw [Ffam_def]
  apply le_antisymm
  · apply le_min
    · exact csInf_le (optSet_bdd _) (wfam_rowa h0 h1)
    · exact csInf_le (optSet_bdd _) (wfam_rowb h0 h1)
  · apply le_csInf ⟨_, wfam_rowa h0 h1⟩
    rintro v ⟨E, hE, δ, κ, hopt, rfl⟩
    exact wfam_lower h0 h1 E hE δ κ hopt

end QUNetsM3
