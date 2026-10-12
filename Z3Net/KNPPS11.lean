/-
Proof module (stage 11, entry KNPP): `def:pprelax` and the general form of `prop:ppsep` as compared
statements; `prop:pp1` for every prime.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.KNMain
public import Z3Net.PPMain
public import Z3Net.PP1All
public import Z3Net.KNPPDefs

@[expose] public section

/-!
# Stage 11 additions to entry KNPP

* `Relax.IsCert` (`def:pprelax`, the certificate as a proposition over all configurations; the
  relaxation `Relax.total` is the kernel-evaluable one of `KNRelax`), `Relax.checkAll_of_isCert`,
  `Relax.sideOK_of_isCert` (the Boolean checks of `KNRelax` follow from it);
* `ppsep_general` (`prop:ppsep` for every odd prime and every design with a certificate), from
  `Geom.sep_of_cert`;
* `pp1_net_all` (`prop:pp1` for every prime, including `p = 2`), from `PP1All.pp1_net_all`.
-/

namespace Z3NetKN.Relax

/-- **`def:pprelax`** (certificate).  `(T, R)` (`R = D.R`) is a certificate for the design
`D.rows` for `(D.p, D.r)` if `T ≤ t_x² + t_y² + t_z²` (`total`) for every configuration `(δ, h)`
(`δ ≠ 0`, `|δ_c| ≤ R_c`, `h_c < L_c`, `h_c = 0` if `δ_c = 0`), `R_c < p` for all `c`,
`T ≤ p² R_c²` for full `c` (`c < r`), and `R_c = 1`, `T ≤ p⁴` for skeleton `c`. -/
def IsCert (D : Design) (T : ℕ) : Prop :=
  (∀ dl : Fin 3 → ℤ, dl ≠ 0 → (∀ c, |dl c| ≤ (D.R c : ℤ)) → ∀ ch : Fin 3 → ℕ,
      (∀ c, ch c < D.L c) → (∀ c, dl c = 0 → ch c = 0) → T ≤ total D dl ch) ∧
    (∀ c, D.R c < D.p) ∧ (∀ c : Fin 3, (c : ℕ) < D.r → T ≤ (D.p * D.R c) ^ 2) ∧
    (∀ c : Fin 3, D.r ≤ (c : ℕ) → D.R c = 1 ∧ T ≤ (D.p * D.p) ^ 2)

lemma s11_mem_steps {R : ℕ} {d : ℤ} (h : d ∈ steps R) : |d| ≤ (R : ℤ) := by
  simp [steps] at h
  obtain ⟨i, hi, rfl⟩ := h
  rw [abs_le]; constructor <;> omega

lemma s11_mem_chains {L : ℕ} {d : ℤ} {c : ℕ} (h : c ∈ chains L d) (hL : 1 ≤ L) :
    c < L ∧ (d = 0 → c = 0) := by
  unfold chains at h
  split_ifs at h with hd
  · simp at h; subst h; exact ⟨hL, fun _ => rfl⟩
  · simp only [List.mem_range] at h; exact ⟨h, fun h' => absurd h' hd⟩

lemma s11_L_pos (D : Design) (c : Fin 3) : 1 ≤ D.L c := by
  unfold Design.L win; split_ifs <;> omega

theorem checkAll_of_isCert (D : Design) (T : ℕ) (h : IsCert D T) : checkAll D T = true := by
  simp only [checkAll, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  intro d0 h0 d1 h1 d2 h2
  by_cases hz : d0 = 0 ∧ d1 = 0 ∧ d2 = 0
  · exact Or.inl ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
  right
  intro c0 hc0 c1 hc1 c2 hc2
  have e0 := s11_mem_chains hc0 (s11_L_pos D 0)
  have e1 := s11_mem_chains hc1 (s11_L_pos D 1)
  have e2 := s11_mem_chains hc2 (s11_L_pos D 2)
  apply h.1
  · intro hdl
    apply hz
    exact ⟨congrFun hdl 0, congrFun hdl 1, congrFun hdl 2⟩
  · intro c; fin_cases c
    · exact s11_mem_steps h0
    · exact s11_mem_steps h1
    · exact s11_mem_steps h2
  · intro c; fin_cases c
    · exact e0.1
    · exact e1.1
    · exact e2.1
  · intro c; fin_cases c
    · exact e0.2
    · exact e1.2
    · exact e2.2

theorem sideOK_of_isCert (D : Design) (T : ℕ) (h : IsCert D T) : sideOK D T = true := by
  simp only [sideOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Design.full, decide_eq_false_iff_not,
    not_lt]
  intro c
  refine ⟨⟨⟨⟨h.2.1 c, s11_L_pos D c⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold Design.L win; split_ifs <;> omega
  · by_cases hc : (c : ℕ) < D.r
    · exact Or.inr (h.2.2.1 c hc)
    · exact Or.inl (by omega)
  · by_cases hc : (c : ℕ) < D.r
    · exact Or.inl hc
    · exact Or.inr (h.2.2.2 c (by omega))

end Z3NetKN.Relax

namespace Z3NetKN

/-! ### The bridge from `def:pprelax` as in `ChallengeKNPP.lean` (definitions `rlxLin`, …, `IsPPCert`, verbatim,
in `Z3Net/KNPPDefs.lean` since stage 13b) to `KNRelax` -/

lemma rlxLin_eq (row : Fin 4 → ℤ) (δ : ℤ) (h : ℕ) : rlxLin row δ h = Relax.lin1 row δ h := by
  rw [rlxLin, Fin.sum_univ_four, Relax.lin1, Relax.sgn]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  rcases h with _ | _ | _ | h <;> simp <;> split_ifs <;> first | ring1 | omega

lemma rlxRes_eq (p : ℕ) (rows : Fin 3 → Fin 4 → ℤ) (δ : Fin 3 → ℤ) (h : Fin 3 → ℕ) :
    rlxRes p rows δ h = Relax.linC rows δ h % (p : ℤ) := by
  rw [rlxRes, Fin.sum_univ_three, Relax.linC, rlxLin_eq, rlxLin_eq, rlxLin_eq]

lemma own_eq (δ : Fin 3 → ℤ) (c : Fin 3) :
    (if ∀ d, d ≠ c → δ d = 0 then (0 : ℤ) else 1) = (if Relax.isOwn δ c then 0 else 1) := by
  fin_cases c <;> simp [Relax.isOwn, Fin.forall_fin_succ]

lemma rlxT_eq (p : ℕ) (b ι ε : ℤ) : rlxT p b ι ε = Relax.tvJ p b ι ε := by
  rfl

lemma rlxTerm_eq (p r : ℕ) (Rg : Fin 3 → ℕ) (R : Rows) (δ : Fin 3 → ℤ) (h : Fin 3 → ℕ)
    (c : Fin 3) : rlxTerm p r R δ h c = Relax.term ⟨p, r, Rg, R⟩ δ h c := by
  rw [rlxTerm, Relax.term, own_eq, rlxRes_eq, rlxRes_eq]
  simp only [Relax.Design.full, decide_eq_true_eq, rlxT_eq]

lemma isCert_of (p r : ℕ) (Rg : Fin 3 → ℕ) (R : Rows) (T : ℕ) (h : IsPPCert p r Rg R T) :
    Relax.IsCert ⟨p, r, Rg, R⟩ T := by
  refine ⟨fun dl hdl hR ch hch hz => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  have := h.1 dl hdl hR ch hch hz
  rw [Fin.sum_univ_three, rlxTerm_eq p r Rg, rlxTerm_eq p r Rg, rlxTerm_eq p r Rg] at this
  exact this

end Z3NetKN

namespace Z3NetKN

open Z3NetKN.Relax

/-- **`prop:ppsep`** (general form). -/
theorem ppsep_general (p r k T : ℕ) (hp : p.Prime) (_hp2 : p ≠ 2)
    (hk : (r = 1 ∧ 3 ≤ k) ∨ (r = 2 ∧ 2 ≤ k)) (R : Rows) (Rg : Fin 3 → ℕ)
    (hcert : IsPPCert p r Rg R T)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (digPoint p (3 * k + r) C v) (digPoint p (3 * k + r) C w) :=
  Geom.sep_of_cert (by omega) (by omega) hp.two_le R Rg T (checkAll_of_isCert _ T (isCert_of p r Rg R T hcert))
    (sideOK_of_isCert _ T (isCert_of p r Rg R T hcert)) C hC v w hvw

/-- **`prop:pp1`** for every prime `p` (including `p = 2`). -/
theorem pp1_net_all (p k : ℕ) (hp : p.Prime) (R : Rows) (hS : CondS1 R)
    (hN : CondN1 p R) (hJ1 : J1 p R = 1) (hJ2 : J2 p R = -1) (hJ3 : J3 p R = 2)
    (hJ4 : J4 p R = 2) (hJ5 : J5 p R = 1) (hk : 3 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) :=
  PP1All.pp1_net_all p k hp R hS hN hJ1 hJ2 hJ3 hJ4 hJ5 hk

end Z3NetKN
