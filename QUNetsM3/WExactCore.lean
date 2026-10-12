/-
`prop:wnet` (4): the certificate of the exact minimum distance of `𝒲_p` at one prime
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WReduce

@[expose] public section

/-!
# The lower bound of `prop:wnet` (4) at one prime

`chkW p d a ρ` enumerates the data of `w_reduce` for `𝒲_p` (`a = h − r`, `ρ = 2r + 1`): the steps
`E ∈ {−2,…,2}³ ∖ 0` (a step with some `|E_c| ≥ 3` has `|D_c| ≥ 2p² + 1`), `D ∈ {σ, σ − p}` with
`σ = (a(E_x + E_y) + ρE_z) mod p`, the wraps `κ` allowed by `lem:wwrap` (necessary part), and the
third-digit changes `F_c ∈ {σ_c, σ_c − p}` of the third rows `(0,1,2)`, `(1,0,1)`, `(0,1,0)`, each wrap
independently (a relaxation: the joint values of the four digits are not used). If every value is
`≥ d`, every pair of distinct points has squared toroidal distance `≥ d` at integer scale `p³`
(`chkW_sound`). With a pair attaining `d` this is the exact minimum (`WExact.lean`).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

/-- The conditions on `(D, κ)` of `w_reduce`. -/
def okDK (p D k : ℤ) : Bool :=
  decide (D ≤ p - 1) && decide (-D ≤ p - 1) && decide (2 * D - p * k ≤ p - 1) &&
    decide (-(2 * D - p * k) ≤ p - 1) &&
    ((decide (k = 0) && decide (2 * D ≤ p - 1) && decide (-(2 * D) ≤ p - 1)) ||
      (decide (k = 1) && decide (0 < D)) || (decide (k = -1) && decide (D < 0)))

/-- The value of one option. -/
def valW (p Ex Ey Ez D k Fx Fy Fz : ℤ) : ℤ :=
  (p ^ 2 * Ex + p * (2 * D - p * k) + Fx) ^ 2 + (p ^ 2 * Ey + p * (2 * D - p * k) + Fy) ^ 2 +
    (p ^ 2 * Ez + p * D + Fz) ^ 2

/-- The certificate: every option of every short step has value `≥ d`, and `d ≤ (2p² + 1)²`. -/
def chkW (p d a ρ : ℤ) : Bool :=
  decide (d ≤ (2 * p ^ 2 + 1) ^ 2) &&
  LW5.all fun Ex => LW5.all fun Ey => LW5.all fun Ez =>
    (Ex == 0 && Ey == 0 && Ez == 0) ||
      ([(a * (Ex + Ey) + ρ * Ez) % p, (a * (Ex + Ey) + ρ * Ez) % p - p].all fun D =>
        LW3.all fun k => !(okDK p D k) ||
          ([(Ey + 2 * Ez) % p, (Ey + 2 * Ez) % p - p].all fun Fx =>
            [(Ex + Ez) % p, (Ex + Ez) % p - p].all fun Fy =>
              [Ey % p, Ey % p - p].all fun Fz =>
                decide (Fx < 1 - p) || decide (Fy < 1 - p) || decide (Fz < 1 - p) ||
                  decide (d ≤ valW p Ex Ey Ez D k Fx Fy Fz)))

/-- An integer `X` with `|X| ≤ p − 1` and `X ≡ Y (mod p)` is `Y mod p` or `Y mod p − p`. -/
theorem mem_two_res {X Y : ℤ} (hp : 0 < (p : ℤ)) (h : (X : ZMod p) = (Y : ZMod p)) (h1 : X ≤ p - 1)
    (h2 : -X ≤ p - 1) : X ∈ [Y % (p : ℤ), Y % (p : ℤ) - p] := by
  rw [ZMod.intCast_eq_intCast_iff'] at h
  have e := Int.emod_add_mul_ediv X p
  have hn := Int.emod_nonneg X (ne_of_gt hp)
  have hl := Int.emod_lt_of_pos X hp
  set k := X / p
  have hk : k = 0 ∨ k = -1 := by
    rcases le_or_gt 1 k with h3 | h3
    · have : (p : ℤ) * 1 ≤ p * k := mul_le_mul_of_nonneg_left h3 hp.le
      omega
    · rcases le_or_gt k (-2) with h4 | h4
      · have : (p : ℤ) * k ≤ p * (-2) := mul_le_mul_of_nonneg_left h4 hp.le
        omega
      · omega
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hk with hk | hk <;> rw [hk] at e
  · left; rw [← h]; linarith
  · right; rw [← h]; linarith

theorem mem_LW5_of_abs {a : ℤ} (h : |a| < 3) : a ∈ LW5 := by
  rw [abs_lt] at h; exact mem_LW5 (by omega) (by omega)

/-- **Soundness of the certificate.** -/
theorem chkW_sound (hp : p.Prime) (hp5 : 5 ≤ p) (d : ℤ)
    (hchk : chkW p d ((hW p : ℤ) - rW p) (2 * rW p + 1) = true) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) : d ≤ sepSqG p (genW p) x x' t := by
  have := Fact.mk hp
  have hodd := odd_of_prime5 hp hp5
  have hC0 : ∀ c s, (genW p c *ᵥ s) 0 = s c := fun c s => genWr_row0 _ s c
  obtain ⟨E, D, κ, F, hE, -, hD, hD1, hD2, hκ, hg1, hg2, hF, hval⟩ :=
    w_reduce hp hp5 (genW p) hC0 (fun s => by simp only [genW, genWr_x1, genWr_y1])
      (fun s => genWr_x1_eq hodd _ s) x x' hx hx' hne t
  rw [hval]
  have hpZ : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  simp only [chkW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨hbig, hall⟩ := hchk
  have q0 := sq_nonneg ((p : ℤ) ^ 2 * E 0 + p * (2 * D - p * κ) + F 0)
  have q1 := sq_nonneg ((p : ℤ) ^ 2 * E 1 + p * (2 * D - p * κ) + F 1)
  have q2 := sq_nonneg ((p : ℤ) ^ 2 * E 2 + p * D + F 2)
  have hp0 : (0 : ℤ) ≤ p := by omega
  -- a long step
  have hlong : ∀ (e y : ℤ), 3 ≤ |e| → y ≤ p ^ 2 - 1 → -y ≤ p ^ 2 - 1 →
      (2 * (p : ℤ) ^ 2 + 1) ^ 2 ≤ ((p : ℤ) ^ 2 * e + y) ^ 2 := by
    intro e y he hy1 hy2
    have hp2 : (0 : ℤ) ≤ (p : ℤ) ^ 2 := by positivity
    rcases le_abs'.1 he with h | h
    · have : (p : ℤ) ^ 2 * e ≤ (p : ℤ) ^ 2 * (-3) := mul_le_mul_of_nonneg_left h hp2
      nlinarith
    · have : (p : ℤ) ^ 2 * 3 ≤ (p : ℤ) ^ 2 * e := mul_le_mul_of_nonneg_left h hp2
      nlinarith
  have hF0 := hF 0; have hF1 := hF 1; have hF2 := hF 2
  have m1 := mul_le_mul_of_nonneg_left hg1 hp0
  have m2 := mul_le_mul_of_nonneg_left hg2 hp0
  have m3 := mul_le_mul_of_nonneg_left hD1 hp0
  have m4 := mul_le_mul_of_nonneg_left hD2 hp0
  have hpg1 : (p : ℤ) * (2 * D - p * κ) + F 0 ≤ p ^ 2 - 1 := by linarith [hF0.2.1]
  have hpg2 : -((p : ℤ) * (2 * D - p * κ) + F 0) ≤ p ^ 2 - 1 := by linarith [hF0.2.2]
  have hpg3 : (p : ℤ) * (2 * D - p * κ) + F 1 ≤ p ^ 2 - 1 := by linarith [hF1.2.1]
  have hpg4 : -((p : ℤ) * (2 * D - p * κ) + F 1) ≤ p ^ 2 - 1 := by linarith [hF1.2.2]
  have hpg5 : (p : ℤ) * D + F 2 ≤ p ^ 2 - 1 := by linarith [hF2.2.1]
  have hpg6 : -((p : ℤ) * D + F 2) ≤ p ^ 2 - 1 := by linarith [hF2.2.2]
  by_cases h3 : 3 ≤ |E 0| ∨ 3 ≤ |E 1| ∨ 3 ≤ |E 2|
  · rcases h3 with h | h | h
    · have := hlong (E 0) _ h hpg1 hpg2
      rw [show (p : ℤ) ^ 2 * E 0 + (p * (2 * D - p * κ) + F 0) =
        (p : ℤ) ^ 2 * E 0 + p * (2 * D - p * κ) + F 0 by ring] at this
      linarith
    · have := hlong (E 1) _ h hpg3 hpg4
      rw [show (p : ℤ) ^ 2 * E 1 + (p * (2 * D - p * κ) + F 1) =
        (p : ℤ) ^ 2 * E 1 + p * (2 * D - p * κ) + F 1 by ring] at this
      linarith
    · have := hlong (E 2) _ h hpg5 hpg6
      rw [show (p : ℤ) ^ 2 * E 2 + (p * D + F 2) = (p : ℤ) ^ 2 * E 2 + p * D + F 2 by ring] at this
      linarith
  push Not at h3
  obtain ⟨hx3, hy3, hz3⟩ := h3
  have hp0' : (0 : ℤ) < p := by omega
  have hcase := hall (E 0) (mem_LW5_of_abs hx3) (E 1) (mem_LW5_of_abs hy3) (E 2) (mem_LW5_of_abs hz3)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcase
  rcases hcase with ⟨⟨h0, h1⟩, h2⟩ | hc
  · exact absurd (funext fun c => by fin_cases c <;> assumption) hE
  -- the residues
  have hDm : D ∈ [(((hW p : ℤ) - rW p) * (E 0 + E 1) + (2 * rW p + 1) * E 2) % (p : ℤ),
      (((hW p : ℤ) - rW p) * (E 0 + E 1) + (2 * rW p + 1) * E 2) % (p : ℤ) - p] := by
    refine mem_two_res hp0' ?_ hD1 hD2
    rw [hD]; simp only [genW, genWr_z1, rhoZ]; push_cast; ring
  have hκm : κ ∈ LW3 := by
    rcases hκ with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide
  have hok : okDK p D κ = true := by
    simp only [okDK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hD1, hD2⟩, hg1⟩, hg2⟩, by
      rcases hκ with ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl (Or.inl ⟨⟨a, b⟩, c⟩)
      · exact Or.inl (Or.inr ⟨a, b⟩)
      · exact Or.inr ⟨a, b⟩⟩
  have hFx : F 0 ∈ [(E 1 + 2 * E 2) % (p : ℤ), (E 1 + 2 * E 2) % (p : ℤ) - p] :=
    mem_two_res hp0' (by rw [hF0.1]; simp only [genW, genWr_x2]; push_cast; ring) hF0.2.1 hF0.2.2
  have hFy : F 1 ∈ [(E 0 + E 2) % (p : ℤ), (E 0 + E 2) % (p : ℤ) - p] :=
    mem_two_res hp0' (by rw [hF1.1]; simp only [genW, genWr_y2]; push_cast; ring) hF1.2.1 hF1.2.2
  have hFz : F 2 ∈ [E 1 % (p : ℤ), E 1 % (p : ℤ) - p] :=
    mem_two_res hp0' (by rw [hF2.1]; simp only [genW, genWr_z2]) hF2.2.1 hF2.2.2
  have := hc D hDm κ hκm
  simp only [Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with hno | hv
  · rw [hok] at hno; exact absurd hno (by decide)
  · have := hv (F 0) hFx (F 1) hFy (F 2) hFz
    rcases this with ((h | h) | h) | h
    · omega
    · omega
    · omega
    · simpa [valW] using h

end QUNetsM3
