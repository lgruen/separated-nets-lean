/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAUstar
public import Z3Net.ThmACover
public import Z3Net.FDsep
public import Z3Net.FDeficit

@[expose] public section

/-!
# Theorem A, part 3: the assembly of `thm:A`(1) and the lower bound of `thm:A`(2)

V14 stage S3. The proof of Theorem A in `sec:Ustar`, with `a*_s` kept abstract:

* the reduction `R_S → ℤ/qℤ` exists for the admissible bases and is unique (`A_hom_core`);
* (1) `cor:tsk` gives the net (`A_net_core`), and one point in every cell gives the covering
  radius (`covering_of_net_core`, `A_covering_core`);
* (2) `prop:D` (through `D_sep_core`, i.e. `lem:Ss` for every `k ≥ 1`) with the dominance of `U*_s`
  gives `δ ≥ (1 - a*_s/q) N^(-1/s)` for `q ≥ 5 a*_s + 4` and every `k ≥ 1`, toroidal
  (`A_sep_core`, `A_sep_real_core`) and Euclidean (`A_sep_eucl_core`).

The generic forms (`*_gen`) hold for every ring homomorphism `ψ : R_S → ℤ/qℤ` and every solution
`(U', β)` of the residual problem and of `prop:Gs`, not only for the chosen ones of `Apoint`.
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Generic: covering radius of a net with one point in every cell -/

theorem covering_of_net_core {s q k : ℕ} (hs : 1 ≤ s) (hq : 2 ≤ q)
    (X : (Fin (s * k) → ZMod q) → Fin s → ℕ) (hX : IsNet0 s q (s * k) X) (x : Fin s → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v, ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by
  refine cover_of_cells hs hq X (fun a ha => ?_) x hx
  have hd : ∑ _c : Fin s, k = s * k := by simp
  obtain ⟨v, hv, _⟩ := hX (fun _ => k) hd a ha
  exact ⟨v, hv⟩

/-! ## The reduction `R_S → ℤ/qℤ` -/

variable {s : ℕ} [NeZero s]

lemma coprime_of_adm (hs : 3 ≤ s) {q : ℕ} (hq : AdmBase s q) : Nat.Coprime q (s - 2).factorial := by
  apply Nat.coprime_of_dvd
  intro p hp hpq hpf
  have h1 := hq.2 p hp hpq
  have h2 := (Nat.Prime.dvd_factorial hp).1 hpf
  omega

lemma hom_unique {q : ℕ} (ψ ψ' : RS s →+* ZMod q) : ψ = ψ' :=
  IsLocalization.ringHom_ext (Submonoid.powers ((((s - 2).factorial : ℕ) : ℤ))) (RingHom.ext_int _ _)

theorem A_hom_core (hs : 3 ≤ s) {q : ℕ} (hq : AdmBase s q) :
    Nonempty (RS s →+* ZMod q) ∧ ∀ ψ ψ' : RS s →+* ZMod q, ψ = ψ' := by
  refine ⟨Z3NetF.Proofs.away_hom_core q (s - 2).factorial (coprime_of_adm hs hq), fun ψ ψ' => ?_⟩
  exact hom_unique ψ ψ'

lemma Apoint_eq {q : ℕ} (k : ℕ) (ψ : RS s →+* ZMod q) :
    Apoint s q k = digPoint q (s * k) (fun c =>
      (PGen k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c).map ψ) := by
  funext v
  unfold Apoint
  rw [dite_eq_left ⟨ψ⟩]
  dsimp only
  rw [hom_unique (Classical.choice _) ψ]

/-! ## `thm:A`(1) -/

theorem A_net_gen {q : ℕ} [NeZero q] (hs : 3 ≤ s) (ψ : RS s →+* ZMod q) (k : ℕ)
    (Ur β : Fin s → ℕ → ℕ → RS s) (hres : Residual (0 : Fin s) placeA (UstarR s) 1 Ur) :
    IsNet0 s q (s * k) (digPoint q (s * k) fun c =>
      (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) :=
  Z3NetF.Proofs.tsk_net_core (k := k) (inf := (0 : Fin s)) (x := placeA) ψ (placesOK (by omega))
    (UstarR s) 1 Ur β hres

theorem A_net_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) :
    IsNet0 s q (s * k) (Apoint s q k) := by
  have : NeZero q := ⟨by have := hq.1; omega⟩
  obtain ⟨ψ⟩ := (A_hom_core hs hq).1
  rw [Apoint_eq k ψ]
  exact A_net_gen hs _ k _ _ (Ustar_data_core hs).1

theorem A_covering_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (x : Fin s → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (s * k) → ZMod q,
      ∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 :=
  covering_of_net_core (by omega) hq.1 _ (A_net_core s q k hs hq) x hx

/-! ## `thm:A`(2), the lower bound -/

theorem A_sep_gen {q : ℕ} [NeZero q] (hs : 3 ≤ s) (ψ : RS s →+* ZMod q) (k : ℕ) (hk : 1 ≤ k)
    (Ur β : Fin s → ℕ → ℕ → RS s) (hres : Residual (0 : Fin s) placeA (UstarR s) 1 Ur)
    (hβ : BetaRel (0 : Fin s) placeA (UstarR s) 1 β) (hq : 5 * aStar s + 4 ≤ q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) v)
        (digPoint q (s * k) (fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) w) :
          ℤ) :=
  Z3NetF.Proofs.D_sep_core (by omega) ψ k hk (0 : Fin s) placeA (placesOK (by omega)) (UstarF s) 1
    Ur β hres hβ alphaS (fun c => (Ustar_diag_core c).1) (fun n c hn => (Ustar_diag_core c).2 n hn)
    (fun c => (Ustar_dominant_core hs c).1.le) (fun c => (Ustar_dominant_core hs c).2) hq v w hvw

theorem A_sep_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (Apoint s q k v) (Apoint s q k w) : ℤ) := by
  have : NeZero q := ⟨by have := hq.1; omega⟩
  obtain ⟨ψ⟩ := (A_hom_core hs hq).1
  rw [Apoint_eq k ψ]
  exact A_sep_gen hs _ k hk _ _ (Ustar_data_core hs).1 (Ustar_data_core hs).2 hqa v w hvw

theorem A_sep_real_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hZ := A_sep_core s q k hs hq hqa hk v w hvw
  unfold torusDist2 at hZ
  have hR : (q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) - (aStar s : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 *
      ∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hsum : ∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (s * k)) ^ 2 = (∑ c, ((cres (q ^ (s * k))
        ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)) ^ 2) / ((q : ℝ) ^ (s * k)) ^ 2 := by
    rw [Finset.sum_div]; exact sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  exact sep_real_of_int (by omega) (by have := hq.1; omega) _ hR

theorem A_sep_eucl_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) := by
  refine (A_sep_real_core s q k hs hq hqa hk v w hvw).trans (Real.sqrt_le_sqrt ?_)
  refine Finset.sum_le_sum fun c _ => ?_
  have hq0 : 0 < q := by have := hq.1; omega
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set X := Apoint s q k
  have hc := Z3NetF.Proofs.Deficit.cres_le_abs (q ^ (s * k)) (pow_pos hq0 _)
    ((X v c : ℤ) - (X w c : ℤ))
  have hc0 : (0 : ℤ) ≤ (cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) := by positivity
  have hsq : ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ)) ^ 2 ≤
      ((X v c : ℤ) - (X w c : ℤ)) ^ 2 := by
    rw [← sq_abs ((X v c : ℤ) - _)]; exact pow_le_pow_left₀ hc0 hc 2
  have : (((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ)) ^ 2 ≤
      ((X v c : ℝ) - (X w c : ℝ)) ^ 2 := by exact_mod_cast hsq
  exact this

end

end Z3NetA.Proofs
