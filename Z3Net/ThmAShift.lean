/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAThm
public import Z3Net.FSepShift2
public import Z3Net.DGSDefs

@[expose] public section

/-!
# V14 stage S10′: `thm:A` under digital shifts (`prop:shift`)

`Apoint` is the digital point set of `AGen` (`Apoint_eq_AGen`); every digital shift of it is again a
`(0,sk,s)`-net with one point in every cell (`A_net_shift_core`, `lem:shift`) and covering radius
`≤ √s N^(-1/s)`, and the lower bound of `thm:A`(2) holds for every shift (`A_sep_shift_core` and its
real and Euclidean forms), through `prop:D` for shifted nets (`Z3NetF.Proofs.D_sep_shift_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

noncomputable section

variable {s : ℕ} [NeZero s]

lemma AGen_eq {q : ℕ} (k : ℕ) (ψ : RS s →+* ZMod q) :
    AGen s q k = fun c => (PGen k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c).map ψ := by
  unfold AGen
  rw [dif_pos ⟨ψ⟩, hom_unique (Classical.choice _) ψ]

/-- `Apoint` is the digital point set with the generator matrices `AGen`. -/
theorem Apoint_eq_AGen (s q k : ℕ) [NeZero s] : Apoint s q k = digPoint q (s * k) (AGen s q k) := by
  by_cases h : Nonempty (RS s →+* ZMod q)
  · obtain ⟨ψ⟩ := h
    rw [Apoint_eq k ψ, AGen_eq k ψ]
  · funext v c
    unfold Apoint AGen
    rw [dif_neg h, dif_neg h]
    simp [digPoint, coord]

theorem A_net_shift_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (τ : Fin s → Fin (s * k) → ZMod q) :
    IsNet0 s q (s * k) (digPointShift q (s * k) (AGen s q k) τ) := by
  have : NeZero q := ⟨by have := hq.1; omega⟩
  have h := A_net_core s q k hs hq
  rw [Apoint_eq_AGen] at h
  exact Z3NetF.Proofs.digPointShift_net _ τ h

theorem A_covering_shift_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (τ : Fin s → Fin (s * k) → ZMod q) (x : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (s * k) → ZMod q,
      ∑ c, (x c - (digPointShift q (s * k) (AGen s q k) τ v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤
        (s : ℝ) / ((q : ℝ) ^ k) ^ 2 :=
  covering_of_net_core (by omega) hq.1 _ (A_net_shift_core s q k hs hq τ) x hx

theorem A_sep_shift_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (digPointShift q (s * k) (AGen s q k) τ v)
        (digPointShift q (s * k) (AGen s q k) τ w) : ℤ) := by
  have : NeZero q := ⟨by have := hq.1; omega⟩
  obtain ⟨ψ⟩ := (A_hom_core hs hq).1
  rw [AGen_eq k ψ]
  exact Z3NetF.Proofs.D_sep_shift_core (by omega) ψ hk (0 : Fin s) placeA (placesOK (by omega))
    (UstarF s) 1 (UrS s) (betaS s) (Ustar_data_core hs).1 (Ustar_data_core hs).2 alphaS
    (fun c => (Ustar_diag_core c).1) (fun n c hn => (Ustar_diag_core c).2 n hn)
    (fun c => (Ustar_dominant_core hs c).1.le) (fun c => (Ustar_dominant_core hs c).2) hqa τ v w hvw

theorem A_sep_shift_real_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
          (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  set X := digPointShift q (s * k) (AGen s q k) τ
  have hZ := A_sep_shift_core s q k hs hq hqa hk τ v w hvw
  unfold torusDist2 at hZ
  have hR : (q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) - (aStar s : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 *
      ∑ c, ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hsum : ∑ c, ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (s * k)) ^ 2 = (∑ c, ((cres (q ^ (s * k))
        ((X v c : ℤ) - (X w c : ℤ)) : ℝ)) ^ 2) / ((q : ℝ) ^ (s * k)) ^ 2 := by
    rw [Finset.sum_div]; exact sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  exact sep_real_of_int (by omega) (by have := hq.1; omega) _ hR

theorem A_sep_shift_eucl_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2) := by
  refine (A_sep_shift_real_core s q k hs hq hqa hk τ v w hvw).trans (Real.sqrt_le_sqrt ?_)
  refine Finset.sum_le_sum fun c _ => ?_
  have hq0 : 0 < q := by have := hq.1; omega
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set X := digPointShift q (s * k) (AGen s q k) τ
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
