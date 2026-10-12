module
public import Mathlib
public import Z3Net.FDefs
public import Z3Net.NetBasic
public import Z3Net.SUFrame
public import Z3Net.SUBoxMinor

@[expose] public section

/-!
# Entry F, part 1: bridges and the row structure of box matrices

* `boxLoc_eq`, `boxMatrix_eq`: the entry-F copies agree with entry U's definitions.
* `pre d c = d_0 + … + d_{c-1}` (entry U's `Z3NetU.Proofs.pre`); row `pre d c + i` of the box
  matrix is row `i` of `C c` (`box_row_pre`), and every row is of this form (`box_row_cover`).
* `box_mul_right`, `box_map`: right multiplication and ring homomorphisms commute with taking box
  matrices.
* `digSum_div_prefix`: the quotient of a base-`q` digit sum by `q^(m-d)` is the digit sum of the
  first `d` digits.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

lemma boxLoc_eq : ∀ (ds : List ℕ) (c r : ℕ), Z3NetF.boxLoc ds c r = Z3NetU.boxLoc ds c r
  | [], _, _ => rfl
  | x :: xs, c, r => by simp only [Z3NetF.boxLoc, Z3NetU.boxLoc, boxLoc_eq xs]

lemma boxMatrix_eq {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) : Z3NetF.boxMatrix C d = Z3NetU.boxMatrix C d := by
  funext r l
  simp only [Z3NetF.boxMatrix, Z3NetU.boxMatrix, boxLoc_eq]

/-- Prefix sums `pre d c = d_0 + … + d_{c-1}`. -/
abbrev pre {s : ℕ} (d : Fin s → ℕ) (c : ℕ) : ℕ := Z3NetU.Proofs.pre d c

lemma le_of_sum {s m : ℕ} (d : Fin s → ℕ) (hd : ∑ c, d c = m) (c : Fin s) : d c ≤ m := by
  rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)

lemma pre_add_lt {s m : ℕ} (d : Fin s → ℕ) (hd : ∑ c, d c = m) (c : Fin s) (i : ℕ)
    (hi : i < d c) : pre d c + i < m := by
  have h1 := Z3NetU.Proofs.pre_succ d c
  have h2 := Z3NetU.Proofs.pre_le_sum d ((c : ℕ) + 1)
  rw [hd] at h2
  simp only [pre] at *
  omega

lemma boxLoc_pre {s : ℕ} (d : Fin s → ℕ) (c : Fin s) (i : ℕ) (hi : i < d c) :
    Z3NetF.boxLoc (List.ofFn d) 0 (pre d c + i) = ((c : ℕ), i) := by
  rw [boxLoc_eq]
  have hlen : (c : ℕ) < (List.ofFn d).length := by simp
  have hget : (List.ofFn d)[(c : ℕ)] = d c := by simp
  have := Z3NetU.Proofs.boxLoc_spec (List.ofFn d) 0 c i hlen (by rw [hget]; exact hi)
  simpa [pre, Z3NetU.Proofs.pre] using this

lemma box_row_pre {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (c : Fin s) (i : ℕ) (hi : i < d c) :
    Z3NetF.boxMatrix C d ⟨pre d c + i, pre_add_lt d hd c i hi⟩ =
      C c ⟨i, lt_of_lt_of_le hi (le_of_sum d hd c)⟩ := by
  funext l
  have hloc := boxLoc_pre d c i hi
  simp only [Z3NetF.boxMatrix, hloc]
  rw [dite_cond_eq_true (eq_true ⟨c.isLt, lt_of_lt_of_le hi (le_of_sum d hd c)⟩)]

lemma box_row_cover {s m : ℕ} (d : Fin s → ℕ) (hd : ∑ c, d c = m) (r : Fin m) :
    ∃ c : Fin s, ∃ i : ℕ, ∃ hi : i < d c, (r : ℕ) = pre d c + i ∧
      Z3NetF.boxLoc (List.ofFn d) 0 r = ((c : ℕ), i) := by
  obtain ⟨c, h1, h2, h3⟩ := Z3NetU.Proofs.loc_spec d hd r
  refine ⟨c, _, h3, h1, ?_⟩
  rw [boxLoc_eq]
  ext
  · exact h2
  · rfl

lemma box_row_get {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (r : Fin m) :
    ∃ c : Fin s, ∃ i : ℕ, ∃ hi : i < d c, (r : ℕ) = pre d c + i ∧
      Z3NetF.boxMatrix C d r = C c ⟨i, lt_of_lt_of_le hi (le_of_sum d hd c)⟩ := by
  obtain ⟨c, i, hi, hr, _⟩ := box_row_cover d hd r
  refine ⟨c, i, hi, hr, ?_⟩
  have : r = ⟨pre d c + i, pre_add_lt d hd c i hi⟩ := Fin.ext hr
  rw [this, box_row_pre C d hd c i hi]

lemma box_mul_right {R : Type*} [CommRing R] {s m : ℕ}
    (C : Fin s → Matrix (Fin m) (Fin m) R) (M : Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) :
    Z3NetF.boxMatrix (fun c => C c * M) d = Z3NetF.boxMatrix C d * M := by
  ext r j
  simp only [Z3NetF.boxMatrix, mul_apply]
  split_ifs <;> simp

lemma box_map {R S : Type*} [CommRing R] [CommRing S] {s m : ℕ} (f : R →+* S)
    (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) :
    Z3NetF.boxMatrix (fun c => (C c).map f) d = (Z3NetF.boxMatrix C d).map f := by
  ext r j
  simp only [Z3NetF.boxMatrix, map_apply]
  split_ifs <;> simp

/-! ## Digit sums -/

lemma digSum_div_prefix (q : ℕ) (hq : 0 < q) : ∀ (m : ℕ) (f : Fin m → ℕ), (∀ j, f j < q) →
    ∀ d (hd : d ≤ m), Z3Net.Proofs.digSum q m f / q ^ (m - d) =
      Z3Net.Proofs.digSum q d (fun j => f ⟨j, lt_of_lt_of_le j.isLt hd⟩) := by
  intro m
  induction m with
  | zero =>
    intro f _ d hd
    obtain rfl : d = 0 := by omega
    simp [Z3Net.Proofs.digSum]
  | succ m ih =>
    intro f hf d hd
    by_cases hdm : d = m + 1
    · subst hdm
      simp only [Nat.sub_self, pow_zero, Nat.div_one]
    · have hd' : d ≤ m := by omega
      rw [Z3Net.Proofs.digSum_succ]
      have hr := hf (Fin.last m)
      rw [show m + 1 - d = (m - d) + 1 by omega, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.mul_add_div hq, Nat.div_eq_of_lt hr, add_zero]
      rw [ih (fun j => f j.castSucc) (fun j => hf _) d hd']
      rfl

lemma digSum_inj (q : ℕ) (hq : 0 < q) (m : ℕ) (f g : Fin m → ℕ) (hf : ∀ j, f j < q)
    (hg : ∀ j, g j < q) (h : Z3Net.Proofs.digSum q m f = Z3Net.Proofs.digSum q m g) : f = g := by
  funext j
  exact Z3Net.Proofs.digSum_div_inj q hq m f g hf hg 0 (by simpa using h) j (by simp)

end

end Z3NetF.Proofs
