module
public import Z3Net.HalfCertDet

@[expose] public section

/-! # Entry Half: kernel check of the `126` box determinants of `(M5h, D5h)` (`decide +kernel`) -/

namespace Z3NetHL.Proofs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chkDet5_0 : chkDet5 0 = true := by decide +kernel
theorem chkDet5_1 : chkDet5 1 = true := by decide +kernel
theorem chkDet5_2 : chkDet5 2 = true := by decide +kernel
theorem chkDet5_3 : chkDet5 3 = true := by decide +kernel
theorem chkDet5_4 : chkDet5 4 = true := by decide +kernel
theorem chkDet5_5 : chkDet5 5 = true := by decide +kernel

theorem chkDet5_all : ∀ a ∈ List.range 6, chkDet5 a = true := by
  intro a ha
  simp only [List.mem_range] at ha
  interval_cases a
  · exact chkDet5_0
  · exact chkDet5_1
  · exact chkDet5_2
  · exact chkDet5_3
  · exact chkDet5_4
  · exact chkDet5_5

/-- No prime outside `S` divides a box determinant of `(M5h, D5h)`. -/
theorem half5_box_ndvd (p : ℕ) (hp : p.Prime)
    (hS : p ∉ ({2, 3, 5, 7, 11, 13, 17, 29, 41, 47, 257} : Finset ℕ)) (d : Fin 5 → ℕ)
    (hd : ∑ c, d c = 5) : ¬ (p : ℤ) ∣ (boxMatrix (halfIntGen M5h D5h) d).det := by
  intro h
  rw [Int.natCast_dvd] at h
  exact hS (prime_dvd_NS hp (h.trans (chkDet5_sound chkDet5_all d hd)))

end Z3NetHL.Proofs
