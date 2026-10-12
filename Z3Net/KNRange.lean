module
public import Z3Net.KNRelax

@[expose] public section

/-!
# Step ranges of the per-prime certificates

`R_c = ⌈√T_p / p⌉` for full coordinates, `1` for skeleton coordinates.
-/

namespace Z3NetKN.Relax

/-- Step ranges for the `m ≡ 1` designs. -/
def rg1 : ℕ → Fin 3 → ℕ
  | 5 => ![2, 1, 1]
  | 7 => ![3, 1, 1]
  | 11 => ![5, 1, 1]
  | 13 => ![5, 1, 1]
  | 17 => ![6, 1, 1]
  | 19 => ![7, 1, 1]
  | 23 => ![8, 1, 1]
  | 29 => ![10, 1, 1]
  | 31 => ![10, 1, 1]
  | 37 => ![11, 1, 1]
  | 41 => ![12, 1, 1]
  | 43 => ![13, 1, 1]
  | 47 => ![14, 1, 1]
  | 53 => ![15, 1, 1]
  | 59 => ![16, 1, 1]
  | 61 => ![16, 1, 1]
  | 67 => ![17, 1, 1]
  | 71 => ![18, 1, 1]
  | 73 => ![18, 1, 1]
  | 79 => ![20, 1, 1]
  | _ => ![0, 0, 0]

/-- Relaxation data of the `m ≡ 1` design at `p`. -/
def cfg1 (p : ℕ) (R : Rows) : Design := ⟨p, 1, rg1 p, R⟩

/-- Step ranges for the `m ≡ 2` designs. -/
def rg2 : ℕ → Fin 3 → ℕ
  | 5 => ![1, 1, 1]
  | 7 => ![2, 2, 1]
  | 11 => ![2, 2, 1]
  | 13 => ![3, 3, 1]
  | 17 => ![3, 3, 1]
  | 19 => ![3, 3, 1]
  | 23 => ![3, 3, 1]
  | 29 => ![4, 4, 1]
  | 31 => ![4, 4, 1]
  | 37 => ![4, 4, 1]
  | 41 => ![4, 4, 1]
  | 43 => ![4, 4, 1]
  | 47 => ![4, 4, 1]
  | 53 => ![4, 4, 1]
  | 59 => ![4, 4, 1]
  | 61 => ![4, 4, 1]
  | 79 => ![5, 5, 1]
  | _ => ![0, 0, 0]

/-- Relaxation data of the `m ≡ 2` design at `p`. -/
def cfg2 (p : ℕ) (R : Rows) : Design := ⟨p, 2, rg2 p, R⟩

end Z3NetKN.Relax
