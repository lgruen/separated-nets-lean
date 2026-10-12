module
public import Z3Net.KNNetGauge
public import Z3Net.KNNetWin1

@[expose] public section

/-!
# Shape data of the KN designs (KN entry, `KN1_net` / `KN2_net`)

For `m = 3k + r`, `r ∈ {1, 2}`: a coordinate `c < r` is *full* (one geometric row, its jitter row),
a coordinate `c ≥ r` is a *skeleton* coordinate (skeleton row and jitter row).  `PF r d` is the
number of geometric rows of the other coordinates (the pivot count of the cell of `d`), `rwF r d`
enumerates them, `geoRow r R c ρ` is the designed row `ρ` of `c`, `Tgt` its value in `ZMod p`.
-/

namespace Z3NetKN.NetKN

open Matrix Z3NetKN.Realize Z3NetKN.Gauge Z3NetKN.Frame

/-- Number of geometric rows of coordinate `c`. -/
def gF (r : ℕ) (c : Fin 3) : ℕ := if (c : ℕ) < r then 1 else 2

/-- Pivot count of the cell of `d`. -/
def PF (r : ℕ) (d : Fin 3) : ℕ :=
  (if d = 0 then 0 else gF r 0) + (if d = 1 then 0 else gF r 1) + (if d = 2 then 0 else gF r 2)

/-- The geometric rows of the coordinates `c ≠ d`, in order. -/
def rwList (r : ℕ) (d : Fin 3) : List (Fin 3 × ℕ) :=
  (List.finRange 3).flatMap fun c => if c = d then [] else (List.range (gF r c)).map fun ρ => (c, ρ)

def rwF (r : ℕ) (d : Fin 3) (a : ℕ) : Fin 3 × ℕ := (rwList r d).getD a (0, 0)

/-- The designed geometric row `ρ` of `c`. -/
def geoRow (r : ℕ) (R : Rows) (c : Fin 3) (ρ : ℕ) : Fin 3 → Fin 4 → ℤ :=
  if (c : ℕ) < r then R.jt c else if ρ = 0 then R.sk c else R.jt c

/-- Target values in `ZMod p`. -/
def Tgt (r p : ℕ) (R : Rows) (c d : Fin 3) (ρ i : ℕ) : ZMod p :=
  ((if h : i < 4 then geoRow r R c ρ d ⟨i, h⟩ else 0 : ℤ) : ZMod p)

lemma layout_ok (r : ℕ) (hr : r = 1 ∨ r = 2) :
    (∀ d, 1 ≤ PF r d) ∧ (∀ d, PF r d ≤ 4) ∧ (∀ c, gF r c ≤ 2) ∧
    (∀ d (a : Fin 4), (a : ℕ) < PF r d → (rwF r d a).1 ≠ d ∧ (rwF r d a).2 < gF r (rwF r d a).1) ∧
    (∀ d c (ρ : Fin 2), c ≠ d → (ρ : ℕ) < gF r c → ∃ a : Fin 4, (a : ℕ) < PF r d ∧ rwF r d a = (c, (ρ : ℕ))) := by
  rcases hr with rfl | rfl <;> decide

/-- The setup for `m = 3k + r`. -/
def setup (r k : ℕ) (hr : r = 1 ∨ r = 2) (hk : 4 ≤ k + r) : Setup (3 * k + r) where
  K := depth r k
  hK := depth_sum r k (by omega)
  g := gF r
  P := PF r
  rw := rwF r
  hP1 := (layout_ok r hr).1
  hP4 := (layout_ok r hr).2.1
  hPK := by
    intro d
    rcases hr with rfl | rfl <;> fin_cases d <;> simp [PF, gF, depth] <;> omega
  hg := (layout_ok r hr).2.2.1
  hbox := by
    intro d
    rcases hr with rfl | rfl <;> fin_cases d <;> simp [PF, gF, depth] <;> omega
  hrw := by
    intro d a ha
    exact (layout_ok r hr).2.2.2.1 d ⟨a, by have := (layout_ok r hr).2.1 d; omega⟩ ha
  hrw_surj := by
    intro d c ρ hc hρ
    obtain ⟨a, ha, h⟩ := (layout_ok r hr).2.2.2.2 d c ⟨ρ, by have := (layout_ok r hr).2.2.1 c; omega⟩
      hc hρ
    exact ⟨a, ha, h⟩

/-- The constant canonical window. -/
def Can (r : ℕ) {F : Type*} [CommRing F] : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  if r = 1 then Can1 else Can2

/-- Certificate data for one design. -/
structure Cert (p : ℕ) where
  L : Fin 3 → Fin 2 → Fin 2 → ZMod p
  U : Fin 3 → Fin 3 → Fin 3 → ZMod p
  μ : Fin 3 → Fin 3 → ZMod p
  Ti : Fin 3 → Fin 4 → Fin 4 → ZMod p

/-- The gauge matrices of a certificate. -/
def Cert.Lm {p : ℕ} (X : Cert p) (c : Fin 3) : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.of (X.L c)
def Cert.Um {p : ℕ} (X : Cert p) (d : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod p) := Matrix.of (X.U d)
def Cert.Tim {p : ℕ} (X : Cert p) (d : Fin 3) : Matrix (Fin 4) (Fin 4) (ZMod p) := Matrix.of (X.Ti d)

/-- The padded target pivot block (`Tpad` of `KNNetReal`, with the layout of `setup`). -/
def TpadF (r p : ℕ) (R : Rows) (d : Fin 3) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  fun a i => if (a : ℕ) < PF r d ∧ (i : ℕ) < PF r d then
    Tgt r p R (rwF r d a).1 d (rwF r d a).2 i else if a = i then 1 else 0

/-- Entry of the transformed canonical window (a plain function, for decidability). -/
def actE (r p : ℕ) (X : Cert p) (c d : Fin 3) (ρ : Fin 2) (i : Fin 3) : ZMod p :=
  act X.Lm X.Um X.μ (Can r) c d ρ i

/-- Entry of `TpadF * Ti`. -/
def tiE (r p : ℕ) (R : Rows) (X : Cert p) (d : Fin 3) (a b : Fin 4) : ZMod p :=
  (TpadF r p R d * X.Tim d) a b

/-- The finite conditions checked per design. -/
def CertOK (r p : ℕ) (R : Rows) (X : Cert p) : Prop :=
  (∀ c : Fin 3, X.L c 0 1 = 0) ∧
  (∀ (c : Fin 3) (a : Fin 2), (a : ℕ) < gF r c → X.L c a a ≠ 0) ∧
  (∀ (d a b : Fin 3), b < a → X.U d a b = 0) ∧
  (∀ (d a : Fin 3), (a : ℕ) + 1 < PF r d → X.U d a a ≠ 0) ∧
  (∀ c d : Fin 3, c ≠ d → X.μ c d ≠ 0) ∧
  (∀ c d : Fin 3, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < gF r c → (i : ℕ) + 1 < PF r d →
    actE r p X c d ρ i = Tgt r p R c d ρ i) ∧
  (∀ (d : Fin 3) (a b : Fin 4), tiE r p R X d a b = if a = b then 1 else 0) ∧
  (∀ c d : Fin 3, c ≠ d → ∀ ρ : Fin 2, (ρ : ℕ) < gF r c → ∀ i : Fin 4, PF r d ≤ (i : ℕ) →
    (i : ℕ) < win r d → geoRow r R c ρ d i = 0)

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
instance (r p : ℕ) (R : Rows) (X : Cert p) : Decidable (CertOK r p R X) := by
  unfold CertOK; infer_instance

end Z3NetKN.NetKN
