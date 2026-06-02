/- XXXV_Fuglede_Criteria.lean - Critères spectraux pour tiling et spectrality. -/

import XXXV_Fuglede_Operator
import Mathlib.MeasureTheory.Measure.Spectral

open SpectralMeasure

variable {d : ℕ} (hd : 1 ≤ d ∧ d ≤ 4) (Ω : Set ℝ^d) (hΩ : MeasurableSet Ω ∧ Bounded Ω ∧ LipschitzBoundary Ω)

/-- Mesure spectrale jointe du tuple (U_Ω^{(1)},...,U_Ω^{(d)}). -/
def E : SpectralMeasure (ℝ^d) (L^2 Ω) := joint_spectral_measure (U_Ω)

/-! ### Critère de pavage -/

/-- Condition : le spectre est un réseau. -/
def lattice_spectrum : Prop := IsLattice (support E) ∧ ∀ x ∈ support E, (E {x}).rank = 1

/-- Équivalence : Ω pave ℝ^d (par un réseau) ssi le spectre est un réseau. -/
axiom tiling_iff_lattice_spectrum : (∃ Λ, tiles Ω Λ) ↔ lattice_spectrum

/-! ### Critère de spectralité -/

/-- Condition : la mesure spectrale E est purement ponctuelle. -/
def purely_point_spectrum : Prop := E.is_purely_point

/-- Équivalence : Ω est spectral ssi le spectre est purement ponctuel. -/
axiom spectral_iff_pure_point : spectral Ω ↔ purely_point_spectrum

/-! ### Corollaire pour la conjecture -/

theorem fuglede_equivalence :
    fuglede_conjecture Ω ↔ (lattice_spectrum ↔ purely_point_spectrum) :=
  by
    rw [fuglede_conjecture, tiling_iff_lattice_spectrum, spectral_iff_pure_point]
    rfl
