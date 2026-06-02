/- XXXV_Fuglede_Config.lean - Configuration de base pour la conjecture de Fuglede. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue
import Mathlib.Topology.MetricSpace.Basic

open Real

/-! ### Paramètres généraux -/

/-- Dimension de l'espace (1 ≤ d ≤ 4). -/
variable (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 4)

/-- Domaine Ω ⊂ ℝ^d : mesurable, borné, à bord Lipschitz. -/
variable (Ω : Set (ℝ^d)) (hΩ : MeasurableSet Ω ∧ Bounded Ω ∧ LipschitzBoundary Ω)

/-! ### Définitions de base -/

/-- La fonction indicatrice du pavage par translations. -/
def tiles (Λ : Set (ℝ^d)) : Prop :=
  IsLattice Λ ∧ (∀ x : ℝ^d, ∃! λ ∈ Λ, x ∈ Ω +ᵥ λ) ∧ (∀ λ1 λ2, λ1 ≠ λ2 → Disjoint (Ω +ᵥ λ1) (Ω +ᵥ λ2))

/-- Existence d'un pavage par un réseau (pas nécessairement spécifié). -/
def tiles_by_some_lattice : Prop := ∃ Λ, tiles Λ

/-- Ω est spectral : L^2(Ω) admet une base orthonormée d'exponentielles. -/
def spectral : Prop :=
  ∃ Λ : Set (ℝ^d), IsLattice Λ ∧ ∀ f : L^2 Ω, ∃! (c : Λ → ℂ),
    f = ∑ λ ∈ Λ, c λ • (exp (2 * π * I * ⟪λ, ·⟫) : L^2 Ω)

/-! ### Énoncé de la conjecture -/
def fuglede_conjecture : Prop := tiles_by_some_lattice Ω ↔ spectral Ω
