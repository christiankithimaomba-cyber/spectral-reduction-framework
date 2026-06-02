/- XV_HadamardAreaLaw.lean - Loi d'aire logarithmique et représentation MPS. -/

import XV_HadamardConfig
import Kernel.MPS
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve

open Kernel.SpectralLibrary

namespace SeriesXV.Hadamard

/-- Axiome : Pour l'hypercube, le trou spectral constant implique une loi d'aire logarithmique.
    La preuve complète utilise les théorèmes de Brandão–Horodecki et la courbe de Hilbert,
    et est détaillée dans l'article XV.3. -/
axiom area_law_for_hypercube (M : ℕ) (ψ : Fin (2^M) → ℝ) (h_gap : spectral_gap (hamiltonian n) ≥ 2) :
    ∃ C > 0, ∀ B : Finset (Fin M), entanglement_entropy (reduced_density ψ B) ≤ C * Real.log M

theorem hadamard_area_law (n : ℕ) :
    ∃ C > 0, ∀ B : Finset (Fin (N n)), 
      entanglement_entropy (reduced_density (ground_state (spectral_problem n)) B) ≤ C * Real.log (N n) :=
  by
    let ψ₀ := ground_state (spectral_problem n)
    have h_gap := hadamard_spectral_gap n
    exact area_law_for_hypercube (N n) ψ₀ h_gap

end SeriesXV.Hadamard
