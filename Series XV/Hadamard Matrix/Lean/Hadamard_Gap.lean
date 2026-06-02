/- XV_HadamardGap.lean - Trou spectral constant via le lemme de Kithima Bridge. -/

import XV_HadamardConfig
import Kernel.KithimaBridge
import Kernel.HypercubeHarper

open Kernel.SpectralLibrary

namespace SeriesXV.Hadamard

theorem hadamard_spectral_gap (n : ℕ) :
    spectral_gap (hamiltonian n) ≥ 2 :=
  by
    let H := hamiltonian n
    let Δ := adjacency n
    let V := diagonal (potential n)
    -- Le trou spectral de l'hypercube (adjacence) est 2.
    have hΔ_gap : spectral_gap Δ = 2 :=
      HypercubeHarper.spectral_gap_adjacency (by simp [N]; exact Nat.one_le_pow n 2)
    -- Le potentiel est diagonal et non négatif.
    have hV_nonneg : ∀ σ, potential n σ ≥ 0 := by
      intro σ; rw [potential]; split_ifs <;> linarith
    -- Application du lemme de Kithima Bridge.
    exact kithima_bridge V (by simp [hV_nonneg]) Δ (by simp) 1 (by norm_num) (le_of_eq hΔ_gap)

end SeriesXV.Hadamard
