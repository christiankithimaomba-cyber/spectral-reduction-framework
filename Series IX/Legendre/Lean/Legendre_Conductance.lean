/- 
LegendreConductance.lean – Borne polynomiale sur la conductance et le trou spectral.
-/

import .LegendreConfig
import Kernel.DiscreteCheeger

open Kernel.SpectralLibrary

theorem legendre_conductance (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) :
    let H := LegendreHamiltonian n λ ε hε
    conductance H ≥ ε / (4 * n) := by
  let ψ := ground_state (LegendreSpectralProblem n λ ε hε)
  have hψ := perron_frobenius (LegendreSpectralProblem n λ ε hε)
  obtain ⟨_, hpos, hλ, hnorm, _⟩ := hψ
  have h_width := Kernel.DiscreteCheeger.path_topological_width (2*n+1) ε hε ψ hpos hnorm
  exact conductance_from_topological_width H ψ h_width (by simp [LegendreHamiltonian])

theorem legendre_spectral_gap (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) :
    let H := LegendreHamiltonian n λ ε hε
    spectral_gap H ≥ ε^2 / (32 * n^2) := by
  let H0 := LegendreHamiltonian n λ ε hε
  have h_cond := legendre_conductance n λ ε hε
  have h_offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ H0 i j := by
    intro i j h; simp [LegendreHamiltonian, adjacencyMatrixOf]; split_ifs <;> linarith
  exact Kernel.DiscreteCheeger.Cheeger_inequality H0 h_offdiag_nonneg h_cond
