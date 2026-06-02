/- XX_PollockOctaHamiltonian.lean - Hamiltonien spectral et quatre piliers. -/

import XX_PollockOctaSAT
import Kernel.SpectralLibrary
import Kernel.KithimaBridge
import Kernel.MPSAreaLaw
import Kernel.DRSP

open SpectralLibrary

variable (N : ℕ) (hN : N ≤ N0)

def Φ := Φ_N N
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ := if satisfies Φ σ then 0 else M^2
def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)
def H : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)

theorem ground_state_unique_pos :
    ∃! ψ : Config → ℝ, (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧ (H *ᵥ ψ = (λ_min H) • ψ) :=
  perron_frobenius H

theorem spectral_gap_constant : spectral_gap H ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V, M]) Δ (by simp) 1 (by norm_num) (hypercube_spectral_gap M)

theorem area_law : ∃ C, ∀ B, entanglement_entropy (ground_state H) B ≤ C * Real.log M :=
  area_law_for_hypercube (spectral_gap_constant)

theorem drsp_correct : ∀ σ, satisfies Φ σ ↔ drsp_solver H = some σ :=
  drsp_correct H
