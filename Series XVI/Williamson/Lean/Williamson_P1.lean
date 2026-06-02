/- XVI_WilliamsonP1.lean - Pilier P1 : état fondamental unique strictement positif. -/

import XVI_WilliamsonSAT
import Kernel.SpectralLibrary

open Kernel.SpectralLibrary

namespace SeriesXVI.Williamson

variable (m : ℕ) (hm : m ≥ 1)

def Φ := Φ_m m
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ := if satisfies Φ σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)

/-- Théorème P1 : existence et unicité d’un état fondamental strictement positif. -/
theorem ground_state_unique_pos :
    ∃! ψ : Config → ℝ, (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧
      (H *ᵥ ψ = (λ_min H) • ψ) :=
  perron_frobenius H

end SeriesXVI.Williamson
