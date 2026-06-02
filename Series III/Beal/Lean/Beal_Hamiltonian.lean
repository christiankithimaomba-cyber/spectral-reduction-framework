/-
BealHamiltonian.lean – Hamiltonien spectral pour l'instance SAT de Beal.
-/

import .BealSAT
import Kernel.SpectralLibrary

open SpectralLibrary

def M : ℕ := (beal_SAT).numVars
def Config := Fin M → Bool

def V_potential (σ : Config) : ℝ :=
  if satisfies beal_SAT σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H_beal : Matrix Config Config ℝ := diagonal V_potential + Δ

lemma H_beal_irreducible : Irreducible H_beal :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)

/-- État fondamental unique positif. -/
noncomputable def ψ0 : Config → ℝ :=
  ground_state (mk_spectral_problem H_beal)
