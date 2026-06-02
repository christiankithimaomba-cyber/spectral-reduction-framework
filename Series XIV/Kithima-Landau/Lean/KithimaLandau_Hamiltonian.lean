/-
KithimaLandauHamiltonian.lean – Hamiltonien spectral pour l'instance SAT.
-/

import .KithimaLandauSAT
import Kernel.SpectralLibrary

open SpectralLibrary

variable (n : ℕ) (hn : Even n ∧ n > 4)

def Φ : SATInstance := kithima_landau_SAT n hn
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ :=
  if satisfies Φ σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H_kl : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H_kl :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)
