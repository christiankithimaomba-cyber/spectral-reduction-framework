/-
FermatCatalanHamiltonian.lean – Hamiltonien spectral pour chaque triple d'exposants.
-/

import .FermatCatalanSAT
import Kernel.SpectralLibrary

open SpectralLibrary

variable (m n k : ℕ) (B : ℕ) (hB : B ≥ 1)

def Φ : SATInstance := fermat_catalan_SAT m n k B hB
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ :=
  if satisfies Φ σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H_fc : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H_fc :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)
