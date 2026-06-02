/-
LemoineHamiltonian.lean – Hamiltonien spectral pour l'instance SAT.
-/

import .LemoineSAT
import Kernel.SpectralLibrary

open SpectralLibrary

variable (n : ℕ) (hn : Odd n ∧ n > 5)

def Φ : SATInstance := lemoine_SAT n hn
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ :=
  if satisfies Φ σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H_lemoine : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H_lemoine :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)
