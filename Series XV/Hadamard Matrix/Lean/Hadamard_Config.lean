/- XV_HadamardConfig.lean - Espace de configuration, potentiel, hamiltonien pour la conjecture de Hadamard (série XV). -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Hypercube
import Kernel.SpectralLibrary

open Matrix

namespace SeriesXV.Hadamard

variable (n : ℕ)

/-- L'ensemble des configurations : matrices n×n à entrées booléennes (0 pour -1, 1 pour +1). -/
def Config := Fin n → Fin n → Bool

/-- Nombre total de bits. -/
def N := n^2

/-- Le graphe sous-jacent est l'hypercube de dimension N (connexe, degré N). -/
def graph : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin N)

lemma graph_connected : graph.Connected := SimpleGraph.hypercube_connected _

/-- Prédicat "être une matrice de Hadamard". -/
def is_hadamard (σ : Config n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (∑ k : Fin n, ((σ i k).toNat * 2 - 1) * ((σ j k).toNat * 2 - 1)) = 0

/-- Décidabilité de is_hadamard (car c'est une quantification finie sur des entiers). -/
instance is_hadamard_decidable : Decidable (is_hadamard σ) :=
  decidable_of_iff' (by infer_instance) Iff.rfl

/-- Potentiel diagonal : 0 pour une matrice de Hadamard, N² sinon. -/
def potential (σ : Config n) : ℝ :=
  if is_hadamard σ then 0 else (N : ℝ)^2

/-- Matrice d'adjacence de l'hypercube. -/
def adjacency : Matrix (Config n) (Config n) ℝ :=
  adjacencyMatrixOf graph

/-- Hamiltonien spectral H = V + Δ. -/
def hamiltonian : Matrix (Config n) (Config n) ℝ :=
  diagonal potential + adjacency

/-- Instance de SpectralProblem pour utiliser les théorèmes du kernel. -/
def spectral_problem : Kernel.SpectralLibrary.SpectralProblem (Config n) :=
  { potential := potential
    graph := graph
    epsilon := 1
    heps := by norm_num
    connected := graph_connected }

end SeriesXV.Hadamard
