/- XVII_MaxDetConfig.lean - Espace de configuration, potentiel, hamiltonien pour le déterminant maximal. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Hypercube
import Kernel.SpectralLibrary

open Matrix

namespace SeriesXVII.MaxDet

variable (n : ℕ) (hn : n ≥ 1)

/-- Configuration : matrice n×n d’entrées booléennes (0 pour -1, 1 pour +1). -/
def Config := Fin n → Fin n → Bool

/-- Nombre total de bits. -/
def N := n^2

/-- Graphe sous-jacent : hypercube de dimension N (connexe, degré N). -/
def graph : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin N)

lemma graph_connected : graph.Connected := SimpleGraph.hypercube_connected _

/-- Valeur du déterminant (entier relatif). -/
def determinant (σ : Config n) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j => if σ i j then 1 else -1)
  det M

/-- Potentiel diagonal : 0 pour une matrice ayant |det| ≥ k, N² sinon.
    Nous paramétrons par k (seuil). -/
def potential (k : ℤ) (σ : Config n) : ℝ :=
  if |determinant σ| ≥ k then 0 else (N : ℝ)^2

/-- Matrice d’adjacence de l’hypercube. -/
def adjacency : Matrix (Config n) (Config n) ℝ := adjacencyMatrixOf graph

/-- Hamiltonien spectral H = V + Δ. -/
def hamiltonian (k : ℤ) : Matrix (Config n) (Config n) ℝ :=
  diagonal (potential k) + adjacency

/-- Instance de SpectralProblem pour utiliser le kernel. -/
def spectral_problem (k : ℤ) : Kernel.SpectralLibrary.SpectralProblem (Config n) :=
  { potential := potential k
    graph := graph
    epsilon := 1
    heps := by norm_num
    connected := graph_connected }

end SeriesXVII.MaxDet
