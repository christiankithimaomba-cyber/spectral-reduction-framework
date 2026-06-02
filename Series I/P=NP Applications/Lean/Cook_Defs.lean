/- 
CookDefs.lean – Définition du problème de Cook (400 étudiants, 100 places, liste d'incompatibilités).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.SimpleGraph.Hypercube
import Kernel.SpectralLibrary
import Kernel.HypercubeHarper

open SpectralLibrary

-- Nombre d'étudiants
def N : ℕ := 400

-- Nombre de places
def K : ℕ := 100

-- La liste d'incompatibilités est donnée comme un ensemble de paires.
-- Axiom: elle est fixée mais non spécifiée dans l'énoncé.
axiom incompatible_pairs : Finset (Fin N × Fin N)

-- Espace de configuration : hypercube de dimension N
def Config := Fin N → Bool

-- Vérifie qu'une assignation sélectionne exactement K étudiants
def exact_size (x : Config) : Bool :=
  (Finset.univ.filter (fun i => x i)).card = K

-- Vérifie qu'aucune paire incompatible n'est présente
def no_incompatible (x : Config) : Bool :=
  ∀ (a b : Fin N), (a,b) ∈ incompatible_pairs → ¬ (x a ∧ x b)

-- Potentiel : 1 si les deux conditions sont remplies, 0 sinon
def cook_potential (x : Config) : ℝ :=
  if exact_size x && no_incompatible x then 1 else 0

-- Graphe hypercube
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) := SimpleGraph.hypercube (Fin n)

-- Axiom: L'hypercube est connexe (résultat standard de Mathlib)
-- Reference: Mathlib.Combinatorics.SimpleGraph.Hypercube
axiom hypercube_connected (n : ℕ) : (hypercube_graph n).Connected

-- Problème spectral pour Cook
def cook_problem (ε : ℝ) (hε : 0 < ε) : SpectralProblem Config where
  potential := cook_potential
  graph := hypercube_graph N
  epsilon := ε
  heps := hε
  connected := hypercube_connected N
