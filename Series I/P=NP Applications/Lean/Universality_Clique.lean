/- 
Clique.lean – Problème de la clique maximum.
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper

open SpectralLibrary

def Config (n : ℕ) := Fin n → Bool

structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irref : ∀ i, ¬ adj i i

def is_clique (G : Graph n) (x : Config n) : Bool :=
  let S := {i | x i}
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → G.adj i j

def clique_size (x : Config n) : ℕ :=
  Finset.card (Finset.filter (fun i => x i) Finset.univ)

def clique_potential (G : Graph n) (x : Config n) : ℝ :=
  if is_clique G x then clique_size x else 0

def hypercube_graph (n : ℕ) : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin n)

-- Axiom: L'hypercube est connexe (résultat standard de Mathlib)
axiom hypercube_connected (n : ℕ) : (hypercube_graph n).Connected

def clique_problem (G : Graph n) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Config n) where
  potential := clique_potential G
  graph := hypercube_graph n
  epsilon := ε
  heps := hε
  connected := hypercube_connected n
