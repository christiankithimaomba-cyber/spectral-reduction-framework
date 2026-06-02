/- 
GraphIsomorphism.lean – Problème de l’isomorphisme de graphes.
-/

import Kernel.SpectralLibrary
import Mathlib.GroupTheory.Perm.Basic

open SpectralLibrary

def Perm (n : ℕ) := Equiv.Perm (Fin n)

def permutation_graph (n : ℕ) : SimpleGraph (Perm n) :=
  let gen := List.map (fun i => Equiv.swap i (i+1)) (List.range (n-1))
  CayleyGraph (Perm n) gen

-- Axiom: Le graphe des transpositions adjacentes est connexe
axiom permutation_graph_connected (n : ℕ) : (permutation_graph n).Connected

structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irref : ∀ i, ¬ adj i i

def is_isomorphism (G1 G2 : Graph n) (σ : Perm n) : Bool :=
  ∀ i j, G1.adj i j ↔ G2.adj (σ i) (σ j)

def isomorphism_potential (G1 G2 : Graph n) (σ : Perm n) : ℝ :=
  if is_isomorphism G1 G2 σ then 1 else 0

def isomorphism_problem (G1 G2 : Graph n) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Perm n) where
  potential := isomorphism_potential G1 G2
  graph := permutation_graph n
  epsilon := ε
  heps := hε
  connected := permutation_graph_connected n
