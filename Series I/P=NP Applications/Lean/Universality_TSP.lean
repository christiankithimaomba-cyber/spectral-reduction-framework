/- 
TSP.lean – Problème du voyageur de commerce.
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

structure TSPInstance (n : ℕ) where
  dist : Fin n → Fin n → ℝ
  symm : ∀ i j, dist i j = dist j i
  diag_zero : ∀ i, dist i i = 0

def tour_cost (inst : TSPInstance n) (σ : Perm n) : ℝ :=
  ∑ i, inst.dist (σ i) (σ (i+1)) where i+1 := if i.val = n-1 then 0 else i+1

def tsp_potential (inst : TSPInstance n) (σ : Perm n) : ℝ :=
  - tour_cost inst σ   -- on maximise la valeur négative

def tsp_problem (inst : TSPInstance n) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Perm n) where
  potential := tsp_potential inst
  graph := permutation_graph n
  epsilon := ε
  heps := hε
  connected := permutation_graph_connected n
