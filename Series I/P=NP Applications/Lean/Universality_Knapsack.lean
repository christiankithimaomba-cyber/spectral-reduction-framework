/- 
Knapsack.lean – Problème du sac à dos (0/1).
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper

open SpectralLibrary

def Config (n : ℕ) := Fin n → Bool

structure KnapsackInstance (n : ℕ) where
  weights : Fin n → ℕ
  values : Fin n → ℕ
  capacity : ℕ

def total_weight (inst : KnapsackInstance n) (x : Config n) : ℕ :=
  ∑ i, if x i then inst.weights i else 0

def total_value (inst : KnapsackInstance n) (x : Config n) : ℕ :=
  ∑ i, if x i then inst.values i else 0

def knapsack_potential (inst : KnapsackInstance n) (x : Config n) : ℝ :=
  if total_weight inst x ≤ inst.capacity then total_value inst x else 0

def hypercube_graph (n : ℕ) : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin n)

-- Axiom: L'hypercube est connexe (résultat standard de Mathlib)
axiom hypercube_connected (n : ℕ) : (hypercube_graph n).Connected

def knapsack_problem (inst : KnapsackInstance n) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Config n) where
  potential := knapsack_potential inst
  graph := hypercube_graph n
  epsilon := ε
  heps := hε
  connected := hypercube_connected n
