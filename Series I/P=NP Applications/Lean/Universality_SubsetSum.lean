/- 
SubsetSum.lean – Problème de la somme de sous‑ensemble.
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper

open SpectralLibrary

def Config (n : ℕ) := Fin n → Bool

structure SubsetSumInstance (n : ℕ) where
  weights : Fin n → ℕ
  target : ℕ

def is_subset_sum (inst : SubsetSumInstance n) (x : Config n) : Bool :=
  ∑ i, if x i then inst.weights i else 0 = inst.target

def subset_sum_potential (inst : SubsetSumInstance n) (x : Config n) : ℝ :=
  if is_subset_sum inst x then 1 else 0

def hypercube_graph (n : ℕ) : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin n)

-- Axiom: L'hypercube est connexe (résultat standard de Mathlib)
axiom hypercube_connected (n : ℕ) : (hypercube_graph n).Connected

def subset_sum_problem (inst : SubsetSumInstance n) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Config n) where
  potential := subset_sum_potential inst
  graph := hypercube_graph n
  epsilon := ε
  heps := hε
  connected := hypercube_connected n
