/- 
Article1_Hypercube.lean – Example usage of the spectral kernel.
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper
import Kernel.DiscreteCheeger

open SpectralLibrary SimpleGraph

variable {n : ℕ}

def ConfigSpace (n : ℕ) := Fin n → Bool

def hypercube_graph (n : ℕ) : SimpleGraph (ConfigSpace n) := SimpleGraph.hypercube (Fin n)

structure SATInstance (n : ℕ) where
  clauses : List (List (Fin n × Bool))

def eval_clause (x : ConfigSpace n) (c : List (Fin n × Bool)) : Bool :=
  c.any fun (p : Fin n × Bool) => let (i, pos) := p; if pos then x i else not (x i)

def satisfies (inst : SATInstance n) (x : ConfigSpace n) : Prop :=
  inst.clauses.all (eval_clause x)

def sat_potential (inst : SATInstance n) (x : ConfigSpace n) : ℝ :=
  if satisfies inst x then 1 else 0

def hypercube_problem (inst : SATInstance n) : SpectralProblem (ConfigSpace n) where
  potential := sat_potential inst
  graph := hypercube_graph n
  epsilon := 1
  heps := by norm_num
  connected := SimpleGraph.hypercube_connected n

-- The Perron‑Frobenius theorem gives a unique positive ground state.
theorem hypercube_p1 (inst : SATInstance n) :
    ∃! ψ : ConfigSpace n → ℝ,
      (∀ x, ψ x > 0) ∧
      (∃ λ, (SpectralLibrary.Hamiltonian (hypercube_problem inst)).mulVec ψ = λ • ψ ∧
            λ = (spectrum (SpectralLibrary.Hamiltonian (hypercube_problem inst))).min) ∧
      (∑ x, (ψ x) ^ 2 = 1) :=
  SpectralLibrary.perron_frobenius (hypercube_problem inst)
