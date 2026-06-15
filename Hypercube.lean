/- 
Article1_Hypercube.lean – Example usage of the spectral kernel.
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper
import Kernel.DiscreteCheeger

open SpectralLibrary SimpleGraph

variable {n : ℕ}

-- On utilise directement le type Config du kernel (Fin n → Bool)
def hypercube_graph (n : ℕ) : SimpleGraph (Config n) := SimpleGraph.hypercube (Fin n)

structure SATInstance (n : ℕ) where
  clauses : List (List (Fin n × Bool))

def eval_clause (x : Config n) (c : List (Fin n × Bool)) : Bool :=
  c.any fun (p : Fin n × Bool) => let (i, pos) := p; if pos then x i else not (x i)

def satisfies (inst : SATInstance n) (x : Config n) : Bool :=
  inst.clauses.all (eval_clause x)

def sat_potential (inst : SATInstance n) (x : Config n) : ℝ :=
  if satisfies inst x then 0 else n^2   -- potentiel profond sur les non‑solutions (P4)

def hypercube_problem (inst : SATInstance n) : SpectralProblem (Config n) where
  potential := sat_potential inst
  graph := hypercube_graph n
  epsilon := 1
  heps := by norm_num
  connected := SimpleGraph.hypercube_connected n

-- Le théorème de Perron‑Frobenius donne un état fondamental unique et strictement positif.
theorem hypercube_p1 (inst : SATInstance n) :
    ∃! ψ : Config n → ℝ,
      (∀ x, ψ x > 0) ∧
      (∃ λ, (Hamiltonian (hypercube_problem inst)).mulVec ψ = λ • ψ ∧
            λ = (spectrum (Hamiltonian (hypercube_problem inst))).min) ∧
      (∑ x, (ψ x) ^ 2 = 1) :=
  perron_frobenius (hypercube_problem inst)
