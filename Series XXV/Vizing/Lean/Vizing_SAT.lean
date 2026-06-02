/-
VizingSAT.lean – Convert Vizing circuit to 3‑SAT.
-/

import .CartesianProductCircuit
import Kernel.Tseitin

open Circuit

variable (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)] [DecidableRel G.Adj] [DecidableRel H.Adj]

def vizing_SAT : SATInstance :=
  tseitin (vizing_circuit G H)

theorem vizing_SAT_correct :
    Satisfiable (vizing_SAT G H) ↔
    ∃ D : Finset (V(G) × V(H)), dominates (cartesian_product G H) D ∧
      D.card < domination_number G * domination_number H :=
  by
    rw [tseitin_correct]
    exact vizing_circuit_correct G H
