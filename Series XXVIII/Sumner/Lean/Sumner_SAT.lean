/-
SumnerSAT.lean – Convert the circuit to a 3‑SAT instance.
-/

import .SumnerCircuit
import Kernel.Tseitin

open Circuit

variable (n : ℕ) (hn : n < N0)

def sumner_SAT : SATInstance := tseitin (counterexample_circuit n hn)

theorem sumner_SAT_correct :
    Satisfiable (sumner_SAT n hn) ↔
    ∃ (T : Tournament (2*n - 2)) (F : OrientedTree n), is_counterexample n T F :=
  by
    rw [tseitin_correct]
    exact counterexample_circuit_correct n hn
