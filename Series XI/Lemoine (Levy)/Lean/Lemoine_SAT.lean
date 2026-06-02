/-
LemoineSAT.lean – Réduction à 3‑SAT via Tseitin.
-/

import .LemoineCircuit
import Kernel.Tseitin

open Circuit

def lemoine_SAT (n : ℕ) (hn : Odd n ∧ n > 5) : SATInstance :=
  tseitin (lemoine_circuit n hn)

theorem lemoine_SAT_correct (n : ℕ) (hn : Odd n ∧ n > 5) :
    Satisfiable (lemoine_SAT n hn) ↔
    ∃ p q : ℕ, Prime p ∧ Prime q ∧ p + 2*q = n :=
  by
    rw [tseitin_correct (lemoine_circuit n hn)]
    exact lemoine_circuit_correct n hn
