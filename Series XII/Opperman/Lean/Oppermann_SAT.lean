/-
OppermannSAT.lean – Réduction à 3‑SAT via Tseitin.
-/

import .OppermannCircuit
import Kernel.Tseitin

open Circuit

def oppermann_SAT (n : ℕ) (hn : n ≥ 1) : SATInstance :=
  tseitin (oppermann_circuit n hn)

theorem oppermann_SAT_correct (n : ℕ) (hn : n ≥ 1) :
    Satisfiable (oppermann_SAT n hn) ↔ oppermann_condition n :=
  by
    rw [tseitin_correct (oppermann_circuit n hn)]
    exact oppermann_circuit_correct n hn
