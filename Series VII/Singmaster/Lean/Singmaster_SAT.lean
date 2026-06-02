/-
SingmasterSAT.lean – Réduction à 3‑SAT via Tseitin.
-/

import .SingmasterCircuit
import Kernel.Tseitin

open Circuit

def singmaster_SAT (t : ℕ) (ht : t ≤ T0) : SATInstance :=
  tseitin (binom_circuit t ht)

theorem singmaster_SAT_correct (t : ℕ) (ht : t ≤ T0) :
    Satisfiable (singmaster_SAT t ht) ↔ ∃ n k : ℕ, 1 ≤ k ∧ 2*k ≤ n ∧ Nat.choose n k = t :=
  by
    rw [tseitin_correct (binom_circuit t ht)]
    exact binom_circuit_correct t ht
