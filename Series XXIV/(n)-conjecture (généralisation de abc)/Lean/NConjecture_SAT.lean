/-
NConjectureSAT.lean – Convert the n-conjecture circuit to a 3‑SAT instance.
-/

import .NConjectureCircuit
import Kernel.Tseitin

open Circuit

variable (n : ℕ) (ε : ℝ) (hε : ε > 0)

def n_conjecture_SAT : SATInstance :=
  tseitin (n_conjecture_circuit n ε hε)

theorem n_conjecture_SAT_correct :
    Satisfiable (n_conjecture_SAT n ε hε) ↔
    ∃ a : Fin n → ℤ,
      (∀ i, a i ≠ 0) ∧
      (Int.gcd_all a) = 1 ∧
      (∀ S : Finset (Fin n), S.nonempty → S ≠ univ → ∑ i in S, a i ≠ 0) ∧
      (∑ i, a i) = 0 ∧
      (max_i |a i|) > (C_const n ε) * (rad (∏ i, |a i|)) ^ (n - 2 + ε) :=
  by
    rw [tseitin_correct]
    exact n_conjecture_circuit_correct n ε hε
