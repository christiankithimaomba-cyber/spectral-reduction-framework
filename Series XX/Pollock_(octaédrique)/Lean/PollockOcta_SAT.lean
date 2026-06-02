/- XX_PollockOctaSAT.lean - Instance SAT via Tseitin. -/

import XX_PollockOctaCircuit
import Tseitin

open Circuit

variable (N : ℕ) (hN : N ≤ N0)

def Φ_N : SATInstance := tseitin (octa_decomp_circuit N)

theorem octa_sat_correct :
    Satisfiable Φ_N ↔ ∃ a b c d e f g : ℕ, octahedral a + octahedral b + octahedral c +
      octahedral d + octahedral e + octahedral f + octahedral g = N :=
  by
    exact octa_circuit_correctness N   -- prouvé dans le kernel
