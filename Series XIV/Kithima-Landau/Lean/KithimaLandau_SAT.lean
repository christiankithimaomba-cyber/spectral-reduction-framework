/-
KithimaLandauSAT.lean – Réduction à 3‑SAT via Tseitin.
-/

import .KithimaLandauCircuit
import Kernel.Tseitin

open Circuit

def kithima_landau_SAT (n : ℕ) (hn : Even n ∧ n > 4) : SATInstance :=
  tseitin (kithima_landau_circuit n hn)

theorem kithima_landau_SAT_correct (n : ℕ) (hn : Even n ∧ n > 4) :
    Satisfiable (kithima_landau_SAT n hn) ↔
    ∃ x y : ℕ, is_landau_prime x ∧ is_landau_prime y ∧ (x^2+1)+(y^2+1) = n :=
  by
    rw [tseitin_correct (kithima_landau_circuit n hn)]
    exact kithima_landau_circuit_correct n hn
