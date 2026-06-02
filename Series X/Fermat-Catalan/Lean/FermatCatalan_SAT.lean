/-
FermatCatalanSAT.lean – Réduction à une instance 3‑SAT.
-/

import .FermatCatalanCircuit
import Kernel.Tseitin

open Circuit

def fermat_catalan_SAT (m n k : ℕ) (B : ℕ) (hB : B ≥ 1) : SATInstance :=
  tseitin (fermat_catalan_circuit m n k B)

theorem fermat_catalan_SAT_correct (m n k : ℕ) (B : ℕ) (hB : B ≥ 1) :
    Satisfiable (fermat_catalan_SAT m n k B hB) ↔
    ∃ a b c : ℕ, a ≤ B ∧ b ≤ B ∧ c ≤ B ∧ a^m + b^n = c^k ∧ Nat.gcd a (Nat.gcd b c) = 1 :=
  by
    rw [tseitin_correct (fermat_catalan_circuit m n k B)]
    exact fermat_catalan_circuit_correct m n k B
