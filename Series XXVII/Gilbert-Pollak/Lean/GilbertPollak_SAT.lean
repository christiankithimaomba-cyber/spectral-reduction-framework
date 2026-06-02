/-
GilbertPollakSAT.lean – Reduction of the circuit to 3‑SAT.
-/

import .GilbertPollakCircuit
import Kernel.Tseitin

open Circuit

variable (n : ℕ) (G : ℕ) (hG : G = grid_size n) (hn : n ≤ N0)

def gp_SAT : SATInstance := tseitin (gp_circuit n G hG hn)

theorem gp_SAT_correct :
    Satisfiable (gp_SAT n G hG hn) ↔
    ∃ points : List (ℤ × ℤ),
      points.length = n ∧
      (∀ (x,y) ∈ points, 0 ≤ x ∧ x ≤ G ∧ 0 ≤ y ∧ y ≤ G) ∧
      let real_pts := points.map (fun (x,y) => (x, y))
      SMT_length real_pts < ρ * MST_length real_pts :=
  by
    rw [tseitin_correct]
    exact gp_circuit_correct n G hG hn
