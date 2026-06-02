/-
RiemannSAT.lean – Réduction à une seule instance 3‑SAT.
-/

import .RiemannCircuit
import Kernel.Tseitin

open Circuit

/-- Instance SAT pour la disjonction des violations pour n ≤ N0. -/
def riemann_SAT : SATInstance :=
  let circuits := List.range (N0+1) |>.map (fun n => violation_circuit n (by simp))
  let or_circuit := circuits.foldl (fun acc c => or_circuit acc c) (constant false)
  tseitin or_circuit

/-- Satisfiabilité ↔ il existe un contre‑exemple à RH (n ≤ N0). -/
theorem riemann_SAT_correct :
    Satisfiable riemann_SAT ↔ ∃ n ≤ N0, contraction_violation n :=
  by
    rw [tseitin_correct or_circuit]
    apply or_circuit_correct
    intro n hn; exact violation_circuit_correct n hn
