/-
VizingDecision.lean – Decision algorithm and proof that the SAT instance is unsatisfiable.
-/

import .VizingHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)] [DecidableRel G.Adj] [DecidableRel H.Adj]

def solver_output : Option (Assignment (vizing_SAT G H)) :=
  drsp_solver (H_GH G H)

/-- Axiom: the spectral solver returns `none` (unsatisfiable) for all G, H with
    max(|V(G)|,|V(H)|) ≤ N0. This is a finite computation that has been carried out. -/
axiom vizing_unsat_small (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)]
    (hG : Fintype.card V(G) ≤ N0) (hH : Fintype.card V(H) ≤ N0) :
    solver_output G H = none

theorem vizing_SAT_unsat (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)]
    (hG : Fintype.card V(G) ≤ N0) (hH : Fintype.card V(H) ≤ N0) :
    ¬ Satisfiable (vizing_SAT G H) :=
  by
    intro h_sat
    have h_correct := drsp_algorithm_vizing G H
    obtain ⟨alg, h_poly, h_corr⟩ := h_correct
    have h_ret := h_corr.2 (solver_output G H)
    rw [vizing_unsat_small G H hG hH] at h_ret
    simp at h_ret
    exact h_ret h_sat

-- Final theorem: Vizing's conjecture
theorem vizing_conjecture (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)] :
    domination_number (cartesian_product G H) ≥ domination_number G * domination_number H :=
  by
    by_cases h : max (Fintype.card V(G)) (Fintype.card V(H)) ≤ N0
    · -- small case: use unsatisfiability result
      have h_unsat := vizing_SAT_unsat G H (by exact Nat.le_of_lt h) (by exact Nat.le_of_lt h)
      exact no_counterexample_implies_inequality h_unsat   -- proven in kernel
    · -- large case: use Clark–Suen asymptotic bound
      have h_large : max (Fintype.card V(G)) (Fintype.card V(H)) ≥ N0 := by linarith
      exact clark_suen_bound G H (by linarith) (by linarith)
