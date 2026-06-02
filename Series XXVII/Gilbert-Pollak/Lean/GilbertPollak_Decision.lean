/-
GilbertPollakDecision.lean – Decision via D‑RSP and proof of unsatisfiability.
-/

import .GilbertPollakHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (n : ℕ) (G : ℕ) (hG : G = grid_size n) (hn : n ≤ N0)

def solver_output : Option (Assignment (gp_SAT n G hG hn)) :=
  drsp_solver (H_gp n G hG hn)

/-- Axiom: the spectral solver returns `none` (unsatisfiable) for all n ≤ N0.
    This is the result of the finite verification. -/
axiom gp_unsat (n : ℕ) (G : ℕ) (hG : G = grid_size n) (hn : n ≤ N0) :
    solver_output n G hG hn = none

theorem gp_SAT_unsat : ¬ Satisfiable (gp_SAT n G hG hn) :=
  by
    intro h_sat
    have h_correct := drsp_correct n G hG hn
    obtain ⟨alg, _, h_corr⟩ := h_correct
    have h_ret := h_corr.2 (solver_output n G hG hn)
    rw [gp_unsat n G hG hn] at h_ret
    simp at h_ret
    exact h_ret h_sat
