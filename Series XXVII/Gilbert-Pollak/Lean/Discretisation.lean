/-
Discretisation.lean – Discretisation of the Euclidean plane for the Gilbert–Pollak conjecture.
Reference: standard computational geometry.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

open Real

/-- For a given number of points n, a grid size G(n) such that any counterexample
    can be moved to the grid. -/
noncomputable def grid_size (n : ℕ) : ℕ := 2^n

/-- Axiom: discretisation theorem. -/
axiom discretisation (n : ℕ) :
    ∀ (P : Finset (ℝ × ℝ)) (h_card : Fintype.card P = n),
      (SMT_length P < ρ * MST_length P) →
      ∃ (Q : Finset (ℤ × ℤ)),
        (∀ p ∈ Q, 0 ≤ p.1 ∧ p.1 ≤ grid_size n ∧ 0 ≤ p.2 ∧ p.2 ≤ grid_size n) ∧
        Fintype.card Q = n ∧
        let real_Q : Finset (ℝ × ℝ) := Q.map (fun (x,y) => (x, y))
        SMT_length real_Q < ρ * MST_length real_Q
