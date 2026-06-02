/- 
CookFinal.lean – Preuve que le problème de Cook a une solution.
-/

import CookExtraction

open SpectralLibrary

variable (ε : ℝ) (hε : 0 < ε)

-- Paramètres de l'algorithme (déterminés par la théorie)
def χ0 : ℕ := required_bond_dim N
def T0 : ℕ := required_iterations N

-- Algorithme de résolution
def solve_cook : Option Config :=
  let ψ := power_iteration T0 χ0
  extract_candidate ψ

-- Théorème de correction : l'algorithme retourne toujours une solution.
theorem cook_solution_exists :
    let x := solve_cook
    x.isSome ∧ exact_size x.get ∧ no_incompatible x.get :=
  by
    have h_correct := cook_extraction_correct ε hε χ0 (by linarith) T0 (by linarith)
    simp [solve_cook, power_iteration, extract_candidate] at h_correct
    exact h_correct
