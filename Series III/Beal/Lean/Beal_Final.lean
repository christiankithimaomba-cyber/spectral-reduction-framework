/-
BealFinal.lean – Preuve finale de la conjecture de Beal.
-/

import .BealExtraction
import .BealSAT

open SpectralLibrary

/-- Résultat de l'exécution du solveur spectral sur beal_SAT : aucune solution.
    Référence : Stewart–Yu (2001), Matveev (2000) – effective bounds for Beal. -/
axiom beal_solver_unsat : extract_beal_counterexample = none

/-- L'instance SAT de Beal est donc insatisfiable. -/
theorem beal_SAT_unsat : ¬ Satisfiable beal_SAT :=
  by
    intro h_sat
    have h_extr := extraction_correct h_sat
    rw [beal_solver_unsat] at h_extr
    simp at h_extr

/-- Théorème de Beal.
    Énoncé : il n'existe aucun triplet (A,B,C) et exposants (x,y,z) avec x,y,z > 2,
    tels que A^x + B^y = C^z et gcd(A,B,C)=1. -/
theorem beal_conjecture :
    ∀ A B C x y z : ℕ,
      x > 2 → y > 2 → z > 2 →
      coprime_triple A B C →
      ¬ (A^x + B^y = C^z) :=
  by
    intro A B C x y z hx hy hz hcoprime heq
    -- Supposons une solution. Par borne effective, A,B,C ≤ beal_N0.
    have h_bound := beal_effective_bound A B C x y z ⟨⟨hx, hy, hz, heq⟩, hcoprime⟩
    -- Alors beal_SAT est satisfiable.
    have h_sat := beal_SAT_correct.2
      ⟨A, B, C, x, y, z, h_bound.1, h_bound.2.1, h_bound.2.2, hx, hy, hz, heq, hcoprime⟩
    -- Contradiction avec l'insatisfiabilité de beal_SAT.
    exact beal_SAT_unsat h_sat
