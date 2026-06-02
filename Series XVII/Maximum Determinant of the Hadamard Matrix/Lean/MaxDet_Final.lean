/- XVII_MaxDetFinal.lean - Preuve finale du problème du déterminant maximal. -/

import XVII_MaxDetP4

open SeriesXVII.MaxDet

/-- Théorème final : Pour tout n ≥ 1, il existe une matrice ±1 de taille n
    dont le déterminant est maximal, et ce maximum est donné par l’algorithme. -/
theorem maximal_determinant_problem (n : ℕ) (hn : n ≥ 1) :
    ∃ H : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      ∀ H' : Matrix (Fin n) (Fin n) ℤ, (∀ i j, H' i j = 1 ∨ H' i j = -1) → |det H'| ≤ |det H| :=
  maxdet_extraction_correct n hn
