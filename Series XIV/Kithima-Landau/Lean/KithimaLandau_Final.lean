/-
KithimaLandauFinal.lean – Preuve finale de la conjecture de Kithima–Landau et du quatrième problème de Landau.
-/

import .KithimaLandauExtraction
import .KithimaLandauSAT

open SpectralLibrary

theorem kithima_landau_conjecture (n : ℕ) (heven : Even n) (hgt : n > 4) :
    ∃ x y : ℕ, is_landau_prime x ∧ is_landau_prime y ∧ (x^2+1)+(y^2+1) = n :=
  by
    by_cases h : n ≤ N0
    · have h_pair := extraction_correct n ⟨heven, hgt⟩ h
      rcases Option.ne_none_iff_exists.1 h_pair with ⟨⟨x,y⟩, h_eq⟩
      exact ⟨x, y, by simp_all⟩
    · have hn : n > N0 := by linarith
      exact kithima_landau_asymptotic n heven hn

-- Corollaire : quatrième problème de Landau
theorem fourth_landau_problem : ∃ infinitely many n, is_landau_prime n :=
  by
    apply kithima_landau_implies_landau kithima_landau_conjecture
