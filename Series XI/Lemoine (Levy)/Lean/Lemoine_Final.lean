/-
LemoineFinal.lean – Preuve finale de la conjecture de Lemoine.
-/

import .LemoineExtraction
import .LemoineSAT

open SpectralLibrary

theorem lemoine_conjecture (n : ℕ) (hodd : Odd n) (hgt : n > 5) :
    ∃ p q : ℕ, Prime p ∧ Prime q ∧ p + 2*q = n :=
  by
    by_cases h : n ≤ N0
    · have h_pair := extraction_correct n ⟨hodd, hgt⟩ h
      rcases Option.ne_none_iff_exists.1 h_pair with ⟨⟨p,q⟩, h_eq⟩
      exact ⟨p, q, by simp_all⟩
    · have hn : n > N0 := by linarith
      exact lemoine_asymptotic n hodd hn
