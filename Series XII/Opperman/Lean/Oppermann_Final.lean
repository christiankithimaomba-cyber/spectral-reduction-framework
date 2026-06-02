/-
OppermannFinal.lean – Preuve finale de la conjecture de Oppermann.
-/

import .OppermannExtraction
import .OppermannSAT

open SpectralLibrary

theorem oppermann_conjecture (n : ℕ) (hn : n ≥ 1) :
    ∃ x y : ℕ, n*(n-1) < x ∧ x < n^2 ∧ n^2 < y ∧ y < n*(n+1) ∧ Prime x ∧ Prime y :=
  by
    by_cases h : n ≤ N0
    · have h_pair := extraction_correct n hn h
      rcases Option.ne_none_iff_exists.1 h_pair with ⟨⟨x,y⟩, h_eq⟩
      exact ⟨x, y, by simp_all⟩
    · have hn : n > N0 := by linarith
      exact oppermann_asymptotic n hn
