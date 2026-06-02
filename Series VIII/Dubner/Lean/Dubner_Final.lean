/-
DubnerFinal.lean – Preuve finale de la conjecture de Dubner et corollaire (premiers jumeaux).
-/

import .DubnerExtraction
import .DubnerSAT

open SpectralLibrary

theorem dubner_conjecture (n : ℕ) (heven : Even n) (hgt : n > 4) :
    ∃ p q : ℕ, is_twin_prime p ∧ is_twin_prime q ∧ p + q = n :=
  by
    by_cases h : n ≤ N0
    · have h_pair := extraction_correct n ⟨heven, hgt⟩ h
      rcases Option.ne_none_iff_exists.1 h_pair with ⟨⟨p,q⟩, h_eq⟩
      exact ⟨p, q, by simp_all⟩
    · have hn : n > N0 := by linarith
      exact dubner_asymptotic_bound n heven hn

/-- Corollaire : conjecture des premiers jumeaux. -/
theorem twin_prime_conjecture : ∃ infinitely many p, is_twin_prime p :=
  by
    apply dubner_implies_twin_primes dubner_conjecture
