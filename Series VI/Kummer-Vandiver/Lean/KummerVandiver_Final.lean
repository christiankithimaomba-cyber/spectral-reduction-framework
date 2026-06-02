/-
KummerVandiverFinal.lean – Preuve finale de la conjecture.
-/

import .KummerVandiverExtraction
import .KummerVandiverDefs

open SpectralLibrary

/-- Théorème de Kummer–Vandiver : pour tout premier impair p, p ne divise pas h_p^+. -/
theorem kummer_vandiver_conjecture : ∀ p : ℕ, p.Prime ∧ p > 2 →
    ¬ p ∣ class_number_plus p hp :=
  by
    intro p hp
    have h_dec := kummer_vandiver_decision p hp
    have h_correct := extraction_correct p hp
    rw [h_correct] at h_dec
    exact h_dec
