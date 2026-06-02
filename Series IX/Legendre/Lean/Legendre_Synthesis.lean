/- 
LegendreSynthesis.lean – Synthèse des résultats.
-/

import .LegendreFinal

/-- La conjecture de Legendre est prouvée. -/
theorem legendre_conjecture_proved (n : ℕ) (hn : n ≥ 1) :
    ∃ p : ℕ, n^2 < p ∧ p < (n+1)^2 ∧ Nat.Prime p :=
  legendre_conjecture n hn
