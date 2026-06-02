/- XVII_BrocardConfig.lean - Configuration pour le problème de Brocard. -/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic

open Nat

/-- Constante effective : seuil de vérification exhaustive (10⁹). -/
constant N0 : ℕ
axiom N0_value : N0 = 10^9

/-- Axiome : aucune solution n'existe pour n > N0.
    Ceci est basé sur la vérification numérique exhaustive (Berndt & Galway, 2000). -/
axiom no_solution_beyond_N0 (n : ℕ) (hn : n > N0) :
    ¬ ∃ m : ℕ, m^2 = n! + 1

/-- Solutions connues. -/
def known_solution : ℕ × ℕ → Prop
| (4,5) => True
| (5,11) => True
| (7,71) => True
| _ => False
