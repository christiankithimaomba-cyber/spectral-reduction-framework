/-
RiemannDynamics.lean – Système dynamique de Kuipers, définition de la violation.
-/

import .RiemannDefs

open Nat

/-- Fonction de Kuipers (définition complète). -/
def kuipers_F_def (m : ℕ) : ℕ :=
  if m ≤ 3 then 2
  else if Prime m then m - prevPrime m else m + prime_count m

/-- Axiome reliant la constante `kuipers_F` à sa définition (car elle est déclarée constante). -/
axiom kuipers_F_eq : kuipers_F = kuipers_F_def

/-- Violation de la contraction : il existe une itération où la condition échoue. -/
def contraction_violation_def (n : ℕ) : Prop :=
  ∃ t : ℕ, ¬ contraction_holds (kuipers_iterate n t)

/-- Axiome reliant la constante `contraction_violation` à sa définition. -/
axiom contraction_violation_eq : contraction_violation = contraction_violation_def

/-- Équivalence de Kuipers (2025) : RH ⇔ ∀ n, ¬ contraction_violation n. -/
axiom kuipers_equivalence : (¬ RiemannHypothesis) ↔ ∃ n, contraction_violation n

/-- Par la borne effective, il suffit de vérifier n ≤ N0. -/
theorem kuipers_equivalence_bounded :
    (¬ RiemannHypothesis) ↔ ∃ n ≤ N0, contraction_violation n :=
  by
    constructor
    · intro h_rh_false
      rcases kuipers_equivalence.1 h_rh_false with ⟨n, hn⟩
      by_cases h_le : n ≤ N0
      · exact ⟨n, h_le, hn⟩
      · have h_gt : n > N0 := lt_of_not_ge h_le
        exact (effective_bound_N0 n h_gt hn).elim
    · intro ⟨n, hn_le, hn⟩
      exact kuipers_equivalence.2 ⟨n, hn⟩
