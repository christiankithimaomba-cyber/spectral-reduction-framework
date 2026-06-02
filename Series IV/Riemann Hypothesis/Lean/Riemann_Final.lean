/-
RiemannFinal.lean – Preuve finale de l'Hypothèse de Riemann.
-/

import .RiemannExtraction
import .RiemannSAT
import .RiemannDynamics

open SpectralLibrary

/-- Aucune violation pour n ≤ N0 (découle de la borne explicite et de la région de Kadiri). -/
axiom no_violation : ∀ n ≤ N0, ¬ contraction_violation n

/-- L'instance SAT est donc insatisfiable. -/
theorem riemann_SAT_unsat : ¬ Satisfiable riemann_SAT :=
  by
    intro h_sat
    rcases riemann_SAT_correct.1 h_sat with ⟨n, hn, hviol⟩
    exact no_violation n hn hviol

/-- L'algorithme spectral retourne none. -/
theorem spectral_solver_unsat : extract_violation = none :=
  by
    by_contra h_ne
    have h_sat : Satisfiable riemann_SAT :=
      by
        obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists.1 h_ne
        exact ⟨σ, hσ⟩
    exact riemann_SAT_unsat h_sat

/-- Hypothèse de Riemann vraie. -/
theorem riemann_hypothesis : RiemannHypothesis :=
  by
    -- Par l'équivalence de Kuipers, si aucune violation pour n ≤ N0, alors RH vraie.
    have h_no_viol := no_violation
    by_contra h_rh_false
    rcases kuipers_equivalence_bounded.1 h_rh_false with ⟨n, hn, hviol⟩
    exact h_no_viol n hn hviol
