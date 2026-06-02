/- XXXIV_BSD_Synthesis.lean - Synthèse finale : théorème de BSD. -/

import XXXIV_BSD_Extraction

open SpectralLibrary

/-- Théorème final : conjecture de BSD. -/
theorem bsd_conjecture (E : EllipticCurve ℚ) :
    rank_E E = analytic_rank E :=
  by
    let N := effective_N0 E
    have hN : N ≥ effective_N0 E := le_refl N
    rw [← multiplicity_equals_analytic_rank, ← rank_equals_multiplicity_compressed E N hN]
    rw [compute_rank_correct E N hN]
    simp [compute_rank, solver_nonempty_iff_rank_ge]
    rfl
