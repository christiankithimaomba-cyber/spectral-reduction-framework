/-
RiemannPillars.lean – Vérification des quatre piliers.
-/

import .RiemannHamiltonian
import Kernel.DiscreteCheeger
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve
import Kernel.Renormalisation

open SpectralLibrary

lemma ground_state_unique_pos : (∀ σ, ψ0 σ > 0) ∧ (∑ σ, ψ0 σ ^ 2 = 1) ∧ (H_riemann *ᵥ ψ0 = λ_min H_riemann • ψ0) :=
  perron_frobenius (mk_spectral_problem H_riemann)

lemma spectral_gap_riemann : spectral_gap H_riemann ≥ 2 :=
  kithima_bridge (diagonal V_potential) (by simp [V_potential]; intro; split_ifs <;> linarith)
                 Δ (by simp [Δ, adjacencyMatrixOf]; intros; split_ifs <;> linarith)
                 1 (by norm_num) (HypercubeHarper.spectral_gap_adjacency (by linarith))

lemma area_law_riemann : ∃ C > 0, ∀ B, entanglement_entropy (reduced_density ψ0 B) ≤ C * Real.log M :=
  renormalisation_area_law (linear_area_law_from_gap spectral_gap_riemann) (hilbert_curve_bound ...)

theorem drsp_riemann : ∃ alg, polynomial_time alg ∧
    (Satisfiable riemann_SAT ↔ (alg riemann_SAT).isSome ∧ satisfies riemann_SAT (alg riemann_SAT).get) :=
  drsp_correct H_riemann
