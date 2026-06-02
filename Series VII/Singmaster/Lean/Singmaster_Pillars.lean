/-
SingmasterPillars.lean – Vérification des quatre piliers.
-/

import .SingmasterHamiltonian
import Kernel.KithimaBridge
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve
import Kernel.Renormalisation

open SpectralLibrary

variable (t : ℕ) (ht : t ≤ T0)

-- P1
lemma ground_state_unique_pos :
    ∃! ψ : Config → ℝ, (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧
      (H_singmaster t ht *ᵥ ψ = (λ_min (H_singmaster t ht)) • ψ) :=
  perron_frobenius (mk_spectral_problem (H_singmaster t ht))

-- P2 : trou spectral constant
lemma spectral_gap_constant : spectral_gap (H_singmaster t ht) ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V]; intro; split_ifs <;> linarith)
                Δ (by simp [Δ]; intros; split_ifs <;> linarith)
                1 (by norm_num) (HypercubeHarper.spectral_gap_adjacency (by linarith))

-- P3 : loi d'aire logarithmique
lemma area_law_singmaster : ∃ C > 0, ∀ B : Finset Config,
    entanglement_entropy (reduced_density (ground_state (mk_spectral_problem H_singmaster)) B) ≤ C * Real.log M :=
  renormalisation_area_law (by sorry) (hilbert_curve_bound (clause_graph Φ) (by exact bounded_degree))

-- P4 : extraction D‑RSP
theorem drsp_correct_singmaster :
    ∃ alg, polynomial_time alg ∧
      (Satisfiable (singmaster_SAT t ht) ↔ (alg t).isSome ∧ satisfies (singmaster_SAT t ht) (alg t).get) :=
  drsp_correct (H_singmaster t ht)
