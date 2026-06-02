/-
KithimaLandauPillars.lean – Vérification des quatre piliers.
-/

import .KithimaLandauHamiltonian
import Kernel.KithimaBridge
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve
import Kernel.MPSAreaLaw

open SpectralLibrary

variable (n : ℕ) (hn : Even n ∧ n > 4)

-- P1
lemma ground_state_unique_pos :
    ∃! ψ : Config → ℝ, (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧
      (H_kl n hn *ᵥ ψ = (λ_min (H_kl n hn)) • ψ) :=
  perron_frobenius (mk_spectral_problem (H_kl n hn))

-- P2 : trou spectral constant
lemma spectral_gap_constant : spectral_gap (H_kl n hn) ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V]; intro; split_ifs <;> linarith)
                Δ (by simp [Δ]; intros; split_ifs <;> linarith)
                1 (by norm_num) (HypercubeHarper.spectral_gap_adjacency (by linarith))

-- P3 : loi d'aire logarithmique
lemma area_law_kl : ∃ C > 0, ∀ B : Finset Config,
    entanglement_entropy (reduced_density (ground_state (mk_spectral_problem H_kl)) B) ≤ C * Real.log M :=
  area_law_for_hypercube (spectral_gap_constant n hn)

-- P4 : extraction D‑RSP
theorem drsp_correct_kl :
    ∃ alg, polynomial_time alg ∧
      (Satisfiable (kithima_landau_SAT n hn) ↔ (alg n).isSome ∧ satisfies _ (alg n).get) :=
  drsp_correct (H_kl n hn)
