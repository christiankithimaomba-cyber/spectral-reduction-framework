/-
DubnerPillars.lean – Vérification des quatre piliers.
-/

import .DubnerHamiltonian
import Kernel.KithimaBridge
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve
import Kernel.MPSAreaLaw   -- pour area_law_for_hypercube

open SpectralLibrary

variable (n : ℕ) (hn : Even n ∧ n > 4)

-- P1
lemma ground_state_unique_pos :
    ∃! ψ : Config → ℝ, (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧
      (H_dubner n hn *ᵥ ψ = (λ_min (H_dubner n hn)) • ψ) :=
  perron_frobenius (mk_spectral_problem (H_dubner n hn))

-- P2 : trou spectral constant
lemma spectral_gap_constant : spectral_gap (H_dubner n hn) ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V]; intro; split_ifs <;> linarith)
                Δ (by simp [Δ]; intros; split_ifs <;> linarith)
                1 (by norm_num) (HypercubeHarper.spectral_gap_adjacency (by linarith))

-- P3 : loi d'aire logarithmique (via le théorème générique du kernel)
lemma area_law_dubner : ∃ C > 0, ∀ B : Finset Config,
    entanglement_entropy (reduced_density (ground_state (mk_spectral_problem (H_dubner n hn))) B) ≤ C * Real.log M :=
  area_law_for_hypercube (spectral_gap_constant n hn)   -- appel à la fonction du kernel

-- P4 : extraction D‑RSP
theorem drsp_correct_dubner :
    ∃ alg, polynomial_time alg ∧
      (Satisfiable (dubner_SAT n hn) ↔ (alg n).isSome ∧ satisfies (dubner_SAT n hn) (alg n).get) :=
  drsp_correct (H_dubner n hn)
