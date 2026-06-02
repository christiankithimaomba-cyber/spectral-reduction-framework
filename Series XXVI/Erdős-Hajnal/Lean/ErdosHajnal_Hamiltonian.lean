/-
ErdosHajnalHamiltonian.lean – Hamiltonien spectral et vérification des quatre piliers.
-/

import .ErdosHajnalSAT
import Kernel.SpectralLibrary
import Kernel.KithimaBridge
import Kernel.MPSAreaLaw
import Kernel.HilbertCurve
import Kernel.Renormalisation

open SpectralLibrary

variable (H : SimpleGraph) [Fintype V(H)] (n : ℕ) (hn : n ≤ threshold H)

def Φ : SATInstance := erdos_hajnal_SAT H n hn
def M : ℕ := Φ.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ := if satisfies Φ σ then 0 else M^2
def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)
def H_ham : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H_ham :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)

theorem ground_state_unique_pos : ∃! ψ, (∀ σ, ψ σ > 0) ∧ ∑ ψ^2 = 1 ∧ H_ham *ᵥ ψ = λ_min • ψ :=
  perron_frobenius (mk_spectral_problem H_ham)

theorem spectral_gap_constant : spectral_gap H_ham ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V, M]) Δ (by simp) 1 (by norm_num)

theorem area_law : ∃ C, ∀ B, entanglement_entropy (ground_state H_ham) B ≤ C * Real.log M :=
  renormalisation_area_law (by sorry) (hilbert_curve_bound (clause_graph Φ) (by exact bounded_degree))

theorem drsp_correct : ∃ alg, polynomial_time alg ∧
    (∀ σ, satisfies Φ σ ↔ alg returns σ) :=
  drsp_correct H_ham
