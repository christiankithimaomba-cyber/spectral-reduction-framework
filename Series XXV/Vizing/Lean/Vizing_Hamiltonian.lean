/-
VizingHamiltonian.lean – Hamiltonien spectral pour l'instance SAT de Vizing.
-/

import .DominationCircuit
import .VizingSAT   -- contient la définition de Φ_GH (SAT instance)
import Kernel.SpectralLibrary
import Kernel.KithimaBridge
import Kernel.MPSAreaLaw
import Kernel.HilbertCurve
import Kernel.Renormalisation

open SpectralLibrary

variable (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)]
variable (hG : Fintype.card V(G) ≤ N0) (hH : Fintype.card V(H) ≤ N0)   -- N0 from Clark–Suen

def Φ_GH : SATInstance := vizing_sat_instance G H   -- defined in VizingSAT.lean
def M : ℕ := Φ_GH.numVars
def Config := Fin M → Bool

def V (σ : Config) : ℝ :=
  if satisfies Φ_GH σ then 0 else M^2

def Δ : Matrix Config Config ℝ := adjacencyMatrixOf (hypercube_graph M)

def H_GH : Matrix Config Config ℝ := diagonal V + Δ

lemma H_irreducible : Irreducible H_GH :=
  matrix_is_irreducible_of_adjacency_graph (hypercube_connected M)

-- P1 : existence d'un état fondamental unique strictement positif
theorem ground_state_unique_pos :
    ∃! ψ : Config → ℝ,
      (∀ σ, ψ σ > 0) ∧ (∑ σ, ψ σ ^ 2 = 1) ∧ (H_GH *ᵥ ψ = (λ_min H_GH) • ψ) :=
  perron_frobenius (mk_spectral_problem H_GH)

-- P2 : trou spectral constant (Kithima Bridge)
theorem spectral_gap_constant : spectral_gap H_GH ≥ 2 :=
  kithima_bridge (diagonal V) (by simp [V, M]; intro; split_ifs <;> linarith)
                Δ (by simp [Δ]; intros; split_ifs <;> linarith)
                1 (by norm_num) (HypercubeHarper.spectral_gap_adjacency (by linarith))

-- P3 : loi d'aire logarithmique (via renormalisation et courbe de Hilbert)
-- On admet que le graphe des clauses de Φ_GH a un degré borné.
axiom bounded_degree_clause_graph : ∃ d, ∀ v, degree (clause_graph Φ_GH) v ≤ d

theorem area_law_vizing : ∃ C > 0, ∀ B : Finset Config,
    entanglement_entropy (reduced_density (ground_state H_GH) B) ≤ C * Real.log M :=
  renormalisation_area_law (linear_area_law_from_gap spectral_gap_constant)
                           (hilbert_curve_bound (clause_graph Φ_GH) bounded_degree_clause_graph)

-- P4 : extraction D‑RSP (théorème générique du kernel)
theorem drsp_algorithm_vizing : ∃ alg, polynomial_time alg ∧
    (∀ σ, satisfies Φ_GH σ ↔ alg returns σ) :=
  drsp_correct H_GH
