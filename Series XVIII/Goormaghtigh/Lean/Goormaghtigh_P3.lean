/- XVIII_GoormaghtighP3.lean - Pilier P3 : loi d’aire logarithmique et compression MPS. -/

import XVIII_GoormaghtighP2
import Kernel.ClusterExpansion
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve

open Kernel.SpectralLibrary

namespace SeriesXVIII.Goormaghtigh

variable (params : Params) (B : ℕ) (hB : B ≥ 1)

def Φ := Φ params B
def M := Φ.numVars
def G_cl := clause_graph_of Φ

lemma G_cl_bounded_degree : ∃ d, ∀ v, degree G_cl v ≤ d :=
  degree_reduction_bounded Φ

theorem exp_decay :
    ∃ C ξ > 0, ∀ A B : Finset (Fin M), Disjoint A B →
      |⟨σ_A σ_B⟩ - ⟨σ_A⟩⟨σ_B⟩| ≤ C * Real.exp (- (graph_distance G_cl A B) / ξ) :=
  cluster_expansion_correlations G_cl (by exact G_cl_bounded_degree) (ground_state (spectral_problem params B)) (goormaghtigh_spectral_gap params B)

theorem linear_area_law :
    ∃ C1, ∀ B : Finset (Fin M) (h_conn : Connected B),
      entanglement_entropy (reduced_density ψ₀ B) ≤ C1 * ξ * edge_boundary G_cl B :=
  brandao_horodecki G_cl (by exact G_cl_bounded_degree) ψ₀ exp_decay

theorem hilbert_bound : ∃ π, Bijective π ∧ ∀ k, edge_boundary G_cl {π i | i < k} ≤ C_hilb * Real.log M :=
  hilbert_curve_bound G_cl (by exact G_cl_bounded_degree)

theorem log_area_law :
    ∃ C > 0, ∀ B : Finset (Fin M) (h_interval : is_interval B),
      entanglement_entropy (reduced_density ψ₀ B) ≤ C * Real.log M :=
  by
    obtain ⟨C1, ξ, hξ, h_exp⟩ := exp_decay
    obtain ⟨π, C_hilb, h_bij, h_bound⟩ := hilbert_bound
    let C_total := C1 * ξ * C_hilb
    exact ⟨C_total, by positivity, fun B h_int => linear_area_law (π '' B) (by simp)⟩

theorem mps_bond_dimension : ∃ c, MPS_representable ψ₀ (M ^ c) :=
  area_law_implies_mps log_area_law

end SeriesXVIII.Goormaghtigh
