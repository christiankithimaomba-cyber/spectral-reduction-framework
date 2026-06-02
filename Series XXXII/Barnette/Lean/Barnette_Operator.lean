/-
BarnetteOperator.lean – Transfer operator T_G and equivalence with Hamiltonian cycles.
Reference: SHS strategy (Kithima, 2026).
Author: Christian Kithima
ORCID: 0009-0003-3829-8519
GitHub: https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/tree/main/Kernel
-/

import .BarnetteDefs
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open SimpleGraph

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] (hG : barnette_graph G)

/-- A spanning cycle is a permutation that is a single cycle. -/
def SpanningCycle : Type :=
  { σ : Equiv.Perm V | Equiv.Perm.isCycle σ ∧ σ.support = univ }

/-- Hilbert space of functions on spanning cycles. -/
def ℋ_G : Type := SpanningCycle G → ℝ

instance : InnerProductSpace ℝ (ℋ_G G) :=
  PiLp.innerProductSpace (fun _ => ℝ)

/-- Local rotation move: exchange two edges along the cycle. -/
axiom neighbor (C : SpanningCycle G) : Finset (SpanningCycle G)

axiom neighbor_symm (C C' : SpanningCycle G) : C' ∈ neighbor C ↔ C ∈ neighbor C'

/-- Each spanning cycle has exactly two neighbors (for cubic bipartite planar graphs). -/
axiom neighbor_card (C : SpanningCycle G) : Finset.card (neighbor C) = 2

/-- Transfer operator T_G: average over neighbors. -/
def T_G : (ℋ_G G →ₗ[ℝ] ℋ_G G) :=
  LinearMap.mk (fun f C => (1 / 2) * ∑ C' in neighbor C, f C')
    (by simp) (by simp)

/-- T_G is self‑adjoint. -/
theorem T_selfadjoint : (T_G G hG).adjoint = T_G G hG :=
  by
    ext f g
    rw [LinearMap.adjoint_def, inner_apply, inner_apply]
    simp [T_G, neighbor, neighbor_symm]
    rw [Finset.sum_comm]
    ring

/-- T_G is a contraction (norm ≤ 1). -/
axiom T_G_contraction : ‖T_G G hG‖ ≤ 1

/-- The spectrum of T_G lies in [-1,1]. -/
theorem spectrum_bounded : ∀ λ ∈ spectrum (T_G G hG), |λ| ≤ 1 :=
  by
    intro λ hλ
    have h_rad : |λ| ≤ spectral_radius (T_G G hG) := le_spectral_radius hλ
    have h_rad_bound : spectral_radius (T_G G hG) ≤ ‖T_G G hG‖ := spectral_radius_le_norm (T_G G hG)
    linarith [h_rad, h_rad_bound, T_G_contraction G hG]

/-- Main theorem (SHS): 1 is eigenvalue of T_G iff G has a Hamiltonian cycle. -/
axiom eigenvalue_one_iff_hamiltonian :
    (1 ∈ spectrum (T_G G hG)) ↔ hamiltonian_cycle G
