/- 
GoldbachAreaLaw.lean – Loi d’aire logarithmique.
-/

import .GoldbachConductance
import Kernel.MPSAreaLaw

open Kernel.MPS

theorem goldbach_area_law (N : ℕ) (λ ε : ℝ) (hε : 0 < ε) :
    let ψ := ground_state (GoldbachSpectralProblem N λ ε hε)
    let ψ_mps := MPS.from_vector ψ (2*N+1)
    ∃ C α, 0 < α ∧ α < 1 ∧ ∀ k,
      ∑ i ≥ k, (SVD.exists_svd (eval_matrix ψ_mps)).2.singularValues i ^ 2 ≤ C * α ^ k :=
  area_law_hastings ψ_mps (ε^2 / (32 * N^4)) (by linarith [goldbach_spectral_gap N λ ε hε])
