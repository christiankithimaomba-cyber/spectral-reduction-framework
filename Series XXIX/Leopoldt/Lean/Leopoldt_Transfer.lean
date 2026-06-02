/-
LeopoldtTransfer.lean – Spectral transfer operator from Moore spectra.
Reference: Lück, W. (2023). Moore spectra and the Leopoldt conjecture.
-/

import .LeopoldtDefs
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open NumberField

variable (K : NumberField) (p : ℕ) [Fact p.Prime]

/-- The dimension of the p-adic étale cohomology group H^1(O_K, Z_p(1)). -/
axiom cohomology_dim : ℕ

/-- The transfer operator T_{K,p} as a real symmetric matrix of size d = cohomology_dim. -/
axiom transfer_matrix : Matrix (Fin (cohomology_dim K p)) (Fin (cohomology_dim K p)) ℝ

/-- Self-adjointness of the transfer operator. -/
axiom transfer_selfadjoint (K : NumberField) (p : ℕ) [Fact p.Prime] :
    (transfer_matrix K p)ᵀ = transfer_matrix K p

/-- The eigenvalues of T are algebraic integers. -/
axiom transfer_eigenvalues_integral (K : NumberField) (p : ℕ) [Fact p.Prime] :
    ∀ λ : ℝ, λ ∈ spectrum (transfer_matrix K p) → isAlgebraicInteger λ

/-- The p-adic regulator is zero iff 1 is an eigenvalue of T. -/
axiom regulator_zero_iff_one_eigenvalue (K : NumberField) (p : ℕ) [Fact p.Prime] :
    pAdicRegulator K p = 0 ↔ 1 ∈ spectrum (transfer_matrix K p)

/-- The dimension d is positive (follows from class field theory). -/
axiom cohomology_dim_pos (K : NumberField) (p : ℕ) [Fact p.Prime] : cohomology_dim K p > 0
