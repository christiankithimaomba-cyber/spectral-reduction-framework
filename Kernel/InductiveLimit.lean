/- 
InductiveLimit.lean – Limites inductives d’espaces de Hilbert et d’opérateurs.
Référence : Kato, T. (1966). Perturbation Theory for Linear Operators. Springer.
-/

import Mathlib.Topology.Limits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum

open Filter

/-- Construction d’une limite inductive d’une suite d’espaces de Hilbert avec inclusions isométriques. -/
axiom inductive_limit_exists {H : ℕ → Type*} [∀ k, InnerProductSpace ℝ (H k)]
    (i : ∀ k, H k →ₗᵢ[ℝ] H (k+1)) : Type*

/-- Opérateur limite inductive d’une suite d’opérateurs compatibles. -/
axiom inductive_limit_op_exists {H : ℕ → Type*} [∀ k, InnerProductSpace ℝ (H k)]
    (i : ∀ k, H k →ₗᵢ[ℝ] H (k+1))
    (T : ∀ k, H k →ₗ[ℝ] H k) (h_compat : ∀ k, i k ∘ T k = T (k+1) ∘ i k) :
    inductive_limit_exists i →ₗ[ℝ] inductive_limit_exists i

/-- Convergence forte des résolvantes pour la limite inductive (Kato). -/
axiom resolvent_convergence {H : ℕ → Type*} [∀ k, InnerProductSpace ℝ (H k)]
    (i : ∀ k, H k →ₗᵢ[ℝ] H (k+1))
    (T : ∀ k, H k →ₗ[ℝ] H k) (h_compat : ∀ k, i k ∘ T k = T (k+1) ∘ i k)
    (z : ℂ) (hz : 0 < im z) :
    tendsto (fun k => resolvent (T k) z) atTop (nhds (resolvent (inductive_limit_op_exists i T h_compat) z))
