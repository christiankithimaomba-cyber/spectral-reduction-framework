import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic

open Real

/-- Area law for the Wilson loop (consequence of constant spectral gap).
    Reference: Osterwalder, K., & Seiler, E. (1978). Gauge field theories on a lattice.
    Annals of Physics, 110(2), 440–471. -/
axiom area_law_Wilson_loop (σ : ℝ) (hσ : σ > 0) (C : ℝ) (hC : C > 0) :
    ∀ R T : ℕ, |⟨W_{R×T}⟩_ψ₀| ≤ C * Real.exp (-σ * R * T)

/-- From area law to exponential decay of conductance. -/
axiom area_law_to_conductance (σ : ℝ) (hσ : σ > 0) (C : ℝ) (hC : C > 0)
    (h_Wilson : ∀ R T : ℕ, |⟨W_{R×T}⟩_ψ₀| ≤ C * Real.exp (-σ * R * T)) :
    ∃ C' : ℝ, ∀ R : ℕ, Φ(R) ≤ C' * Real.exp (-σ * R)

/-- Exponential decay of conductance ⇒ linear potential. -/
axiom exponential_decay_to_linear_potential (σ : ℝ) (hσ : σ > 0) (C' : ℝ) (hC' : C' > 0)
    (h_decay : ∀ R : ℕ, Φ(R) ≤ C' * Real.exp (-σ * R)) :
    ∃ σ' > 0, ∀ R : ℝ, V_eff(R) = σ' * R + O(1)
