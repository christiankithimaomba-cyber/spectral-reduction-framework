import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log

/-- Renormalisation: linear area law + Hilbert curve ⇒ logarithmic area law.
    Reference: Standard renormalisation group argument (see e.g. Hastings 2007). -/
axiom renormalisation_area_law {V : Type*} [Fintype V] (ψ : V → ℝ)
    (h_linear : ∃ C1 : ℝ, ∀ B : Finset V, (h_conn : Connected B) →
        entanglement_entropy (reduced_density ψ B) ≤ C1 * edge_boundary (graph ψ) B)
    (h_hilbert : ∃ (π : V → Fin (Fintype.card V)) (C2 : ℝ), Bijective π ∧
        ∀ k, edge_boundary (graph ψ) {π i | i < k} ≤ C2 * Real.log (Fintype.card V)) :
    ∃ C : ℝ, ∀ B : Finset V,
        entanglement_entropy (reduced_density ψ B) ≤ C * Real.log (Fintype.card V)
