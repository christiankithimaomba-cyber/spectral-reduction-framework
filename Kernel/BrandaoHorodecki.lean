/- 
BrandaoHorodecki.lean – Axiome du théorème de Brandão‑Horodecki : décroissance exponentielle ⇒ loi d’aire.
Référence : Brandão, F. G. S. L., & Horodecki, M. (2013). Exponential decay of correlations implies area law.
Communications in Mathematical Physics, 333(2), 761‑798.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-- Axiome : si les corrélations décroissent exponentiellement avec la distance dans un graphe de degré borné,
    alors l’entropie d’intrication de tout ensemble connexe est bornée par une constante fois la frontière. -/
axiom brandao_horodecki {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_deg : ∃ d, ∀ v, degree G v ≤ d)
    (ψ : V → ℝ) (h_exp : ∃ C ξ > 0, ∀ A B : Finset V, Disjoint A B →
        |⟨σ_A σ_B⟩_ψ - ⟨σ_A⟩_ψ * ⟨σ_B⟩_ψ| ≤ C * Real.exp (- (graph_distance G A B) / ξ)) :
    ∃ C' > 0, ∀ B : Finset V, (h_conn : Connected (Subgraph.induce B)) →
        entanglement_entropy (reduced_density ψ B) ≤ C' * edge_boundary G B
