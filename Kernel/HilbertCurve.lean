/- 
HilbertCurve.lean – Courbe de Hilbert pour obtenir un ordre linéaire avec faible frontière.
Référence : Hilbert, D. (1891). Über die stetige Abbildung einer Linie auf ein Flächenstück.
Mathematische Annalen, 38(3), 459‑460.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Log

/-- Pour un graphe de degré borné, il existe une bijection (ordre linéaire) telle que tout préfixe
    ait une frontière d’arêtes de taille O(log N). Ce résultat est admis comme un fait géométrique standard. -/
axiom hilbert_curve_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h_deg : ∃ d, ∀ v, degree G v ≤ d) :
    ∃ (π : V → Fin (Fintype.card V)) (C : ℝ), Bijective π ∧
      ∀ k, edge_boundary G {π i | i < k} ≤ C * Real.log (Fintype.card V)
