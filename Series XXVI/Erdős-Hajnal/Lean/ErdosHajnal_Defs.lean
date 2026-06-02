/-
ErdosHajnalDefs.lean – Définitions de base pour la conjecture d'Erdős–Hajnal.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

/-- Un graphe G est H‑free s'il ne contient pas H comme sous‑graphe induit. -/
def H_free (G H : SimpleGraph) : Prop :=
  ¬ ∃ (F : SimpleGraph), F ≤_ind G ∧ F ≃ H

/-- Un contre‑exemple pour un H donné et un entier n : un graphe G sur n sommets,
    H‑free, avec max(ω(G), α(G)) < n^{ε(H)}. -/
def is_counterexample (H : SimpleGraph) (n : ℕ) (G : SimpleGraph) [Fintype V(G)] : Prop :=
  Fintype.card V(G) = n ∧
  H_free G H ∧
  max (cliqueNumber G) (independenceNumber G) < (n : ℝ) ^ epsilon H

/-- La conjecture d'Erdős–Hajnal pour un H fixé : il existe ε(H) > 0 tel que
    pour tout entier n, tout graphe H‑free sur n sommets a un clique ou un
    ensemble indépendant de taille ≥ n^{ε(H)}. -/
def erdos_hajnal_conjecture (H : SimpleGraph) : Prop :=
  ∃ ε > 0, ∀ (n : ℕ) (G : SimpleGraph) [Fintype V(G)],
    Fintype.card V(G) = n → H_free G H →
    max (cliqueNumber G) (independenceNumber G) ≥ (n : ℝ) ^ ε
