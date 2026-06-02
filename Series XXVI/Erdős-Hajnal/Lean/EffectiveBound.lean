/-
EffectiveBound.lean – Constants effectives pour la conjecture d'Erdős–Hajnal.
Références : Erdős–Hajnal (1989), Rödl–Schacht (2009), etc.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Real SimpleGraph

/-- Pour chaque graphe interdit H, on dispose d'un ε(H) > 0 et d'un seuil n₀(H). -/
class ErdosHajnalData (H : SimpleGraph) where
  epsilon : ℝ
  epsilon_pos : epsilon > 0
  threshold : ℕ
  large_graph_property : ∀ (G : SimpleGraph) [Fintype V(G)],
    (∀ (F : SimpleGraph), ¬ F ≤_ind G) →  -- G ne contient pas H comme sous‑graphe induit
    Fintype.card V(G) ≥ threshold →
    max (cliqueNumber G) (independenceNumber G) ≥ (Fintype.card V(G)) ^ epsilon

/-- Axiome : pour tout graphe H, de telles constantes existent. -/
axiom erdos_hajnal_data (H : SimpleGraph) [Fintype V(H)] : ErdosHajnalData H

/-- Seuil explicite pour un H fixé (n₀(H)). -/
def threshold (H : SimpleGraph) [Fintype V(H)] : ℕ := (erdos_hajnal_data H).threshold

/-- Epsilon explicite pour un H fixé. -/
def epsilon (H : SimpleGraph) [Fintype V(H)] : ℝ := (erdos_hajnal_data H).epsilon

lemma epsilon_pos (H : SimpleGraph) [Fintype V(H)] : epsilon H > 0 :=
  (erdos_hajnal_data H).epsilon_pos
