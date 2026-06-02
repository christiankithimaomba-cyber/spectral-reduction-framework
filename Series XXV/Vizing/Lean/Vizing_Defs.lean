/-
VizingDefs.lean – Basic definitions for Vizing's conjecture.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Prod

open SimpleGraph

/-- Domination number γ(G) (minimum size of a dominating set). -/
noncomputable def domination_number (G : SimpleGraph) [Fintype V(G)] : ℕ :=
  Finset.min (Finset.filter (fun (D : Finset V(G)) => D.dominates G) (Finset.powerset Finset.univ)) |>.get

/-- Predicate: a set D is dominating. -/
def dominates (G : SimpleGraph) (D : Finset V(G)) : Prop :=
  ∀ v : V(G), v ∈ D ∨ ∃ u ∈ D, G.Adj u v

/-- Cartesian product of two graphs. -/
def cartesian_product (G H : SimpleGraph) : SimpleGraph (V(G) × V(H)) :=
  SimpleGraph.cartesianProduct G H

/-- Vizing's conjecture: γ(G □ H) ≥ γ(G) * γ(H). -/
def vizing_conjecture (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)] : Prop :=
  domination_number (cartesian_product G H) ≥ domination_number G * domination_number H
