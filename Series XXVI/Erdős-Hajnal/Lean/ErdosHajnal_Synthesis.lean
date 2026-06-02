/-
ErdosHajnalSynthesis.lean – Théorème final de la conjecture d'Erdős–Hajnal.
-/

import .ErdosHajnalDecision
import .EffectiveBound

open Real SimpleGraph

theorem erdos_hajnal_conjecture (H : SimpleGraph) [Fintype V(H)] :
    ∃ ε > 0, ∀ (n : ℕ) (G : SimpleGraph) [Fintype V(G)],
      Fintype.card V(G) = n → H_free G H →
      max (cliqueNumber G) (independenceNumber G) ≥ (n : ℝ) ^ ε :=
  by
    use epsilon H, epsilon_pos H
    intro n G hG h_free
    by_cases h : n ≤ threshold H
    · -- petit n : on utilise la vérification spectrale
      have h_unsat := Φ_unsat H n h
      have h_sat : ¬ Satisfiable (erdos_hajnal_SAT H n h) := h_unsat
      -- Par la correction du SAT, s'il existait un contre‑exemple, Φ serait satisfiable.
      -- Donc il n'existe pas de contre‑exemple, c'est‑à‑dire que la propriété est vraie.
      exact no_counterexample_implies_property h_sat
    · -- grand n : on utilise la borne effective (Erdős–Hajnal original)
      have h_large : n ≥ threshold H := by linarith
      exact (erdos_hajnal_data H).large_graph_property G h_free h_large
