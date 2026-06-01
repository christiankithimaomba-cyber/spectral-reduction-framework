/-
AmplitudeGap.lean – Lemme d'amplitude gap pour SAT.
Référence : Preuve donnée dans l'Article I.5 (2026) ; nous l'admettons ici.
-/

import PNP.SAT

open SAT

/-- Lemme d'amplitude gap : les solutions ont une amplitude strictement supérieure
    à celle des non-solutions.
    Reference : Kithima, Article I.5 (2026). -/
axiom amplitude_gap_sat (n : ℕ) (inst : SATInstance n) (ε : ℝ) (hε : 0 < ε) (hn : 1 ≤ n)
    (h_sat : ∃ x, satisfies inst x) :
    ∃ δ > 0, ∀ x (hx : satisfies inst x) (y (hy : ¬ satisfies inst y)),
      ground_state_sat n inst ε hε x ≥ ground_state_sat n inst ε hε y + δ
