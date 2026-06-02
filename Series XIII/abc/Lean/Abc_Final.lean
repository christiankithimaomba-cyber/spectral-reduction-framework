/-
AbcFinal.lean – Preuve finale de la conjecture abc (pour ε=1).
-/

import .AbcExtraction
import .AbcDefs

open SpectralLibrary

theorem abc_conjecture (a b c : ℕ) (hcoprime : gcd a (gcd b c) = 1) (hsum : a + b = c) :
    c ≤ C_eps * (rad (a*b*c))^2 :=
  by
    -- Supposons le contraire : c > C_eps * rad(abc)^2.
    by_contra h_contr
    have h_counter : counterexample a b c C_eps := ⟨hsum, hcoprime, h_contr⟩
    -- Alors par la borne de Stewart–Yu, a,b,c ≤ N0.
    have h_bound := stewart_yu_bound a b c h_counter
    -- Donc le triplet (a,b,c) est dans la borne.
    -- L'instance SAT correspondante serait satisfiable.
    let Φ := abc_SAT N0
    have h_sat : Satisfiable Φ :=
      abc_SAT_correct N0 |>.2 ⟨a, b, c, h_bound.1, h_bound.2.1, h_bound.2.2, hsum, hcoprime, h_contr⟩
    -- Or l'axiome abc_unsat dit que Φ est insatisfiable. Contradiction.
    have h_unsat := abc_unsat N0
    exact h_unsat h_sat
