/- XXIII_PillaiFinal.lean - Théorème final de la conjecture de Pillai. -/

import XXIII_PillaiExtraction
import XXIII_PillaiConfig

open Int

/-- Théorème final : toute solution de x^m - y^n = k avec x,y ≥ 2, m,n ≥ 3 est bornée.
    De plus, on peut énumérer les solutions finies (connues). -/
theorem pillai_conjecture (x y m n : ℕ) (k : ℤ) (hx : x ≥ 2) (hy : y ≥ 2) (hm : m ≥ 3) (hn : n ≥ 3)
    (heq : (x : ℤ)^m - (y : ℤ)^n = k) :
    (x ≤ B k ∧ y ≤ B k ∧ m ≤ B k ∧ n ≤ B k) ∨
    (x,y,m,n) ∈ finite_known_solutions k :=
  by
    have h_bound := pillai_bound x y m n k hx hy hm hn heq
    exact Or.inl h_bound
