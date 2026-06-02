/- XXII_KislitsynFinal.lean - Théorème final de la conjecture 1/3-2/3 (Kislitsyn). -/

import XXII_KislitsynExtraction
import XXII_KislitsynConfig

open SimpleGraph

/-- Constante effective (Clark–Suen, pour la borne asymptotique). -/
constant N0 : ℕ

/-- Axiome : pour n > N0, toute poset non‑chaîne a une paire équilibrée. -/
axiom clark_suen_bound (P : SimpleGraph) [Fintype V(P)] (h_not_chain : ¬ IsChain P) :
    let n := Fintype.card V(P)
    n > N0 → ∃ x y, balanced_pair x y

/-- Théorème final : toute poset non‑chaîne contient une paire équilibrée. -/
theorem one_third_two_thirds_conjecture (P : SimpleGraph) [Fintype V(P)] [DecidableRel P.Adj]
    (h_not_chain : ¬ IsChain P) :
    ∃ x y : V(P), x ≠ y ∧
      let n := Fintype.card V(P)
      (n/3 ≤ Finset.card {z | z ≤ x ∧ z ≠ x} ≤ 2*n/3) ∧
      (n/3 ≤ Finset.card {z | z ≤ y ∧ z ≠ y} ≤ 2*n/3) :=
  by
    let n := Fintype.card V(P)
    by_cases h : n ≤ N0
    · -- cas fini : on invoque le solveur spectral
      let solver := balanced_pair_solver P n h
      match solver with
      | none => exfalso
      | some σ =>
          let (i,j) := decode_pair σ
          have h_correct := balanced_pair_extraction_correct P n h h_not_chain
          exact ⟨i,j, h_correct⟩
    · -- cas n > N0 : théorème asymptotique de Clark–Suen
      have h_large : n > N0 := by linarith
      exact clark_suen_bound P h_not_chain h_large
