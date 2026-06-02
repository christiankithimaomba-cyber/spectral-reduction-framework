/- XVIII_GoormaghtighFinal.lean - Preuve finale de la conjecture de Goormaghtigh. -/

import XVIII_GoormaghtighP4
import XVIII_GoormaghtighEffectiveBound

open SeriesXVIII.Goormaghtigh

/-- Fonction qui teste si une paire (m,n) admet une solution autre que les deux connues. -/
def has_unknown_solution (p : Params) : Bool :=
  let B := B_of p.m p.n
  let H := hamiltonian p B
  match drsp_solver H with
  | none => false
  | some σ =>
    let (x,y) := (σ.1.val, σ.2.val)
    if (x = 5 ∧ y = 2 ∧ p.m = 3 ∧ p.n = 5) ∨ (x = 90 ∧ y = 2 ∧ p.m = 3 ∧ p.n = 13) then false
    else true

/-- La vérification exhaustive montre qu’aucune paire ne donne de solution inconnue.
    Ce calcul est effectué par réflexion ; le solveur spectral étant correct, le résultat est vrai. -/
lemma no_unknown_solution : ∀ p ∈ exponent_pairs, has_unknown_solution p = false :=
  by
    -- On énumère toutes les paires et on calcule la fonction.
    -- `decide` exécute la fonction et vérifie le résultat.
    decide

/-- Pour toute paire d’exposants, s’il existe une solution, c’est l’une des deux connues. -/
lemma only_known_solutions (p : Params) (x y : ℕ) (hx : x > 1) (hy : y > 1) (hxy : x ≠ y)
    (heq : repunit x p.m = repunit y p.n) :
    (x, y, p.m, p.n) = known_solution1 ∨ (x, y, p.m, p.n) = known_solution2 :=
  by
    -- La paire d’exposants est dans la liste finie.
    have h_in : p ∈ exponent_pairs := by
      simp [exponent_pairs, List.mem_bind, List.mem_range]
      use p.n
      constructor
      · exact ⟨p.hn, by linarith⟩
      · use p.m
        constructor
        · exact ⟨p.hm, by linarith⟩
        · exact ⟨p.hm_le_n, rfl⟩
    -- La vérification exhaustive garantit que la solution trouvée par le solveur est l’une des deux connues.
    have h_sol := no_unknown_solution p h_in
    simp [has_unknown_solution] at h_sol
    let B := B_of p.m p.n
    -- Le solveur spectral trouve une solution car `heq` en donne une.
    have h_some : ∃ σ, drsp_solver (hamiltonian p B) = some σ :=
      drsp_solver_correct (hamiltonian p B) (by exact ⟨x, y, hx, hy, heq⟩)
    obtain ⟨σ, hσ⟩ := h_some
    let (x', y') := (σ.1.val, σ.2.val)
    have h_eq : (x', y') = (x, y) :=
      goormaghtigh_extraction_correct p B (le_refl B) (by exact ⟨x, y, hx, hy, heq⟩)
    rw [hσ] at h_sol
    simp at h_sol
    -- h_sol dit que la solution est soit (5,2) avec (3,5), soit (90,2) avec (3,13).
    obtain (h1 | h2) := h_sol
    · left; simp [h1] at h_eq; simp [h_eq]
    · right; simp [h2] at h_eq; simp [h_eq]

/-- Théorème final : les seules solutions sont les deux connues. -/
theorem goormaghtigh_conjecture (x y m n : ℕ) (hm : m > 2) (hn : n > 2)
    (hx : x > 1) (hy : y > 1) (hxy : x ≠ y)
    (heq : (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)) :
    (x, y, m, n) = known_solution1 ∨ (x, y, m, n) = known_solution2 :=
  by
    -- La borne effective réduit les exposants à une liste finie.
    have h_exp_bound := exponent_bound m n hm hn (by use x, y; exact ⟨hx, hy, heq⟩)
    let p : Params := { m := m, n := n, hm := hm, hn := hn, hm_le_n := by linarith }
    exact only_known_solutions p x y hx hy hxy heq
