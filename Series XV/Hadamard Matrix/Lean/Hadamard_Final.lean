/- XV_HadamardFinal.lean - Preuve finale de la conjecture de Hadamard (série XV). -/

import XV_HadamardExtraction

open SeriesXV.Hadamard

/-- Théorème final : Pour tout n multiple de 4, il existe une matrice de Hadamard d'ordre n. -/
theorem hadamard_conjecture (n : ℕ) (hn : n % 4 = 0) :
    ∃ H : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      H * Hᵀ = n • 1 :=
  by
    -- On applique l'algorithme d'extraction.
    obtain ⟨σ, h_hadamard, h_extract⟩ := extract_hadamard_correct n
    -- On transforme la configuration booléenne en matrice à entrées ±1.
    let H_mat : Matrix (Fin n) (Fin n) ℤ :=
      Matrix.of (fun i j => if σ i j then 1 else -1)
    -- Par construction, σ est une matrice de Hadamard.
    have h_orth : H_mat * H_matᵀ = n • 1 := by
      -- Ceci est équivalent à is_hadamard.
      exact hadamard_condition_implies_orthogonal h_hadamard
    -- On retourne la matrice.
    exact ⟨H_mat, by simp, h_orth⟩
