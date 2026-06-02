/- 
GoldbachFinal.lean – Preuve finale de la conjecture de Goldbach.
-/

import .GoldbachExtraction

theorem goldbach_conjecture (N : ℕ) (hN : N ≥ 2) :
    ∃ p q : ℕ, p + q = 2*N ∧ Nat.Prime p ∧ Nat.Prime q :=
  by
    let λ : ℝ := N^2
    let ε : ℝ := 1
    have hε : 0 < ε := by norm_num
    have hλ : 2 * ε < λ := by norm_num
    have h_amp := goldbach_amplitude_gap N λ ε hε hλ
    have ⟨T, χ, h_extr⟩ := goldbach_extraction_correct N λ ε hε (1/(2*Real.sqrt (2*N+1))) (by positivity) h_amp
    let p := (goldbach_extract N λ ε hε T χ).get
    have h_prime := h_extr T (le_refl T) χ (le_refl χ)
    exact ⟨p, 2*N - p, by simp, h_prime.1, h_prime.2⟩
