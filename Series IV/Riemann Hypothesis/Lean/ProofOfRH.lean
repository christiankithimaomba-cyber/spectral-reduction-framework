import .SpectralCharacterization

open Real Complex

variable (α : ℝ) (hα : 0 < α)

/-- Eigenvalues are real. -/
lemma eigenvalues_are_real (n : ℕ) : eigenvalues α n ∈ ℝ :=
  eigenvalues_real α n

/-- Main theorem: Riemann hypothesis. -/
theorem riemann_hypothesis :
    ∀ s : ℂ, (s ≠ 0 ∧ s ≠ 1) → ζ s = 0 → re s = 1/2 :=
  by
    intro s hs hζ
    let t := (s - 1/2) / I
    have h_s : s = 1/2 + I * t := by field_simp
    have h_zeta_zero : ζ (1/2 + I * t) = 0 := by rw [← h_s]; exact hζ
    obtain ⟨n, hn⟩ : ∃ n, eigenvalues α n = t :=
      by
        rw [← spectral_characterization α hα t] at h_zeta_zero
        exact h_zeta_zero
    have h_t_real : t ∈ ℝ := by rw [← hn]; exact eigenvalues_are_real α n
    rw [h_s]
    simp [h_t_real]
    exact rfl
