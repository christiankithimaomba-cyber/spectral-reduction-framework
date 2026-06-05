import .FredholmDeterminant
import Mathlib.NumberTheory.ZetaFunction

open Real Complex

variable (α : ℝ) (hα : 0 < α)

/-- Axiom: xi(s₀) is non‑zero. -/
axiom xi_s0_ne_zero : xi s₀ ≠ 0

/-- The reference point s₀ is not an eigenvalue. -/
lemma s₀_not_eigenvalue (n : ℕ) : eigenvalues α n ≠ s₀ :=
  by
    have h_det : fredholm_det α s₀ ≠ 0 :=
      by
        rw [fredholm_equals_xi α s₀]
        simp [xi_s0_ne_zero]
    intro hn
    rw [hn] at h_det
    exact h_det (Fredholm.determinant_zero_of_eigenvalue (eigenvalues α n) hn)

/-- An eigenvalue of H corresponds to a zero of the Fredholm determinant. -/
theorem eigenvalue_iff_det_zero (s : ℂ) :
    (∃ n, eigenvalues α n = s) ↔ s ≠ s₀ ∧ fredholm_det α s = 0 :=
  by
    constructor
    · intro ⟨n, hn⟩
      have h_ne : s ≠ s₀ := by
        intro h
        rw [h, hn] at h
        exact s₀_not_eigenvalue α n h
      have h_det : fredholm_det α s = 0 :=
        by
          rw [fredholm_equals_xi α s, hn]
          have h_xi_zero : xi (eigenvalues α n) = 0 :=
            eigenvalue_implies_xi_zero α (eigenvalues α n) (by use n)
          simp [h_xi_zero]
      exact ⟨h_ne, h_det⟩
    · intro ⟨h_ne, h_det⟩
      exact det_zero_implies_eigenvalue α s h_det

/-- Axiom: the product (1/2) s (s-1) π^{-s/2} Γ(s/2) does not vanish for s = 1/2 + i t with t real. -/
axiom gamma_product_nonzero (t : ℝ) :
    (1/2) * (1/2 + I * t) * (1/2 + I * t - 1) * π^(-(1/2 + I * t)/2) * Gamma.Gamma ((1/2 + I * t)/2) ≠ 0

/-- On the critical line, ξ vanishes exactly where ζ vanishes. -/
lemma xi_zero_iff_zeta_zero (t : ℝ) : ξ (1/2 + I * t) = 0 ↔ ζ (1/2 + I * t) = 0 :=
  by
    let s := 1/2 + I * t
    have h_factors_nonzero := gamma_product_nonzero t
    rw [xi, mul_eq_zero_iff]
    simp [h_factors_nonzero]

/-- Final spectral characterization. -/
theorem spectral_characterization (t : ℝ) :
    (∃ n, eigenvalues α n = t) ↔ ζ (1/2 + I * t) = 0 :=
  by
    rw [← xi_zero_iff_zeta_zero t]
    constructor
    · intro h_eigen; apply eigenvalue_implies_xi_zero α t h_eigen
    · intro h_xi; apply xi_zero_implies_eigenvalue α t h_xi
