import .TraceIdentity
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.FredholmDeterminant

open Real Complex

variable (α : ℝ) (hα : 0 < α)

/-- Fixed reference point. -/
noncomputable def s₀ : ℂ := 2

/-- Fredholm determinant of (sI - H) / (s₀I - H). -/
noncomputable def fredholm_det (s : ℂ) : ℂ :=
  ∏' n, (s - eigenvalues α n) / (s₀ - eigenvalues α n)

/-- Axiom: identification with the Riemann xi function (Berry–Connes, Valamontes–Adamopoulos). -/
axiom fredholm_equals_xi (s : ℂ) :
    fredholm_det α s = xi s / xi s₀

/-- A zero of the Fredholm determinant corresponds to an eigenvalue. -/
lemma det_zero_implies_eigenvalue (s : ℂ) (h : fredholm_det α s = 0) :
    ∃ n, eigenvalues α n = s :=
  Fredholm.determinant_zero_iff_eigenvalue h

/-- Axiom: every eigenvalue gives a zero of ξ. -/
axiom eigenvalue_implies_xi_zero (λ : ℝ) (h : ∃ n, eigenvalues α n = λ) :
    ξ (1/2 + I * λ) = 0

/-- Axiom: every zero of ξ on the critical line gives an eigenvalue. -/
axiom xi_zero_implies_eigenvalue (t : ℝ) (h : ξ (1/2 + I * t) = 0) :
    ∃ n, eigenvalues α n = t
