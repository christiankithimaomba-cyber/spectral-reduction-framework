/- 
KatoTheory.lean – Théorèmes de Kato sur la convergence des résolvantes et la semi‑continuité du spectre.
Référence : Kato, T. (1966). Perturbation Theory for Linear Operators. Springer.
-/

import Mathlib.Topology.Limits.Basic
import Mathlib.Analysis.NormedSpace.Basic

/-- Si une suite d’opérateurs auto‑adjoints converge au sens des résolvantes,
    alors le spectre est semi‑continu inférieurement : les trous spectraux ne peuvent pas diminuer. -/
axiom kato_lower_semicontinuity {E : Type*} [InnerProductSpace ℝ E]
    {T_n : ℕ → (E →ₗ[ℝ] E)} [∀ n, IsSelfAdjoint (T_n n)]
    {T : E →ₗ[ℝ] E} [IsSelfAdjoint T]
    (h_conv : ∀ z : ℂ, 0 < im z → tendsto (fun n => resolvent (T_n n) z) atTop (nhds (resolvent T z)))
    (m : ℝ) (hm : 0 < m) (h_gap_n : ∀ n, spectral_gap (T_n n) ≥ m) :
    spectral_gap T ≥ m
