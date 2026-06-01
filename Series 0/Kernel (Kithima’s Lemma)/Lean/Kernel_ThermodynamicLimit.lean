/- 
ThermodynamicLimit.lean – Limite thermodynamique pour une famille de Hamiltoniens.
-/

import .InductiveLimit
import .KatoTheory

open Filter

/-- Suite croissante de boîtes (axiome). -/
axiom increasing_boxes : ℕ → Type*

/-- Espace de Hilbert pour la boîte k. -/
axiom H_space (k : ℕ) : Type*  -- ℓ²(increasing_boxes k) (à adapter)

/-- Isométrie d’inclusion. -/
axiom incl (k : ℕ) : H_space k →ₗᵢ[ℝ] H_space (k+1)

/-- Hamiltonien sur la boîte k. -/
axiom H_k (k : ℕ) : H_space k →ₗ[ℝ] H_space k

/-- Compatibilité des Hamiltoniens avec les inclusions. -/
axiom H_compat (k : ℕ) : incl k ∘ H_k k = H_k (k+1) ∘ incl k

/-- Limite inductive des espaces. -/
noncomputable def H_inf : Type :=
  inductive_limit_exists incl

/-- Limite inductive des opérateurs. -/
noncomputable def H_inf_op : H_inf →ₗ[ℝ] H_inf :=
  inductive_limit_op_exists incl H_k H_compat

/-- Convergence forte des résolvantes (Kato). -/
axiom resolvent_convergence_limit (z : ℂ) (hz : 0 < im z) :
    tendsto (fun k => resolvent (H_k k) z) atTop (nhds (resolvent H_inf_op z))

/-- Semi‑continuité inférieure du trou spectral. -/
lemma gap_persists (m : ℝ) (hm : 0 < m) (h_gap_k : ∀ k, spectral_gap (H_k k) ≥ m) :
    spectral_gap H_inf_op ≥ m :=
  kato_lower_semicontinuity resolvent_convergence_limit hm h_gap_k
