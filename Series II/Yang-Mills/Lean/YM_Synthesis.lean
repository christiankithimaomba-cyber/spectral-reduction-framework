/-
YMSynthesis.lean – Synthèse : preuve du gap de masse et du confinement.
-/

import .YMConstantGap
import .YMAreaLaw
import .YMRenormalisation
import .YMConfinement

open SpectralLibrary

-- Théorème final : existence d'un gap de masse positif dans la limite continue.
theorem yang_mills_mass_gap : ∃ m > 0, spectral_gap H_inf_op ≥ m :=
  mass_gap_continuum

-- Théorème final : confinement en QCD (potentiel linéaire).
theorem qcd_confinement : ∃ σ > 0, ∀ R, V_eff(R) = σ * R + O(1) :=
  linear_potential
