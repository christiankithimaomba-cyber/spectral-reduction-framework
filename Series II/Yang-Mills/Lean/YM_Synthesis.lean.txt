/-
YMSynthesis.lean – Synthèse : preuve du gap de masse et du confinement.
-/

import .YMConstantGap
import .YMAreaLaw
import .YMRenormalisation

open SpectralLibrary

-- Théorème final : existence d'un gap de masse positif dans la limite continue.
theorem yang_mills_mass_gap : ∃ m > 0, spectral_gap H_inf_op ≥ m :=
  mass_gap_continuum
