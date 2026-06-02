import .YMHamiltonian
import Kernel.ClusterExpansion
import Kernel.BrandaoHorodecki
import Kernel.HilbertCurve
import Kernel.Renormalisation   -- ajout

-- ... (même code) ...

-- Au lieu de renormalisation_area_law (axiome), on l'utilise.
theorem log_area_law_YM : ∃ C > 0, ∀ B : Finset (Fin M),
    entanglement_entropy (reduced_density (ground_state_YM) B) ≤ C * Real.log M :=
  renormalisation_area_law (linear_area_law_YM) (hilbert_bound)
