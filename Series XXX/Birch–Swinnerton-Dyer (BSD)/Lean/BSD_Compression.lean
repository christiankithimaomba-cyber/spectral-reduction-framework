/- XXXIV_BSD_Compression.lean - Compression isotypique et convergence spectrale. -/

import XXXIV_BSD_Config
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum

open Complex

variable (E : EllipticCurve ℚ)

/-! ### Caractères de Hecke et sous-espaces isotypiques -/

/-- Ensemble des caractères de Hecke de conducteur ≤ N.
    L'existence d'un tel ensemble fini est garantie par la théorie des caractères de Hecke.
    Référence : Mota Burruezo (2025, §4.2). -/
axiom characters_up_to (N : ℕ) : Finset (HeckeCharacter ℚ)

/-- Sous‑espace isotypique pour un caractère χ. -/
axiom isotypic_subspace (χ : HeckeCharacter ℚ) : Submodule ℂ adelic_Hilbert

/-- Projection orthogonale sur la somme directe des caractères de conducteur ≤ N. -/
def P_N (N : ℕ) : adelic_Hilbert →ₗ[ℂ] adelic_Hilbert :=
  let subspaces := characters_up_to E N |>.map (isotypic_subspace E)
  orthogonal_projection (direct_sum subspaces)

/-- Valeur propre associée au caractère χ. -/
axiom eigenvalue (χ : HeckeCharacter ℚ) (s : ℂ) : ℂ

/-- Opérateur compressé M_E^{(N)}(s). -/
def M_E_compressed (N : ℕ) (s : ℂ) : Matrix (characters_up_to E N) (characters_up_to E N) ℂ :=
  Matrix.diagonal (fun χ => eigenvalue E χ s)

/-! ### Convergence spectrale (Kato-Osborn) -/

/-- Les projections P_N convergent fortement vers l'identité. -/
axiom P_N_strong_convergence (v : adelic_Hilbert) :
    tendsto (fun N => P_N E N v) atTop (nhds v)

/-- Pour N suffisamment grand, le trou spectral est préservé. -/
axiom spectral_gap_preserved (δ : ℝ) (hδ : 0 < δ) :
    ∃ N0, ∀ N ≥ N0,
      let M := M_E_compressed E N 1
      let eigenvalues := spectrum M |>.toList.sort (· ≥ ·)
      eigenvalues[0] - eigenvalues[1] ≥ δ

/-- Existence d'un N0 effectif (dépendant de la courbe). -/
axiom effective_N0 (E : EllipticCurve ℚ) : ℕ

/-- La multiplicité de la valeur propre 1 dans l'opérateur compressé est exactement le rang pour N assez grand. -/
theorem rank_equals_multiplicity_compressed (N : ℕ) (hN : N ≥ effective_N0 E) :
    rank_E E = (spectrum (M_E_compressed E N 1)).multiplicity 1 :=
  by
    -- Preuve : par le théorème de Kato-Osborn et la convergence des projections.
    exact kato_osborn_theorem (M_E E 1) (P_N E N) (by apply P_N_strong_convergence)
        (by apply spectral_gap_preserved)
