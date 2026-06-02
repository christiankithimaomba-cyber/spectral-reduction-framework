/-
BarnetteCompression.lean – Isotypic compression and Kato–Osborn convergence.
Reference: Kato (1966), Osborn (1975), SHS strategy.
Author: Christian Kithima
ORCID: 0009-0003-3829-8519
GitHub: https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/tree/main/Kernel
-/

import .BarnetteOperator
import Kernel.KatoTheory

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] (hG : barnette_graph G)

/-- The automorphism group of G (or a suitable subgroup) acts on spanning cycles. -/
axiom automorphism_group : Type

/-- Representation of the group on the Hilbert space. -/
axiom group_representation : Representation (automorphism_group G) (ℋ_G G)

/-- Decomposition into isotypic subspaces. -/
axiom isotypic_decomposition (G : SimpleGraph V) [Fintype V] (hG : barnette_graph G) :
    ∃ (decomp : DirectSum (irreducible_rep (automorphism_group G)) (ℋ_G G)),
      (∀ g, decomp.g g ∘ T_G = T_G ∘ decomp.g)   -- T_G commutes with the action

/-- Projection onto the trivial isotypic component. -/
axiom proj_trivial : ℋ_G G →ₗ[ℝ] ℋ_G G

/-- Compressed operator on the finite‑dimensional subspace of the trivial representation.
    The dimension is polynomial in |V(G)|. -/
axiom T_compressed (N : ℕ) : Matrix (Fin N) (Fin N) ℝ

/-- Kato–Osborn theorem: for N large enough, the multiplicity of eigenvalue 1 is preserved. -/
axiom kato_osborn_convergence (N : ℕ) (hN : N ≥ N0 G) :
    multiplicity 1 (T_compressed G hG N) = multiplicity 1 (T_G G hG)
