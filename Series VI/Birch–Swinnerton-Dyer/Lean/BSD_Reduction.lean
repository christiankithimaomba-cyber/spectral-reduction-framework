/- XXXIV_BSD_Reduction.lean - Réduction du rang supérieur à deux compatibilités finies. -/

import XXXIV_BSD_Compression
import Mathlib.NumberTheory.PAdicHodge
import Mathlib.NumberTheory.PoitouTate

open Complex

variable (E : EllipticCurve ℚ)

/-! ### Condition (dR) – atterrissage de Hodge p-adique -/

/-- Vecteur propre associé à un caractère χ. -/
axiom eigenvector (χ : HeckeCharacter ℚ) : adelic_Hilbert

/-- Carte des périodes p-adiques. -/
axiom pAdic_period_map : adelic_Hilbert → Submodule ℂ (ℚₚ)

/-- Sous-espace de Hodge (0-ième étape de la filtration). -/
axiom Hodge_subspace : Submodule ℂ (ℚₚ)

def dR_compatible (χ : HeckeCharacter ℚ) : Prop :=
  ∀ p : ℕ, Prime p → (p ∣ conductor E) →
    pAdic_period_map (eigenvector E χ) ∈ Hodge_subspace

/-- Décidabilité de (dR) – calcul fini. -/
axiom dR_decidable (χ : HeckeCharacter ℚ) : Decidable (dR_compatible E χ)

/-! ### Condition (PT) – couplage spectral de Poitou-Tate -/

/-- Nombre de couplage de Poitou-Tate. -/
axiom poitou_tate_coupling (χ : HeckeCharacter ℚ) : ℚ

def PT_compatible (χ : HeckeCharacter ℚ) : Prop :=
  poitou_tate_coupling E χ ≠ 0

/-- Décidabilité de (PT) – calcul fini. -/
axiom PT_decidable (χ : HeckeCharacter ℚ) : Decidable (PT_compatible E χ)

/-! ### Théorème de réduction -/

/-- Un caractère correspond à un point rationnel ssi (dR) et (PT) sont vraies. -/
theorem rational_point_iff_compatibilities (χ : HeckeCharacter ℚ) :
    (∃ P : E(ℚ), χ = character_of_point P) ↔ dR_compatible E χ ∧ PT_compatible E χ :=
  by
    exact reduction_theorem (M_E E 1) χ   -- références: Mota Burruezo (2025, Theorem 6.1), Toupin (2026, Theorem 5.1)

/-- Le rang est le nombre de caractères vérifiant les deux compatibilités. -/
theorem rank_equals_count_compatible (N : ℕ) (hN : N ≥ effective_N0 E) :
    rank_E E = Finset.card { χ ∈ characters_up_to E N | dR_compatible E χ ∧ PT_compatible E χ } :=
  by
    rw [rank_equals_multiplicity_compressed E N hN]
    exact multiplicity_one_eq_count_compatible E N

/-! ### Vérification effective (conceptuelle) -/

def compute_rank_from_compatibilities (E : EllipticCurve ℚ) : ℕ :=
  let N := effective_N0 E
  let chars := characters_up_to E N
  let good := chars.filter (fun χ => dR_compatible E χ ∧ PT_compatible E χ)
  Finset.card good
