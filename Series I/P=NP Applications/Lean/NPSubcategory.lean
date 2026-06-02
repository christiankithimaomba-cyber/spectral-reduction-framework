/- 
NPSubcategory.lean – Sous‑catégorie des objets NP.
-/

import SpecCategory

/-- Un objet NP : un objet spectral avec un vérificateur polynomial. -/
structure NPObject extends SpecObject where
  verifier : V → List Bool → Bool
  verifier_poly : ∃ p : ℕ → ℕ, ∀ x w, time_to_compute (verifier x w) (|x|+|w|) ≤ p (|x|)
  verifier_correct : ∀ x, (∃ w, verifier x w = true) ↔ (ψ x > 0.5)   -- simplifié

/-- Les morphismes entre objets NP sont ceux de Spec qui préservent la structure NP. -/
def NPMorphism (X Y : NPObject) := SpecMorphism X.toSpecObject Y.toSpecObject

-- La sous‑catégorie NP (pleine)
instance : Category NPObject where
  Hom := NPMorphism
  id X := ⟨SpecMorphism.id X.toSpecObject⟩
  comp f g := ⟨SpecMorphism.comp f.1 g.1⟩
