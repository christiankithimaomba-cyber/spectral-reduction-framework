/- 
SpecCategory.lean – Définition de la catégorie Spec.
-/

import Mathlib.CategoryTheory.Category.Basic
import Kernel.SpectralLibrary

open CategoryTheory

/-- Un objet de la catégorie Spec : un triple spectral (Ω, H, ψ) satisfaisant les propriétés spectrales. -/
structure SpecObject where
  V : Type*
  [Fintype V] [DecidableEq V]
  H : Matrix V V ℝ
  ψ : V → ℝ
  ψ_pos : ∀ x, ψ x > 0
  ψ_norm : ∑ x, ψ x ^ 2 = 1
  ψ_eig : H *ᵥ ψ = (λ_min H) • ψ
  conductance_bound : conductance H ≥ 1 / (2 * Fintype.card V)
  gap_bound : spectral_gap H ≥ 1 / (8 * (Fintype.card V)^2)

/-- Un morphisme dans Spec : une fonction (pas nécessairement polynomiale pour la catégorie abstraite). -/
structure SpecMorphism (X Y : SpecObject) where
  toFun : X.V → Y.V
  gap_pres : Y.gap_bound ≥ X.gap_bound
  compat : ∀ x, Y.ψ (toFun x) ≥ X.ψ x / 2

def id_spec (X : SpecObject) : SpecMorphism X X where
  toFun := id
  gap_pres := by rfl
  compat := by simp

def comp_spec {X Y Z : SpecObject} (f : SpecMorphism X Y) (g : SpecMorphism Y Z) :
    SpecMorphism X Z where
  toFun := g.toFun ∘ f.toFun
  gap_pres := le_trans f.gap_pres g.gap_pres
  compat := by
    intro x
    have h1 := f.compat x
    have h2 := g.compat (f.toFun x)
    linarith

instance : Category SpecObject where
  Hom := SpecMorphism
  id X := id_spec X
  comp f g := comp_spec f g
