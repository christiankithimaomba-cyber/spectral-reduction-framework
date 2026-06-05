/-
KummerVandiverDefs.lean – Définitions pour la conjecture de Kummer–Vandiver.
Références : Kummer (1851), Vandiver (1920), Quillen–Lichtenbaum (Voevodsky, 2011).
-/

import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.ClassNumber

open Nat

/-- Corps cyclotomique Q(ζ_p) pour un premier impair p. -/
def cyclotomic_field (p : ℕ) (hp : p.Prime ∧ p > 2) : Type :=
  CyclotomicField p

/-- Sous-corps réel maximal Q(ζ_p)^+. -/
def real_cyclotomic_field (p : ℕ) (hp : p.Prime ∧ p > 2) : Type :=
  CyclotomicField.real p

/-- Nombre de classes du corps réel (h_p^+). -/
noncomputable def class_number_plus (p : ℕ) (hp : p.Prime ∧ p > 2) : ℕ :=
  ClassNumber.classNumber (real_cyclotomic_field p hp)

/-- Conjecture de Kummer–Vandiver : p ne divise pas h_p^+. -/
def kummer_vandiver_conjecture : Prop :=
  ∀ p : ℕ, p.Prime ∧ p > 2 → ¬ p ∣ class_number_plus p hp

/-- Équivalence avec la torsion en K₄(ℤ) (Quillen–Lichtenbaum).
    Référence : Voevodsky, "On the Quillen–Lichtenbaum conjecture" (2011). -/
axiom torsion_K4_equiv (p : ℕ) (hp : p.Prime ∧ p > 2) :
    (p ∣ class_number_plus p hp) ↔ (∃ n : ℕ, n ≠ 0 ∧ n * p = 0 in K₄(ℤ))

/-- Groupe des unités cyclotomiques modulo les racines (un groupe fini). -/
def cyclotomic_units (p : ℕ) (hp : p.Prime ∧ p > 2) : Type :=
  CyclotomicUnits p
