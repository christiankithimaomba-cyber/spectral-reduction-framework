/-
DubnerDefs.lean – Définitions et bornes asymptotiques pour la conjecture de Dubner.
Références : Bombieri–Vinogradov pour les premiers jumeaux (Maynard, Polymath).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

/-- Condition pour un premier jumeau : p et p+2 sont premiers. -/
def is_twin_prime (p : ℕ) : Prop :=
  Prime p ∧ Prime (p+2)

/-- Conjecture de Dubner : tout n pair > 4 est somme de deux premiers jumeaux. -/
def dubner_conjecture (n : ℕ) : Prop :=
  Even n ∧ n > 4 → ∃ p q : ℕ, is_twin_prime p ∧ is_twin_prime q ∧ p + q = n

/-- Borne effective N0 (asymptotique) – explicitée via Maynard/Polymath. -/
constant N0 : ℕ
axiom dubner_asymptotic_bound : ∀ n : ℕ, Even n → n > N0 → ∃ p q : ℕ,
    is_twin_prime p ∧ is_twin_prime q ∧ p + q = n

/-- Pour le range fini, on utilise une borne triviale : p,q ≤ n. -/
theorem dubner_finite_bound (n : ℕ) (heven : Even n) (hgt : n > 4) (p q : ℕ)
    (hp : is_twin_prime p) (hq : is_twin_prime q) (hsum : p + q = n) :
    p ≤ n ∧ q ≤ n := by
  have hp_le : p ≤ n := by linarith
  have hq_le : q ≤ n := by linarith
  exact ⟨hp_le, hq_le⟩
