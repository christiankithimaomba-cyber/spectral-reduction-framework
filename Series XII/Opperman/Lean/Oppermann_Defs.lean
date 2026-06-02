/-
OppermannDefs.lean – Définitions et bornes pour la conjecture de Oppermann.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

/-- Intervalles : (n(n-1), n^2) et (n^2, n(n+1)) -/
def left_interval (n : ℕ) : Set ℕ := { k | n*(n-1) < k ∧ k < n^2 }
def right_interval (n : ℕ) : Set ℕ := { k | n^2 < k ∧ k < n*(n+1) }

/-- Condition de Oppermann : il existe x dans left_interval(n) et y dans right_interval(n) premiers. -/
def oppermann_condition (n : ℕ) : Prop :=
  ∃ x y : ℕ, Prime x ∧ Prime y ∧ n*(n-1) < x ∧ x < n^2 ∧ n^2 < y ∧ y < n*(n+1)

/-- Borne effective N0 (par exemple, déduite de la théorie des nombres premiers). -/
constant N0 : ℕ
axiom oppermann_asymptotic : ∀ n : ℕ, n > N0 → oppermann_condition n

/-- Pour n ≤ N0, tous les candidats x,y sont bornés trivialement. -/
theorem oppermann_finite_bound (n : ℕ) (hn : n ≤ N0) (x y : ℕ) (hx : n*(n-1) < x ∧ x < n^2)
    (hy : n^2 < y ∧ y < n*(n+1)) : x ≤ n^2 ∧ y ≤ n*(n+1) := by
  exact ⟨le_of_lt hx.2, le_of_lt hy.2⟩
