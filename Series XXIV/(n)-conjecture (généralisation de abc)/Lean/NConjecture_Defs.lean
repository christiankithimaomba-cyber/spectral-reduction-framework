/-
NConjectureDefs.lean – Basic definitions for the n-conjecture.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.ABC

open Int

/-- n-conjecture inequality: max |a_i| ≤ C * rad(∏ |a_i|)^(n-2+ε). -/
def n_conjecture_inequality (n : ℕ) (ε : ℝ) (C : ℝ) (a : Fin n → ℤ) : Prop :=
  max_i |a i| ≤ C * (rad (∏ i, |a i|)) ^ (n - 2 + ε)

/-- Predicate for a tuple being a counterexample for given n, ε. -/
def is_counterexample (n : ℕ) (ε : ℝ) (C : ℝ) (a : Fin n → ℤ) : Prop :=
  (∀ i, a i ≠ 0) ∧
  (Int.gcd_all a) = 1 ∧
  (∀ S : Finset (Fin n), S.nonempty → S ≠ univ → ∑ i in S, a i ≠ 0) ∧
  (∑ i, a i) = 0 ∧
  ¬ n_conjecture_inequality n ε C a

-- The constant C(n, ε) is taken from the effective bound theorem.
noncomputable def C_const (n : ℕ) (ε : ℝ) : ℝ := 2   -- placeholder; actual value is explicit
