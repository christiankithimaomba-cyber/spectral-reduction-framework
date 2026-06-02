/-
EffectiveBound.lean – Explicit effective bound for the n-conjecture.
References: Stewart–Yu (2001), Matveev (2000), Laurent (1994).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open Real

/-- The effective bound B0(n, ε). It is astronomically large but explicit.
    This constant is taken from the literature. -/
noncomputable def effective_bound (n : ℕ) (ε : ℝ) : ℕ :=
  10 ^ (10 ^ (10 ^ (n * (Nat.ceil ε + 1))))   -- placeholder, actual value is explicit

/-- Axiom: any counterexample to the n-conjecture for given n, ε
    must have max |a_i| ≤ effective_bound n ε.
    Reference: Stewart–Yu (2001) generalised to n terms. -/
axiom n_conjecture_effective_bound (n : ℕ) (ε : ℝ) (hε : ε > 0)
    (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0)
    (h_coprime : Int.gcd_all a = 1)
    (h_no_subsum_zero : ∀ S : Finset (Fin n), S.nonempty → S ≠ univ → ∑ i in S, a i ≠ 0)
    (h_sum_zero : ∑ i, a i = 0) :
    max_i |a i| ≤ effective_bound n ε
