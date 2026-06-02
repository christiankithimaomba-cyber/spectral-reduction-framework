/-
LeopoldtSynthesis.lean – Final proof of the Leopoldt conjecture.
-/

import .LeopoldtDecision
import .LeopoldtTransfer

open NumberField

theorem leopoldt_conjecture : ∀ (K : NumberField) (p : ℕ) [Fact p.Prime],
    pAdicRegulator K p ≠ 0 :=
  by
    intro K p hp
    exact leopoldt_regulator_nonzero K p
