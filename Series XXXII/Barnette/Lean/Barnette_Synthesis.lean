/-
BarnetteSynthesis.lean – Final theorem: Barnette's conjecture is true.
Author: Christian Kithima
ORCID: 0009-0003-3829-8519
GitHub: https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/tree/main/Kernel
-/

import .BarnetteExtraction

open SimpleGraph

theorem barnette_conjecture (G : SimpleGraph V) [Fintype V] [DecidableEq V] (hG : barnette_graph G) :
    hamiltonian_cycle G :=
  by
    let n := Fintype.card V
    by_cases h : n ≤ 200
    · exact barnette_for_small_graphs G hG h
    · have h_size : n > 200 := by linarith
      exact barnette_for_large_graphs G hG h_size
