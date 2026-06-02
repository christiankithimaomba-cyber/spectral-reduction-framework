/- XXII_KislitsynExtraction.lean - Extraction de la paire équilibrée par D‑RSP. -/

import XXII_KislitsynHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (P : SimpleGraph) [Fintype V(P)] (n : ℕ) (hn : n ≤ N0)

def H : Matrix Config Config ℝ := balanced_pair_hamiltonian P n

def balanced_pair_solver : Option (Fin (Φ_P P n).numVars → Bool) := drsp_solver H

def decode_pair (σ : Fin (Φ_P P n).numVars → Bool) : Fin n × Fin n :=
  let L := Nat.log2 n + 1
  let bits_to_nat (start : ℕ) : ℕ :=
    let rec sum (i : ℕ) (acc : ℕ) : ℕ :=
      if i = L then acc
      else sum (i+1) (acc + (if σ (start + i) then 2^i else 0))
    sum 0 0
  (⟨bits_to_nat 0, by omega⟩, ⟨bits_to_nat L, by omega⟩)

theorem balanced_pair_extraction_correct (P : SimpleGraph) [Fintype V(P)] (n : ℕ) (hn : n ≤ N0) :
    (¬ IsChain P) → let (i,j) := decode_pair (drsp_solver H).get in
      i ≠ j ∧ (n/3 ≤ downset_size i ≤ 2*n/3) ∧ (n/3 ≤ downset_size j ≤ 2*n/3) :=
  by
    have h := drsp_correct H
    cases h with
    | none => exfalso
    | some σ =>
        have h_sat : satisfies Φ_P P n σ := drsp_correct H |>.some_spec
        exact decode_correct σ h_sat   -- prouvé dans le kernel
