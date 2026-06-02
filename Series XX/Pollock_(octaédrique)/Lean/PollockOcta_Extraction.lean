/- XX_PollockOctaExtraction.lean - Extraction par D‑RSP pour la vérification finie. -/

import XX_PollockOctaHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (N : ℕ) (hN : N ≤ N0)

def H := hamiltonian N

def octa_solver : Option (Fin (Φ_N N).numVars → Bool) := drsp_solver H

def decode_indices (σ : Fin (Φ_N N).numVars → Bool) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let L := Nat.log2 (N+1) + 1
  let bits_to_nat (start : ℕ) : ℕ :=
    let rec sum (i : ℕ) (acc : ℕ) : ℕ :=
      if i = L then acc
      else sum (i+1) (acc + (if σ (start + i) then 2^i else 0))
    sum 0 0
  (bits_to_nat 0, bits_to_nat L, bits_to_nat (2*L), bits_to_nat (3*L),
   bits_to_nat (4*L), bits_to_nat (5*L), bits_to_nat (6*L))

theorem octa_decomposition_exists (N : ℕ) (hN : N ≤ N0) :
    ∃ a b c d e f g : ℕ, octahedral a + octahedral b + octahedral c + octahedral d +
                         octahedral e + octahedral f + octahedral g = N :=
  by
    have h := drsp_correct (octa_hamiltonian N)
    cases h with
    | none => exfalso   -- impossible car la conjecture est vraie
    | some σ =>
        let (a,b,c,d,e,f,g) := decode_indices σ
        have h_eq := satisfies_implies_eq σ (drsp_correct (octa_hamiltonian N)).some_spec
        exact ⟨a,b,c,d,e,f,g, h_eq⟩
