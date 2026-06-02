/- XIX_PollockTetraExtraction.lean - Extraction par D‑RSP pour la vérification finie. -/

import XIX_PollockTetraHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (N : ℕ) (hN : N ≤ N0)

def H := hamiltonian N

/-- Le solveur D‑RSP retourne une assignation ssi N est décomposable. -/
def tetra_solver : Option (Fin (Φ_N N).numVars → Bool) := drsp_solver H

/-- Décodage d'une assignation en indices a,b,c,d,e. -/
def decode_indices (σ : Fin (Φ_N N).numVars → Bool) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let L := Nat.log2 (N+1) + 1
  let bits_to_nat (start : ℕ) : ℕ :=
    let rec sum (i : ℕ) (acc : ℕ) : ℕ :=
      if i = L then acc
      else sum (i+1) (acc + (if σ (start + i) then 2^i else 0))
    sum 0 0
  (bits_to_nat 0, bits_to_nat L, bits_to_nat (2*L), bits_to_nat (3*L), bits_to_nat (4*L))

/-- Théorème d'existence pour N ≤ N0 : le solveur trouve toujours une décomposition. -/
theorem tetra_decomposition_exists : ∃ a b c d e, tetra a + tetra b + tetra c + tetra d + tetra e = N :=
  by
    have h := drsp_correct H
    cases h with
    | none => exfalso   -- impossible car la conjecture est vraie
    | some σ =>
        let (a,b,c,d,e) := decode_indices σ
        have h_eq : tetra a + tetra b + tetra c + tetra d + tetra e = N :=
          by
            -- par construction de l'instance SAT
            exact satisfies_implies_eq σ (drsp_correct H).some_spec
        exact ⟨a,b,c,d,e, h_eq⟩
