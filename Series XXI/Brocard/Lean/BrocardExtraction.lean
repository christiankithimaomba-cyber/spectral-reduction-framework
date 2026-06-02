/- XVII_BrocardExtraction.lean - Extraction par D‑RSP pour la vérification finie. -/

import XVII_BrocardHamiltonian
import Kernel.DRSP

open SpectralLibrary

variable (n : ℕ) (hn : n ≤ N0)

def H := brocard_hamiltonian n

def brocard_solver : Option (Fin (Φ_n n).numVars → Bool) := drsp_solver H

/-- Convertit une liste de bits (MSB en tête) en entier. -/
def bits_to_nat (bits : List Bool) : ℕ :=
  bits.foldl (fun acc b => (acc * 2) + (if b then 1 else 0)) 0

/-- Décodage des bits d'entrée m à partir de l'affectation σ.
    On suppose que les premiers `L` bits de σ correspondent aux bits de m. -/
def decode_m (σ : Fin (Φ_n n).numVars → Bool) : ℕ :=
  let C := n! + 1
  let M := Nat.sqrt C
  let L := Nat.log2 (M + 1) + 1
  let bits := List.ofFn (fun i : Fin L => σ i)
  bits_to_nat bits

/-- Le solveur retourne une affectation ssi n!+1 est un carré parfait, et alors l'affectation
    décodée donne la racine carrée. -/
theorem brocard_decomposition_exists (n : ℕ) (hn : n ≤ N0) :
    (∃ m : ℕ, m^2 = n! + 1) ↔
    let σ := brocard_solver n hn
    σ.isSome ∧ (decode_m σ.get)^2 = n! + 1 :=
  by
    have h := drsp_correct (brocard_hamiltonian n hn)
    rw [← sat_iff_solver_nonempty] at h
    exact h
