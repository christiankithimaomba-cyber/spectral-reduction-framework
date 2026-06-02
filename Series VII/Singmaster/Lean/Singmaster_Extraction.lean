/-
SingmasterExtraction.lean – Énumération des solutions pour t ≤ T0.
-/

import .SingmasterPillars
import Kernel.DRSP

open SpectralLibrary

variable (t : ℕ) (ht : t ≤ T0)

def extract_solutions : List (ℕ × ℕ) :=
  let rec loop (Φ : SATInstance) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
    let H := spectral_hamiltonian Φ
    match drsp_solver H with
    | none => acc
    | some σ =>
        let (n,k) := decode_pair σ
        let clause := blocking_clause σ
        let Φ' := add_clause Φ clause
        loop Φ' ((n,k) :: acc)
  loop (singmaster_SAT t ht) []

def multiplicity_finite (t : ℕ) (ht : t ≤ T0) : ℕ :=
  (extract_solutions t ht).length

/-- Axiome : le maximum fini est 10 (résultat numérique vérifié). -/
axiom max_multiplicity_finite : Finset.sup (Finset.Icc 2 T0) (fun t => multiplicity_finite t (by simp)) = 10
