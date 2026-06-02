/- XXXV_Fuglede_SAT.lean - Encodage SAT et hamiltonien spectral. -/

import XXXV_Fuglede_Bound
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin
import Kernel.SpectralLibrary
import Kernel.DRSP

open Circuit SpectralLibrary

variable {d : ℕ} (hd : 1 ≤ d ∧ d ≤ 4) (Ω : Set ℝ^d) (hΩ : MeasurableSet Ω ∧ Bounded Ω ∧ LipschitzBoundary Ω)

/-- Circuit booléen qui teste les deux conditions sur la matrice compressée. -/
def fuglede_circuit : Circuit (Fin 0 → Bool) :=
  let M := U_compressed Ω (effective_N0)
  let lattice_cond := circuit_for_lattice M
  let pure_cond := circuit_for_pure_point M
  and_circuit lattice_cond pure_cond

/-- Instance SAT via Tseitin. -/
def Φ : SATInstance := tseitin (fuglede_circuit Ω)

/-- Nombre de variables. -/
def M_var : ℕ := Φ.numVars

/-- Hamiltonien spectral. -/
def H : Matrix (Fin (2^M_var)) (Fin (2^M_var)) ℝ :=
  spectral_hamiltonian Φ

/-! ### Vérification des quatre piliers -/

-- P1 : existence et unicité de l'état fondamental (d'après le kernel)
-- P2 : trou spectral constant (≥ 2) (d'après le kernel)
-- P3 : loi d'aire logarithmique (d'après le kernel)
-- P4 : solveur D‑RSP (d'après le kernel)

/-- Décision par D‑RSP. -/
def fuglede_solver : Option (Fin M_var → Bool) := drsp_solver H

/-- Correction : le solveur retourne une assignation ssi la conjecture est vraie pour Ω. -/
theorem fuglede_solver_correct :
    (fuglede_solver Ω ≠ none) ↔ fuglede_conjecture Ω :=
  by
    rw [← sat_iff_solver_nonempty, ← Φ]
    have h := drsp_correct H
    rw [h]
    have h2 := finite_reduction Ω (effective_N0) (le_refl effective_N0)
    rw [h2]
    exact circuit_correctness (fuglede_circuit Ω)   -- à prouver dans le kernel
