/- XVII_BrocardCircuit.lean - Circuit booléen pour tester l'équation de Brocard. -/

import XVII_BrocardConfig
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin

open Circuit

variable (n : ℕ) (hn : n ≤ N0)

/-- Valeur de n!+1 (constante précalculée). -/
def C : ℕ := n! + 1

/-- Borne supérieure pour m : m ≤ √(n!+1). -/
def M : ℕ := Nat.sqrt C   -- floor sqrt; si C est un carré parfait, M = √C

/-- Nombre de bits pour représenter m. -/
def L : ℕ := Nat.log2 (M+1) + 1

/-- Circuit principal : prend les bits de m et teste m² = C. -/
def brocard_circuit : Circuit (Fin L → Bool) :=
  let m := input 0 L
  let m2 := mul m m
  eq m2 (constant C)

/-- Instance SAT via Tseitin. -/
def Φ_n : SATInstance := tseitin (brocard_circuit n)

/-- Correction : Φ_n est satisfiable ssi n!+1 est un carré parfait. -/
theorem brocard_sat_correct :
    Satisfiable Φ_n ↔ ∃ m : ℕ, m^2 = n! + 1 :=
  by
    -- La preuve utilise la correction du circuit de multiplication et de l'égalité.
    exact brocard_circuit_correctness n   -- prouvé dans le kernel
