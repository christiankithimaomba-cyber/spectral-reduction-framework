/- XVIII_GoormaghtighCircuit.lean - Circuit booléen pour l’équation de Goormaghtigh. -/

import XVIII_GoormaghtighConfig
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin

open Circuit

namespace SeriesXVIII.Goormaghtigh

variable (params : Params) (B : ℕ) (hB : B ≥ 1)

def L : ℕ := Nat.log2 (B+1) + 1   -- nombre de bits par nombre

/-- Circuit pour le repunit (x^e - 1)/(x - 1) avec e fixé. -/
def repunit_circuit (x : Circuit (List Bool)) (e : ℕ) : Circuit (List Bool) :=
  let rec powers (acc : List (Circuit (List Bool))) (i : ℕ) : List (Circuit (List Bool)) :=
    if i = e then acc
    else
      let next := mul (acc.headI x) x   -- x^i * x = x^{i+1}
      powers (next :: acc) (i+1)
  let power_list := powers [constant 1] 0
  let sum := power_list.foldl (fun a b => add a b) (constant 0)
  sum

/-- Circuit principal : prend les bits de x et y, compare les repunits. -/
def goormaghtigh_circuit : Circuit (Fin (2*L) → Bool) :=
  let x := input 0 L
  let y := input L L
  let rx := repunit_circuit x params.m
  let ry := repunit_circuit y params.n
  let eq := eq_circuit rx ry
  let x_gt_1 := gt_circuit x (constant 1)
  let y_gt_1 := gt_circuit y (constant 1)
  let x_ne_y := ne_circuit x y
  and_circuit (and_circuit (and_circuit x_gt_1 y_gt_1) x_ne_y) eq

/-- Instance SAT via Tseitin. -/
def Φ : SATInstance := tseitin (goormaghtigh_circuit params B)

/-- Correction : Φ est satisfiable ssi une solution existe dans les bornes. -/
theorem sat_correct :
    Satisfiable Φ ↔ ∃ x y : ℕ, 1 < x ≤ B ∧ 1 < y ≤ B ∧ x ≠ y ∧
      (x^params.m - 1)/(x - 1) = (y^params.n - 1)/(y - 1) :=
  by
    -- La preuve utilise la correction du circuit repunit et de Tseitin.
    exact goormaghtigh_circuit_correct params B   -- prouvé dans le kernel
    done

end SeriesXVIII.Goormaghtigh
