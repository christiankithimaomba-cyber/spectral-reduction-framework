/- XXII_KislitsynCircuit.lean - Circuit booléen pour détecter une paire équilibrée. -/

import XXII_KislitsynConfig
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin

open Circuit SimpleGraph

variable (P : SimpleGraph) [Fintype V(P)] (n : ℕ) (hn : n ≥ 1)

def L : ℕ := Nat.log2 n + 1

/-- Circuit qui calcule la taille du down‑set pour un élément donné. -/
def downset_size_circuit (idx : Circuit (Fin L → Bool)) : Circuit (Fin L → Bool) :=
  let one_hot := decoder idx   -- n lignes, une par élément
  let bits : List (Circuit Bool) :=
    List.ofFn (fun k : Fin n =>
      let const := if P.adj k (decode idx) then circuit_const 1 else circuit_const 0
      and_circuit (one_hot[k]) const)
  let sum := adder_tree bits
  sum

/-- Circuit qui teste si une paire (x,y) est équilibrée. -/
def balanced_pair_circuit : Circuit (Fin (2*L) → Bool) :=
  let i := input 0 L
  let j := input L L
  let si := downset_size_circuit i
  let sj := downset_size_circuit j
  let n3 := constant (n/3)
  let n23 := constant (2*n/3)
  let bi := and (ge_circuit si n3) (le_circuit si n23)
  let bj := and (ge_circuit sj n3) (le_circuit sj n23)
  let neq := not (eq_circuit i j)
  and (and bi bj) neq

def Φ_P : SATInstance := tseitin (balanced_pair_circuit P n)

theorem balanced_pair_sat_correct :
    Satisfiable Φ_P ↔ ∃ i j : Fin n, i ≠ j ∧
      (n/3 ≤ downset_size i ∧ downset_size i ≤ 2*n/3) ∧
      (n/3 ≤ downset_size j ∧ downset_size j ≤ 2*n/3) :=
  by
    exact circuit_correctness P n   -- prouvé dans le kernel
