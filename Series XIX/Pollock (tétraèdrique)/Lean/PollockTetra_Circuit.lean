/- XIX_PollockTetraCircuit.lean - Circuit booléen pour tester une décomposition en cinq tétraédriques. -/

import XIX_PollockTetraConfig
import Circuit.Basic
import Circuit.Arithmetic

open Circuit

variable (N : ℕ) (hN : N ≤ N0)

def L : ℕ := Nat.log2 (N+1) + 1   -- nombre de bits pour les indices (car tetra n ≤ N ⇒ n ≤ N)

/-- Circuit pour le nombre tétraédrique d'un indice donné. -/
def tetra_circuit (x : Circuit (List Bool)) : Circuit (List Bool) :=
  let x1 := add_const x 1
  let x2 := add_const x 2
  let p1 := mul x x1
  let p2 := mul p1 x2
  div_const p2 6

/-- Circuit qui prend cinq indices et teste si la somme des tétraédriques égale N. -/
def tetra_decomp_circuit : Circuit (Fin (5*L) → Bool) :=
  let a := input 0 L
  let b := input L L
  let c := input (2*L) L
  let d := input (3*L) L
  let e := input (4*L) L
  let ta := tetra_circuit a
  let tb := tetra_circuit b
  let tc := tetra_circuit c
  let td := tetra_circuit d
  let te := tetra_circuit e
  let sum := add (add (add (add ta tb) tc) td) te
  eq sum (constant N)
