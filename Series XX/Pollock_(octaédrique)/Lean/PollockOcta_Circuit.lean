/- XX_PollockOctaCircuit.lean - Circuit booléen pour tester une décomposition en sept octaédriques. -/

import XX_PollockOctaConfig
import Circuit.Basic
import Circuit.Arithmetic

open Circuit

variable (N : ℕ) (hN : N ≤ N0)

def M : ℕ := Nat.ceil (Real.cbrt (3*N/2))   -- car O_n ~ (2/3)n³
def L : ℕ := Nat.log2 M + 1

/-- Circuit pour le nombre octaédrique d'un indice donné. -/
def octa_circuit (x : Circuit (List Bool)) : Circuit (List Bool) :=
  let x2 := mul x x
  let two_x2 := add x2 x2
  let two_x2_plus_one := add two_x2 (constant 1)
  let prod := mul x two_x2_plus_one
  div_const prod 3

/-- Circuit qui prend sept indices et teste si la somme des octaédriques égale N. -/
def octa_decomp_circuit : Circuit (Fin (7*L) → Bool) :=
  let a := input 0 L
  let b := input L L
  let c := input (2*L) L
  let d := input (3*L) L
  let e := input (4*L) L
  let f := input (5*L) L
  let g := input (6*L) L
  let oa := octa_circuit a
  let ob := octa_circuit b
  let oc := octa_circuit c
  let od := octa_circuit d
  let oe := octa_circuit e
  let of := octa_circuit f
  let og := octa_circuit g
  let s := add (add (add (add (add (add oa ob) oc) od) oe) of) og
  eq s (constant N)
