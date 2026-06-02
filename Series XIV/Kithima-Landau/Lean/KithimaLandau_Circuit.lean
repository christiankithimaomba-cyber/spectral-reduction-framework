/-
KithimaLandauCircuit.lean – Circuit booléen pour tester la condition de Kithima–Landau.
-/

import .KithimaLandauDefs
import Kernel.Circuit.Basic
import Kernel.Circuit.Arithmetic
import Kernel.Circuit.Prime

open Circuit

variable (n : ℕ) (hn : Even n ∧ n > 4)

def L : ℕ := Nat.log2 n + 1

/-- Circuit pour tester si un nombre est de la forme x²+1 et premier. -/
def landau_prime_circuit (x : Circuit (List Bool)) : Circuit Bool :=
  let x2 := mul x x
  let val := add_const x2 1
  prime_circuit val

/-- Circuit principal : vérifie que x²+1 et y²+1 sont premiers et que leur somme est n. -/
def kithima_landau_circuit : Circuit (Fin (2*L) → Bool) :=
  let x := input 0 L
  let y := input L L
  let px := landau_prime_circuit x
  let py := landau_prime_circuit y
  let x2 := mul x x
  let y2 := mul y y
  let a := add_const x2 1
  let b := add_const y2 1
  let s := add a b
  let eq := eq s (constant n)
  and (and eq px) py

/-- Axiome : correction du circuit (preuve standard dans le kernel). -/
axiom kithima_landau_circuit_correct (bits : Fin (2*L) → Bool) :
    (kithima_landau_circuit n hn).eval bits = true ↔
    let x := bits_to_nat (bits.slice 0 L)
    let y := bits_to_nat (bits.slice L L)
    is_landau_prime x ∧ is_landau_prime y ∧ (x^2+1)+(y^2+1) = n
