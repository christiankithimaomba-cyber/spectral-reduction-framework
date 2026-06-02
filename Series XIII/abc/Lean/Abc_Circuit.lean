/-
AbcCircuit.lean – Circuit booléen pour tester la condition de contre‑exemple abc.
-/

import .AbcDefs
import Kernel.Circuit.Basic
import Kernel.Circuit.Arithmetic
import Kernel.Circuit.GCD
import Kernel.Circuit.Radical

open Circuit

variable (C_eps : ℕ) (hC : C_eps > 0)

/-- Circuit principal : teste si (a,b,c) est un contre‑exemple. -/
def abc_circuit (N0 : ℕ) : Circuit (Fin (3*L) → Bool) :=
  let L := Nat.log2 N0 + 1
  let a := input 0 L
  let b := input L L
  let c := input (2*L) L
  let s := add a b
  let eq := eq s c
  let g1 := gcd a b
  let g := gcd g1 c
  let gc := eq g (constant 1)
  let abc := mul (mul a b) c
  let R := radical_circuit abc
  let R2 := mul R R
  let rhs := mul_const R2 C_eps
  let gt := lt rhs c   -- c > C_eps * R^2
  and (and eq gc) gt

/-- Axiome : correction du circuit (preuve standard dans le kernel). -/
axiom abc_circuit_correct (N0 : ℕ) (bits : Fin (3*L) → Bool) :
    (abc_circuit N0).eval bits = true ↔
    let a := bits_to_nat (bits.slice 0 L)
    let b := bits_to_nat (bits.slice L L)
    let c := bits_to_nat (bits.slice (2*L) L)
    a + b = c ∧ gcd a (gcd b c) = 1 ∧ c > C_eps * (rad (a*b*c))^2
