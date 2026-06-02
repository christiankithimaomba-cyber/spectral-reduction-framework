/- XXIII_PillaiCircuit.lean - Circuit booléen pour tester l'équation de Pillai. -/

import XXIII_PillaiConfig
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin

open Circuit

variable (k : ℤ) (B : ℕ) (hB : B = B k)

def L : ℕ := Nat.log2 B + 1

/-- Circuit de multiplication de deux nombres L-bit (produit jusqu'à 2L bits). -/
def mul_circuit : Circuit (List Bool) → Circuit (List Bool) → Circuit (List Bool) :=
  Kernel.Arithmetic.mul

/-- Circuit d'exponentiation par un exposant constant (déroulé pour l'exposant codé en binaire). -/
def pow_circuit (base : Circuit (List Bool)) (exp_bits : List Bool) : Circuit (List Bool) :=
  let rec loop (acc : Circuit (List Bool)) (bits : List Bool) : Circuit (List Bool) :=
    match bits with
    | [] => acc
    | b :: rest =>
        let acc_sq := mul_circuit acc acc
        if b then
          let new_acc := mul_circuit base acc_sq
          loop new_acc rest
        else
          loop acc_sq rest
  loop (constant 1) exp_bits

/-- Circuit principal : prend les bits de x, y, m, n et teste x^m - y^n = k. -/
def pillai_circuit : Circuit (Fin (4*L) → Bool) :=
  let x := input 0 L
  let y := input L L
  let m_bits := input (2*L) L   -- bits de l'exposant m
  let n_bits := input (3*L) L
  let x_pow := pow_circuit x (List.ofFn (fun i => m_bits i))
  let y_pow := pow_circuit y (List.ofFn (fun i => n_bits i))
  let diff := sub x_pow y_pow
  let eq := eq diff (constant k)
  let x_ge2 := ge x (constant 2)
  let y_ge2 := ge y (constant 2)
  let m_val := bits_to_nat (List.ofFn (fun i => m_bits i))
  let n_val := bits_to_nat (List.ofFn (fun i => n_bits i))
  let m_ge3 := ge (constant m_val) (constant 3)
  let n_ge3 := ge (constant n_val) (constant 3)
  let cond := and (and x_ge2 y_ge2) (and m_ge3 n_ge3)
  and eq cond

def Φ_k : SATInstance := tseitin (pillai_circuit k (B k))

theorem pillai_sat_correct :
    Satisfiable Φ_k ↔ ∃ x y m n : ℕ,
      x ≤ B k ∧ y ≤ B k ∧ m ≤ B k ∧ n ≤ B k ∧
      x ≥ 2 ∧ y ≥ 2 ∧ m ≥ 3 ∧ n ≥ 3 ∧
      (x : ℤ)^m - (y : ℤ)^n = k :=
  by
    -- Preuve par correction du circuit et Tseitin (prouvée dans le kernel)
    exact pillai_circuit_correctness k (B k) (by rfl)
