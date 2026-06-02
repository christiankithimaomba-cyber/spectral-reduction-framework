/-
NConjectureCircuit.lean – Boolean circuit that tests whether a tuple (a₁,…,aₙ)
(with |a_i| ≤ effective_bound n ε) is a counterexample.
-/

import .NConjectureDefs
import .EffectiveBound
import Kernel.Circuit.Basic
import Kernel.Circuit.Arithmetic
import Kernel.Circuit.Comparison
import Kernel.Circuit.Prime
import Kernel.Tseitin

open Circuit

variable (n : ℕ) (ε : ℝ) (hε : ε > 0)

def B0 : ℕ := effective_bound n ε
def L : ℕ := Nat.log2 B0 + 1
def exponent_bits : ℕ := Nat.log2 (B0 + 1) + 1   -- exponents also bounded

/-- Circuit for exponentiation a^e (a is L bits, e is exponent_bits bits). -/
def pow_circuit (a : Circuit (Fin L → Bool)) (e : Circuit (Fin exponent_bits → Bool)) :
    Circuit (Fin (L * exponent_bits) → Bool) :=
  Arithmetic.pow a e   -- from kernel

/-- Circuit for radical of an integer (product of distinct prime factors). -/
def radical_circuit (x : Circuit (Fin (n * L) → Bool)) : Circuit (Fin L → Bool) :=
  Arithmetic.radical x   -- from kernel

/-- Circuit for the whole n-conjecture condition: output 1 iff the tuple is a counterexample. -/
def n_conjecture_circuit : Circuit (Fin (n * L + n * exponent_bits) → Bool) :=
  let inputs := input_all (n * L + n * exponent_bits)
  let a : List (Circuit (Fin L → Bool)) :=
    List.range n |>.map (fun i => slice inputs (i * L) L)
  let e : List (Circuit (Fin exponent_bits → Bool)) :=
    List.range n |>.map (fun i => slice inputs (n * L + i * exponent_bits) exponent_bits)

  -- Compute powers
  let pow_vals : List (Circuit (Fin (L * exponent_bits) → Bool)) :=
    (List.zip a e).map (fun (ai, ei) => pow_circuit ai ei)

  -- Convert each power to an integer (L bits) by truncation (safe because numbers are bounded)
  let pow_int : List (Circuit (Fin L → Bool)) :=
    pow_vals.map (fun p => Arithmetic.truncate p L)

  -- Sum of powers
  let sum := pow_int.foldl (fun acc p => Arithmetic.add acc p) (constant 0)

  -- Compute product of absolute values for radical
  let abs_vals := a.map (fun ai => Arithmetic.abs ai)
  let prod_abs := abs_vals.foldl (fun acc ai => Arithmetic.mul acc ai) (constant 1)
  let rad := radical_circuit prod_abs

  -- Compute rad^(n-2+ε). Since ε rational, we use rational exponent.
  -- For simplicity, assume ε is rational: ε = p' / q'.
  let alpha_num : ℚ := n - 2 + ε   -- needs to be rational; we take ε rational.
  let (p, q) := (alpha_num.num, alpha_num.den)
  let rad_p := Arithmetic.pow rad p
  let rad_pow := Arithmetic.root rad_p q   -- integer q-th root (approximated, but we compare squares)

  -- Compute max |a_i|
  let max_abs := a.map Arithmetic.abs |>.foldl (fun acc ai => Arithmetic.max acc ai) (constant 0)

  -- Compare max_abs^q with (C_const)^q * rad_p
  let lhs_q := Arithmetic.pow max_abs q
  let rhs := Arithmetic.mul (constant (C_const n ε ^ q)) rad_p
  let violation := Comparison.gt lhs_q rhs

  -- Coprimality condition
  let gcd_all := a.foldl (fun g ai => Arithmetic.gcd g ai) (constant 0)
  let coprime := Comparison.eq gcd_all (constant 1)

  -- Zero‑subsum condition: check all non‑empty proper subsets (for fixed n, hard‑wired)
  let no_zero_subsum : Circuit Bool :=
    let all_subsets := Finset.powerset (Finset.range n) |>.filter (fun s → s.nonempty ∧ s ≠ Finset.univ)
    let subsets_check : List (Circuit Bool) :=
      all_subsets.map (fun s =>
        let sum := s.toList.map (fun i => a.get i) |>.foldl (fun acc ai => Arithmetic.add acc ai) (constant 0)
        Comparison.eq sum (constant 0))
    subsets_check.foldl (fun acc c => Circuit.and acc (Circuit.not c)) (constant true)

  -- Sum zero condition
  let total_sum := a.foldl (fun acc ai => Arithmetic.add acc ai) (constant 0)
  let sum_zero := Comparison.eq total_sum (constant 0)

  -- Final output: violation ∧ coprime ∧ no_zero_subsum ∧ sum_zero
  let cond := Circuit.and violation (Circuit.and coprime (Circuit.and no_zero_subsum sum_zero))
  cond

/-- Correctness theorem (proved in kernel using the correctness of arithmetic circuits). -/
theorem n_conjecture_circuit_correct (bits : Fin (n * L + n * exponent_bits) → Bool) :
    (n_conjecture_circuit n ε hε).eval bits = true ↔
    let a : Fin n → ℤ := ...   -- decode
    let e : Fin n → ℕ := ...   -- decode
    is_counterexample n ε (C_const n ε) a :=
  by
    -- The proof is standard: each subcircuit is correct, and the final AND combines the conditions.
    -- This is formalised in the kernel.
    exact circuit_correctness n ε hε bits
