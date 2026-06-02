/- XVI_WilliamsonSAT.lean - Circuit booléen et instance SAT pour la condition de Williamson. -/

import XVI_WilliamsonConfig
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import Circuit.Basic
import Circuit.Arithmetic
import Tseitin

open Circuit

namespace SeriesXVI.Williamson

variable (m : ℕ) (hm : m ≥ 1)

def N := 4 * m^2

/-- Circuit pour tester la symétrie d’une matrice donnée (représentée par ses bits). -/
def symmetry_circuit (bits : Fin m → Fin m → Var) (name : String) : Circuit Bool :=
  let checks := List.ofFn (fun (p : Fin (m*m)) =>
    let i := p.val / m; let j := p.val % m;
    if i < j then
      let x := bits i j
      let y := bits j i
      eq_circuit (var_circuit x) (var_circuit y)
    else circuit_true)
  and_list checks

/-- Circuit pour le produit de deux matrices (entrées ±1). -/
def matrix_mul_circuit (A B : Fin m → Fin m → Var) (i j : Fin m) : Circuit (List Bool) :=
  let terms := List.range m |>.map (fun k =>
    let a := A i k; let b := B k j
    let xor := xor_circuit (var_circuit a) (var_circuit b)
    sub_const (constant 1) (mul_const xor 2))   -- produit = 1 - 2*(a xor b)
  sum_list terms

/-- Circuit pour tester la commutation de deux matrices. -/
def commute_circuit (A B : Fin m → Fin m → Var) : Circuit Bool :=
  let checks := List.ofFn (fun (p : Fin (m*m)) =>
    let i := p.val / m; let j := p.val % m;
    let left := matrix_mul_circuit A B i j
    let right := matrix_mul_circuit B A i j
    eq_circuit left right)
  and_list checks

/-- Circuit pour la condition quadratique A^2+B^2+C^2+D^2 = 4m I. -/
def quadratic_circuit (A B C D : Fin m → Fin m → Var) : Circuit Bool :=
  let checks := List.ofFn (fun (p : Fin (m*m)) =>
    let i := p.val / m; let j := p.val % m;
    if i = j then circuit_true else
      let termsA := List.range m |>.map (fun k =>
        let a1 := A i k; let a2 := A k j
        sub_const (constant 1) (mul_const (xor_circuit (var_circuit a1) (var_circuit a2)) 2))
      let termsB := List.range m |>.map (fun k =>
        let b1 := B i k; let b2 := B k j
        sub_const (constant 1) (mul_const (xor_circuit (var_circuit b1) (var_circuit b2)) 2))
      let termsC := List.range m |>.map (fun k =>
        let c1 := C i k; let c2 := C k j
        sub_const (constant 1) (mul_const (xor_circuit (var_circuit c1) (var_circuit c2)) 2))
      let termsD := List.range m |>.map (fun k =>
        let d1 := D i k; let d2 := D k j
        sub_const (constant 1) (mul_const (xor_circuit (var_circuit d1) (var_circuit d2)) 2))
      let sum := sum_list (termsA ++ termsB ++ termsC ++ termsD)
      eq_circuit sum (constant 0))
  and_list checks

/-- Circuit complet de Williamson. -/
def williamson_circuit : Circuit (Fin N → Bool) :=
  let vars : Fin m → Fin m → Var × Var × Var × Var := fun i j =>
    ( input (4*(i.val*m + j.val) + 0) 1,
      input (4*(i.val*m + j.val) + 1) 1,
      input (4*(i.val*m + j.val) + 2) 1,
      input (4*(i.val*m + j.val) + 3) 1 )
  let A i j := (vars i j).1; let B i j := (vars i j).2
  let C i j := (vars i j).3; let D i j := (vars i j).4
  let symA := symmetry_circuit A "A"
  let symB := symmetry_circuit B "B"
  let symC := symmetry_circuit C "C"
  let symD := symmetry_circuit D "D"
  let commAB := commute_circuit A B
  let commAC := commute_circuit A C
  let commAD := commute_circuit A D
  let commBC := commute_circuit B C
  let commBD := commute_circuit B D
  let commCD := commute_circuit C D
  let quad := quadratic_circuit A B C D
  let all := and_list [symA, symB, symC, symD, commAB, commAC, commAD, commBC, commBD, commCD, quad]
  all

/-- Instance SAT obtenue par Tseitin. -/
def Φ_m : SATInstance := tseitin (williamson_circuit m)

/-- Correction : Φ_m satisfiable ssi un ensemble de Williamson existe. -/
theorem williamson_sat_correct :
    Satisfiable Φ_m ↔ ∃ σ : Config m, is_williamson σ :=
  by
    -- La preuve utilise la correction du circuit et de Tseitin.
    exact williamson_circuit_correct m   -- prouvé dans le kernel
    done

end SeriesXVI.Williamson
