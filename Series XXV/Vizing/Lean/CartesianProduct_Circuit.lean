/-
CartesianProductCircuit.lean – Circuit that tests whether a subset D of V(G□H)
is a dominating set with |D| < γ(G)*γ(H).
-/

import .VizingDefs
import .DominationCircuit
import Kernel.Circuit.Basic
import Kernel.Circuit.Arithmetic
import Kernel.Circuit.Comparison
import Kernel.Tseitin

open Circuit SimpleGraph

variable (G H : SimpleGraph) [Fintype V(G)] [Fintype V(H)] [DecidableRel G.Adj] [DecidableRel H.Adj]

def nG : ℕ := Fintype.card V(G)
def nH : ℕ := Fintype.card V(H)
def N : ℕ := nG * nH

/-- Circuit for Vizing counterexample condition.
    Input: N bits (one per vertex of the product) encoding a subset D.
    Output: 1 iff D is dominating and |D| < γ(G)*γ(H). -/
def vizing_circuit : Circuit (Fin N → Bool) :=
  let x := input_all N
  -- Build domination condition for product
  let dom_vertices : List (Circuit Bool) :=
    List.ofFn (fun (i : Fin nG) =>
      List.ofFn (fun (j : Fin nH) =>
        let idx := i.val * nH + j.val
        let inD := x idx
        let neigh_G : List (Circuit Bool) :=
          List.ofFn (fun i' => if G.Adj i.val i'.val then x (i'.val * nH + j.val) else constant false)
        let neigh_H : List (Circuit Bool) :=
          List.ofFn (fun j' => if H.Adj j.val j'.val then x (i.val * nH + j'.val) else constant false)
        let all_neigh := (inD :: neigh_G) ++ neigh_H
        let or_all := all_neigh.foldl or_circuit (constant false)
        or_all))
  let dom := (dom_vertices.flatten).foldl and_circuit (constant true)
  -- Size of D
  let size := Arithmetic.add_list (List.ofFn x)
  -- Precomputed domination numbers
  let γG : ℕ := domination_number G
  let γH : ℕ := domination_number H
  let product := γG * γH
  let size_lt_product := Comparison.lt size (constant product)
  and_circuit dom size_lt_product

/-- Correctness theorem (admitted, standard). -/
axiom vizing_circuit_correct (bits : Fin N → Bool) :
    (vizing_circuit G H).eval bits = true ↔
    let D := Finset.filter (fun (i : Fin N) => bits i) Finset.univ
    dominates (cartesian_product G H) D ∧ D.card < domination_number G * domination_number H
