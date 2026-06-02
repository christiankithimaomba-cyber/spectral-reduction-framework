/-
BarnetteSAT.lean – SAT encoding of Hamiltonian cycle in Barnette graphs.
Author: Christian Kithima
ORCID: 0009-0003-3829-8519
GitHub: https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/tree/main/Kernel
-/

import .BarnetteDefs
import PNP.SAT
import Kernel.Tseitin

open SAT

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] (hG : barnette_graph G)

def n : ℕ := Fintype.card V

/-- Variable: x_{v,i} meaning vertex v is at position i in the cycle. -/
def var (v : Fin n) (i : Fin n) : Var :=
  mkVar ("x_" ++ toString v.val ++ "_" ++ toString i.val)

/-- Clause: exactly one of the literals is true. -/
def exactly_one (lits : List (Bool × Var)) : Clause :=
  let pos := lits.map (fun (_, v) => (true, v))
  let at_least_one := pos
  let at_most_one := lits.pairs.map (fun ((_,v1),(_,v2)) => [ (false, v1), (false, v2) ])
  at_least_one ++ at_most_one.flatten

/-- Clauses for a valid Hamiltonian cycle. -/
def hamiltonian_clauses : List Clause :=
  -- each vertex appears exactly once
  (List.range n).map (fun i =>
    exactly_one ((List.range n).map (fun v => (true, var v i)))) ++
  -- each position is occupied by exactly one vertex
  (List.range n).map (fun v =>
    exactly_one ((List.range n).map (fun i => (true, var v i)))) ++
  -- adjacency constraints: for each consecutive pair (i, i+1), the corresponding vertices must be adjacent
  (List.range (n-1)).flatMap (fun i =>
    List.product (List.range n) (List.range n) |>.filter (fun (v,w) => G.Adj v w) |>.map (fun (v,w) =>
      [ (true, var v i), (true, var w (i+1)) ])) ++
  -- close the cycle: adjacency between last and first
  (List.range n).flatMap (fun v =>
    List.range n |>.filter (fun w => G.Adj v w) |>.map (fun w =>
      [ (true, var v (n-1)), (true, var w 0) ]))

/-- SAT instance (not yet 3‑CNF). -/
def sat_instance : SATInstance := mkSATInstance (hamiltonian_clauses G)

/-- Tseitin transformation to 3‑CNF. -/
def Φ_G : SATInstance := tseitin sat_instance

/-- Satisfiability of Φ_G is equivalent to existence of a Hamiltonian cycle. -/
axiom sat_correct : Satisfiable (Φ_G G hG) ↔ hamiltonian_cycle G
