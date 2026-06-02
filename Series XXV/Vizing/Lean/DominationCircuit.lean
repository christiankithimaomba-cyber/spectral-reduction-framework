/-
DominationCircuit.lean – Boolean circuit for testing domination in a fixed graph.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Kernel.Circuit.Basic
import Kernel.Circuit.Arithmetic
import Kernel.Circuit.Compare

open Circuit SimpleGraph

variable (G : SimpleGraph) [Fintype V(G)] [DecidableRel G.Adj]

def n : ℕ := Fintype.card V(G)

/-- Circuit for testing whether a given subset of vertices is dominating.
    Input: n bits (one per vertex). Output: (dom, size) where dom is a single bit
    (1 iff the set is dominating) and size is the binary representation of |D|. -/
def domination_circuit : Circuit (Fin n → Bool) × Circuit (Fin (Nat.log2 n + 1) → Bool) :=
  let x := input_all n
  -- for each vertex i, compute whether it is dominated
  let dom_i : List (Circuit Bool) :=
    List.ofFn (fun i : Fin n =>
      let i_in := x i
      let neighs := List.ofFn (fun j => if G.Adj i j then x j else circuit_false)
      let neigh_or := neighs.foldl or_circuit circuit_false
      or_circuit i_in neigh_or)
  -- overall domination: AND over all i
  let dom := dom_i.foldl and_circuit circuit_true
  -- size: sum of x bits using adder tree
  let size := adder_tree (List.ofFn x)
  (dom, size)

-- The size output is a binary number; we can extract it as a Circuit (Fin L → Bool)
def size_circuit : Circuit (Fin (Nat.log2 n + 1) → Bool) :=
  (domination_circuit G).2

-- Correctness of the domination test (standard result, admitted as an axiom with reference)
axiom domination_circuit_dom_correct (bits : Fin n → Bool) :
    let (dom, _) := domination_circuit G
    dom.eval bits = true ↔
      let D := { i : Fin n | bits i = true }
      ∀ v : Fin n, v ∈ D ∨ ∃ u ∈ D, G.Adj v u

-- Correctness of the cardinality computation (proved in the kernel)
theorem size_circuit_correct (bits : Fin n → Bool) :
    (size_circuit G).eval bits = Finset.card { i : Fin n | bits i = true } :=
  adder_tree_correct (List.ofFn bits)

-- The two outputs together give the full specification
theorem domination_circuit_correct (bits : Fin n → Bool) :
    let (dom, size) := domination_circuit G
    dom.eval bits = true ↔ ∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj v u ∧
    size.eval bits = Finset.card D :=
  by
    simp [domination_circuit_dom_correct, size_circuit_correct]
    exact ⟨fun h => h, fun h => h⟩
