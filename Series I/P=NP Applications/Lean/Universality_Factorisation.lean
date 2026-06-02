/- 
Factorisation.lean – Problème de factorisation entière.
-/

import Kernel.SpectralLibrary
import Kernel.HypercubeHarper
import Mathlib.Data.Nat.Sqrt

open SpectralLibrary

def Config (n : ℕ) := Fin n → Bool

-- Fonctions auxiliaires pour convertir une liste de bits en entier
def bits_to_int (bits : List Bool) : ℕ :=
  bits.foldr (fun b acc => if b then 2 * acc + 1 else 2 * acc) 0

def take {n : ℕ} (k : ℕ) (f : Fin n → Bool) : List Bool :=
  (List.range k).map (fun i => f ⟨i, by linarith⟩)

def drop {n : ℕ} (k : ℕ) (f : Fin n → Bool) : List Bool :=
  (List.range (n - k)).map (fun i => f ⟨k + i, by linarith⟩)

def factorisation_potential (N : ℕ) (bits : Config (2*n)) : ℝ :=
  let a := bits_to_int (take n bits)
  let b := bits_to_int (drop n bits)
  Real.exp (- |a*b - N|)

def hypercube_graph (m : ℕ) : SimpleGraph (Config m) := SimpleGraph.hypercube (Fin m)

-- Axiom: L'hypercube est connexe
axiom hypercube_connected (m : ℕ) : (hypercube_graph m).Connected

def factorisation_problem (N : ℕ) (ε : ℝ) (hε : 0 < ε) : SpectralProblem (Config (2 * n)) where
  potential := factorisation_potential N
  graph := hypercube_graph (2 * n)
  epsilon := ε
  heps := hε
  connected := hypercube_connected (2 * n)
