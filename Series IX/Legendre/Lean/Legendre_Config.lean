/- 
LegendreConfig.lean – Configuration space, potential, Hamiltonian for Legendre.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.Combinatorics.SimpleGraph.Path
import Kernel.SpectralLibrary

open Matrix

/-- Configuration space : {n², n²+1, ..., (n+1)²} -/
def LegendreConfig (n : ℕ) : Type := { k : ℕ // n^2 ≤ k ∧ k ≤ (n+1)^2 }

/-- Potentiel : 0 sur les nombres premiers, λ sinon -/
def LegendrePotential (n : ℕ) (λ : ℝ) (k : LegendreConfig n) : ℝ :=
  if Nat.Prime k.val then 0 else λ

/-- Graphe : chemin sur 2n+1 sommets (isomorphe à Fin (2n+1)) -/
def LegendreGraph (n : ℕ) : SimpleGraph (LegendreConfig n) :=
  let f : LegendreConfig n ≃ Fin (2*n + 1) :=
    { toFun := fun k => ⟨k.val - n^2, by
        have h₁ : n^2 ≤ k.val := k.property.1
        have h₂ : k.val ≤ (n+1)^2 := k.property.2
        exact Nat.sub_lt_of_pos_le (by linarith) h₁ h₂ ⟩,
      invFun := fun i => ⟨n^2 + i.val, by
        have : i.val ≤ 2*n := by linarith [i.isLt]
        exact ⟨by linarith, by linarith⟩⟩,
      left_inv := by intro k; simp; ring,
      right_inv := by intro i; simp; ring }
  SimpleGraph.comap f (SimpleGraph.pathGraph (2*n + 1))

/-- Hamiltonien spectral -/
noncomputable def LegendreHamiltonian (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) :
    Matrix (LegendreConfig n) (LegendreConfig n) ℝ :=
  let V := diagonal (LegendrePotential n λ)
  let Δ := adjacencyMatrixOf (LegendreGraph n)
  V + ε • Δ

/-- Instance de SpectralProblem -/
def LegendreSpectralProblem (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) :
    Kernel.SpectralLibrary.SpectralProblem (LegendreConfig n) where
  potential := LegendrePotential n λ
  graph := LegendreGraph n
  epsilon := ε
  heps := hε
  connected := by
    apply SimpleGraph.comap_connected
    exact SimpleGraph.pathGraph_connected (2*n + 1)
