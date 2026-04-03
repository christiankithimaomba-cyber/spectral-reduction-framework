/- 
DiscreteCheeger.lean – Borne polynomiale du trou spectral de l'hypercube.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Eigen
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import HypercubeHarper
import SpectralLibrary

open BigOperators Finset Matrix Real

variable {n : ℕ}

def Config (n : ℕ) := Fin n → Bool

def spectral_volume (ψ : Config n → ℝ) (S : Finset (Config n)) : ℝ :=
  ∑ x in S, (ψ x) ^ 2

def spectral_boundary (ε : ℝ) (S : Finset (Config n)) : ℝ :=
  ε * (HypercubeHarper.edge_boundary S : ℝ)

def adjacency_matrix (n : ℕ) : Matrix (Config n) (Config n) ℝ :=
  Matrix.of (fun x y => if HypercubeHarper.is_edge x y then 1 else 0)

noncomputable def spectral_gap (A : Matrix (Config n) (Config n) ℝ) : ℝ :=
  let ev := (spectrum A).toList
  if ev.length ≥ 2 then ev[1]! - ev[0]! else 0

lemma courant_fischer_monotone (A B : Matrix (Config n) (Config n) ℝ) (hA_sym : Aᵀ = A) (hB_sym : Bᵀ = B)
    (h_le : ∀ x, x ⬝ᵥ A ⬝ᵥ x ≤ x ⬝ᵥ B ⬝ᵥ x) (k : ℕ) (hk : k < Fintype.card (Config n)) :
    (spectrum A).sort k ≤ (spectrum B).sort k := by
  exact Matrix.IsSymm.eigenvalues_monotone A B (by convert hA_sym) (by convert hB_sym) h_le k hk

lemma spectral_gap_smul (ε : ℝ) (A : Matrix (Config n) (Config n) ℝ) :
    spectral_gap (ε • A) = ε * spectral_gap A := by
  have h : spectrum (ε • A) = ε • (spectrum A) := spectrum_smul
  rw [spectral_gap, spectral_gap]
  simp [h, List.map, List.get?_map, List.get?_eq_get]
  ring

lemma kithima_bridge (V : Matrix (Config n) (Config n) ℝ) (ε : ℝ) (hε : 0 < ε)
    (hV_diag : ∀ i j, i ≠ j → V i j = 0) (hV_nonneg : ∀ i, V i i ≥ 0) :
    spectral_gap (V + ε • adjacency_matrix n) ≥ spectral_gap (ε • adjacency_matrix n) := by
  let H := V + ε • adjacency_matrix n
  let B := ε • adjacency_matrix n
  have h_sym_H : Hᵀ = H := by
    have hV_sym : Vᵀ = V := by ext i j; by_cases h : i = j <;> simp [hV_diag, h]
    have hB_sym : (ε • adjacency_matrix n)ᵀ = ε • adjacency_matrix n := by simp [adjacency_matrix, transpose_smul]
    rw [H, transpose_add, hV_sym, hB_sym]
  have h_sym_B : Bᵀ = B := by simp [adjacency_matrix, transpose_smul]
  have h_ge : ∀ x, x ⬝ᵥ H ⬝ᵥ x ≥ x ⬝ᵥ B ⬝ᵥ x := by
    intro x
    simp [H, B, dot_product, mul_vec, sum_add_distrib, add_le_add_left]
    apply sum_nonneg
    intro i _
    have : V i i ≥ 0 := hV_nonneg i
    exact mul_nonneg this (pow_two_nonneg (x i))
  apply courant_fischer_monotone B H h_sym_B h_sym_H (by intro x; linarith [h_ge x])
  exact (by linarith : 0 < Fintype.card (Config n))

theorem spectral_gap_lower_bound_hypercube (ε : ℝ) (ψ : Config n → ℝ)
    (hψ_pos : ∀ x, 0 < ψ x) (hψ_norm : ∑ x, (ψ x) ^ 2 = 1)
    (hn : 1 ≤ n) (V : Matrix (Config n) (Config n) ℝ) (hV_diag : ∀ i j, i ≠ j → V i j = 0)
    (hV_nonneg : ∀ i, V i i ≥ 0) :
    spectral_gap (V + ε • adjacency_matrix n) ≥ 2 * ε := by
  have h_gap_B : spectral_gap (ε • adjacency_matrix n) = 2 * ε := by
    rw [spectral_gap_smul ε (adjacency_matrix n)]
    rw [HypercubeHarper.spectral_gap_adjacency hn]
    ring
  apply le_trans (kithima_bridge V ε (by linarith) hV_diag hV_nonneg) (le_of_eq h_gap_B)
