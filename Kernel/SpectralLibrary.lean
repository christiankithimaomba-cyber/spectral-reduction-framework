/- 
SpectralLibrary.lean – Noyau commun : classe SpectralProblem, Hamiltonien, Perron‑Frobenius.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PerronFrobenius
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Matrix Finset BigOperators

universe u

/-- Type alias pour les configurations (hypercube). -/
def Config (n : ℕ) := Fin n → Bool

/-- Classe abstraite d’un problème spectral. -/
class SpectralProblem (V : Type u) [Fintype V] [DecidableEq V] where
  potential : V → ℝ
  graph : SimpleGraph V
  epsilon : ℝ
  heps : 0 < epsilon
  connected : graph.Connected

namespace SpectralLibrary

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Matrice d’adjacence d’un graphe simple. -/
def adjacencyMatrixOf (G : SimpleGraph V) : Matrix V V ℝ :=
  fun i j => if G.Adj i j then 1 else 0

/-- Hamiltonien spectral H = diag(potential) + ε * adjacency. -/
def Hamiltonian (P : SpectralProblem V) : Matrix V V ℝ :=
  (diagonal (fun v => P.potential v)) + (P.epsilon • adjacencyMatrixOf P.graph)

theorem Hamiltonian_symm (P : SpectralProblem V) : (Hamiltonian P)ᵀ = Hamiltonian P := by
  simp [Hamiltonian, diagonal_transpose, adjacencyMatrixOf, ← transpose_add]
  rw [adjacencyMatrixOf, ← transpose_smul, ← transpose_add]
  congr; ext i j; simp [adjacencyMatrixOf, SimpleGraph.adj_symm]

/-- Décalage pour obtenir une matrice non‑négative. -/
noncomputable def shifted_matrix (P : SpectralProblem V) : Matrix V V ℝ :=
  let max_pot := (Finset.univ : Finset V).fold max 0 (fun v => P.potential v)
  let α := max_pot + 2 * P.epsilon + 1
  α • 1 - Hamiltonian P

theorem shifted_nonneg (P : SpectralProblem V) : ∀ i j, 0 ≤ (shifted_matrix P) i j := by
  intro i j
  dsimp [shifted_matrix, Hamiltonian, adjacencyMatrixOf]
  by_cases h : i = j
  · simp [h]
    have : P.potential i ≤ (Finset.univ : Finset V).fold max 0 (fun v => P.potential v) :=
      Finset.le_fold_max (by simp)
    linarith [P.heps]
  · simp [h]
    split_ifs with adj
    · have : P.epsilon > 0 := P.heps; linarith
    · linarith

theorem shifted_irreducible (P : SpectralProblem V) : Irreducible (shifted_matrix P) := by
  apply Matrix.isIrreducible_of_adjacency_graph
  convert P.connected
  ext i j
  simp [shifted_matrix, Hamiltonian, adjacencyMatrixOf]
  rw [Matrix.isIrreducible_of_adjacency_graph_iff]
  exact P.connected

/-- État fondamental : unique vecteur propre strictement positif de H pour la plus petite valeur propre. -/
noncomputable def ground_state (P : SpectralProblem V) : V → ℝ :=
  let M := shifted_matrix P
  have hM_nonneg := shifted_nonneg P
  have hM_irred := shifted_irreducible P
  let ⟨v, hv_pos, hv_eig⟩ := PerronFrobenius.exists_eigenvector_positive M hM_nonneg hM_irred
  let nrm := Real.sqrt (∑ x, (v x) ^ 2)
  have h_nrm_pos : 0 < nrm := by
    obtain ⟨x, hx⟩ := hv_pos
    have : 0 < (v x) ^ 2 := by linarith [hx]
    apply Real.sqrt_pos.2
    apply sum_pos
    · intro y _; apply sq_nonneg
    · exact ⟨x, mem_univ _, this⟩
  fun x => v x / nrm

/-- Évaluation ponctuelle du produit matrice-vecteur. -/
theorem Hamiltonian_apply_point (H : Matrix V V ℝ) (ψ : V → ℝ) (y : V) :
    (H *ᵥ ψ) y = (H y y) * ψ y + ∑ z in (univ.erase y), (H y z) * ψ z :=
  by
    simp [mulVec, dot_product]
    rw [Finset.sum_eq_add_sum_diff (mem_univ y)]
    ring

/-- Spectre de αI - M. -/
lemma spectrum_sub_smul (α : ℝ) (M : Matrix V V ℝ) :
    spectrum (α • 1 - M) = α -ᵥ (spectrum M) :=
  spectrum_sub_left α M

/-- Unicité du vecteur propre positif de Perron‑Frobenius. -/
lemma perron_frobenius_unique (M : Matrix V V ℝ) (hM_nonneg : ∀ i j, 0 ≤ M i j) (hM_irred : Irreducible M)
    (v w : V → ℝ) (hv : ∀ x, 0 < v x) (hw : ∀ x, 0 < w x)
    (hv_eig : M *ᵥ v = ρ • v) (hw_eig : M *ᵥ w = ρ • w) :
    ∃ c : ℝ, w = c • v :=
  PerronFrobenius.unique_positive_eigenvector M hM_nonneg hM_irred v hv hv_eig w hw hw_eig

/-- Théorème de Perron‑Frobenius pour SpectralProblem. -/
theorem perron_frobenius (P : SpectralProblem V) :
    ∃! ψ : V → ℝ,
      (∀ x, ψ x > 0) ∧
      (∃ λ, Hamiltonian P *ᵥ ψ = λ • ψ ∧ λ = (spectrum (Hamiltonian P)).min) ∧
      (∑ x, (ψ x) ^ 2 = 1) := by
  let H := Hamiltonian P
  let M := shifted_matrix P
  let α := (Finset.univ : Finset V).fold max 0 (fun v => P.potential v) + 2 * P.epsilon + 1
  have hM_nonneg := shifted_nonneg P
  have hM_irred := shifted_irreducible P
  obtain ⟨v, hv_pos, hv_eig⟩ := PerronFrobenius.exists_eigenvector_positive M hM_nonneg hM_irred
  let ψ := ground_state P
  -- Positivité
  have hpos : ∀ x, ψ x > 0 := by
    intro x
    have : v x > 0 := hv_pos x
    have : nrm > 0 := by dsimp [ψ, ground_state]; exact Real.sqrt_pos.2 (by positivity)
    exact div_pos (hv_pos x) (by positivity)
  -- Valeur propre de H
  have hv_eig_H : ∃ λ, H *ᵥ ψ = λ • ψ ∧ λ = α - PerronFrobenius.spectral_radius M := by
    let ρM := PerronFrobenius.spectral_radius M
    have : M *ᵥ v = ρM • v := hv_eig
    have : (α • 1 - H) *ᵥ v = ρM • v := by rw [shifted_matrix]; exact this
    have : α • v - H *ᵥ v = ρM • v := by rwa [Matrix.mulVec_smul, Matrix.mulVec_one] at this
    have : H *ᵥ v = (α - ρM) • v := by
      rw [← sub_eq_iff_eq_add, eq_comm, ← sub_smul]
      exact eq_sub_of_add_eq (by simp [this])
    let λ0 := α - ρM
    have h_eig : H *ᵥ v = λ0 • v := this
    have : ψ = (1 / nrm) • v := by funext x; simp [ψ, ground_state, mul_comm]
    rw [this, mulVec_smul]
    simp [h_eig, smul_smul, mul_comm]
    exact ⟨λ0, rfl⟩
  -- Normalisation
  have hnorm : ∑ x, (ψ x) ^ 2 = 1 := by
    simp [ψ, ground_state, ← sum_div, ← sum_mul, mul_assoc, ← mul_pow, div_pow]
    field_simp [nrm_sq]
    ring
  -- Minimalité de λ
  obtain ⟨λ, hλ_eig, hλ_min⟩ : ∃ λ, H *ᵥ ψ = λ • ψ ∧ λ = (spectrum H).min := by
    obtain ⟨λ, hλ_eig, hλ_eq⟩ := hv_eig_H
    have hλ_min : λ = (spectrum H).min := by
      have : ρM = (spectrum M).max :=
        PerronFrobenius.spectral_radius_eq_max_eigenvalue M hM_nonneg hM_irred
      have : λ = α - (spectrum M).max := by rw [hλ_eq, this]
      have : (spectrum H).min = α - (spectrum M).max := by
        rw [spectrum_sub_smul α M, ← spectrum_neg, ← spectrum_smul]
        simp
      exact this
    exact ⟨λ, hλ_eig, hλ_min⟩
  -- Unicité
  have huniq : ∀ φ, (∀ x, φ x > 0) → (∃ μ, H *ᵥ φ = μ • φ ∧ μ = (spectrum H).min) → φ = ψ := by
    intro φ hφ_pos ⟨μ, hμ_eig, hμ_min⟩
    have : M *ᵥ φ = (α - μ) • φ := by
      rw [shifted_matrix, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_one]
      simp [hμ_eig, smul_sub, smul_smul]
    let ρM := PerronFrobenius.spectral_radius M
    have hρM_eq : α - μ = ρM := by
      have : μ = (spectrum H).min := hμ_min
      have : α - μ = (spectrum M).max := by
        rw [spectrum_sub_smul α M, ← spectrum_neg, ← spectrum_smul] at this
        simp [this]
      exact (PerronFrobenius.spectral_radius_eq_max_eigenvalue M hM_nonneg hM_irred).symm.trans this
    obtain ⟨c, hc⟩ := perron_frobenius_unique M hM_nonneg hM_irred v φ hv_pos hφ_pos hv_eig (by rwa [hρM_eq] at this)
    have c_pos : 0 < c := by
      have : ∃ x, φ x > 0 := by use some x from hφ_pos
      rw [hc] at this
      have : v x > 0 := hv_pos x
      exact pos_of_mul_pos this (by positivity)
    -- Normalisation
    have norm_φ : ∑ x, (φ x) ^ 2 = c ^ 2 * ∑ x, (v x) ^ 2 := by simp [hc, ← sum_mul, ← mul_pow]
    have norm_ψ : ∑ x, (ψ x) ^ 2 = (1 / nrm ^ 2) * ∑ x, (v x) ^ 2 := by
      simp [ψ, ground_state, ← sum_div, ← sum_mul, mul_pow]
      ring
    have h_nrm_eq : ∑ x, (v x) ^ 2 = nrm ^ 2 := by simp [nrm, Real.sq_sqrt]
    rw [norm_φ, norm_ψ, h_nrm_eq] at hnorm
    have : φ = ψ := by
      rw [hc, ψ, ground_state, ← mul_smul, ← smul_smul]
      have c_eq : c = 1 / nrm := by
        rw [norm_φ, hnorm] at hnorm
        have : c ^ 2 = (1 / nrm) ^ 2 := by
          rw [norm_φ, hnorm] at hnorm
          simp [hnorm, ← mul_pow, mul_eq_mul_right_iff]
          left; linarith
        exact Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity) (by rw [this]; simp)
      simp [c_eq]
    exact this
  exact ⟨ψ, hpos, ⟨λ, hλ_eig, hλ_min⟩, hnorm, huniq⟩

end SpectralLibrary
