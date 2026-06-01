import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Eigen
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import .HypercubeHarper
import .SpectralLibrary

open BigOperators Finset Matrix Real

variable {V : Type*} [Fintype V] [DecidableEq V]

def spectral_gap (A : Matrix V V ℝ) : ℝ :=
  let ev := (spectrum A).toList.sort (· ≤ ·)
  if ev.length ≥ 2 then ev[1]! - ev[0]! else 0

lemma spectral_gap_smul (ε : ℝ) (hε : ε > 0) (A : Matrix V V ℝ) :
    spectral_gap (ε • A) = ε * spectral_gap A := by
  rw [spectral_gap, spectral_gap, spectrum_smul]
  simp [List.map_sort (· ≤ ·) (· * ε) (by intros; simp [mul_le_mul_right hε])]
  rw [← mul_assoc, mul_comm ε, ← mul_assoc]
  congr 1

/-- Kithima Bridge : ajouter une diagonale non négative ne diminue pas le trou spectral. -/
lemma kithima_bridge (V : Matrix V V ℝ) (hV_diag : ∀ i j, i ≠ j → V i j = 0) (hV_nonneg : ∀ i, V i i ≥ 0)
    (Δ : Matrix V V ℝ) (hΔ_sym : Δᵀ = Δ) (hΔ_off : ∀ i j, i ≠ j → Δ i j ≥ 0)
    (ε : ℝ) (hε : ε > 0) :
    spectral_gap (V + ε • Δ) ≥ spectral_gap (ε • Δ) :=
  by
    let H₁ := ε • Δ
    let H₂ := V + ε • Δ
    have h₁ : H₁.IsSymm := by
      rw [IsSymm, transpose_smul, hΔ_sym]
    have h₂ : H₂.IsSymm := by
      rw [IsSymm, transpose_add, transpose_smul, hΔ_sym, diagonal_transpose]
      congr; ext i j; simp [hV_diag]
    -- Pour tout vecteur x, xᵀ H₂ x ≥ xᵀ H₁ x car xᵀ V x ≥ 0
    have h_quad : ∀ x, dot (x ᵀ) (H₂ *ᵥ x) ≥ dot (x ᵀ) (H₁ *ᵥ x) := by
      intro x
      have hV_quad : dot (x ᵀ) (V *ᵥ x) = ∑ i, V i i * (x i)^2 := by
        simp [mulVec, dot, hV_diag, Finset.sum_ite, mul_pow, mul_assoc]
        ring
      have hV_nonneg_quad : 0 ≤ dot (x ᵀ) (V *ᵥ x) := by
        rw [hV_quad]; apply sum_nonneg; intros; apply mul_nonneg (hV_nonneg _) (sq_nonneg _)
      exact le_add_of_nonneg_left hV_nonneg_quad
    -- Monotonie des valeurs propres par le principe min-max
    have h_eig_mono : ∀ k, (spectrum H₂).sort (· ≤ ·) k ≥ (spectrum H₁).sort (· ≤ ·) k :=
      Matrix.IsSymm.eigenvalues_monotone H₁ H₂ h₁ h₂ (fun x => by simp [h_quad x]) k
    let ev₁ := (spectrum H₁).toList.sort (· ≤ ·)
    let ev₂ := (spectrum H₂).toList.sort (· ≤ ·)
    have h_len : ev₁.length = ev₂.length := by
      simp [spectrum_card, Fintype.card V]
    rw [spectral_gap, spectral_gap]
    by_cases h_card : Fintype.card V ≥ 2
    · have h0 : ev₂[0]! ≥ ev₁[0]! := h_eig_mono 0
      have h1 : ev₂[1]! ≥ ev₁[1]! := h_eig_mono 1
      linarith
    · simp [h_card]

/-- Application à l'hypercube (matrice d'adjacence). -/
theorem spectral_gap_lower_bound_hypercube (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : ε > 0)
    (V : Matrix (Fin n → Bool) (Fin n → Bool) ℝ)
    (hV_diag : ∀ i j, i ≠ j → V i j = 0) (hV_nonneg : ∀ i, V i i ≥ 0) :
    spectral_gap (V + ε • adjacency_matrix n) ≥ 2 * ε :=
  by
    have h_gap_adj : spectral_gap (ε • adjacency_matrix n) = 2 * ε := by
      rw [spectral_gap_smul ε hε (adjacency_matrix n)]
      rw [HypercubeHarper.spectral_gap_adjacency hn]
      ring
    exact le_trans (kithima_bridge V hV_diag hV_nonneg (adjacency_matrix n)
                    (by simp [adjacency_matrix, transpose_adjacency]) (by simp) ε hε) (le_of_eq h_gap_adj)
