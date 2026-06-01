/-
EckartYoung.lean – Théorème d'Eckart‑Young pour la troncature SVD.
-/

import Mathlib.LinearAlgebra.SVD
import Mathlib.LinearAlgebra.Matrix.Norms
import Mathlib.Tactic

open Matrix Real

variable {m n : Type*} [Fintype m] [Fintype n]

def frobenius_norm (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

lemma frobenius_norm_sq (A : Matrix m n ℝ) : (frobenius_norm A) ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 :=
  sq_sqrt (by apply sum_nonneg; intros; apply sq_nonneg)

theorem truncation_error (A : Matrix m n ℝ) (k : ℕ) :
    let ⟨U, s, V, hSVD⟩ := SVD.exists_svd A
    let σ := s.singularValues
    let Σ_k := diagonal (fun i => if i.val < k then σ i else 0)
    let B := U ⬝ Σ_k ⬝ Vᵀ
    rank B ≤ k ∧ (frobenius_norm (A - B)) ^ 2 = ∑ i in Finset.univ.filter (fun i => i.val ≥ k), (σ i) ^ 2 :=
  by
    rcases SVD.exists_svd A with ⟨U, s, V, hSVD⟩
    let σ := s.singularValues
    let Σ := s.toMatrix
    have A_eq : A = U ⬝ Σ ⬝ Vᵀ := hSVD
    have hU : Uᵀ ⬝ U = 1 := SVD.orthogonal_U hSVD
    have hV : Vᵀ ⬝ V = 1 := SVD.orthogonal_V hSVD
    have rank_Σk : rank Σ_k ≤ k := by
      apply rank_diagonal_le k
      intro i hi
      simp [Σ_k, hi]
    have rank_B : rank B ≤ k := by
      have r1 : rank (U ⬝ Σ_k) ≤ rank Σ_k := rank_mul_le_left U Σ_k
      have r2 : rank ((U ⬝ Σ_k) ⬝ Vᵀ) ≤ rank (U ⬝ Σ_k) := rank_mul_le_right (U ⬝ Σ_k) Vᵀ
      exact le_trans r2 r1 rank_Σk
    have diff : A - B = U ⬝ (Σ - Σ_k) ⬝ Vᵀ := by
      rw [A_eq, B, ← matrix.mul_sub, ← matrix.sub_mul]
      simp
    have frob_inv (X : Matrix m n ℝ) (U : Matrix m m ℝ) (V : Matrix n n ℝ)
        (hU : Uᵀ ⬝ U = 1) (hV : Vᵀ ⬝ V = 1) :
        frobenius_norm (U ⬝ X ⬝ Vᵀ) = frobenius_norm X := by
      rw [frobenius_norm_mul_orthogonal_right (U ⬝ X) V hV]
      rw [frobenius_norm_mul_orthogonal_left X U hU]
    rw [frob_inv (Σ - Σ_k) U V hU hV]
    have diff_diag : Σ - Σ_k = diagonal (fun i => if i.val ≥ k then σ i else 0) := by
      ext i j
      simp [Σ, Σ_k, diagonal, sub_diagonal, sub_eq_sub_iff_add_eq_add]
      by_cases h : i = j
      · subst h
        simp [diagonal_apply_eq, Σ, Σ_k, s.toMatrix_apply_eq]
        split_ifs <;> ring
      · simp [diagonal_apply_ne, h, Σ, Σ_k, s.toMatrix_apply_ne]
    rw [diff_diag]
    have err_sq : (frobenius_norm (diagonal (fun i => if i.val ≥ k then σ i else 0))) ^ 2 =
        ∑ i in Finset.univ.filter (fun i => i.val ≥ k), (σ i) ^ 2 := by
      simp [frobenius_norm_sq, diagonal, Finset.sum_ite]
      apply Finset.sum_congr rfl; intros i _; simp [pow_two]
    exact ⟨rank_B, err_sq⟩
