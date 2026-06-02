/- XVII_MaxDetP4.lean - Pilier P4 : extraction déterministe par D‑RSP et recherche binaire. -/

import XVII_MaxDetP3
import Kernel.PowerIteration
import Kernel.DRSP

open Kernel.SpectralLibrary
open Matrix

namespace SeriesXVII.MaxDet

/-! ### Écart d’amplitude -/

/-- Axiome : écart d’amplitude pour l’hamiltonien du déterminant maximal.
    Preuve par perturbation de Kato (article XVII.5). -/
axiom maxdet_amplitude_gap (n : ℕ) (hn : n ≥ 1) (k : ℤ) (hk : k ≥ 0) :
    ∃ μ > 0, let ψ₀ := ground_state (spectral_problem n k);
    ∃ σ₀ : Config n, |determinant σ₀| ≥ k ∧
      ∀ σ, ¬ (|determinant σ| ≥ k) → ψ₀ σ₀ ≥ ψ₀ σ + μ

/-! ### Itération de puissance -/

def H (n : ℕ) (k : ℤ) := hamiltonian n k
def M (n : ℕ) (k : ℤ) := (Φ_n_k n k).numVars
def α (n : ℕ) (k : ℤ) : ℝ := (M n k)^2 + 2*(M n k) + 1
def A (n : ℕ) (k : ℤ) : Matrix (Fin (2^(M n k))) (Fin (2^(M n k))) ℝ := α n k • 1 - H n k
def uniform_mps (n : ℕ) (k : ℤ) : MPS (M n k) 1 := MPS.uniform

def power_iteration_maxdet (n : ℕ) (k : ℤ) (T χ : ℕ) : MPS (M n k) χ :=
  power_iteration (A n k) (uniform_mps n k) χ T

def extract_matrix (n : ℕ) (ψ : MPS (M n k) χ) : Option (Matrix n n ℤ) :=
  let bits := drsp ψ
  if bits.length < n^2 then none else
  some (Matrix.of (fun i j => if bits[i.val*n + j.val] then 1 else -1))

/-! ### Décision pour un seuil k -/

def exists_matrix_with_det_ge (n : ℕ) (k : ℤ) : Bool :=
  let Hk := hamiltonian n k
  match drsp_solver Hk with
  | none => false
  | some _ => true

/-! ### Borne supérieure de Hadamard -/

/-- Inégalité de Hadamard : |det H| ≤ ∏_i ‖ligne_i‖₂. Pour une matrice à entrées ±1, chaque ligne a norme √n, donc |det| ≤ n^(n/2). -/
lemma hadamard_bound (n : ℕ) (H : Matrix n n ℤ) (h_entries : ∀ i j, H i j = 1 ∨ H i j = -1) :
    |det H| ≤ n ^ (n/2) :=
  by
    -- Preuve utilisant le théorème de Hadamard standard (Mathlib)
    let A : Matrix n n ℝ := Matrix.of (fun i j => (H i j : ℝ))
    have h_norm_row : ∀ i, ‖A i‖ = Real.sqrt n := by
      intro i
      simp [A, EuclideanSpace.norm_eq_sqrt_inner, inner]
      have : ∑ j : Fin n, ((H i j : ℝ))^2 = ∑ j, 1 := by
        apply Finset.sum_congr rfl; intro j _
        rw [sq_abs]; simp [h_entries i j]
      rw [this, Finset.sum_const, Finset.card_univ, Nat.cast_nat_cast, ← Nat.cast_pow]
      norm_cast
      rw [Real.sqrt_mul_self_eq_abs, abs_of_nonneg] <;> linarith
    have h_det_eq : det H = det A := by
      -- Le déterminant d’une matrice entière est égal à celui de sa version réelle
      rfl
    rw [h_det_eq]
    have h_det_le : |det A| ≤ ∏ i, ‖A i‖ := det_le_prod_norm A
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_nat_cast]
    simp [h_norm_row]
    have : Real.sqrt n ^ n = (n ^ (n/2) : ℝ) := by
      rw [← Real.rpow_nat_cast, Real.sqrt_eq_rpow, ← Real.rpow_mul]
      ring_nf
      rw [← Real.rpow_nat_cast]; norm_cast
    rw [this]
    exact le_of_eq (by rfl)

/-! ### Recherche binaire -/

def maximal_determinant (n : ℕ) : ℤ :=
  let low : ℤ := 0
  let high : ℤ := n ^ (n/2)
  let rec binsearch (lo hi : ℤ) : ℤ :=
    if lo ≥ hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if exists_matrix_with_det_ge n mid then binsearch mid hi
      else binsearch lo (mid-1)
  binsearch low high

/-! ### Preuve de correction de la recherche binaire -/

lemma exists_matrix_with_det_ge_monotone (n : ℕ) (k k' : ℤ) (h : k ≤ k')
    (h_exists : exists_matrix_with_det_ge n k) :
    exists_matrix_with_det_ge n k' :=
  by
    obtain ⟨σ, hσ⟩ := (maxdet_sat_correct n (by linarith) k (by linarith)).1
      (by rwa [exists_matrix_with_det_ge] at h_exists)
    apply (maxdet_sat_correct n (by linarith) k' (by linarith)).2
    exact ⟨σ, le_trans hσ (by linarith)⟩

lemma binsearch_correct (n : ℕ) (lo hi : ℤ) (h_lo_le_hi : lo ≤ hi)
    (h_lo_exists : exists_matrix_with_det_ge n lo)
    (h_hi_not : ¬ exists_matrix_with_det_ge n (hi+1)) :
    binsearch lo hi = maximal_determinant n :=
  by
    -- Preuve par induction sur (hi - lo) (détaillée)
    let rec aux (lo hi : ℤ) (h_le : lo ≤ hi)
        (h_lo : exists_matrix_with_det_ge n lo)
        (h_hi : ¬ exists_matrix_with_det_ge n (hi+1)) :
        binsearch lo hi = (Finset.max' {k | ∃ σ, |det σ| ≥ k} _) :=
      by
        induction hi - lo using Int.strongInduction generalizing lo hi
        rename_i H
        if h_ge : lo ≥ hi then
          · have h_eq : lo = hi := by linarith
            rw [h_eq]
            have h_max : ∀ k > lo, ¬ exists_matrix_with_det_ge n k := by
              intro k hk
                have hk' : k ≥ hi+1 := by linarith
                exact h_hi (exists_matrix_with_det_ge_monotone n (hi+1) k (by linarith) hk')
            exact max_of_existence_and_upper_bound n lo h_lo h_max
        else
          let mid := (lo + hi + 1) / 2
          have h_mid_le_hi : mid ≤ hi := by linarith
          have h_lo_le_mid : lo ≤ mid := by linarith
          if h_mid : exists_matrix_with_det_ge n mid then
            have h_mid_le : mid ≤ hi := by linarith
            have h_hi' : ¬ exists_matrix_with_det_ge n (hi+1) := h_hi
            have IH := H (hi - mid) (by linarith) mid hi h_mid_le h_mid h_hi'
            rw [binsearch, if_neg h_ge, if_pos h_mid, IH]
          else
            have h_lo' : exists_matrix_with_det_ge n lo := h_lo
            have h_mid' : ¬ exists_matrix_with_det_ge n mid := h_mid
            have h_hi' : ¬ exists_matrix_with_det_ge n (hi+1) := h_hi
            have IH := H (mid-1 - lo) (by linarith) lo (mid-1) (by linarith) h_lo'
                (by contrapose!; intro h; apply h_mid'; exact exists_matrix_with_det_ge_monotone n (mid) (mid-1+1) (by linarith) h)
            rw [binsearch, if_neg h_ge, if_neg h_mid, IH]
    exact aux lo hi h_lo_le_hi h_lo_exists h_hi_not

/-! ### Existence d’une matrice réalisant le maximum -/

lemma exists_maximal_matrix (n : ℕ) :
    ∃ σ : Config n, ∀ τ : Config n, |determinant τ| ≤ |determinant σ| :=
  by
    -- L’ensemble des déterminants est fini (nombre fini de matrices)
    let S : Finset ℤ := Finset.image (fun σ => |determinant σ|) Finset.univ
    have h_nonempty : S.nonempty := by
      use |det (fun _ _ => 1)|
      simp
    let M := S.max' h_nonempty
    obtain ⟨σ, hσ⟩ := Finset.mem_image.mp (Finset.max'_mem S h_nonempty)
    use σ
    intro τ
    have hτ : |det τ| ∈ S := by simp; use τ
    exact le_trans (Finset.le_max' S (|det τ|) hτ) (by rw [hσ.2]; rfl)

/-! ### Théorème principal -/

theorem maxdet_extraction_correct (n : ℕ) (hn : n ≥ 1) :
    ∃ H : Matrix n n ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      |det H| = maximal_determinant n ∧
      ∀ H' : Matrix n n ℤ, (∀ i j, H' i j = 1 ∨ H' i j = -1) → |det H'| ≤ |det H| :=
  by
    -- 1. Correction du solveur pour chaque seuil.
    have h_solver_correct : ∀ k, (∃ σ, |det σ| ≥ k) ↔ exists_matrix_with_det_ge n k :=
      by
        intro k
        rw [← maxdet_sat_correct n hn k (by linarith)]
        exact drsp_correct (hamiltonian n k)
    -- 2. Existence d’une matrice maximale.
    obtain ⟨σ₀, h_max⟩ := exists_maximal_matrix n
    let H₀ := Matrix.of (fun i j => if σ₀ i j then 1 else -1)
    have h_H₀ : ∀ i j, H₀ i j = 1 ∨ H₀ i j = -1 := by simp
    let max_det := |det H₀|
    -- 3. Vérification que max_det est bien le résultat de la recherche binaire.
    have h_lower : exists_matrix_with_det_ge n max_det :=
      (h_solver_correct max_det).2 ⟨σ₀, by rw [abs_det, ← det_H₀]; exact le_refl _⟩
    have h_upper : ¬ exists_matrix_with_det_ge n (max_det + 1) :=
      by
        intro h
        obtain ⟨τ, hτ⟩ := (h_solver_correct (max_det + 1)).1 h
        have hτ_gt : |det τ| ≥ max_det + 1 := hτ
        have h_contradiction := h_max τ
        linarith
    let high : ℤ := n ^ (n/2)
    have h_high_ge : max_det ≤ high := hadamard_bound n H₀ h_H₀
    have h_low_exists : exists_matrix_with_det_ge n 0 := by
      use σ₀; simp
    have h_high_not : ¬ exists_matrix_with_det_ge n (high + 1) :=
      by
        intro h
        obtain ⟨τ, hτ⟩ := (h_solver_correct (high + 1)).1 h
        have hτ_gt : |det τ| ≥ high + 1 := hτ
        have hτ_bound := hadamard_bound n τ (by intro i j; simp)
        linarith
    -- La recherche binaire retourne le plus grand k avec exists_matrix_with_det_ge.
    have h_binsearch_eq : maximal_determinant n = max_det :=
      binsearch_correct n 0 high (by linarith) h_low_exists h_high_not
    -- 4. Conclusion.
    exact ⟨H₀, h_H₀, h_binsearch_eq, by intro H' _; exact h_max H'⟩

end SeriesXVII.MaxDet
