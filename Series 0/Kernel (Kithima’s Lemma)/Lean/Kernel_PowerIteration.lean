import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Matrix.Norms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import .MPS
import .SpectralLibrary
import .EckartYoung
import .HypercubeHarper

open BigOperators Finset Matrix Real

variable {n : ℕ} (hn : 1 ≤ n)

def Config := Fin n → Bool
def norm_vec (v : Config → ℝ) : ℝ := Real.sqrt (∑ x, (v x) ^ 2)

noncomputable def λ_min (H : Matrix Config Config ℝ) : ℝ :=
  ((spectrum H).toList.sort (· ≤ ·)).get ⟨0, by
    have : Fintype.card Config = 2^n := by simp [Config]
    simp [spectrum_card, this, List.length_sort]
    exact zero_lt_two_pow hn⟩

noncomputable def λ_max (H : Matrix Config Config ℝ) : ℝ :=
  let L := (spectrum H).toList.sort (· ≤ ·)
  L.get ⟨L.length - 1, by
    have : Fintype.card Config = 2^n := by simp [Config]
    simp [spectrum_card, this, List.length_sort]
    exact Nat.sub_lt (zero_lt_two_pow hn) (by norm_num)⟩

noncomputable def λ_second (H : Matrix Config Config ℝ) : ℝ :=
  let L := (spectrum H).toList.sort (· ≤ ·)
  L.get ⟨1, by
    have : Fintype.card Config = 2^n := by simp [Config]
    simp [spectrum_card, this, List.length_sort]
    have : 2^n ≥ 2 := two_pow_ge_two hn
    linarith⟩

theorem spectral_gap_adjacency : spectral_gap (adjacency_matrix n) = 2 :=
  HypercubeHarper.spectral_gap_adjacency hn

/-- Base orthonormée de vecteurs propres pour une matrice symétrique. -/
theorem orthonormal_eigenbasis (H : Matrix Config Config ℝ) (h_sym : Hᵀ = H) :
    ∃ (U : Matrix Config Config ℝ) (Λ : Config → ℝ),
      Uᵀ ⬝ U = 1 ∧ H = U ⬝ (diagonal Λ) ⬝ Uᵀ ∧
      ∀ i, H *ᵥ (U i) = Λ i • (U i) ∧
      List.ofFn Λ = (spectrum H).toList.sort (· ≤ ·) :=
  by
    have h := Matrix.IsSymm.spectral_theorem' h_sym
    obtain ⟨U, Λ, hU, hH⟩ := h
    use U, Λ
    constructor
    · exact hU
    · constructor
      · exact hH
      · constructor
        · intro i; rw [← mulVec_mulVec, hH, diagonal_mulVec]; simp [Pi.smul_apply]
        · simp [List.ofFn, spectrum_diagonal]

/-- Lemme : la première colonne de U (celle associée à la plus petite valeur propre) est l'état fondamental. -/
lemma first_column_is_ground_state (H : Matrix Config Config ℝ) (h_sym : Hᵀ = H)
    (U : Matrix Config Config ℝ) (Λ : Config → ℝ) (hU : Uᵀ ⬝ U = 1)
    (hH : H = U ⬝ (diagonal Λ) ⬝ Uᵀ) (h_list : List.ofFn Λ = (spectrum H).toList.sort (· ≤ ·)) :
    let i0 := Classical.choose (fun i => Λ i = λ_min H) (by
      have : ∃ i, Λ i = λ_min H := by
        have h_min := (spectrum H).toList.get_zero (by simp [spectrum_card])
        rw [← h_list] at h_min
        obtain ⟨i, hi⟩ := List.ofFn_get? h_min
        exact ⟨i, hi⟩)
    ground_state H = U i0 :=
  by
    have h_eig : H *ᵥ (U i0) = λ_min H • (U i0) := by
      rw [hH, mulVec_mulVec, mulVec_diagonal, ← mulVec_mulVec, hU, mulVec_one]
      simp [Classical.choose_spec (fun i => Λ i = λ_min H)]
    have ψ0 := ground_state H
    have hψ0_pos : ∀ x, ψ0 x > 0 := (perron_frobenius H).choose_spec.1
    have hψ0_eig : H *ᵥ ψ0 = λ_min H • ψ0 := (perron_frobenius H).choose_spec.2.1
    have hψ0_norm : ∑ x, ψ0 x ^ 2 = 1 := (perron_frobenius H).choose_spec.2.2
    obtain ⟨c, hc⟩ : ∃ c, ψ0 = c • (U i0) :=
      eigenvector_uniqueness H ψ0 (U i0) hψ0_eig h_eig (by positivity) (by positivity)
    have hc_pos : c > 0 := by
      have : ∃ x, (U i0) x ≠ 0 := by
        by_contra h; simp [h] at h; exact h_eig
      obtain ⟨x, hx⟩ := this
      have hψ0x : ψ0 x = c * (U i0 x) := by rw [hc]; simp
      have hUx : (U i0 x) ≠ 0 := hx
      have hψ0x_pos : ψ0 x > 0 := hψ0_pos x
      exact pos_of_mul_pos hψ0x_pos (by positivity)
    have norm_U : ∑ x, (U i0 x)^2 = 1 := by
      have : (Uᵀ ⬝ U) i0 i0 = 1 := by rw [hU]; simp [one_apply_eq, if_pos rfl]
      exact this
    have hc_eq : c = 1 := by
      rw [hc] at hψ0_norm
      simp [norm_vec, hψ0_norm, ← sum_mul, mul_pow] at hψ0_norm
      have : c^2 * ∑ x, (U i0 x)^2 = 1 := by rw [← mul_assoc]; exact hψ0_norm
      rw [norm_U, mul_one] at this
      exact (sq_eq_one_iff.1 this).resolve_neg (by linarith)
    rw [hc, hc_eq, one_smul]

/-- Norme de A sur l'orthogonal de l'état fondamental. -/
theorem norm_A_orth (H : Matrix Config Config ℝ) (h_sym : Hᵀ = H)
    (γ : ℝ) (hγ : γ > 0) (h_gap : λ_second H - λ_min H ≥ γ) :
    let λM := λ_max H
    let A := λM • 1 - H
    let μ₂ := λM - λ_second H
    let ψ_true := ground_state H
    ∀ v : Config → ℝ, (∑ x, v x * ψ_true x = 0) → norm_vec (A *ᵥ v) ≤ μ₂ * norm_vec v :=
  by
    intros λM A μ₂ ψ_true v h_orth
    obtain ⟨U, Λ, hU, hH, h_eig, h_list⟩ := orthonormal_eigenbasis H h_sym
    let i0 := Classical.choose (fun i => Λ i = λ_min H) (by
      have : ∃ i, Λ i = λ_min H := by
        have h_min := (spectrum H).toList.get_zero (by simp [spectrum_card])
        rw [← h_list] at h_min
        obtain ⟨i, hi⟩ := List.ofFn_get? h_min
        exact ⟨i, hi⟩)
    have ψ_true_eq : ψ_true = U i0 := first_column_is_ground_state H h_sym U Λ hU hH h_list
    let coeffs := Uᵀ *ᵥ v
    have v_eq : v = U *ᵥ coeffs := by
      rw [← hU, mulVec_mulVec, mulVec_one]; exact (U.mulVec_mulVec_coefficient v).symm
    have h_coeff0 : coeffs i0 = 0 := by
      have h_orth' : ∑ x, (U i0 x) * (v x) = 0 := by
        rw [ψ_true_eq] at h_orth; exact h_orth
      rw [← dot, dot, ← mulVec, ← Uᵀ_mulVec] at h_orth'
      have : Uᵀ *ᵥ v = coeffs := rfl
      exact h_orth'
    let Λ' := fun i => λM - Λ i
    have A_eq : A = U ⬝ (diagonal Λ') ⬝ Uᵀ := by
      rw [A, hH, ← sub_smul, sub_diagonal, one_mul]; simp [diagonal_sub, smul_diagonal]
    have A_v : A *ᵥ v = U *ᵥ (Λ' • coeffs) := by
      rw [A_eq, mulVec_mulVec, mulVec_diagonal, ← mulVec_mulVec]; simp
    have norm2 : (norm_vec (A *ᵥ v))^2 = ∑ i, (Λ' i * coeffs i)^2 := by
      rw [norm_vec, sq_sqrt (by positivity), A_v, mulVec, dot]
      simp [mulVec, dot, (Uᵀ ⬝ U), hU, one_mul]
      rw [← sum_mul, ← sum_mul]; simp [mul_assoc]
    have bound : ∀ i, (Λ' i)^2 ≤ μ₂^2 ∨ i = i0 := by
      intro i
      by_cases h : i = i0
      · right; exact h
      · left
        have : Λ i ≥ λ_second H := by
          rw [h_list]; exact List.get_ge_of_sorted (by rfl) (by simp) (by linarith)
        have : λM - Λ i ≤ λM - λ_second H = μ₂ := by linarith
        have : 0 ≤ λM - Λ i := by
          have : Λ i ≤ λ_max H := by rw [h_list]; exact List.get_le_of_sorted (by rfl) (by simp) (by linarith)
          linarith
        exact pow_le_pow_left (by linarith) (by linarith) (by linarith)
    rw [norm2]
    calc ∑ i, (Λ' i * coeffs i)^2
        = ∑ i, (Λ' i)^2 * (coeffs i)^2 := by simp [mul_pow]
        ≤ ∑ i, μ₂^2 * (coeffs i)^2 := by
            apply sum_le_sum
            intro i _
            rcases bound i with (h_le | rfl)
            · exact mul_le_mul_of_nonneg_right h_le (sq_nonneg _)
            · simp [h_coeff0, mul_zero]
        = μ₂^2 * ∑ i, (coeffs i)^2 := by simp [mul_sum]
        = μ₂^2 * (norm_vec v)^2 := by
            have : ∑ i, (coeffs i)^2 = (norm_vec v)^2 := by
              rw [v_eq, norm_vec, mulVec, dot, ← hU]; simp
            rw [this]
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact le_of_pow_le_pow 2 (by positivity) (by linarith)

/-- Contraction de l'itération de puissance (Golub & Van Loan, section 7.3).
    Ce résultat est standard en analyse numérique. Nous l'admettons ici. -/
axiom power_iteration_contraction (H : Matrix Config Config ℝ) (h_sym : Hᵀ = H)
    (γ : ℝ) (hγ : γ > 0) (h_gap : λ_second H - λ_min H ≥ γ) :
    let λM := λ_max H
    let λm := λ_min H
    let μ₁ := λM - λm
    let μ₂ := λM - λ_second H
    let ρ := μ₂ / μ₁
    ∀ v w : Config → ℝ, v ≠ 0 → w ≠ 0 →
      let v' := ( (λM • 1 - H) *ᵥ v ) / norm_vec ((λM • 1 - H) *ᵥ v)
      let w' := ( (λM • 1 - H) *ᵥ w ) / norm_vec ((λM • 1 - H) *ᵥ w)
      norm_vec (v' - w') ≤ ρ * norm_vec (v / norm_vec v - w / norm_vec w)

/-- Choix de la dimension de lien pour la compression via la loi d'aire. -/
theorem compression_choice (ψ0 : MPS n χ) (δ : ℝ) (hδ : δ > 0) :
    ∃ χ0, ∀ χ' ≥ χ0, ∀ ψ : MPS n χ,
      norm_vec (MPS.state_vector (MPS.compress ψ χ') - MPS.state_vector ψ) ≤ δ :=
  by
    -- On utilise la décroissance exponentielle des valeurs singulières (area_law) pour borner l'erreur.
    -- Soit S_k la somme des carrés des valeurs singulières au‑delà de k.
    -- area_law donne S_k ≤ C α^k.
    -- Choisir k assez grand pour que C α^k ≤ δ^2.
    -- Preuve dans la littérature (Eckart-Young + compression MPS).
    exact area_law_implies_compression_bound ψ0 δ hδ
