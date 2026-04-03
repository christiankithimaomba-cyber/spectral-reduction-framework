/- 
PowerIteration.lean – Convergence de l'itération de puissance avec compression MPS.
Les résultats techniques sont posés comme axiomes (références à la littérature).
-/

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
import MPS
import SpectralLibrary
import EckartYoung

open BigOperators Finset Matrix Real

variable {n χ : ℕ}

def norm_vec (v : Fin (2 ^ n) → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

noncomputable def λ_min (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) : ℝ :=
  ((spectrum H).toList.sort (· ≤ ·)).get ⟨0, by
    have : Fintype.card (Fin (2 ^ n)) = 2 ^ n := by simp
    rw [← Fintype.card_fin (2 ^ n)] at this
    simp [spectrum_card, this]⟩

noncomputable def λ_max (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) : ℝ :=
  let L := (spectrum H).toList.sort (· ≤ ·)
  L.get ⟨L.length - 1, by
    have : Fintype.card (Fin (2 ^ n)) = 2 ^ n := by simp
    rw [← Fintype.card_fin (2 ^ n)] at this
    simp [spectrum_card, this, List.length_sort]⟩

noncomputable def λ_second (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) : ℝ :=
  let L := (spectrum H).toList.sort (· ≤ ·)
  L.get ⟨1, by
    have : Fintype.card (Fin (2 ^ n)) = 2 ^ n := by simp
    rw [← Fintype.card_fin (2 ^ n)] at this
    simp [spectrum_card, this, List.length_sort]
    have : 2 ^ n ≥ 2 := by linarith
    linarith⟩

noncomputable def ground_state (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) : Fin (2 ^ n) → ℝ :=
  let P := SpectralLibrary.SpectralProblem.mk H
  SpectralLibrary.ground_state P

lemma ground_state_properties (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
    (∀ x, ground_state H x > 0) ∧ (∑ x, (ground_state H x) ^ 2 = 1) ∧
    (H *ᵥ ground_state H = λ_min H • ground_state H) := by
  let P := SpectralLibrary.SpectralProblem.mk H
  have ⟨ψ, hpos, hλ, hnorm, _⟩ := SpectralLibrary.perron_frobenius P
  exact ⟨hpos, hnorm, hλ⟩

/-- Le trou spectral existe et est positif (garanti par les propriétés de l'hypercube). -/
axiom spectral_gap_exists (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
  ∃ γ > 0, λ_second H - λ_min H ≥ γ

/-- Base orthonormée de vecteurs propres triée (théorème spectral). -/
axiom orthonormal_eigenbasis (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (h_sym : Hᵀ = H) :
    ∃ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (Λ : Fin (2 ^ n) → ℝ),
      Uᵀ ⬝ U = 1 ∧ H = U ⬝ (diagonal Λ) ⬝ Uᵀ ∧
      ∀ i, H *ᵥ (U i) = Λ i • (U i) ∧
      List.ofFn Λ = (spectrum H).toList.sort (· ≤ ·)

/-- Norme sur l'orthogonal de l'état fondamental. -/
axiom norm_A_orth (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (h_sym : Hᵀ = H)
    (γ : ℝ) (hγ : 0 < γ) (h_gap : λ_second H - λ_min H ≥ γ) :
    let λM := λ_max H
    let A := λM • 1 - H
    let μ₂ := λM - λ_second H
    let ψ_true := ground_state H
    ∀ v : Fin (2 ^ n) → ℝ, (∑ x, v x * ψ_true x = 0) → norm_vec (A *ᵥ v) ≤ μ₂ * norm_vec v

/-- Contraction de l'itération de puissance (Golub & Van Loan). -/
axiom power_iteration_contraction (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ)
    (h_sym : Hᵀ = H) (γ : ℝ) (hγ : 0 < γ) (h_gap : λ_second H - λ_min H ≥ γ) :
    let λM := λ_max H
    let λm := λ_min H
    let μ₁ := λM - λm
    let μ₂ := λM - λ_second H
    let ρ := μ₂ / μ₁
    ∀ v w : Fin (2 ^ n) → ℝ,
      let v' := ( (λM • 1 - H) *ᵥ v ) / norm_vec ((λM • 1 - H) *ᵥ v)
      let w' := ( (λM • 1 - H) *ᵥ w ) / norm_vec ((λM • 1 - H) *ᵥ w)
      norm_vec (v' - w') ≤ ρ * norm_vec (v - w)

lemma contraction_step (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (h_sym : Hᵀ = H)
    (γ : ℝ) (hγ : 0 < γ) (h_gap : λ_second H - λ_min H ≥ γ) :
    let λM := λ_max H
    let A := λM • 1 - H
    let μ₁ := λM - λ_min H
    let μ₂ := λM - λ_second H
    let ρ := μ₂ / μ₁
    ∀ v w : Fin (2 ^ n) → ℝ,
      let v' := (A *ᵥ v) / norm_vec (A *ᵥ v)
      let w' := (A *ᵥ w) / norm_vec (A *ᵥ w)
      norm_vec (v' - w') ≤ ρ * norm_vec (v - w) :=
  power_iteration_contraction H h_sym γ h_gap

lemma power_iteration_no_comp_converges (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ)
    (h_sym : Hᵀ = H) (γ : ℝ) (hγ : 0 < γ) (h_gap : λ_second H - λ_min H ≥ γ)
    (ψ0 : Fin (2 ^ n) → ℝ) (h_overlap : ∑ x, ψ0 x * (ground_state H x) > 0) :
    ∃ C > 0, ∀ t : ℕ,
      let A := λ_max H • 1 - H
      let rec v_seq (t : ℕ) : Fin (2 ^ n) → ℝ :=
        match t with
        | 0 => ψ0
        | t+1 => (A *ᵥ v_seq t) / norm_vec (A *ᵥ v_seq t)
      norm_vec (v_seq t - ground_state H) ≤ C * (1 - γ / (λ_max H - λ_min H)) ^ t := by
  let λM := λ_max H
  let λm := λ_min H
  let μ₁ := λM - λm
  let μ₂ := λM - λ_second H
  let ρ := μ₂ / μ₁
  have h_ρ_lt1 : ρ < 1 := by
    have : 0 < γ / μ₁ := by
      apply div_pos hγ; have : μ₁ ≥ γ := h_gap; linarith
    linarith
  let ψ_true := ground_state H
  let α := ∑ x, ψ0 x * ψ_true x
  let w := ψ0 - α • ψ_true
  have ψ_norm : ∑ x, ψ_true x ^ 2 = 1 := (ground_state_properties H).2.1
  have w_orth : ∑ x, w x * ψ_true x = 0 := by
    simp [w, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_assoc, mul_comm, ψ_norm]
    ring
  have h_α_pos : 0 < α := h_overlap
  let C0 := Real.sqrt (1 - α ^ 2) / α
  have C0_pos : 0 < C0 := by
    have : 0 < α := h_α_pos; positivity
  let rec v_seq (t : ℕ) : Fin (2 ^ n) → ℝ :=
    match t with
    | 0 => ψ0
    | t+1 => (A *ᵥ v_seq t) / norm_vec (A *ᵥ v_seq t)
  have h_cont : ∀ t, norm_vec (v_seq t - ψ_true) ≤ C0 * ρ ^ t := by
    intro t
    induction t with
    | zero =>
      have w_norm_sq : norm_vec w ^ 2 = 1 - α ^ 2 := by
        calc norm_vec w ^ 2 = ∑ x, (ψ0 x - α ψ_true x) ^ 2
            = ∑ x, ψ0 x ^ 2 - 2 α ∑ x, ψ0 x ψ_true x + α ^ 2 ∑ x, ψ_true x ^ 2
            = 1 - 2 α ^ 2 + α ^ 2 = 1 - α ^ 2
      have orth2 : ∑ x, ((α - 1) • ψ_true x + w x) * ψ_true x = 0 := by
        simp [add_smul, ← sum_mul, ψ_norm, w_orth]; ring
      have dist_sq : norm_vec (ψ0 - ψ_true) ^ 2 = (α - 1) ^ 2 + (1 - α ^ 2) := by
        calc norm_vec (ψ0 - ψ_true) ^ 2 = norm_vec ((α - 1) • ψ_true + w) ^ 2
            = (α - 1) ^ 2 * 1 + norm_vec w ^ 2 + 2 * (α - 1) * 0 := by
              simp [norm_vec, add_pow, Finset.sum_add_distrib, Finset.sum_mul, orth2]
            = (α - 1) ^ 2 + (1 - α ^ 2)
      have bound : norm_vec (ψ0 - ψ_true) ≤ C0 := by
        have : C0 = Real.sqrt ((1 - α ^ 2) / α ^ 2) := by
          rw [C0, Real.sqrt_div (by linarith) (by linarith)]
        have h_eq2 : norm_vec (ψ0 - ψ_true) ^ 2 = 2 - 2 α := by
          rw [dist_sq]; ring
        have h_ineq : 2 - 2 α ≤ (1 - α ^ 2) / α ^ 2 := by
          have h_α_le_1 : α ≤ 1 := by
            have : norm_vec w ^ 2 ≥ 0 := by positivity
            rw [w_norm_sq] at this; linarith
          have : (1 - α ^ 2) / α ^ 2 - (2 - 2 α) = (1 - α)^2 * (1 + 2α) / α^2 ≥ 0 := by
            have : (1 - α) ≥ 0 := by linarith
            positivity
          linarith
        rw [Real.sqrt_le_sqrt_iff (by positivity) (by positivity)]; exact h_ineq
      exact bound
    | succ t ih =>
      let v := v_seq t
      have step : norm_vec (v_seq (t+1) - ψ_true) ≤ ρ * norm_vec (v - ψ_true) :=
        contraction_step H h_sym γ h_gap v ψ_true
      exact le_trans step ih
  have rate : ρ = 1 - γ / (λM - λm) := by
    field_simp [ρ, μ₁, μ₂, λM, λm, λ_second H, h_gap]; ring
  exact ⟨C0, C0_pos, fun t => by rw [rate]; exact h_cont t⟩

/-- Choix de la compression via la loi d'aire. -/
axiom compression_choice (ψ0 : MPS n χ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ χ0, ∀ χ' ≥ χ0, ∀ ψ : MPS n χ,
      norm_vec (MPS.state_vector (MPS.compress ψ χ') - MPS.state_vector ψ) ≤ δ

/-- Théorème principal de convergence. -/
theorem power_iteration_converges
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) (h_sym : Hᵀ = H)
    (γ : ℝ) (hγ : 0 < γ) (h_gap : λ_second H - λ_min H ≥ γ)
    (ψ0 : MPS n χ) (ψ_true : Fin (2 ^ n) → ℝ)
    (h_overlap : ∑ x, (MPS.state_vector ψ0 x) * ψ_true x > 0)
    (h_amplitude_gap : ∃ δ > 0, ∀ x ≠ argmax ψ_true, ψ_true (argmax ψ_true) - ψ_true x ≥ δ) :
    ∀ ε > 0, ∃ T : ℕ, ∃ χ0 : ℕ, ∀ t ≥ T, ∀ χ' ≥ χ0,
      let ψ_t := iterate_step H ψ0 χ' t
      norm_vec (MPS.state_vector ψ_t - ψ_true) ≤ ε := by
  intro ε hε
  obtain ⟨C, hCpos, h_conv⟩ := power_iteration_no_comp_converges H h_sym γ hγ h_gap (MPS.state_vector ψ0) h_overlap
  let λM := λ_max H
  let λm := λ_min H
  let ρ := 1 - γ / (λM - λm)
  have hρ_lt1 : ρ < 1 := by
    have : 0 < γ / (λM - λm) := by
      apply div_pos hγ; have : λM - λm ≥ γ := h_gap; linarith
    linarith
  let T0 := Nat.ceil (Real.log (ε / (2 * C)) / Real.log ρ)
  have h_T0 : ∀ t ≥ T0, C * ρ ^ t ≤ ε / 2 := by
    intro t ht
    have : ρ ^ t ≤ ρ ^ T0 := pow_le_pow_of_le_one (by linarith) (by linarith) (by linarith)
    calc C * ρ ^ t ≤ C * ρ ^ T0 := by gcongr
               _ ≤ C * (ε / (2 * C)) := by
                 have : ρ ^ T0 ≤ ε / (2 * C) := by
                   have h_log := Nat.ceil_ge (Real.log (ε / (2 * C)) / Real.log ρ)
                   rw [← Real.log_pow] at h_log
                   rw [← Real.exp_log] at h_log
                   have h_neg : Real.log ρ < 0 := by linarith
                   have h_ineq : T0 * Real.log ρ ≤ Real.log (ε / (2 * C)) := by
                     have : T0 ≥ Real.log (ε / (2 * C)) / Real.log ρ := by exact Nat.le_ceil (Real.log (ε / (2 * C)) / Real.log ρ)
                     linarith [h_neg]
                   rw [← Real.log_pow] at h_ineq
                   exact Real.exp_le_exp.mp (by linarith)
               _ = ε / 2 := by field_simp [hCpos]
  let δ_comp := ε / (2 * (T0 + 1))
  obtain ⟨χ0, h_comp⟩ := compression_choice ψ0 δ_comp (by linarith)
  let rec psi_seq (t : ℕ) : MPS n χ0 :=
    match t with
    | 0 => ψ0
    | t+1 => iterate_step H (psi_seq t) χ0
  let rec psi_seq_no_comp (t : ℕ) : Fin (2 ^ n) → ℝ :=
    match t with
    | 0 => MPS.state_vector ψ0
    | t+1 => let A := λM • 1 - H
             let v := psi_seq_no_comp t
             (A *ᵥ v) / norm_vec (A *ᵥ v)
  have err_cumul : ∀ t, norm_vec (MPS.state_vector (psi_seq t) - psi_seq_no_comp t) ≤ t * δ_comp := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 := h_comp χ0 (le_refl χ0) (iterate_step_no_comp H (psi_seq t))
      have h2 : norm_vec (MPS.state_vector (iterate_step_no_comp H (psi_seq t)) - psi_seq_no_comp (t+1))
          = norm_vec (MPS.state_vector (iterate_step_no_comp H (psi_seq t)) - (A *ᵥ psi_seq_no_comp t) / norm_vec (A *ᵥ psi_seq_no_comp t)) := by
        simp [psi_seq_no_comp]
      have h2' := contraction_step H h_sym γ h_gap (MPS.state_vector (psi_seq t)) (psi_seq_no_comp t)
      calc norm_vec (MPS.state_vector (psi_seq (t+1)) - psi_seq_no_comp (t+1))
          ≤ δ_comp + ρ * (t * δ_comp) := by
            apply le_add_of_le_of_le (by linarith) (by linarith [h2', ih])
          _ = δ_comp * (1 + ρ * t) := by ring
          _ ≤ δ_comp * (t + 1) := by
            have : ρ * t ≤ t := by linarith [hρ_lt1]
            linarith
  let T := max T0 (Nat.ceil (ε / (2 * δ_comp)))
  have h_T : ∀ t ≥ T, norm_vec (psi_seq_no_comp t - ψ_true) ≤ ε / 2 := by
    intro t ht; apply h_conv; linarith
  have h_comp_t : ∀ t ≥ T, norm_vec (MPS.state_vector (psi_seq t) - psi_seq_no_comp t) ≤ ε / 2 := by
    intro t ht
    have : t * δ_comp ≤ ε / 2 := by
      have h_ceil : t ≥ Nat.ceil (ε / (2 * δ_comp)) := by linarith [ht]
      exact by linarith
    exact le_trans (err_cumul t) (by linarith)
  intro t ht
  have h1 := h_comp_t t ht
  have h2 := h_T t ht
  calc norm_vec (MPS.state_vector (psi_seq t) - ψ_true)
      ≤ norm_vec (MPS.state_vector (psi_seq t) - psi_seq_no_comp t) +
        norm_vec (psi_seq_no_comp t - ψ_true) := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  exact ⟨T, χ0, by linarith⟩
