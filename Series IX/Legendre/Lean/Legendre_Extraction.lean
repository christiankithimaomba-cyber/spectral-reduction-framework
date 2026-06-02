/- 
LegendreExtraction.lean – Algorithme d’extraction d’un nombre premier.
-/

import .LegendreAreaLaw
import .LegendreAmplitudeGap
import Kernel.PowerIteration

open Kernel.PowerIteration

def legendre_extract (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) (T χ : ℕ) : Option ℕ :=
  let H := LegendreHamiltonian n λ ε hε
  let ψ0 := MPS.uniform_state (2*n+1)
  let ψT := power_iteration H ψ0 χ T
  let vec := MPS.state_vector ψT
  let i_max := Finset.argmax vec Finset.univ
  if let some k := i_max then
    if Nat.Prime k then some k else none
  else none

theorem legendre_extraction_correct (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ)
    (h_amp : ∃ p, Nat.Prime p ∧ n^2 < p ∧ p < (n+1)^2 ∧
        ∀ q, ¬(Nat.Prime q ∧ n^2 < q ∧ q < (n+1)^2) → ψ0 H q ≤ ψ0 H p - δ) :
    ∃ T χ, ∀ t ≥ T, ∀ χ' ≥ χ,
      let p := legendre_extract n λ ε hε t χ'
      p.isSome ∧ Nat.Prime p.get := by
  let H := LegendreHamiltonian n λ ε hε
  let ψ_true := ground_state (LegendreSpectralProblem n λ ε hε)
  let ψ0_vec := MPS.state_vector (MPS.uniform_state (2*n+1))
  have h_overlap : ∑ x, ψ0_vec x * ψ_true x > 0 :=
    sum_pos (fun x _ => mul_pos (by positivity) (ψ0_pos H hε x)) (by simp)
  have h_gap := legendre_spectral_gap n λ ε hε
  obtain ⟨T0, χ0, h_conv⟩ := power_iteration_converges H (by apply IsSymm.adjoint_symm)
      (λ_min H) (by linarith) h_gap ψ0_vec ψ_true h_overlap h_amp (δ/4) (by linarith)
  exact ⟨T0, χ0, h_conv⟩
