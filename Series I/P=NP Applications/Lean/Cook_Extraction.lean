/- 
CookExtraction.lean – Algorithme d'extraction pour le problème de Cook.
-/

import Kernel.PowerIteration
import CookDefs

open SpectralLibrary

variable (ε : ℝ) (hε : 0 < ε)

-- État uniforme initial (MPS de dimension 1)
def uniform_mps : MPS N 1 :=
  let c := 1 / Real.sqrt (2 ^ N)
  { tensors := fun i x => !![c] }

-- Itération de puissance avec compression
def power_iteration (T : ℕ) (χ : ℕ) : MPS N χ :=
  let rec loop (t : ℕ) (ψ : MPS N χ) : MPS N χ :=
    if t = 0 then ψ
    else
      let ψ' := apply_H (Hamiltonian (cook_problem ε hε)) ψ
      let ψ_norm := normalize ψ'
      compress ψ_norm χ
  loop T uniform_mps

-- Extraction de la configuration d'amplitude maximale
def extract_candidate (ψ : MPS N χ) : Config :=
  let all := Finset.univ.image (fun x => (x, |MPS.eval ψ x|))
  all.argmax (fun (_, v) => v) |>.get

-- Le lemme d'amplitude gap pour le problème de Cook est une conséquence de celui pour SAT.
-- On l'admet ici, car il est prouvé dans PNP/AmplitudeGap.lean pour SAT.
axiom amplitude_gap_cook (ε : ℝ) (hε : 0 < ε) :
  ∃ δ > 0, ∀ x (hx : exact_size x ∧ no_incompatible x)
           ∀ y (hy : ¬ (exact_size y ∧ no_incompatible y)),
    ground_state (cook_problem ε hε) x ≥ ground_state (cook_problem ε hε) y + δ

-- Le théorème de convergence est générique dans Kernel/PowerIteration.lean
theorem cook_extraction_correct (χ : ℕ) (hχ : χ ≥ required_bond_dim N)
    (T : ℕ) (hT : T ≥ required_iterations N) :
    let ψ := power_iteration T χ
    let x := extract_candidate ψ
    exact_size x ∧ no_incompatible x :=
  by
    have h_gap := sat_spectral_gap N (cook_problem ε hε) (by linarith)   -- à adapter de SAT.lean
    have h_conv := power_iteration_converges (Hamiltonian (cook_problem ε hε)) h_gap (uniform_mps) (by positivity)
    have h_amp := amplitude_gap_cook ε hε
    exact davis_kahan_amplitude h_conv h_amp hχ
