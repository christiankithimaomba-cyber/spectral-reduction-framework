/-
KummerVandiverHamiltonian.lean – Hamiltonien spectral H_p = T_p - I.
-/

import .KummerVandiverTransfer
import Kernel.SpectralLibrary

open SpectralLibrary

variable (p : ℕ) (hp : p.Prime ∧ p > 2)

/-- L'espace de configuration est isomorphe à Fin 4 (via la base de K₄(ℤ)). -/
def Config := Fin 4

/-- La matrice de l'opérateur de transfert sur cette base. -/
noncomputable def T : Matrix Config Config ℝ := transfer_operator p hp

/-- Hamiltonien spectral H = T - I. -/
noncomputable def H_KV : Matrix Config Config ℝ := T - 1

/-- H est auto‑adjoint. -/
lemma H_selfadjoint : H_KVᵀ = H_KV := by
  rw [H_KV, transpose_sub, transfer_selfadjoint, transpose_one]; rfl

/-- Le spectre de H est le spectre de T décalé de -1. -/
lemma spectrum_H : spectrum H_KV = (λ x : ℝ, x - 1) '' (spectrum T) :=
  spectrum_sub_left 1 T
