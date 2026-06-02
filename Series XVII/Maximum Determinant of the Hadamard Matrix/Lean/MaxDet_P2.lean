/- XVII_MaxDetP2.lean - Pilier P2 : trou spectral constant via Kithima Bridge. -/

import XVII_MaxDetP1
import Kernel.KithimaBridge

open Kernel.SpectralLibrary

namespace SeriesXVII.MaxDet

variable (n : ℕ) (hn : n ≥ 1) (k : ℤ) (hk : k ≥ 0)

def H := hamiltonian n k
def Δ := adjacency n
def V := diagonal (potential n k)

lemma V_nonneg : ∀ σ, potential n k σ ≥ 0 := by
  intro σ; rw [potential]; split_ifs <;> linarith

lemma Δ_off_nonneg : ∀ i j, i ≠ j → Δ i j ≥ 0 := by
  intro i j h; simp [Δ]; split_ifs <;> linarith

theorem maxdet_spectral_gap : spectral_gap H ≥ 2 :=
  kithima_bridge V V_nonneg Δ Δ_off_nonneg 1 (by norm_num) (hypercube_spectral_gap (N n))

end SeriesXVII.MaxDet
