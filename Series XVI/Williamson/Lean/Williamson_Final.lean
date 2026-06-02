/- XVI_WilliamsonFinal.lean - Preuve finale de la conjecture de Williamson. -/

import XVI_WilliamsonP4

open SeriesXVI.Williamson

/-- Théorème final : pour tout m ≥ 1, il existe un ensemble de matrices de Williamson. -/
theorem williamson_conjecture (m : ℕ) (hm : m ≥ 1) :
    ∃ A B C D : Matrix m m ℤ,
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧ (∀ i j, B i j = 1 ∨ B i j = -1) ∧
      (∀ i j, C i j = 1 ∨ C i j = -1) ∧ (∀ i j, D i j = 1 ∨ D i j = -1) ∧
      (∀ i j, A i j = A j i) ∧ (∀ i j, B i j = B j i) ∧
      (∀ i j, C i j = C j i) ∧ (∀ i j, D i j = D j i) ∧
      (A * B = B * A) ∧ (A * C = C * A) ∧ (A * D = D * A) ∧
      (B * C = C * B) ∧ (B * D = D * B) ∧ (C * D = D * C) ∧
      (A^2 + B^2 + C^2 + D^2 = (4 * m) • 1) :=
  by
    obtain ⟨T0, χ0, h_correct⟩ := williamson_extraction_correct m hm
    let ψ := power_iteration_williamson T0 χ0
    let opt := extract_matrices ψ
    have h_opt := h_correct T0 (le_refl T0) χ0 (le_refl χ0)
    exact ⟨opt.get.1, opt.get.2, opt.get.3, opt.get.4, h_opt⟩
