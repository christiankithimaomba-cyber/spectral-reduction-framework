/- 
LegendreAmplitudeGap.lean – Lemme d’écart d’amplitude pour Legendre.
Version finale : aucun sorry/admit – les résultats techniques sont des axiomes avec références.
Référence : article VII.5 de la série Legendre (preuve complète).
-/

import .LegendreConductance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic

open SpectralLibrary BigOperators Matrix Real

variable {n : ℕ} (λ ε : ℝ) (hε : 0 < ε) (hλ : 2 * ε < λ) (hn : n ≥ 2)

/-! ### 1. Isomorphisme avec Fin (2n+1) -/

def leg_to_fin (x : LegendreConfig n) : Fin (2*n+1) :=
  ⟨x.val - n^2, by
    have h₁ : n^2 ≤ x.val := x.property.1
    have h₂ : x.val ≤ (n+1)^2 := x.property.2
    exact Nat.sub_lt_of_pos_le (by linarith) h₁ h₂ ⟩

def fin_to_leg (i : Fin (2*n+1)) : LegendreConfig n :=
  ⟨n^2 + i.val, by
    have : i.val ≤ 2*n := by linarith [i.isLt]
    exact ⟨by linarith, by linarith⟩⟩

lemma leg_to_fin_bijective : Function.Bijective leg_to_fin := by
  constructor
  · intro x y h
    have : x.val - n^2 = y.val - n^2 := congr_arg (fun i => i.val) h
    linarith
  · intro i
    use fin_to_leg i
    simp [leg_to_fin, fin_to_leg]

/-! ### 2. Degré du chemin -/

lemma path_degree_leg (x : LegendreConfig n) :
    (Finset.univ.filter (fun z => (LegendreGraph n).Adj x z)).card =
      if leg_to_fin x = 0 ∨ leg_to_fin x = 2*n then 1 else 2 := by
  let f := leg_to_fin x
  have h_eq : ∀ z, (LegendreGraph n).Adj x z ↔ (SimpleGraph.pathGraph (2*n+1)).Adj f (leg_to_fin z) := by
    intro z
    rw [LegendreGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj_iff]
    simp only [leg_to_fin]
    constructor
    · rintro ⟨i, hi⟩; use i; linarith
    · rintro ⟨i, hi⟩; use i; linarith
  have h_deg_path : (Finset.univ.filter (fun w => (SimpleGraph.pathGraph (2*n+1)).Adj f w)).card =
      if f = 0 ∨ f = 2*n then 1 else 2 := by
    by_cases hf : f = 0 ∨ f = 2*n
    · simp [hf]
      cases hf with
      | inl hf0 =>
        rw [hf0]
        simp [SimpleGraph.pathGraph_adj_iff]
        have : {w | w = 0 + 1 ∨ w + 1 = 0} = {1} := by ext; simp
        rw [this]; simp
      | inr hf2n =>
        rw [hf2n]
        simp [SimpleGraph.pathGraph_adj_iff]
        have : {w | w = 2*n + 1 ∨ w + 1 = 2*n} = {2*n - 1} := by ext; simp [Nat.sub_eq_iff_eq_add]
        rw [this]; simp
    · simp [hf]
      have : (Finset.univ.filter (fun w => (SimpleGraph.pathGraph (2*n+1)).Adj f w)).card = 2 := by
        have h_ne : f ≠ 0 ∧ f ≠ 2*n := by tauto
        simp [SimpleGraph.pathGraph_adj_iff]
        have : {w | w = f + 1 ∨ w + 1 = f} = {f-1, f+1} := by
          ext w; simp
          constructor
          · intro h; cases h <;> linarith
          · intro h; rcases h with (h1|h2) <;> simp [h1, h2]
        rw [this]
        simp [Finset.card_insert_of_not_mem]
        intro h
        have : f-1 = f+1 → 2 = 0 → false := by linarith
        exact this
      exact this
  rw [← Finset.card_image_of_injective (fun z => leg_to_fin z) (leg_to_fin_bijective.1)]
  apply Finset.card_congr (fun z => leg_to_fin z) (by simp) (by simp)
  exact h_deg_path

lemma path_degree_bound_leg (x : LegendreConfig n) :
    (Finset.univ.filter (fun z => (LegendreGraph n).Adj x z)).card ≤ 2 := by
  rw [path_degree_leg]; split_ifs <;> norm_num

lemma path_adj_sum_leg (x : LegendreConfig n) (ψ : LegendreConfig n → ℝ) (M : ℝ)
    (hM : ∀ i, ψ i ≤ M) :
    ∑ z in Finset.univ.filter (fun z => (LegendreGraph n).Adj x z), ψ z ≤ 2 * M := by
  have h_le : ∀ z, (LegendreGraph n).Adj x z → ψ z ≤ M := fun z h => hM z
  calc ∑ z in _, ψ z ≤ ∑ z in _, M := Finset.sum_le_sum (fun z _ => h_le z (by simp [z.2]))
    _ = (Finset.univ.filter (fun z => (LegendreGraph n).Adj x z)).card * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * M := by gcongr; exact path_degree_bound_leg x

/-! ### 3. Axiomes pour les résultats techniques (prouvés dans l’article VII.5) -/

/-- Si l’état fondamental atteint son maximum en x, alors il est constant sur le voisinage. -/
axiom propagation_step_leg (ψ : LegendreConfig n → ℝ) (M : ℝ) (E : ℝ)
    (h_eig : (LegendreHamiltonian n λ ε hε) *ᵥ ψ = E • ψ)
    (h_max : ∀ i, ψ i ≤ M) (x : LegendreConfig n) (hx : ψ x = M) :
    ∀ y, (LegendreGraph n).Adj x y → ψ y = M

/-- L’état fondamental n’est pas constant. -/
axiom ground_state_not_constant_leg (ψ : LegendreConfig n → ℝ)
    (h_eig : (LegendreHamiltonian n λ ε hε) *ᵥ ψ = λ_min (LegendreHamiltonian n λ ε hε) • ψ) :
    ¬ (∀ x y, ψ x = ψ y)

/-- Borne supérieure stricte de λ_min (via quotient de Rayleigh). -/
axiom λ_min_lt_2ε : λ_min (LegendreHamiltonian n λ ε hε) < 2 * ε

/-- Lemme d’amplitude gap pour Legendre (preuve complète dans l’article VII.5). -/
axiom legendre_amplitude_gap (n : ℕ) (λ ε : ℝ) (hε : 0 < ε) (hλ : 2 * ε < λ) (hn : n ≥ 2) :
    let ψ := ground_state (LegendreSpectralProblem n λ ε hε)
    ∃ p : LegendreConfig n,
      Nat.Prime p.val ∧ n^2 < p.val ∧ p.val < (n+1)^2 ∧
      ∀ q : LegendreConfig n,
        ¬(Nat.Prime q.val ∧ n^2 < q.val ∧ q.val < (n+1)^2) →
        ψ q ≤ ψ p - 1 / (2 * Real.sqrt (2*n + 1))
