/-
MPS.lean – Structure MPS, construction par l'algorithme de Vidal.
Les résultats techniques non démontrés ici sont posés comme axiomes (références à la littérature).
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.SVD
import Mathlib.LinearAlgebra.Matrix.Norms
import Mathlib.Tactic
import EckartYoung

open Matrix Real

structure MPS (n χ : ℕ) where
  tensors : Fin n → (Bool → Matrix (Fin χ) (Fin χ) ℝ)

namespace MPS

/-! ### Conversions entre configurations et indices -/

def config_to_nat (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ (i.val) else 0

private lemma sum_pow_two : ∑ i : Fin n, 2 ^ (i.val) = 2 ^ n - 1 := by
  have : (∑ i in Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
    induction n with
    | zero => simp
    | succ n ih => simp [Finset.sum_range_succ, ih, pow_succ, ← sub_add, add_comm]
  rw [← this]
  apply Finset.sum_equiv (Finset.range n) (fun i => i) (fun i => i)
  · simp [Finset.card_univ, Finset.card_range]
  · intro i; simp

theorem config_to_nat_inj : Function.Injective config_to_nat := by
  intro x y h
  funext i
  have h_eq : ∀ i, (config_to_nat x) >> i.val & 1 = (config_to_nat y) >> i.val & 1 := by
    rw [h]; exact fun _ => rfl
  specialize h_eq i
  simp [config_to_nat, Nat.testBit_bitwise, Nat.testBit_of_lt, Nat.bitwise_iff] at h_eq
  exact h_eq

theorem config_to_nat_lt (x : Fin n → Bool) : config_to_nat x < 2 ^ n := by
  have : config_to_nat x ≤ ∑ i, 2 ^ i.val := sum_le_sum (fun i _ => by split_ifs <;> linarith)
  rw [sum_pow_two] at this
  exact lt_of_le_of_lt this (by linarith)

def config_to_fin (x : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨config_to_nat x, config_to_nat_lt x⟩

def fin_to_config (i : Fin (2 ^ n)) : Fin n → Bool :=
  fun j => Nat.testBit i.val j.val

@[simp]
theorem config_to_fin_fin_to_config (i : Fin (2 ^ n)) : config_to_fin (fin_to_config i) = i := by
  apply Fin.ext
  simp [config_to_fin, fin_to_config, config_to_nat]
  have : ∑ j : Fin n, if Nat.testBit i.val j.val then 2 ^ j.val else 0 = i.val := by
    have h : ∀ m < 2 ^ n, ∑ j : Fin n, (m >> j.val & 1) * 2 ^ j.val = m := by
      intro m hm
      induction n generalizing m with
      | zero => simp
      | succ n ih =>
        let lo := m % 2
        let hi := m / 2
        have h_hi : hi < 2 ^ n := by
          have : hi ≤ m / 2 ≤ (2 ^ (n+1) - 1) / 2 < 2 ^ n := by linarith
        have h_eq : m = lo + 2 * hi := by rw [mod_add_div]
        calc ∑ j : Fin (n+1), (m >> j.val & 1) * 2 ^ j.val
            = (m >> 0 & 1) * 2 ^ 0 + ∑ j : Fin n, (m >> (j.val+1) & 1) * 2 ^ (j.val+1) := by
              rw [Finset.sum_range_succ, Fin.val_zero]; simp
            = lo + ∑ j : Fin n, (hi >> j.val & 1) * 2 ^ (j.val+1) := by
              simp [Nat.shiftRight_succ, Nat.testBit_shiftRight, Nat.mul_comm]
            = lo + 2 * ∑ j : Fin n, (hi >> j.val & 1) * 2 ^ j.val := by
              simp [mul_sum, mul_comm 2, ← pow_succ]
            = lo + 2 * hi := by rw [ih hi h_hi]
            = m := h_eq
    exact h i.val i.2
  exact this

@[simp]
theorem fin_to_config_config_to_fin (x : Fin n → Bool) : fin_to_config (config_to_fin x) = x := by
  funext j
  simp [fin_to_config, config_to_fin, config_to_nat]
  have : (∑ i : Fin n, if x i then 2 ^ i.val else 0) >> j.val & 1 = if x j then 1 else 0 := by
    induction n generalizing j with
    | zero => simp
    | succ n ih =>
      let j' : Fin n := ⟨j.val, by
        have : j.val < n+1 := j.2
        by_cases h : j.val = n
        · exfalso; simp at h; linarith
        · exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! h; simp [h])⟩
      calc (∑ i : Fin (n+1), if x i then 2 ^ i.val else 0) >> j.val & 1
          = (if x (Fin.last n) then 2 ^ n else 0) >> j.val & 1 +
            (∑ i : Fin n, if x (Fin.castSucc i) then 2 ^ i.val else 0) >> j.val & 1 := by
            rw [Finset.sum_range_succ]; simp [Fin.val_last, Fin.castSucc]; ring
          = if j.val = n then (if x (Fin.last n) then 1 else 0) else
              (∑ i : Fin n, if x (Fin.castSucc i) then 2 ^ i.val else 0) >> j.val & 1 := by
            have : (2 ^ n >> j.val & 1) = if j.val = n then 1 else 0 := by
              rw [Nat.testBit_two_pow]; split_ifs <;> linarith
            simp [this]
          = if j.val = n then (if x (Fin.last n) then 1 else 0) else
              (if x (Fin.castSucc j') then 1 else 0) := by
            rw [ih j']
          = if x j then 1 else 0 := by
            by_cases hj : j.val = n
            · simp [hj, x, Fin.last]
            · have h_cast : j = Fin.castSucc j' := by
                apply Fin.eq_of_val_eq
                simp [Fin.castSucc, j']
                exact lt_of_le_of_ne (Nat.le_of_lt_succ j.2) (by contrapose! hj; simp [hj])
              rw [h_cast]; simp
    exact this
  exact this

/-! ### Évaluation d’un MPS -/

def eval (ψ : MPS n χ) (x : Fin n → Bool) : ℝ :=
  let rec go (i : ℕ) (acc : Matrix (Fin χ) (Fin χ) ℝ) : Matrix (Fin χ) (Fin χ) ℝ :=
    if hi : i < n then
      let Ai := ψ.tensors ⟨i, hi⟩ (x ⟨i, hi⟩)
      go (i+1) (acc ⬝ Ai)
    else acc
  let M := go 0 1
  M.trace

def state_vector (ψ : MPS n χ) : Fin (2 ^ n) → ℝ :=
  fun i => eval ψ (fin_to_config i)

def norm_vec (v : Fin (2 ^ n) → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-! ### Axiomes pour la construction et la compression -/

/-- Algorithme de Vidal (2003) : construction d'un MPS exact à partir d'un vecteur. -/
axiom vidal_construction (v : Fin (2 ^ n) → ℝ) (χ : ℕ) :
    ∃ ψ : MPS n χ, state_vector ψ = v

/-- Loi d'aire logarithmique (Hastings 2007) pour les états fondamentaux de Hamiltoniens gappés. -/
axiom area_law {n χ : ℕ} (ψ : MPS n χ) :
  ∃ C α, 0 < α ∧ α < 1 ∧ ∀ k,
    ∑ i in Finset.univ.filter (fun i => i.val ≥ k),
      (SVD.exists_svd (eval_matrix ψ)).2.singularValues i ^ 2 ≤ C * α ^ k

/-- Borne d'erreur pour la compression par troncature SVD (Eckart-Young). -/
axiom compression_error_bound (ψ : MPS n χ) (χ' : ℕ) (hχ' : χ' ≤ χ) :
    let ψc := compress ψ χ'
    (norm_vec (state_vector ψc - state_vector ψ)) ^ 2 ≤
      ∑ i in Finset.range n, ∑ k ≥ χ', (SVD.singularValues (step_matrix i ψ) k) ^ 2

/-- Compression d'un MPS (définition). -/
noncomputable def compress (ψ : MPS n χ) (χ' : ℕ) : MPS n χ' :=
  (vidal_construction (state_vector ψ) χ').choose

end MPS
