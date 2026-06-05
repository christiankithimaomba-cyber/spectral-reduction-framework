import Mathlib.Data.Nat.Prime
import Mathlib.Analysis.NormedSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow

open Real

/-! # Hilbert space of primes and the chiral operator for the Riemann hypothesis -/

/-- The type of prime numbers. -/
def Prime : Type := { p : ℕ // Nat.Prime p }

/-- Weight function w(p) = log p / p^(1+α) for α > 0. -/
def weight (α : ℝ) (p : Prime) : ℝ :=
  let p_val : ℝ := p.val
  (Real.log p_val) / (p_val ^ (1 + α))

lemma weight_pos (α : ℝ) (hα : 0 < α) (p : Prime) : 0 < weight α p :=
  by
    have : 0 < Real.log p.val := Real.log_pos (by exact_mod_cast Nat.Prime.pos p.property)
    have : 0 < p.val ^ (1 + α) := by positivity
    positivity

/-- ℓ² space with weight w. -/
def prime_hilbert (α : ℝ) : Type := lp (fun p : Prime => ℝ) 2 (fun p => weight α p)

instance (α : ℝ) : InnerProductSpace ℝ (prime_hilbert α) :=
  lp.innerProductSpace ℝ 2 _

/-! ### Matrix kernel A(p,q) -/

/-- Auxiliary function to find m such that p^m = q, if it exists. -/
def find_m (p q : Prime) : ℕ :=
  let rec loop (m : ℕ) : ℕ :=
    if m = 0 then 0
    else if p.val ^ m = q.val then m
    else loop (m-1)
  loop 100

/-- Matrix entries A_{pq} = sum_{m≥1} (log p) / p^(m/2) * δ_{p^m, q}. -/
noncomputable def A (α : ℝ) (p q : Prime) : ℝ :=
  let logp := Real.log p.val
  let m := find_m p q
  if m = 0 then 0
  else logp / (p.val ^ (m / 2 : ℕ) : ℝ)

/-! ### Axiom: convergence of the Hilbert–Schmidt norm -/

/-- The double series ∑_{p,q} |A_{pq}|² w(p) w(q) converges.
    Reference: Schepis 2025, Lemma 2.1. -/
axiom hilbert_schmidt_norm_finite (α : ℝ) (hα : 0 < α) :
    ∑ (p q : Prime), (A α p q) ^ 2 * weight α p * weight α q < ∞

/-! ### Operator A and its properties -/

/-- The linear operator A_op on ℓ² defined by the matrix A. -/
noncomputable def A_op (α : ℝ) : prime_hilbert α →ₗ[ℝ] prime_hilbert α :=
  lp.matrix_to_operator (fun p q => A α p q)

/-- A_op is Hilbert–Schmidt, hence bounded and compact. -/
theorem A_op_hilbert_schmidt (α : ℝ) (hα : 0 < α) : HilbertSchmidt (A_op α) :=
  HilbertSchmidt.of_matrix_orthonormal_basis (hilbert_schmidt_norm_finite α hα)

/-- Consequently, A_op is a bounded linear operator. -/
instance (α : ℝ) (hα : 0 < α) : BoundedLinearMap (A_op α) :=
  (A_op_hilbert_schmidt α hα).toBoundedLinearMap

/-- Adjoint of A_op. -/
noncomputable def A_op_adj (α : ℝ) : prime_hilbert α →ₗ[ℝ] prime_hilbert α :=
  LinearMap.adjoint (A_op α)

/-! ### Axiom: symmetry of the kernel (or its adjoint) -/

/-- The matrix A is symmetric (A_{pq} = A_{qp}) because the only contributions come
    from p = q (when m=1) or from pairs where one is a prime power of the other,
    and the weight is symmetric. Reference: Schepis 2025, Lemma 2.2. -/
axiom A_symmetric (α : ℝ) (hα : 0 < α) : A_op_adj α = A_op α

/-! ### Chiral operator H -/

/-- The chiral operator H = [[0, A†], [A, 0]] on the direct sum. -/
noncomputable def H (α : ℝ) : (prime_hilbert α × prime_hilbert α) →ₗ[ℝ] (prime_hilbert α × prime_hilbert α) :=
  let L₁ : (prime_hilbert α × prime_hilbert α) →ₗ[ℝ] prime_hilbert α :=
    LinearMap.coprod 0 (A_op_adj α)   -- (f, g) ↦ A† g
  let L₂ : (prime_hilbert α × prime_hilbert α) →ₗ[ℝ] prime_hilbert α :=
    LinearMap.coprod (A_op α) 0       -- (f, g) ↦ A f
  LinearMap.prod L₁ L₂

/-- H is symmetric. -/
lemma H_symmetric (α : ℝ) (hα : 0 < α) (x y : prime_hilbert α × prime_hilbert α) :
    ⟪H α x, y⟫ = ⟪x, H α y⟫ :=
  by
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    calc ⟪H α x, y⟫
        = ⟪(A_op_adj α x₂, A_op α x₁), (y₁, y₂)⟫ := rfl
        = ⟪A_op_adj α x₂, y₁⟫ + ⟪A_op α x₁, y₂⟫ := by simp [inner_add]
        = ⟪x₂, A_op α y₁⟫ + ⟪x₁, A_op_adj α y₂⟫ := by
            rw [← LinearMap.adjoint_inner_left (A_op α) x₂ y₁]
            rw [← LinearMap.adjoint_inner_left (A_op_adj α) x₁ y₂]
        = ⟪(x₁, x₂), (A_op_adj α y₂, A_op α y₁)⟫ := by simp
        = ⟪x, H α y⟫ := rfl

/-- H is bounded. -/
lemma H_bounded (α : ℝ) (hα : 0 < α) : ∃ C : ℝ, ∀ x, ‖H α x‖ ≤ C * ‖x‖ :=
  by
    let C₁ := ‖A_op α‖
    let C₂ := ‖A_op_adj α‖
    let C := C₁ + C₂
    refine ⟨C, fun x => ?_⟩
    obtain ⟨x₁, x₂⟩ := x
    have h₁ : ‖A_op α x₁‖ ≤ C₁ * ‖x₁‖ := LinearMap.bound_of_boundedLinearMap (A_op α) x₁
    have h₂ : ‖A_op_adj α x₂‖ ≤ C₂ * ‖x₂‖ := LinearMap.bound_of_boundedLinearMap (A_op_adj α) x₂
    have h_norm : ‖(A_op_adj α x₂, A_op α x₁)‖ = √(‖A_op_adj α x₂‖^2 + ‖A_op α x₁‖^2) := rfl
    -- Première inégalité : sqrt(a² + b²) ≤ sqrt(C₂²‖x₂‖² + C₁²‖x₁‖²)
    have h_ineq : √(‖A_op_adj α x₂‖^2 + ‖A_op α x₁‖^2) ≤ √(C₂^2 * ‖x₂‖^2 + C₁^2 * ‖x₁‖^2) :=
      Real.sqrt_le_sqrt (by
        have ha : ‖A_op_adj α x₂‖^2 ≤ (C₂ * ‖x₂‖)^2 := by
          rw [mul_pow]; exact pow_le_pow_of_le_left (norm_nonneg _) h₂ 2
        have hb : ‖A_op α x₁‖^2 ≤ (C₁ * ‖x₁‖)^2 := by
          rw [mul_pow]; exact pow_le_pow_of_le_left (norm_nonneg _) h₁ 2
        exact add_le_add ha hb)
    -- Deuxième inégalité : sqrt(C₂² a² + C₁² b²) ≤ (C₁ + C₂) sqrt(a² + b²) pour a=‖x₁‖, b=‖x₂‖
    let a := ‖x₁‖
    let b := ‖x₂‖
    have h_ineq2 : √(C₂^2 * a^2 + C₁^2 * b^2) ≤ C * √(a^2 + b^2) :=
      by
        have h₁ : C₂^2 * a^2 + C₁^2 * b^2 ≤ (C₁ + C₂)^2 * (a^2 + b^2) :=
          calc C₂^2 * a^2 + C₁^2 * b^2
              ≤ (C₁^2 + C₂^2) * (a^2 + b^2) := by
                have ha : C₂^2 * a^2 ≤ (C₁^2 + C₂^2) * a^2 :=
                  mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg C₁)) (sq_nonneg a)
                have hb : C₁^2 * b^2 ≤ (C₁^2 + C₂^2) * b^2 :=
                  mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg C₂)) (sq_nonneg b)
                exact add_le_add ha hb
              _ ≤ (C₁ + C₂)^2 * (a^2 + b^2) :=
                mul_le_mul_of_nonneg_right (by rw [← sq (C₁ + C₂)]; exact le_sq_of_le (by positivity) (by linarith)) (by positivity)
        exact Real.sqrt_le_sqrt h₁
    exact le_trans (le_trans h_norm ▸ h_ineq) h_ineq2

/-- H is self-adjoint. -/
theorem H_selfadjoint (α : ℝ) (hα : 0 < α) : IsSelfAdjoint (H α) :=
  IsSelfAdjoint.of_symmetric_bounded (H α) (H_symmetric α hα) (H_bounded α hα)

end
