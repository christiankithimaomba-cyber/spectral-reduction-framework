/- 
HypercubeHarper.lean – Valeurs propres de l'hypercube par caractères de Fourier.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace
import Mathlib.LinearAlgebra.Finrank

open BigOperators Finset Matrix

universe u

/-- Configuration space `{0,1}^n` -/
def Config (n : ℕ) := Fin n → Bool

namespace HypercubeHarper

variable {n : ℕ}

/-- Poids de Hamming -/
def hammingWeight (x : Config n) : ℕ :=
  ∑ i, if x i then 1 else 0

/-- Arête entre deux configurations -/
def is_edge (x y : Config n) : Prop :=
  ∑ i, if x i = y i then 0 else 1 = 1

/-- Frontière d’arêtes (nombre d’arêtes sortant de S) -/
def edge_boundary (S : Finset (Config n)) : ℕ :=
  (S.bind fun x => (Finset.univ : Finset (Config n)).filter fun y => y ∉ S ∧ is_edge x y).card

/-- Matrice d’adjacence de l’hypercube -/
def adjacency_matrix (n : ℕ) : Matrix (Config n) (Config n) ℝ :=
  Matrix.of (fun x y => if is_edge x y then 1 else 0)

/-- Caractère de Fourier associé à α -/
def fourier_char (α : Config n) (x : Config n) : ℝ :=
  ∏ i, if α i then (if x i then -1 else 1) else 1

/-! ### Bijection entre Config (n+1) et Config n × Bool -/

/-- Embedding of Config (n+1) into Config n × Bool. -/
def embed (x : Config (n+1)) : Config n × Bool :=
  (fun i => x (Fin.castSucc i), x (Fin.last n))

/-- Inverse embedding. -/
def embed_inv (p : Config n × Bool) : Config (n+1) :=
  fun i => if h : i = Fin.last n then p.2 else
    have hi : i.val < n := by
      have : i.val < n+1 := i.2
      have : i ≠ Fin.last n := by contrapose! h; simp [h]
      exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! h; simp [Fin.ext_iff, h])
    p.1 (Fin.castLT i hi)

theorem embed_bijective : Function.Bijective (embed : Config (n+1) → Config n × Bool) := by
  constructor
  · intro x y h
    have h1 : ∀ i, x (Fin.castSucc i) = y (Fin.castSucc i) :=
      congr_fun (congr_arg Prod.fst h)
    have h2 : x (Fin.last n) = y (Fin.last n) := congr_arg Prod.snd h
    funext i
    by_cases hi : i = Fin.last n
    · rw [hi, h2]
    · have h_cast : i = Fin.castSucc (Fin.castLT i (by
          have : i.val < n+1 := i.2
          have : i ≠ Fin.last n := hi
          exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! hi; simp [Fin.ext_iff, hi]))) :=
        by apply Fin.eq_of_val_eq; simp [Fin.castSucc, Fin.castLT]
      rw [h_cast, h1 (Fin.castLT i _)]
  · intro p
    use embed_inv p
    funext i
    by_cases hi : i = Fin.last n
    · simp [embed, embed_inv, hi]
    · simp [embed, embed_inv, hi]
      have h_cast : i = Fin.castSucc (Fin.castLT i (by
          have : i.val < n+1 := i.2
          have : i ≠ Fin.last n := hi
          exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! hi; simp [Fin.ext_iff, hi]))) :=
        by apply Fin.eq_of_val_eq; simp [Fin.castSucc, Fin.castLT]
      rw [h_cast]
      rfl

/-! ### Orthogonalité des caractères -/

theorem fourier_char_orthogonal (α β : Config n) :
    ∑ x : Config n, (fourier_char α x) * (fourier_char β x) = if α = β then 2 ^ n else 0 := by
  induction n with
  | zero =>
    have : Fintype.card (Config 0) = 1 := by simp [Config, Fintype.card_pi, Fintype.card_bool]
    rcases α with ⟨_, ⟨⟩⟩; rcases β with ⟨_, ⟨⟩⟩
    simp only [fourier_char, Finset.sum_singleton]
    split_ifs <;> simp [Nat.cast_zero, Nat.cast_one]
  | succ n ih =>
    let C := Config n
    let C' := Config (n+1)
    have F : C' ≃ (C × Bool) := ⟨embed, embed_inv, by intro x; simp [embed_bijective.left_inv], by intro p; simp [embed_bijective.right_inv]⟩
    rw [Finset.sum_equiv F.symm]
    simp [fourier_char]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl (fun b _ => ?_)
    let α' : Config n := fun i => α (Fin.castSucc i)
    let a := α (Fin.last n)
    let β' : Config n := fun i => β (Fin.castSucc i)
    let b := β (Fin.last n)
    -- Décomposer le produit pour α
    have h_prod_α : ∏ i, if α i then (if (embed_inv (x, b)) i then -1 else 1) else 1 =
        (∏ i, if α' i then (if x i then -1 else 1) else 1) *
        (if a then (if b then -1 else 1) else 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite]
      let F := (Finset.univ : Finset (Fin (n+1))).filter (fun i => i ≠ Fin.last n)
      let last := {Fin.last n}
      have h_disj : Finset.univ = F ∪ last := by
        ext i; simp; by_cases h : i = Fin.last n <;> simp [h]
      rw [h_disj, Finset.prod_union]
      · simp [Finset.prod_filter, Finset.prod_singleton]
        congr 1
        apply Finset.prod_congr rfl; intro i hi
        simp [embed_inv, Fin.castSucc, Fin.castLT, hi.1]
        have hi_ne : i ≠ Fin.last n := hi.1
        have h_cast : i = Fin.castSucc (Fin.castLT i (by
            have : i.val < n+1 := i.2
            have : i ≠ Fin.last n := hi_ne
            exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! hi_ne; simp [Fin.ext_iff, hi_ne]))) :=
          by apply Fin.eq_of_val_eq; simp [Fin.castSucc, Fin.castLT]
        rw [h_cast]
        simp
      · simp [Finset.disjoint_iff]; intro i hi; simp [hi]
    -- Décomposer le produit pour β (symétrique)
    have h_prod_β : ∏ i, if β i then (if (embed_inv (x, b)) i then -1 else 1) else 1 =
        (∏ i, if β' i then (if x i then -1 else 1) else 1) *
        (if b then (if b then -1 else 1) else 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite]
      let F := (Finset.univ : Finset (Fin (n+1))).filter (fun i => i ≠ Fin.last n)
      let last := {Fin.last n}
      have h_disj : Finset.univ = F ∪ last := by
        ext i; simp; by_cases h : i = Fin.last n <;> simp [h]
      rw [h_disj, Finset.prod_union]
      · simp [Finset.prod_filter, Finset.prod_singleton]
        congr 1
        apply Finset.prod_congr rfl; intro i hi
        simp [embed_inv, Fin.castSucc, Fin.castLT, hi.1]
        have hi_ne : i ≠ Fin.last n := hi.1
        have h_cast : i = Fin.castSucc (Fin.castLT i (by
            have : i.val < n+1 := i.2
            have : i ≠ Fin.last n := hi_ne
            exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (by contrapose! hi_ne; simp [Fin.ext_iff, hi_ne]))) :=
          by apply Fin.eq_of_val_eq; simp [Fin.castSucc, Fin.castLT]
        rw [h_cast]
        simp
      · simp [Finset.disjoint_iff]; intro i hi; simp [hi]
    rw [h_prod_α, h_prod_β]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    have sum_last : ∑ b', (if a then (if b' then -1 else 1) else 1) * (if b then (if b' then -1 else 1) else 1) =
        if a = b then 2 else 0 := by
      simp [Finset.sum_bool, ite_mul]
      by_cases ha : a
      · by_cases hb : b
        · simp [ha, hb]; ring
        · simp [ha, hb]; ring
      · by_cases hb : b
        · simp [ha, hb]; ring
        · simp [ha, hb]; ring
    rw [← sum_last]
    have inner_sum : ∑ x, (∏ i, if α' i then (if x i then -1 else 1) else 1) *
        (∏ i, if β' i then (if x i then -1 else 1) else 1) =
        if α' = β' then 2 ^ n else 0 := by
      exact ih α' β'
    simp [inner_sum, sum_last]
    split_ifs
    · have h_eq : α = β ↔ α' = β' ∧ a = b := by
        funext i; by_cases hi : i = Fin.last n <;> simp [hi]
      rw [h_eq]
      split_ifs <;> simp [pow_succ, mul_comm]
    · simp

/-! ### Valeurs propres -/

/-- Les caractères de Fourier sont vecteurs propres de l’adjacence. -/
theorem fourier_char_eigenvalue (α : Config n) (x : Config n) :
    (adjacency_matrix n).mulVec (fourier_char α) x =
      (n - 2 * hammingWeight α) * (fourier_char α x) := by
  simp [adjacency_matrix, mulVec]
  have h_neighbors : {y | is_edge x y} = {y | ∃ i, y = x with i := not (x i)} := by
    ext y; simp [is_edge, Function.update_apply]; constructor
    · intro hy; obtain ⟨i, hi⟩ := exists_unique_of_sum_one hy; use i; ext j; by_cases h : j = i <;> simp [h, hi]
    · rintro ⟨i, rfl⟩; simp [is_edge]; rw [Finset.sum_eq_single i]; simp [Function.update_apply]; intros j hj; simp [hj]
  rw [h_neighbors]
  calc ∑ y in (Finset.univ : Finset (Config n)), if ∃ i, y = x with i := not (x i) then fourier_char α y else 0
      = ∑ i, fourier_char α (x with i := not (x i)) := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl; intro i _; rfl
        · intro i j; simp [Function.update_apply]; intro h; ext k; by_cases hk : k = i <;> by_cases hk' : k = j <;> simp [hk, hk'] at h ⊢
  have h_char : ∀ i, fourier_char α (x with i := not (x i)) = (if α i then -1 else 1) * fourier_char α x := by
    intro i; simp [fourier_char, Finset.prod_mul_distrib, Finset.prod_ite, Function.update_apply]
    rw [Finset.prod_eq_single i]; simp; intros j hj; simp [hj]
    simp [if_neg, Ne.symm hj]
  simp_rw [h_char]
  rw [Finset.sum_mul, Finset.sum_ite]
  simp [hammingWeight, Finset.sum_ite, Finset.sum_const, Finset.card_univ]
  ring

/-- Normalisation des caractères pour obtenir une base orthonormée. -/
def normalized_fourier_char (α : Config n) : Config n → ℝ :=
  (1 / Real.sqrt (2 ^ n)) • fourier_char α

/-- Orthonormalité des caractères normalisés. -/
theorem normalized_fourier_orthonormal (α β : Config n) :
    ∑ x, (normalized_fourier_char α x) * (normalized_fourier_char β x) = if α = β then 1 else 0 := by
  simp [normalized_fourier_char, ← sum_div, div_mul_eq_mul_div, mul_comm, ← mul_pow, Real.sq_sqrt (by positivity)]
  rw [fourier_char_orthogonal α β]
  split_ifs <;> simp [pow_two]

/-- Les caractères normalisés forment une base orthonormée. -/
theorem normalized_fourier_basis :
    (∀ α β, ∑ x, normalized_fourier_char α x * normalized_fourier_char β x = if α = β then 1 else 0) ∧
    (∀ v : Config n → ℝ, ∃ c, v = ∑ α, c α • normalized_fourier_char α) := by
  have h_orth := normalized_fourier_orthonormal
  -- Indépendance linéaire
  have h_lin_indep : LinearIndependent ℝ (normalized_fourier_char) :=
    orthonormal_linearIndependent h_orth
  -- Dimension de l'espace des fonctions
  have h_dim : finrank ℝ (Config n → ℝ) = Fintype.card (Config n) :=
    finrank_fintype_fun ℝ (Config n)
  -- Le sous-espace engendré a la même dimension
  have h_rank : finrank ℝ (Submodule.span ℝ (Set.range normalized_fourier_char)) =
      Fintype.card (Config n) :=
    finrank_span_of_linearIndependent h_lin_indep (by simp [Finset.card_univ, Fintype.card_fin])
  -- Donc il est égal à l'espace total
  have h_span : Submodule.span ℝ (Set.range normalized_fourier_char) = ⊤ :=
    eq_top_of_finrank_eq h_dim h_rank
  -- Décomposition de tout vecteur
  intro v
  have : v ∈ Submodule.span ℝ (Set.range normalized_fourier_char) := by rw [h_span]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_finite_of_finite (by simp) this
  exact ⟨c, hc⟩

/-- Valeurs propres de l’adjacence : n-2k pour k=0..n. -/
theorem eigenvalues_adjacency (k : ℕ) (hk : k ≤ n) :
    (n - 2 * k : ℝ) ∈ spectrum (adjacency_matrix n) := by
  let α : Config n := fun i => i.val < k
  have hw : hammingWeight α = k := by
    simp [hammingWeight, α]
    have : (Finset.univ : Finset (Fin n)).sum (fun i => if i.val < k then 1 else 0) = k := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.card_filter, Finset.card_univ]
      simp [k]
    exact this
  have h_eig : ∀ x, (adjacency_matrix n).mulVec (fourier_char α) x = (n - 2 * k) * (fourier_char α x) := by
    intro x; rw [fourier_char_eigenvalue α x, hw]
  have h_nonzero : ∃ x, fourier_char α x ≠ 0 := by
    use fun _ => false
    simp [fourier_char]
    have : ∏ i, (if α i then (if false then -1 else 1) else 1) = 1 := by
      apply Finset.prod_eq_one; intro i _; split_ifs <;> simp
    exact this
  exact ⟨h_nonzero, h_eig⟩

/-- Pour chaque μ dans le spectre, il existe k tel que μ = n - 2k. -/
theorem eigenvalues_adjacency_exist (μ : ℝ) (hμ : μ ∈ spectrum (adjacency_matrix n)) :
    ∃ k, 0 ≤ k ∧ k ≤ n ∧ μ = n - 2 * k := by
  obtain ⟨v, hv, hv_eig⟩ := hμ
  let ψα := normalized_fourier_char
  have h_basis := normalized_fourier_basis
  obtain ⟨c, hc⟩ := h_basis.2 v
  have h_v : v = ∑ α, c α • ψα α := hc
  have h_eig_α : ∀ α, adjacency_matrix n *ᵥ ψα α = (n - 2 * hammingWeight α) • ψα α := by
    intro α; simp [ψα, mulVec_smul, fourier_char_eigenvalue, smul_smul, mul_comm]
  rw [h_v, mulVec_sum, sum_smul] at hv_eig
  have h_eq : ∑ α, c α • ((n - 2 * hammingWeight α) • ψα α) = ∑ α, c α • (μ • ψα α) := by
    rw [hv_eig, h_v, sum_smul]
    congr; ext α; simp [← smul_assoc, mul_smul]
  have h_diff : ∑ α, (c α * (n - 2 * hammingWeight α) - c α * μ) • ψα α = 0 := by
    rw [← Finset.sum_sub]
    simp [h_eq, ← sub_smul, ← smul_sub]
  have h_lin_indep : LinearIndependent ℝ (fun α => ψα α) := by
    apply orthonormal_linearIndependent
    intro α β; rw [normalized_fourier_orthonormal α β]
    by_cases h : α = β
    · simp [h, one_ne_zero]
    · simp [h, zero_ne_one]
  have h_coeff_zero : ∀ α, c α * (n - 2 * hammingWeight α) - c α * μ = 0 := by
    intro α
    apply linearIndependent_iff.1 h_lin_indep (fun β => c β * (n - 2 * hammingWeight β) - c β * μ) (by simp [h_diff])
    exact α
  obtain ⟨α, hc_ne⟩ : ∃ α, c α ≠ 0 := by
    by_contra h; have h_all : ∀ α, c α = 0 := by simpa using h
    rw [h_v, Finset.sum_congr rfl (fun α _ => by rw [h_all α, zero_smul]), Finset.sum_const_zero] at h_v
    exact hv (by rw [h_v])
  have h_eq : c α * (n - 2 * hammingWeight α) = c α * μ := by
    rw [sub_eq_zero] at h_coeff_zero α; exact h_coeff_zero α
  rw [mul_eq_mul_left_iff] at h_eq
  cases h_eq
  · contradiction
  · exact ⟨hammingWeight α, by linarith, by linarith, h_eq⟩

/-- Le trou spectral de l'adjacence de l'hypercube est 2. -/
theorem spectral_gap_adjacency (hn : 1 ≤ n) : spectral_gap (adjacency_matrix n) = 2 := by
  have h0 : (n : ℝ) ∈ spectrum (adjacency_matrix n) := eigenvalues_adjacency 0 (zero_le n)
  have h1 : (n - 2 : ℝ) ∈ spectrum (adjacency_matrix n) := eigenvalues_adjacency 1 (by linarith)
  let M := (spectrum (adjacency_matrix n)).toMultiset
  have h_max_val : M.max = n := by
    apply Multiset.max_eq_of_forall_ge_and_mem
    · intro μ hμ; obtain ⟨k, hk, hμ⟩ := eigenvalues_adjacency_exist μ hμ; exact hμ ▸ by linarith [hk.2]
    · exact h0
  have h_second_val : (M.erase n).max = n - 2 := by
    apply Multiset.max_eq_of_forall_ge_and_mem
    · intro μ hμ
      obtain ⟨k, hk, hμ⟩ := eigenvalues_adjacency_exist μ (Multiset.mem_of_mem_erase hμ)
      have hk_ge1 : k ≥ 1 := by
        contrapose! hμ; rw [hμ]; simp; linarith
      exact hμ ▸ by linarith [hk.2, hk_ge1]
    · exact Multiset.mem_erase.mpr ⟨by linarith, h1⟩
  have h_gap : spectral_gap (adjacency_matrix n) = (M.erase n).max - M.max := by
    rw [spectral_gap]
    let L := M.sort (· ≥ ·)
    have h_len : L.length = M.card := by simp
    have h_nonempty : L.length ≥ 2 := by
      have : Fintype.card (Config n) = 2 ^ n := by simp [Config, Fintype.card_pi, Fintype.card_bool]
      have : 2 ^ n ≥ 2 := by exact pow_le_pow_right (by norm_num) hn
      rw [h_len, spectrum_card, Fintype.card_pi, Fintype.card_bool]
      simp [this]
    have h_first : L[0] = M.max := by
      apply List.max_of_sorted (by exact Multiset.sorted_sort (· ≥ ·) M) (by linarith)
      rw [← Multiset.mem_toList, L]; exact Multiset.mem_toMultiset.mpr (by exact h_max_val.symm)
    have h_rest : (L.drop 1).toMultiset = M.erase (M.max) :=
      Multiset.sort_drop (· ≥ ·) M 1 (by linarith [h_nonempty])
    have h_second' : L[1] = (M.erase (M.max)).max := by
      have h_rest_nonempty : (L.drop 1) ≠ [] := by
        have : L.length ≥ 2 := h_nonempty
        simp [List.length_drop, tsub_pos_iff_lt] at this ⊢
        linarith
      rw [List.get_eq_iff (by linarith)]
      have h_rest_sorted : List.Sorted (· ≥ ·) (L.drop 1) :=
        List.sorted_drop (Multiset.sorted_sort (· ≥ ·) M) 1
      apply List.max_of_sorted h_rest_sorted (by linarith)
      rw [← Multiset.mem_toList, L.drop 1, h_rest, ← Multiset.mem_toMultiset]
      exact h_second_val.symm
    rw [h_second']
  rw [h_gap, h_second_val, h_max_val]
  ring

end HypercubeHarper
