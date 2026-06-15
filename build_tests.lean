/- 
tests/build_tests.lean – Simple tests for the spectral kernel.
-/

import Mathlib.Tactic
import Kernel.HypercubeHarper
import Kernel.SpectralLibrary
import Kernel.DiscreteCheeger

open HypercubeHarper

-- Helper definition: set of configurations with Hamming weight exactly k.
def hammingLayer (n k : ℕ) : Finset (Config n) :=
  Finset.filter (fun x => hammingWeight x = k) Finset.univ

-- The number of such configurations is the binomial coefficient.
lemma card_hammingLayer (n k : ℕ) (hk : k ≤ n) : (hammingLayer n k).card = Nat.choose n k := by
  -- Map a finset of vertices of size k to its characteristic function
  let f (s : Finset (Fin n)) : Config n := fun i => decide (i ∈ s)
  have hf_inj : Function.Injective f := by
    intro s t h
    ext i
    have : decide (i ∈ s) = decide (i ∈ t) := congr_fun h i
    simp only [decide_eq_decide] at this
    exact this
  have h_image : f '' (Finset.powerset_len k Finset.univ) = hammingLayer n k := by
    ext x
    simp [hammingLayer, hammingWeight, Finset.powerset_len, Finset.mem_image]
    constructor
    · intro ⟨s, hs, hx⟩
      rw [← hx]
      -- The Hamming weight of f s is exactly s.card
      have h_card : hammingWeight (f s) = s.card := by
        simp [hammingWeight, f, decide_eq_true_eq]
        rw [Finset.card_filter_of_mem (fun i _ => by simp)]
      rw [h_card, hs]
      -- Also ensure the functional equality holds for the reverse direction
      exact ⟨h_card, rfl⟩
    · intro ⟨h_card, h_eq⟩
      let s := Finset.filter (fun i => x i = true) Finset.univ
      have h_card' : s.card = k := by
        rw [← h_card]
        simp [s, hammingWeight]
      have h_eq' : x = f s := by
        funext i
        simp [f, decide_eq_true_eq, Finset.mem_filter]
        by_cases h : x i
        · simp [h, decide_True]
        · simp [h, decide_False]
      exact ⟨s, h_card', h_eq'⟩
  rw [← h_image, Finset.card_image_of_injective hf_inj]
  exact Finset.card_powerset_len k

-- Test: for n = 3, k = 1, the size is 3.
example : (hammingLayer 3 1).card = 3 := by
  have : Nat.choose 3 1 = 3 := rfl
  rw [card_hammingLayer 3 1 (by linarith)]
  exact this

-- Trivial test that always passes.
example : True := by trivial
