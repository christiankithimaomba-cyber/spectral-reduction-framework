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
  let f (s : Finset (Fin n)) : Config n := fun i => i ∈ s
  have hf_inj : Function.Injective f := by
    intro s t h
    ext i
    have : f s i = f t i := congr_fun h i
    simp [f] at this
    exact this
  have h_image : f '' (Finset.powerset_len k Finset.univ) = hammingLayer n k := by
    ext x
    simp [hammingLayer, hammingWeight, Finset.powerset_len, Finset.mem_image]
    constructor
    · intro ⟨s, hs, hx⟩
      rw [← hx]
      have h_card : (Finset.filter (fun i => f s i) Finset.univ).card = k := by
        rw [← hs]
        exact Finset.card_filter_of_mem (fun i _ => by simp [f])
      exact ⟨h_card, rfl⟩
    · intro ⟨h_card, rfl⟩
      let s := Finset.filter (fun i => x i) Finset.univ
      have h_card' : s.card = k := by
        rw [← h_card]
        simp [s, hammingWeight]
      exact ⟨s, h_card', rfl⟩
  rw [← h_image, Finset.card_image_of_injective hf_inj]
  exact Finset.card_powerset_len k

-- Test: for n = 3, k = 1, the size is 3.
example : (hammingLayer 3 1).card = 3 := by
  have : Nat.choose 3 1 = 3 := rfl
  rw [card_hammingLayer 3 1 (by linarith)]
  exact this

-- Trivial test that always passes.
example : True := by trivial
