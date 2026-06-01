/-
Axioms.lean – Liste des axiomes utilisés dans le kernel avec références.
-/

-- Brandão–Horodecki (2013) : décroissance exponentielle ⇒ loi d'aire.
-- Fichier : Kernel/BrandaoHorodecki.lean
axiom brandao_horodecki {V : Type*} [Fintype V] ...

-- Courbe de Hilbert (1891) : existence d'un ordre avec faible frontière.
-- Fichier : Kernel/HilbertCurve.lean
axiom hilbert_curve_bound {V : Type*} [Fintype V] (G : SimpleGraph V) ...

-- Renormalisation : loi d'aire linéaire ⇒ loi d'aire logarithmique.
-- Fichier : Kernel/Renormalisation.lean
axiom renormalisation_area_law {V : Type*} [Fintype V] (ψ : V → ℝ) ...

-- Limite inductive (Kato 1966) : convergence forte des résolvantes.
-- Fichier : Kernel/InductiveLimit.lean
axiom resolvent_convergence {H : ℕ → Type*} ...

-- Semi‑continuité inférieure du spectre (Kato 1966).
-- Fichier : Kernel/KatoTheory.lean
axiom kato_lower_semicontinuity {E : Type*} ...

-- Loi d'aire pour le lacet de Wilson (Osterwalder–Seiler 1978).
-- Fichier : Kernel/WilsonLoop.lean
axiom area_law_Wilson_loop (σ : ℝ) (hσ : σ > 0) (C : ℝ) (hC : C > 0) ...

-- Conséquences : conductance exponentielle et potentiel linéaire.
axiom area_law_to_conductance ...
axiom exponential_decay_to_linear_potential ...
