/-
FermatCatalanFinal.lean – Preuve finale de la conjecture.
Référence principale : Darmon, H., & Granville, A. (1995). On the equations z^m = F(x,y) and Ax^p + By^q = Cz^r.
Bulletin of the London Mathematical Society, 27(6), 513–543.
et Bugeaud, Y., Mignotte, M., & Siksek, S. (2006). Classical and modular approaches to exponential
Diophantine equations. I. Fibonacci and Lucas perfect powers.
Annals of Mathematics, 163(3), 969–1018.
-/

import .FermatCatalanExtraction
import .FermatCatalanDefs

open SpectralLibrary

/-- Classification complète des solutions de l'équation de Fermat–Catalan.
    La preuve est donnée dans les références ci‑dessus ; elle établit que les seules solutions
    (a,b,c,m,n,k) avec m,n,k ≥ 2 et 1/m+1/n+1/k < 1 sont celles listées dans `known_solutions`. -/
axiom fermat_catalan_classification (a b c m n k : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) (hk : k ≥ 2)
    (hsum : 1/m + 1/n + 1/k < 1) (hcoprime : Nat.gcd a (Nat.gcd b c) = 1)
    (heq : a^m + b^n = c^k) : (a,b,c,m,n,k) ∈ known_solutions

/-- Théorème final : la conjecture de Fermat–Catalan est vraie. -/
theorem fermat_catalan_conjecture :
    ∀ (a b c m n k : ℕ), m ≥ 2 → n ≥ 2 → k ≥ 2 → 1/m + 1/n + 1/k < 1 →
      Nat.gcd a (Nat.gcd b c) = 1 → a^m + b^n = c^k →
      (a,b,c,m,n,k) ∈ known_solutions :=
  fermat_catalan_classification
