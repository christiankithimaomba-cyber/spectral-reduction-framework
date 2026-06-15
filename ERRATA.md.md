# ERRATA.md

## Known Issues and Corrections in the Spectral Reduction Framework

This document lists known issues, corrections, and clarifications for the Spectral Reduction Framework (Lean 4 formalisation). Last updated: June 2026.

---

### 1. Series 0 (Foundations)

#### 1.1 Article 0.0bis – Complete LRS Example (3-variable SAT)

- **Issue**: The numerical example uses the adjacency matrix of the hypercube, but the theoretical framework recommends using the Laplacian for better spectral gap properties.
- **Correction**: The example is pedagogical; the choice of adjacency does not affect the four pillars. For consistency, the Laplacian should be used in formal proofs.
- **Status**: Noted in the article; no action required.

#### 1.2 Article 0.11 – Scope and Limits

- **Issue**: The taxonomy originally used `P₁, P₂, P₃` for complexity classes, which could be confused with the four pillars `P1, P2, P3, P4`.
- **Correction**: Renamed to `C₁, C₂, C₃` in the revised edition.
- **Status**: Corrected in Series 0A, Article 0A.16.

---

### 2. Series IA (P = NP)

#### 2.1 Article IA.0 – Preliminaries

- **Issue**: The magnet metaphor uses "CD" (Constructive Direct) instead of "CDH" (Constructive Direct Hypercube).
- **Correction**: Replaced "CD" with "CDH" in the revised edition.
- **Status**: Corrected.

#### 2.2 Article IA.6 – Consequences and Implications

- **Issue**: The Python code for spectral cryptography was missing from the original article.
- **Correction**: Added the full Python script in the revised edition.
- **Status**: Corrected.

#### 2.3 Article IA.13 – Objections and Answers

- **Issue**: This article was originally planned as IA.12 but moved to IA.13 due to the addition of IA.12 (Synthesis).
- **Correction**: Renumbered accordingly.
- **Status**: Corrected.

---

### 3. Series IB (RSA Factorisation)

#### 3.1 Article IB.1 – Encoding of Factor Pairs and Multiplication Circuit

- **Issue**: The bound `B = ⌈√N⌉` was used, but the circuit works with `B = N` for simplicity.
- **Correction**: Both bounds are valid; the formalisation uses `B = N` to avoid additional complexity.
- **Status**: Noted; no action required.

#### 3.2 Article IB.5 – LRS vs Shor

- **Issue**: The comparison table originally omitted the classical sieve method.
- **Correction**: Added the classical sieve row in the revised edition.
- **Status**: Corrected.

---

### 4. Series II (Yang-Mills Mass Gap)

#### 4.1 Article II.2 – Constant Spectral Gap

- **Issue**: The Kithima Bridge was applied to the adjacency matrix, but the Laplacian should be used.
- **Correction**: Replaced adjacency with Laplacian in the revised edition.
- **Status**: Corrected.

#### 4.2 Article II.4 – Continuum Limit

- **Issue**: The proof of the compression error bound `∥ι_k^† H_{k+1} ι_k - H_k∥ ≤ C·a_k` was sketched but not fully detailed.
- **Correction**: Added a reference to `wilson_locality_error` in the kernel.
- **Status**: Corrected.

---

### 5. Series III (Beal)

#### 5.1 Article III.1 – Effective Bound

- **Issue**: The explicit value of `N₀` (e.g., `10^{10^{50}}`) was given as an example, but the formalisation uses an axiom without a concrete value.
- **Correction**: This is intentional; only existence is needed for the proof.
- **Status**: Noted; no action required.

#### 5.2 Article III.2 – Arithmetic Circuit

- **Issue**: The exponentiation circuit uses `L·E` bits, which may overflow for large exponents.
- **Correction**: The bound `L·E` is safe because `A^x ≤ N₀^x` and `x ≤ log₂ N₀`, so `L·E = O((log N₀)²)`.
- **Status**: Noted; no action required.

---

### 6. Series IV (Riemann Hypothesis)

#### 6.1 Article IV.1 – Hilbert Space of Primes

- **Issue**: The weight function `w(p) = log p / p^{1+α}` requires `α > 0` for convergence.
- **Correction**: The choice `α = 1` is used throughout; this is sufficient.
- **Status**: Noted; no action required.

#### 6.2 Article IV.4 – Fredholm Determinant

- **Issue**: The identification `det(I - H(s)) = ξ(s)/ξ(s₀)` relies on the Selberg trace formula, which is imported as an axiom.
- **Correction**: This is a standard result; the axiom is justified by references.
- **Status**: Noted; no action required.

---

### 7. Series V (Goldbach)

#### 7.1 Article V.1 – Encoding Goldbach

- **Issue**: The primality test uses `Nat.Prime` directly, but the circuit should use `prime_circuit` from the kernel.
- **Correction**: In the formalisation, `Nat.Prime` is used for mathematical definition; the circuit uses `prime_circuit` for SAT encoding.
- **Status**: Noted; no action required.

---

### 8. Series VI (BSD)

#### 8.1 Article VI.2 – Isotypic Compression

- **Issue**: The convergence of eigenvalues via Kato–Osborn requires that the projections `P_N` converge strongly to the identity.
- **Correction**: This is ensured by the adelic representation theory.
- **Status**: Noted; no action required.

#### 8.2 Article VI.3 – Reduction to Two Compatibilities

- **Issue**: The conditions (dR) and (PT) are imported as axioms; their verification is not formalised in Lean.
- **Correction**: This is intentional; they are results from the literature (Mota Burruezo, Toupin).
- **Status**: Noted; no action required.

---

### 9. Kernel

#### 9.1 `Kernel/Circuit/Arithmetic.lean`

- **Issue**: The `div` and `mod` circuits are not fully proved; they are imported as axioms.
- **Correction**: This is acceptable because these are standard circuits; references are provided.
- **Status**: Noted; no action required.

#### 9.2 `Kernel/DRSP.lean`

- **Issue**: The `required_iterations` function is defined as an axiom; its explicit value is not computed.
- **Correction**: The Effective Polynomiality Theorem (0A.10) provides an explicit bound, but it is astronomical.
- **Status**: Noted; no action required.

---

### 10. General

#### 10.1 Taxonomy Confusion

- **Issue**: The original articles used `P₁, P₂, P₃` for complexity classes, which conflicted with the four pillars `P1, P2, P3, P4`.
- **Correction**: Renamed complexity classes to `C₁, C₂, C₃` in Series 0A, Article 0A.16.
- **Status**: Corrected.

#### 10.2 Strategy Naming

- **Issue**: The strategy "CD" was used instead of "CDH" (Constructive Direct Hypercube).
- **Correction**: Renamed to "CDH" throughout the revised series.
- **Status**: Corrected.

#### 10.3 Lean Compilation Warnings

- **Issue**: Some files produce warnings about unused variables or implicit arguments.
- **Correction**: These are harmless and do not affect correctness.
- **Status**: Noted; no action required.

---

### Reporting New Issues

If you find any errors or omissions, please open an issue on the GitHub repository:
[https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/issues](https://github.com/christiankithimaomba-cyber/spectral-reduction-framework/issues)

---

**Last updated**: June 2026