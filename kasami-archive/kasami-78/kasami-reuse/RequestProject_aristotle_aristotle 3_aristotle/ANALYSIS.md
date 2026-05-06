# Analysis: Does This Formalization Solve the Conjecture?

## The Conjecture

Let k be coprime with n. For every b ∈ GF(2ⁿ), let F(b) = b^(4^k − 2^k + 1).
Let Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2ⁿ)}.
Then, for every distinct nonzero v₁, v₂ ∈ GF(2ⁿ):

  |{(x, y, z) ∈ Δ³ : v₁·x + v₂·y + (v₁ + v₂)·z = 0}| = 2^(2n−3)

## What the Formalization Actually Proves

### 1. Normalization.lean — Gold Function Derivative Analysis
- Defines the **Gold function** f(x) = x^(2^k + 1) (NOT the Kasami function)
- Shows the derivative Δ_u f(x) = f(x+u) + f(x) can be normalized via y = x/u
  to Lnorm(y) = y^(2^k) + y + 1
- Proves the root count bound: |{y : Lnorm(y) = 0}| ≤ 2^k

### 2. Factorization.lean — Linearized Polynomial Roots
- Factors L₀(y) = y^(2^k) + y through L₁(y) = y² + y and L₂(y) = Σ y^(2^i)
- Proves root bounds for L₀, L₁, L₂, and the shifted operator y^(2^k) + y + 1

### 3. Counting.lean — Abstract Spectral Framework
- Defines **abstract** Walsh coefficients W : ι → ι → ℤ and differential counts δ : ι → ι → ℕ
- **Hypothesizes** (does not prove) Parseval identity, fourth moment identity, row sums, etc.
- Proves: AB (Almost Bent) ⟹ APN (Almost Perfect Nonlinear)
- Proves: If AB, then |Walsh support| = 2^(n−1)
- Proves: C(2^(n−1), 2) = 2^(n−2) · (2^(n−1) − 1)

### 4. Kasami_Final_Theorem.lean — Bridge
- Combines the above into `kasami_bridge`: under AB + all hypotheses,
  conclude APN + support size + pair count
- Proves arithmetic: (2^(n−1))² / 2 = 2^(2n−3)

## Critical Gaps

### Gap 1: Wrong Function
The conjecture is about the **Kasami function** F(b) = b^(4^k − 2^k + 1), whose
exponent is 2^(2k) − 2^k + 1. The formalization only defines and analyzes the
**Gold function** f(x) = x^(2^k + 1). These are fundamentally different functions.

### Gap 2: The Set Δ Is Never Defined
The conjecture defines Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2ⁿ)}. The formalization
defines `walshSupport W b = {a | W(a,b) ≠ 0}` — a Walsh spectral set, not the
image set from the conjecture. These are mathematically different objects.

### Gap 3: No Triple Counting
The conjecture asks about |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}|. The
formalization computes C(|support|, 2) and |support|²/2, which are different
combinatorial quantities. The linear constraint v₁x + v₂y + (v₁+v₂)z = 0 is
never formalized.

### Gap 4: All Key Identities Are Hypothesized
The core spectral results (Parseval, fourth moment identity, row sums) are all
**assumed as hypotheses**, not derived from the function definition. The formalization
proves "if these hold, then AB ⟹ APN", but never connects this to any concrete function.

### Gap 5: AB Property Not Established
The formalization assumes the function is Almost Bent. Whether the Kasami function
is AB when gcd(k,n) = 1 is a deep theorem that is not addressed at all.

### Gap 6: Coprimality of k and n
The conjecture requires gcd(k,n) = 1. This condition appears nowhere in the formalization
(it would be needed to ensure the Kasami function has the desired spectral properties).

## Is It "From First Principles"?

**Partially.** The polynomial root bounds in Normalization.lean and Factorization.lean
are proved from relatively basic facts. However:
- The abstract framework in Counting.lean assumes all the hard Fourier-analytic
  identities rather than deriving them
- The connection to GF(2ⁿ) and specific power functions is never made
- Key Mathlib facts about finite fields, characters, and Frobenius are used but
  the critical bridge between abstract hypotheses and concrete constructions is missing

## Verdict

**The formalization does NOT solve the conjecture.** It proves some correct but
tangential results:
- General spectral theory: AB ⟹ APN (correct, but hypothesized)
- Polynomial root bounds for the Gold function (correct, but wrong function)
- Arithmetic identities involving 2^(2n−3) (correct but not connected to the conjecture)

The formalization would need:
1. A definition of the Kasami function b^(4^k − 2^k + 1) over GF(2ⁿ)
2. A definition of Δ = {F(b) + F(b+1) + 1 : b ∈ GF(2ⁿ)}
3. A proof that the Kasami function is AB when gcd(k,n) = 1
4. A formalization of the triple counting problem
5. A proof connecting |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^(2n−3)
