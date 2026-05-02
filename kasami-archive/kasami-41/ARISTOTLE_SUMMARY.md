# Summary of changes for run 9795d431-d967-4e6b-95ff-e3acf9ef3e43
## Formalization: Kasami Functions are Almost Bent (AB)

I've created a Lean 4 formalization of the theorem that Kasami functions are AB (Almost Bent) over finite fields of characteristic 2, following Kasami's 1971 paper.

### File Structure

- **`RequestProject/Defs.lean`** — Core definitions:
  - `AbsoluteTrace`: Trace map Tr: F → GF(2)
  - `WalshTransform`: W_f(a,b) = Σ_x (-1)^{Tr(b·f(x) + a·x)}
  - `IsAlmostBent`: AB property (three-valued Walsh spectrum {0, ±2^((n+1)/2)})
  - `IsAPN`: Almost Perfect Nonlinear property
  - `kasamiExponent k`: d = 2^(2k) - 2^k + 1
  - `kasamiFunction`: x ↦ x^d

- **`RequestProject/Helpers.lean`** — Helper lemmas:
  - Characteristic 2 algebra (negation, Frobenius additivity)
  - Linearized polynomial L(y) = y^(2^(2k)) + y^(2^k) + y
  - Root counting: |{y : y^(2^m) + y = 0}| = 2^gcd(m,n) (**fully proved**)
  - Kernel inclusion: L(y) = 0 ⟹ y^(2^(3k)) + y = 0 (**fully proved**)

- **`RequestProject/KasamiAB.lean`** — Main theorem and proof:
  - Key factorization: (2^k + 1)·d = 2^(3k) + 1 (**proved**)
  - gcd(d, 2^n-1) = 1 when gcd(k,n) = 1, n odd (**proved**)
  - x ↦ x^d is a permutation when gcd(d, |F|-1) = 1 (**proved**)
  - APN property reduces to derivative bound (**structure proved**)
  - Walsh spectrum: W² ∈ {0, 2^(n+1)} ⟹ W ∈ {0, ±2^((n+1)/2)} (**proved**)
  - **Main theorem** `kasami_is_AB`: Kasami functions are AB (**structure complete**)

- **`RequestProject/README.md`** — Detailed documentation

### What's Proved vs Sorry'd

**16 lemmas fully proved**, including all the number-theoretic foundations and the Walsh spectrum extraction logic. The main theorem's logical structure is complete: `kasami_is_AB` correctly decomposes into constituent parts.

**3 deep results remain sorry'd** — these correspond to the hardest parts of Kasami's 1971 paper:
1. `kasami_derivative_at_most_two`: The derivative equation has ≤ 2 solutions (Kasami's Lemma 1)
2. `linearized_kernel_bound`: Kernel bound for the linearized polynomial
3. `kasami_walsh_squared`: Three-valued Walsh spectrum (Kasami's Theorem 3 + Corollary 2, page 18)

These require formalization of linearized polynomial theory and Reed-Muller code weight enumerators that don't yet exist in Mathlib. The proof outline is thoroughly documented in comments.