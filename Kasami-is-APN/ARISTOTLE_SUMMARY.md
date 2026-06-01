# Summary of changes for run fa123a29-e7ba-4866-b327-3e5a0863f33b
## Kasami APN Extended to Even k — Complete, Sorry-Free

I created `RequestProject/KasamiEvenK.lean` (330 lines, 0 sorries) containing a fully machine-verified extension of the Kasami APN theorem to **all valid k values**, removing the `Odd k` restriction from the original `kasami_is_apn`.

### What was added

The new file builds 8 DAG layers on top of the existing sorry-free infrastructure:

**Layer A — APN under additive bijection** (`apn_comp_additive_bijective`)
- The APN property is invariant under composing with additive bijections (abstract "Morita equivalence" for APN).

**Layer B — Frobenius properties**
- `frob_additive`: (x+y)^{2^j} = x^{2^j} + y^{2^j} (from Mathlib's `add_pow_char_pow`)
- `frob_bijective`: x ↦ x^{2^j} is bijective on finite fields (via Mathlib's `iterateFrobenius` ring hom)
- `frob_pow_card`: x^{2^n} = x on GF(2ⁿ) (from Mathlib's `FiniteField.pow_card`)
- `apn_frob_twist`: APN preserved under Frobenius twist x^d → x^{d·2^j}

**Layer C — Kasami exponent congruence** (`kasami_exp_congr_mod`)
- The key arithmetic bridge: d_k ≡ d_{n-k} · 2^{2k} (mod 2ⁿ-1)

**Layer D — Power function identity** (`kasami_pow_frob_identity`, `kasami_apn_of_complement`)
- On GF(2ⁿ): x^{d_k} = Frob_{2k}(x^{d_{n-k}}) — reduces even k to odd n-k

**Layer E — Gold APN** (for edge case k = n-1)
- `frob_fixed_implies_GF2`: x^{2^k} = x with gcd(k,n)=1 implies x ∈ {0,1} (finite field intersection GF(2^k) ∩ GF(2^n) = GF(2))
- `gold_differential`: The Gold differential is GF(2)-affine
- `gold_kernel_eq`: Gold kernel ↔ Frobenius fixed point
- `gold_is_apn`: **Gold APN Theorem** — x^{2^k+1} is APN when gcd(k,n) = 1

**Layer F — Parity & coprimality transfer**
- `odd_sub_even`: n odd, k even ⟹ n-k odd (via `Nat.Odd.sub_even`)
- `coprime_sub_self`: gcd(k,n) = 1 ⟹ gcd(n-k,n) = 1

**Layer G — Even k theorems**
- `kasami_is_apn_even_k`: Even k with n-k ≥ 2 (Frobenius twist to odd case)
- `kasami_is_apn_even_k_edge`: Even k with n-k = 1 (reduces to Gold APN)

**Layer H — Unified general theorem**
- `kasami_is_apn_general`: **Kasami APN for ALL valid k** — no parity restriction

### Mathematical strategy

When k is even and n is odd, the companion parameter n-k is odd with gcd(n-k,n) = gcd(k,n) = 1. The Kasami exponents satisfy d_k ≡ d_{n-k} · 2^{2k} (mod 2ⁿ-1), so on GF(2ⁿ) the power function x^{d_k} equals the Frobenius twist Frob_{2k}(x^{d_{n-k}}). Since Frobenius is an additive bijection, APN is preserved. The edge case k = n-1 (where n-k = 1) reduces to Gold APN (d₁ = 3), proved from scratch via the linear differential and finite field intersection theory.

### Project totals

- **11 files, 2377 lines, 0 sorries**
- All theorems depend only on standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Updated `README.md` with the full dependency DAG and new theorem documentation

# Summary of changes for run 50b207a4-69a6-4ca8-a6c5-270ce693daad
# Kasami APN Theorem — Fully Formalized & Connected to Theorem 3.2

## What was accomplished

I created `KasamiAPN.lean` (404 lines, 0 sorries) containing a **complete, machine-verified proof** that the Kasami power function x^d is APN (Almost Perfect Nonlinear) on GF(2ⁿ), where d = 2^{2k} - 2^k + 1, with k odd, n odd, 1 < k < n, gcd(k,n) = 1.

The proof is **directly connected to the Dempwolff–Müller Theorem 3.2** (`LxXk'_bijective` from `Thm32.lean`) as its core engine.

## How the connection works (3 layers)

### Layer 1 — Key Polynomial Identity (`kasami_key_identity`)
I proved the identity:
```
((x+1)^d + x^d + 1) · (x²+x)^q = (x^q + x)^{q+1}
```
This reduces the Kasami differential to the **truncated trace** L_k from Theorem 3.2.

### Layer 2 — Decomposition via Theorem 3.2 (`phi_injective_on_units`)
The map Φ(u) = L_k(u)^{q+1}/u^q factors as `(L_k(u)·u^{e'})^{q+1}` where e' satisfies the condition of `LxXk'_bijective`. I proved:
- **Arithmetic identity** (`kasami_arith_identity`): e₀·(2ⁿ-1-2^k) ≡ 2^{k-1}·(2^k+1) mod (2ⁿ-1)
- **Existence of linking exponent** (`exists_linking_exp`): e' exists with the right properties
- **Gold coprimality** (`gold_coprime`): gcd(2^k+1, 2ⁿ-1) = 1, making y^{q+1} a permutation

### Layer 3 — Composition of Bijections
Since L_k(·)·(·)^{e'} is bijective (Thm 3.2's `LxXk'_bijective`) and y^{q+1} is bijective (Gold coprimality), their composition Φ is bijective on GF(2ⁿ)*, ruling out all nontrivial collisions.

## 11 lemmas proved (all sorry-free)

| Lemma | Role |
|-------|------|
| `truncTrace_artin_schreier` | L_k(x²+x) = x^{2^k} + x |
| `kasami_key_identity` | The key polynomial identity |
| `gold_coprime` | gcd(2^k+1, 2ⁿ-1) = 1 |
| `gold_pow_bijective` | y^{2^k+1} is a permutation |
| `kasami_arith_identity` | Arithmetic linking identity |
| `exists_linking_exp` | Existence of the e' exponent |
| `phi_injective_on_units` | Φ is injective on units |
| `kasami_collision_forces_equal_u` | Collision ⟹ x²+x = y²+y |
| `sq_add_self_eq_zero_char2` | u²+u = 0 ↔ u ∈ {0,1} |
| `kasami_exp_coprime` | d coprime to 2ⁿ-1 |
| `apn_of_normalized` | WLOG reduction to a=1 |

## Project totals

- **10 files, 2047 lines, 0 sorries**
- All theorems depend only on standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Updated `README.md` with dependency DAG showing how `KasamiAPN.lean` connects to `Thm32.lean`

# Summary of changes for run af37efd5-77d9-4a06-be03-41b13642d49c
## Complete Sorry-Free Formalization of Theorem 3.2 (Dempwolff–Müller)

All sorries have been eliminated. The project now contains a **fully machine-verified proof** of Theorem 3.2 from "Permutation polynomials and translation planes of even order" by U. Dempwolff and P. Müller (Adv. Geom. 2013).

### What was proved

**Theorem 3.2.** Let F = GF(2ⁿ) with n odd. Let m be odd with 1 < m < n and gcd(m,n) = 1. Let L(X) = ∑_{i=0}^{m-1} X^{2^i}. Set k = 2^{n-1} - 2^{m-1} - 1. Then:
- `L(X)·X^k` is a permutation polynomial on F (`theorem_3_2`, `LxXk_bijective`)
- `L(X)·X^{k'}` is also a permutation polynomial when k·k' ≡ 2^{m-1} mod (2ⁿ-1) (`LxXk'_bijective`)

Both theorems depend only on standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

### Project structure (8 files, 1643 lines, 0 sorries)

| File | Lines | Role |
|------|-------|------|
| `AutBase.lean` | 288 | Semilinear operators, additive polynomials, support theory, Lemma 4.2 |
| `FrobAlg.lean` | 169 | Frobenius cycling/periodicity, Frobenius-bijection transfer, exponent reduction |
| `TraceNorm.lean` | 143 | Frobenius sums, trace additivity/invariance/nondegeneracy, adjoint property |
| `ExpArith.lean` | 91 | Units group, power map bijectivity, Mersenne GCD, arithmetic identities |
| `Lemma31.lean` | 133 | Lemma 3.1: L(x)·M(x) injective ↔ L*(x)·M⁻¹(x) injective (LinearMap version) |
| `BareLemma31Skeleton.lean` | 218 | Lemma 3.1 for bare additive functions (used by adjoint transfer) |
| `AdjointBij.lean` | 89 | Adjoint bijectivity transfer engine |
| `Thm32.lean` | 488 | Main theorem: all 12 layers of the proof |

### Mathematical highlights

The proof follows the paper's 12-layer decomposition:
1. **Truncated trace additivity** — Frobenius in characteristic 2
2. **Telescoping identity** — L(x)² + L(x) = x^{2^m} + x
3. **Kernel triviality** — coprime Frobenius fixed-point argument via Bezout
4. **Dickson recursion** — x·f_{m+1}(x) = f_m(x)² + x^{2^{m+1}}
5. **Functional equation** — f_m(z+z⁻¹) = z^{2^m-1} + z^{-(2^m-1)} by induction
6. **Arithmetic identity** — 2k + (2^m+1) = 2ⁿ-1
7. **Mersenne coprimality** — gcd(2^m-1, 2^{2n}-1) = 1 via odd m, gcd(m,n)=1
8. **Coprime power map injectivity** on finite groups
9. **Dickson injectivity** — lifting to algebraic closure, using the functional equation and Mersenne coprimality
10. **Reduction** — L(x⁻¹)²·x^{2^m+1} = f_m(x)
11. **Main injectivity** — L(x)·x^k injective on F* by squaring and Dickson
12. **k' transfer** — via trace-adjoint duality (Lemma 3.1) and Frobenius composition

# Summary of changes for run 2a420a1b-bfab-402e-817c-a139d81b98c0
# Kasami APN Cross-Session Synthesis

I've written a comprehensive analysis document at `KASAMI_SYNTHESIS.md` (~350 lines). Here are the key findings:

## The Convergence Pattern
All 10+ sessions, 5+ MVP approaches, topos bridges, co-Kasami analysis, and polynomial methods converge to **one single sorry**: `collision_in_L_kernel` — if the Kasami differential has a collision, the difference of collision points (normalized) lies in ker(L_k).

## Key Cross-Session Insights

1. **The Kasami differential is NOT additive** (Session: MVP1, disproved). This is the most important negative result — it rules out the direct Gold-style approach and explains why Kasami is fundamentally harder.

2. **The c=1 case IS proved** (Session: CoKasamiCollision). The biconditional `g(t) = 1 ↔ L_k(t) = 0` is sorry-free. The hard part is collisions at values c ≠ 1.

3. **The norm equation alone gives tautologies** (Session: CoKasamiCollision). Applying Frobenius to the ratio equation produces A = A. This means approaches relying only on the norm relation will hit a wall.

4. **The full co-collision is FALSE for k ≥ 2** (Session: CollisionProof). Any approach trying to prove a bidirectional equivalence between collisions and kernel membership will fail.

5. **Phantom solutions are blocked by trace conditions** (computational verification in GF(16)). The proof likely needs to invoke trace/Artin-Schreier theory.

## The Missing Ingredient (New Analysis)

I worked through the algebra carefully and identified what none of the sessions have exploited: there are **TWO independent equations** relating the collision variables r = L_k(t)/L_k(h) and τ = L_1(h)/L_1(t):

- **Eq1** (from Cross factorization, close to proved): `r^{q+1}·τ^q = r^q + r + 1`
- **Eq2** (from L_comm, close to proved): `r²v² + rv = τ^{-q}w^q + τ^{-1}w`

Each equation alone gives tautologies under Frobenius. But **together**, eliminating τ produces a polynomial F(r) = 0 of bounded degree, which can be handled by `Polynomial.card_roots_le_degree`.

## Recommended Path Forward

1. **Formalize the two-equation system** — both sides involve already-proved identities
2. **Eliminate τ** by substitution to get a single polynomial equation F(r) = 0
3. **Bound deg(F)** ≤ q+1 (or similar)
4. **Apply polynomial root counting** from Mathlib
5. **Map back** to show bounded collisions → `collision_in_L_kernel`

This gives ~5-10 concrete lemmas, each a manageable algebraic step, building on the substantial sorry-free infrastructure already accumulated across sessions.

## Warnings from Negative Results
- Don't try to prove Kasami differential is additive (disproved)
- Don't try to prove full co-collision for k≥2 (false)
- Don't rely on norm equation alone (gives tautologies)
- Hilbert 90 approach needs too much new infrastructure vs. polynomial degree bounds