# Foundational Layers — From Ad-Hoc to Architectural

This document describes **foundational layers** that transform the current
formalization from ad-hoc lemma-patching into a reusable mathematical infrastructure.
Each layer is a "Tool" (in the sense of the architectural metaphor): once built,
it collapses entire classes of `sorry`s into trivial applications.

## Diagnosis: What are the current `sorry`s really asking for?

| Sorry | File | What it *really* needs |
|-------|------|----------------------|
| `truncTrace_adj_trace_prop` | Thm32Kprime | **Frobenius cycling** on finite sums + **trace bilinearity** |
| `LadjXe_bijective` | Thm32Kprime | **Frobenius composition** preserves bijection + **linearized poly algebra** |
| `adjoint_swap_bijective` | Thm32Kprime | **Power-map multiplicative bijection** instantiation of Lemma 3.1 |
| `exp_k'_eq_on_units` | Thm32Kprime | **Exponent arithmetic** mod `2^n−1` + **Fermat's little theorem** |
| `LxXk'_bijective` | Thm32 | Assembly of the above |

These are not five independent problems — they are five symptoms of three missing
foundational layers.

---

## Layer F1: Frobenius Operator Algebra (`FrobAlg.lean`)

**The Tool:** A systematic theory of the Frobenius endomorphism `φ : x ↦ x^p`
acting on `GF(p^n)`, its iterates `φ^r : x ↦ x^{p^r}`, and their interaction
with linearized polynomials `L(x) = ∑ aᵢ x^{p^i}`.

**Key results to formalize:**

1. **Frobenius cycling:** `φ^n = id` on `GF(p^n)`, i.e., `x^{p^n} = x`.
2. **Frobenius on sums:** `(∑ fᵢ)^{p^r} = ∑ fᵢ^{p^r}` (ring hom property).
3. **Linearized polynomial composition:**
   - `L(x)^{p^s} = L_s(x)` where `L_s` has shifted coefficients.
   - `L(x^{p^s}) = L_s'(x)` where `L_s'` has shifted indices.
4. **Frobenius-stable subsets:** `GF(p^k) = {x ∈ GF(p^n) | x^{p^k} = x}`.
5. **Bijection preservation:** If `f` is bijective on `GF(p^n)`, then
   `φ^r ∘ f ∘ φ^{-r}` is bijective.

**Sorries collapsed:** `truncTrace_adj_trace_prop` (B3), `LadjXe_bijective` (E1),
and the Frobenius-trace interaction lemmas in Thm32Kprime Layers A–B.

**Future impact:** Enables kernel computations (Lemma 4.3), automorphism theory
(Lemmas 4.2–4.5), and the Dickson polynomial theory in a uniform way.

**Dependencies:** Mathlib (`iterateFrobenius`, `FiniteField.pow_card`), AutBase.

---

## Layer F2: Trace and Norm over Extension Fields (`TraceNorm.lean`)

**The Tool:** The full theory of the relative trace `Tr_{n:k} : GF(p^n) → GF(p^k)`
and relative norm `N_{n:k} : GF(p^n) → GF(p^k)` for `k | n`.

**Key results to formalize:**

1. **Definition:** `Tr_{n:k}(x) = ∑_{i=0}^{n/k−1} x^{p^{ik}}` (the truncated trace
   `truncTrace` is the special case `Tr_{n:1}` restricted to the first `m` terms).
2. **Transitivity:** `Tr_{n:k} = Tr_{m:k} ∘ Tr_{n:m}` for `k | m | n`.
3. **Surjectivity:** `Tr_{n:k}` is surjective onto `GF(p^k)`.
4. **Nondegeneracy:** The bilinear form `(x, y) ↦ Tr_{n:1}(xy)` is nondegenerate.
5. **Adjoint property:** `Tr(L(w) · z) = Tr(w · L*(z))` for any linearized
   polynomial and its trace-adjoint.
6. **Frobenius interaction:** `Tr(x^{p^j} · y) = Tr(x · y^{p^{n-j}})`.
7. **Norm properties:** `N_{n:k}(x) = x^{(p^n−1)/(p^k−1)}`, multiplicativity,
   surjectivity onto `GF(p^k)*`.

**Sorries collapsed:** `truncTrace_adj_trace_prop` (B3), `fullTrace_surjective` (C1),
`fullTrace_nondegenerate` (C2), and the trace identities throughout Thm32Kprime.

**Future impact:** Directly enables Theorem 3.3 (which uses `Tr_{n:dᵢ}`),
the symplectic spread theory (Section 6), and any APN/permutation polynomial
result that involves trace conditions.

**Dependencies:** Layer F1, Mathlib finite field theory.

---

## Layer F3: Exponent Arithmetic Engine (`ExpArith.lean`)

**The Tool:** A systematic theory of the multiplicative group `GF(p^n)*` as
a cyclic group of order `p^n − 1`, and the resulting "modular exponent" calculus.

**Key results to formalize:**

1. **Fermat reduction:** `x^a = x^{a mod (p^n−1)}` for `x ∈ GF(p^n)*`,
   and `x^{p^n−1} = 1`.
2. **Power map bijectivity:** `x ↦ x^a` is bijective on `GF(p^n)*` iff
   `gcd(a, p^n−1) = 1`.
3. **Inverse computation:** If `gcd(a, p^n−1) = 1`, there exists `b` with
   `ab ≡ 1 (mod p^n−1)`, and then `(x^a)^b = x` on `GF(p^n)*`.
4. **Coprimality of Mersenne-like numbers:**
   - `gcd(p^a − 1, p^b − 1) = p^{gcd(a,b)} − 1`.
   - `gcd(p^a + 1, p^b − 1)` computations for specific parities.
5. **Congruence-to-equality lifting:** If `a ≡ b (mod p^n−1)` then
   `x^a = x^b` for all `x ∈ GF(p^n)*`.

**Sorries collapsed:** `exp_k'_eq_on_units` (G1), `k_coprime_order` (D1),
`exists_pow_inverse` (D2), and `coprime_mersenne_double` (Layer 7 of Thm32).

**Future impact:** Any future permutation polynomial result that involves
exponent manipulation (Kasami, Welch, Niho, Gold exponents, etc.) would
become a simple application of this layer.

**Dependencies:** Mathlib (`ZMod`, `Fintype.card`, `FiniteField`).

---

## Layer F4: Linearized Polynomial Algebra (`LinPoly.lean`)

**The Tool:** The algebra of linearized (additive) polynomials over `GF(p^n)`,
including their representation as circulant-like matrices, composition, and
kernel theory.

**Key results to formalize:**

1. **Ring structure:** Linearized polynomials form a (non-commutative) ring
   under addition and symbolic composition `L₁ ∘ L₂`.
2. **Matrix representation:** A linearized polynomial `L(x) = ∑ aᵢ x^{p^i}`
   corresponds to a matrix `M_L` in `GL(n, GF(p))` via the basis
   `{1, α, α², ..., α^{n-1}}` of `GF(p^n)/GF(p)`.
3. **Kernel dimension:** `|ker(L)| = p^{dim(ker(M_L))}`.
4. **Circulant structure:** When `aᵢ ∈ GF(p)` (as in the truncated trace),
   `M_L` is a circulant matrix, and its eigenvalues are determined by
   the roots of `∑ aᵢ X^i` in `GF(p^n)`.
5. **Inverse polynomial:** If `L` is bijective, `L⁻¹` is again linearized.
6. **Support under conjugation:** `spi(T_s(a) L T_t(b)⁻¹) = {i + (s−t) | i ∈ spi(L)}`
   (this is the "structural version" of Lemma 4.2, already in AutBase).

**Sorries collapsed:** `truncTrace_ker_trivial` (already proved, but this layer
would make the proof a one-liner), `frobShift_ker_card` (if it existed),
and future kernel computations for Kasami/Welch/Niho exponents.

**Future impact:** Lemma 4.3 (kernel = GF(p^r)), Lemma 4.7 (semifield
polynomial structure), Lemma 4.9 (inverse polynomial properties for type I).

**Dependencies:** Layer F1, Mathlib linear algebra.

---

## Layer F5: Spread Set and Translation Plane Theory (`SpreadSet.lean`)

**The Tool:** The formal theory of spread sets and their associated
translation planes, specialized to the `L(X)·X^k` construction.

**Key results to formalize:**

1. **Spread set definition:** `Σ = {N(x) = L_x ∘ T_0(x^k) | x ∈ F}`
   where `L_x(y) = L(xy)`.
2. **Spread condition:** `Σ` is a spread set iff `N(x) − N(y)` is
   invertible for all `x ≠ y`, iff `L(X)·X^k` is a permutation polynomial.
3. **Dual spread:** `Σ* = {N(x)* | x ∈ F}` where `*` is the trace-adjoint.
4. **Symplectic condition:** `Σ` is symplectic iff there exists `A ∈ GL(F)`
   with `N(x)*A = A*N(x)` for all `x`.
5. **Isomorphism criterion:** Two spread sets define isomorphic planes iff
   they are related by `Σ' = {T_s(b) N(T_t(a)⁻¹ x) | x ∈ F}` (up to
   the V(0)↔V(∞) swap).

**Sorries collapsed:** None directly (these are Section 4–6 results), but this
layer is the *target* of the entire paper — everything else is infrastructure.

**Future impact:** Sections 4, 5, 6 of the paper become direct applications.
Also enables formalization of other translation plane constructions
(Kantor-Williams, André, semifield planes).

**Dependencies:** Layers F1–F4, Prop21.

---

## DAG Structure

```
Mathlib
  │
  ├─► [F1] FrobAlg.lean (Frobenius Operator Algebra)
  │     │
  │     ├─► [F2] TraceNorm.lean (Trace/Norm Theory)
  │     │     │
  │     │     ├─► Thm32Kprime sorry B3 collapsed
  │     │     ├─► Thm33.lean (Theorem 3.3)
  │     │     └─► SymplTypeI/II.lean (Section 6)
  │     │
  │     ├─► [F4] LinPoly.lean (Linearized Polynomial Algebra)
  │     │     │
  │     │     ├─► AutKernel.lean (Lemma 4.3)
  │     │     ├─► AutTypeI.lean (Lemma 4.9)
  │     │     └─► AutTypeII.lean (Lemma 4.12)
  │     │
  │     └─► Thm32Kprime sorry E1 collapsed
  │
  ├─► [F3] ExpArith.lean (Exponent Arithmetic)
  │     │
  │     ├─► Thm32Kprime sorries D, G collapsed
  │     └─► Future APN exponent work
  │
  ├─► [F5] SpreadSet.lean (Spread Sets)
  │     │
  │     ├─► IsoTypeI/II.lean (Section 5)
  │     └─► SymplTypeI/II.lean (Section 6)
  │
  └─► AutBase.lean (already built — Layer B1)
        │
        └─► All of Section 4
```

## Priority Order for Implementation

1. **F1 (FrobAlg)** — Most foundational; everything depends on it.
2. **F3 (ExpArith)** — Independent of F1; collapses arithmetic sorries.
3. **F2 (TraceNorm)** — Depends on F1; collapses the hardest sorry (B3).
4. **F4 (LinPoly)** — Depends on F1; enables Section 4.
5. **F5 (SpreadSet)** — Depends on F1–F4; the geometric capstone.
