# Mathlib Foundations of the Normalization × Factorization → Counting Pipeline

This document identifies the simplest concepts, recurring patterns, and most general Mathlib structures that the formalization (Normalization.lean, Factorization.lean, Counting.lean, and the final Kasami bridge) builds on or relates to, organized from simplest/most concrete to most general/abstract.

---

## 1. Foundational Algebra

### 1.1 Finite Fields and Characteristic (`CharP`, `Field`, `Fintype`)

The entire formalization is parameterized by:
```
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
```

This is the most basic building block — a finite field of characteristic 2. The Mathlib concepts involved:

| Concept | Mathlib location | Role in the project |
|---------|-----------------|---------------------|
| `CharP F 2` | `Mathlib.Algebra.CharP.Basic` | Characteristic-2 arithmetic: `x + x = 0`, `-x = x`, `sub = add` |
| `Field F` | `Mathlib.Algebra.Field.Basic` | Division, inverses (`u⁻¹`), `mul_inv_cancel` |
| `Fintype F` | `Mathlib.Data.Fintype.Basic` | `Fintype.card F`, finiteness of the universe |

**Simplest pattern here:** `CharP.cast_eq_zero F 2` yields `(2 : F) = 0`, from which `neg_eq_of_add_eq_zero_left` gives `-x = x` and subtraction = addition. This is the most elementary algebraic fact the whole pipeline rests on.

### 1.2 The Frobenius Endomorphism (`frobenius F p`)

In Factorization.lean:
```
def frob2 : F →+* F := frobenius F 2
def frobIter : F →+* F := (frobenius F 2) ^ k
```

| Concept | Mathlib location | Role |
|---------|-----------------|------|
| `frobenius F p` | `Mathlib.FieldTheory.Perfect` / `Mathlib.RingTheory.FrobeniusEndomorphism` | The ring homomorphism `x ↦ x^p` |
| `RingHom.iterateFrobenius` | (iterated Frobenius) | `x ↦ x^(p^k)` |
| `add_pow_char_pow` | `Mathlib.Algebra.CharP.Basic` | `(a + b)^(p^k) = a^(p^k) + b^(p^k)` in char p — the key identity for expanding the Gold function derivative |

**Pattern:** The Frobenius is the fundamental "linearization" tool — it turns the nonlinear power map into something additive. The factorization L₁ ∘ L₂ = L₀ is essentially a decomposition in the ring of additive (Frobenius-semilinear) operators.

### 1.3 Power and Exponent Arithmetic (`pow`, `Nat.pow`)

The Gold exponent `2^k + 1` and all root-count bounds involve:

| Concept | Role |
|---------|------|
| `pow_ne_zero` | `u^d ≠ 0` when `u ≠ 0` |
| `pow_pos` | Positivity of `2^n` |
| `Nat.pow_le_pow_right` | Monotonicity of `2^k` |
| `pow_mul` / `pow_add` / `pow_succ` | Exponent arithmetic for Frobenius iteration |

These are the simplest Nat/Int lemmas — pure arithmetic scaffolding.

---

## 2. Polynomial Theory (Factorization & Normalization)

### 2.1 Polynomial Root Counting

Both Normalization.lean and Factorization.lean use the same core pattern to bound the number of roots:

```
Polynomial.card_roots' p  :  p.roots.card ≤ p.natDegree
Multiset.toFinset_card_le  :  s.toFinset.card ≤ s.card
```

**The pattern (used 4 times across the two files):**
1. Construct a polynomial `p : Polynomial F` whose roots are exactly the elements satisfying some equation.
2. Show the filter set embeds into `p.roots.toFinset`.
3. Chain: `filter.card ≤ toFinset.card ≤ roots.card ≤ natDegree`.

| Concept | Mathlib location | Role |
|---------|-----------------|------|
| `Polynomial.card_roots'` | `Mathlib.RingTheory.Polynomial.Basic` | Degree bound on number of roots |
| `Polynomial.natDegree` | `Mathlib.Algebra.Polynomial.Degree.Definitions` | Degree computation |
| `Polynomial.eval_finset_sum` | `Mathlib.Algebra.Polynomial.Eval` | Evaluating sum-of-monomials polynomials |
| `Polynomial.IsRoot` / `Polynomial.mem_roots` | | Connecting set-theoretic roots to polynomial roots |

**This is the single most important Mathlib pattern in the factorization/normalization layer** — every root-count bound (`card_roots_Lnorm_le`, `card_roots_L₀_le`, `card_ker_L₁`, `card_ker_L₂`, `card_roots_shifted_le`) follows this template.

### 2.2 Degree Calculations

Computing `natDegree` of constructed polynomials requires:

| Lemma | Use |
|-------|-----|
| `Polynomial.natDegree_add_eq_left_of_natDegree_lt` | `deg(X^(2^k) + X + 1) = 2^k` |
| `Polynomial.natDegree_X_pow` | `deg(X^n) = n` |
| `Polynomial.natDegree_sum_eq_of_disjoint` | `deg(∑ X^(2^i)) = 2^(k-1)` (for L₂) |

The disjoint-degree-sum lemma is more specialized — it captures the fact that a sum of monomials with distinct degrees has degree equal to the maximum.

---

## 3. Combinatorics (Counting.lean)

### 3.1 Finset Manipulation

The counting arguments are built on `Finset` operations:

| Concept | Mathlib location | Role |
|---------|-----------------|------|
| `Finset.filter` | `Mathlib.Data.Finset.Basic` | Defining solution sets `{x | f(x+u) + f(x) = v}` |
| `Finset.card` | | Counting solutions |
| `Finset.sum_comm` | `Mathlib.Algebra.BigOperators.Group.Finset` | Swapping summation order (critical for Walsh↔differential exchange) |
| `Finset.sum_congr` | | Rewriting summands |
| `Finset.sum_le_sum` / `Finset.sum_lt_sum` | | Pointwise inequality lifting |
| `Finset.card_le_card` | | Monotonicity of cardinality under subset |
| `Finset.filter_ne'` | | Splitting sums at zero |

### 3.2 The Sum-Splitting Pattern

Both `fourth_moment_split` and `delta_sum_split` use the same pattern: split `∑_{x ∈ univ}` into the `x = 0` term plus `∑_{x ≠ 0}`, via `Finset.filter_ne'`. This is the combinatorial analog of case-splitting on whether a parameter is zero.

### 3.3 `Nat.choose` and Pair Counting

```
Nat.choose_two_right : Nat.choose n 2 = n * (n - 1) / 2
```

Used in `triple_count_pairs` to convert support cardinality to pair count. This is elementary combinatorics formalized.

---

## 4. The Abstract Framework Pattern (Most General)

### 4.1 Abstraction over `ι`

Counting.lean introduces the most general pattern in the formalization:

```
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ)  -- Walsh coefficients
variable (δ : ι → ι → ℕ)  -- Differential counts
```

This abstracts away from any specific field or function. The theorems (`AB_implies_APN`, `triple_count_eq`, `kasami_bridge`) work for **any** finite type with a zero element, given axioms about Walsh coefficients and differential counts. This is a powerful Mathlib-style generalization: the algebraic content (Parseval, orthogonality, fourth moment identity) is packaged as hypotheses, and the combinatorial-algebraic argument is purely structural.

**This is the most general Mathlib pattern:** parameterizing over abstract finite types with algebraic hypotheses, rather than working concretely with `ZMod (2^n)` or `GaloisField 2 n`.

### 4.2 Hypothesis-Driven Theorem Structure

The `AB_implies_APN` theorem takes 12 hypotheses. This mirrors Mathlib's style of stating theorems with maximal generality — each Fourier-analytic fact (Parseval, trivial character values, row sums, fourth moment identity, char-2 pairing) is a separate hypothesis rather than being derived internally. This makes the theorem:
- Reusable across different character-theoretic setups
- Independently verifiable at each hypothesis
- Composable (the Kasami bridge theorem simply feeds the right hypotheses)

---

## 5. Analysis / Number Theory Connections

### 5.1 Additive Characters (`AddChar F ℂ`)

The definition of `WalshCoeff` uses:
```
noncomputable def WalshCoeff (ψ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, ψ (a * x + b * f x)
```

| Concept | Mathlib location | Role |
|---------|-----------------|------|
| `AddChar F ℂ` | `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` | Additive characters for Fourier analysis over finite fields |
| `Complex.normSq` | `Mathlib.Analysis.SpecialFunctions.Complex.Norm` | `|W|²` for the AB condition |

This connects to the general Mathlib theory of characters on abelian groups, though the formalization abstracts this away into ℤ-valued hypotheses for the main proofs.

### 5.2 `nlinarith` and `omega` as Proof Engines

The arithmetic lemmas (`sq_ge_two_mul_of_even`, `le_two_of_sq_le_two_mul`, `pow_sq_identity`, `half_sq_pow`) are proved using `nlinarith` and `omega` — Mathlib's nonlinear arithmetic and linear arithmetic decision procedures. These are the "most general" proof tools used, handling the numerical side automatically.

---

## 6. Cross-Cutting Mathlib Patterns (Summary)

### From Simplest to Most General:

1. **`CharP F 2` arithmetic** — `x + x = 0`, `-x = x` (elementary ring theory)
2. **`pow` lemmas** — exponent manipulation (basic ℕ arithmetic)
3. **`Polynomial.card_roots'`** — root counting via degree bounds (univariate polynomial theory)
4. **`frobenius F 2` / `add_pow_char_pow`** — Frobenius linearity (positive characteristic algebra)
5. **`Finset.filter` / `Finset.card` / `Finset.sum`** — discrete counting and summation (finite combinatorics)
6. **`Finset.sum_le_sum` / `sum_lt_sum`** — pointwise-to-global inequality lifting (ordered algebra over finsets)
7. **`Nat.choose` / `Nat.div`** — combinatorial counting (elementary combinatorics)
8. **`AddChar` / `Complex.normSq`** — Fourier analysis over finite groups (analytic number theory)
9. **Abstract `[Fintype ι] [Zero ι]` parameterization** — hypothesis-driven theorems over abstract finite types (the most general Mathlib design pattern used)

### The Central Pipeline Pattern:

```
Normalization (geometry of substitution y = x/u)
    ↓  kernel isomorphism
Factorization (algebra of L₁ ∘ L₂ = L₀)
    ↓  root count ≤ degree
Counting (combinatorics of Parseval + AB ⟹ support size)
    ↓  pair counting
Kasami Bridge (synthesis: APN + |S_b| + C(|S_b|,2))
```

Each layer uses a different fragment of Mathlib:
- **Normalization:** `Field` + `inv_mul_cancel` + `CharP` (algebraic geometry flavor)
- **Factorization:** `Polynomial` + `frobenius` + `Finset.sum` (algebraic number theory flavor)  
- **Counting:** `Finset` + `BigOperators` + `nlinarith` (additive combinatorics flavor)
- **Bridge:** Pure composition of the above (categorical/structural flavor)

---

## 7. Connections to Broader Mathlib Theories

The formalization, while self-contained, touches on or relates to several deeper Mathlib theories that it does not directly use but that generalize its patterns:

| Broader Theory | Connection |
|---------------|------------|
| **`GaloisField`** (`Mathlib.FieldTheory.Galois`) | The concrete `F = GF(2^n)` is never instantiated; the formalization works for any finite field of char 2 |
| **`LinearMap` / `Module`** | `L₀`, `L₁`, `L₂` are 𝔽₂-linear maps, but formalized as plain functions with separate additivity lemmas rather than using `LinearMap` |
| **`MvPolynomial` / `PowerSeries`** | The factorization L₁ ∘ L₂ could be expressed in the ring of linearized polynomials (a non-commutative polynomial ring under composition) |
| **`Finset.sum_product`** | The double sums `∑_a ∑_b` relate to sums over product types |
| **`ZMod` / `AddChar` orthogonality** | The Parseval and fourth-moment identities are hypothesized rather than derived from character orthogonality |
| **Coding theory** (`Mathlib` has limited coverage) | APN/AB functions are central to optimal code/cipher design; this formalization builds the spectral bridge that connects them |
