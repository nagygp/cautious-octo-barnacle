# Kasami APN/AB Formalization — Deep Analysis

## Table of Contents
1. [CLRS Algorithm Pattern Mappings](#1-clrs-algorithm-pattern-mappings)
2. [Category Theory Connections](#2-category-theory-connections)
3. [Type Theory Patterns](#3-type-theory-patterns)
4. [HoTT (Homotopy Type Theory) Connections](#4-hott-connections)
5. [Higher Category Theory & Higher Operads](#5-higher-category-theory--higher-operads)
6. [Opetopes](#6-opetopes)
7. [Universal Arrows & Beautiful Patterns](#7-universal-arrows--beautiful-patterns)
8. [Lean Best Practices & Clean Code](#8-lean-best-practices--clean-code)
9. [Functional Programming Principles](#9-functional-programming-principles)
10. [Refactoring Suggestions](#10-refactoring-suggestions)

---

## 1. CLRS Algorithm Pattern Mappings

The formalization encodes several algorithmic patterns that have direct counterparts in
Cormen, Leiserson, Rivest & Stein's *Introduction to Algorithms* (CLRS).

### 1.1 Divide and Conquer (CLRS Ch. 4)

**Pattern in code:** The proof of `AB_implies_APN` decomposes the fourth-moment sum into
trivial (b=0) and nontrivial (b≠0) parts via `fourth_moment_split`, then independently
bounds each part. This mirrors CLRS divide-and-conquer: split, conquer subproblems,
combine.

```
∑_{a,b} W(a,b)⁴  =  [trivial part: b=0]  +  [nontrivial: b≠0]
```

The `delta_sum_split` lemma does the same for the differential side. Each sub-sum is
bounded independently, then the results are recombined.

**CLRS connection:** This is the *Master Theorem* pattern (CLRS §4.5) applied to
algebraic identities rather than recurrences — we split a global sum into independent
pieces of known structure.

### 1.2 Counting & Enumeration (CLRS Ch. 5, Appendix C)

**Pattern in code:** `triple_count_eq` and `triple_count_pairs` count elements of
`walshSupport W b` and compute `Nat.choose |S_b| 2`. This is classic combinatorial
counting: given a set of size k, how many unordered pairs exist?

**CLRS connection:** CLRS Appendix C (Counting and Probability) — binomial coefficients,
the identity C(n,2) = n(n-1)/2, and the technique of computing a global quantity by
counting local contributions.

### 1.3 Polynomial Root Finding (CLRS Ch. 30)

**Pattern in code:** `card_roots_Lnorm_le` and `card_roots_L₀_le` bound the number of
roots of polynomials over finite fields. The factorization `L₁ ∘ L₂ = L₀` is a
*polynomial factorization* that reduces root-counting to analyzing simpler factors.

**CLRS connection:** CLRS Ch. 30 (Polynomials and the FFT) — polynomial evaluation,
degree bounds, and the fundamental theorem that a degree-d polynomial has ≤ d roots.
The factorization `L₁_comp_L₂` is analogous to the FFT's recursive factorization of
the DFT polynomial.

### 1.4 Graph/Matrix Structure (CLRS Ch. 22–26)

**Pattern in code:** The Walsh coefficient matrix `W : ι → ι → ℤ` and differential
table `δ : ι → ι → ℕ` are essentially adjacency-matrix-like structures. The fourth
moment identity `∑ W⁴ = q² · ∑ δ²` is a *spectral graph theory* identity relating
the spectrum (Walsh) to the combinatorial structure (differential).

**CLRS connection:** CLRS Ch. 22 (Graph representations) — adjacency matrices, and
the general theme that spectral properties of a matrix encode combinatorial properties
of the underlying structure.

### 1.5 Amortized Analysis / Pigeonhole (CLRS Ch. 17)

**Pattern in code:** The key forcing step in `AB_implies_APN` uses an *amortized argument*:
- Global sum: `∑_{u≠0} ∑_v δ(u,v)² = 2q(q-1)`
- Pointwise lower bound: `δ(u,v)² ≥ 2·δ(u,v)` (from evenness)
- Row constraint: `∑_v δ(u,v) = q`
- Combined: `∑_v δ(u,v)² ≥ 2q` per row, with equality iff each δ(u,v) ∈ {0,2}
- Total rows contribute exactly `2q(q-1)`, forcing equality everywhere

This is a *potential method* argument (CLRS §17.3): the "potential" ∑δ² cannot exceed
the budget, and the lower bound forces each term to be tight.

### 1.6 Dynamic Programming / Memoization (CLRS Ch. 15)

**Pattern in code:** The proof structure itself follows optimal substructure:
- Normalization.lean solves the kernel isomorphism subproblem
- Factorization.lean solves the root-counting subproblem  
- Counting.lean solves the Walsh support counting subproblem
- Kasami_Final_Theorem.lean combines them (like the final DP table)

Each file's results are "memoized" as proven lemmas, reused without re-derivation.

### 1.7 Reduction / Problem Transformation (CLRS Ch. 34)

**Pattern in code:** `kernel_iso_normalized` reduces the problem "count roots of
Δ_u f(x) = 0" to "count roots of Lnorm(y) = 0" via the substitution y = x/u.
This is a classic *polynomial-time reduction* — transforming one problem instance
to an equivalent but simpler one.

**CLRS connection:** CLRS Ch. 34 (NP-Completeness) — the art of reduction. Here it's
an *algebraic reduction* rather than a computational complexity reduction, but the
structural pattern is identical: prove an equivalence, then solve the simpler version.

---

## 2. Category Theory Connections

### 2.1 The Normalization as a Natural Isomorphism

The kernel isomorphism `kernel_iso_normalized` establishes:

```
{x ∈ F | Δ_u f(x) = 0}  ≅  {y ∈ F | Lnorm(y) = 0}
```

via the map `y ↦ y · u`. In categorical language, this is a **natural isomorphism**
between two functors:

- **Functor 1:** `F* → Set`, sending `u ↦ ker(Δ_u f)`
- **Functor 2:** `F* → Set`, sending `u ↦ u · ker(Lnorm)`

The naturality square commutes because the substitution `y = x · u⁻¹` is functorial
in `u`.

### 2.2 The Frobenius as an Endofunctor

`frob2 : F →+* F` (the Frobenius x ↦ x²) is a **ring endomorphism**, hence an
endofunctor on the category of F-modules (or F-algebras). The iterated Frobenius
`frobIter k` = φ^k is the k-fold composition of this endofunctor.

In the category **FAlg** of F-algebras:
- `frob2` is an endofunctor
- `frobIter` is the free monoid action of ℕ on End(F)
- The factorization `L₁ ∘ L₂ = L₀` is a factorization in the endomorphism monoid

### 2.3 The Walsh Transform as a Functor

The Walsh transform `W : ι → ι → ℤ` can be viewed as a **profunctor**
`W : ι^op × ι → Ab` (where Ab = abelian groups). The Parseval identity
`∑_a W(a,b)² = q²` is the **trace condition** on this profunctor.

More precisely, the Walsh transform is the **matrix of a natural transformation**
between representable functors in the category of F-vector spaces, expressed in
the character basis.

### 2.4 The Differential Table as a Hom-Functor

`δ : ι → ι → ℕ` counts morphisms (solutions) in a category of "difference equations."
For fixed u, the function `v ↦ δ(u,v)` is the **hom-functor** Hom(u, −) applied to
the difference operator Δ_u.

The constraint `∑_v δ(u,v) = q` says: **the total number of morphisms out of u equals
|F|** — a completeness condition analogous to the Yoneda lemma's statement that
Hom(u, −) determines u up to isomorphism.

### 2.5 The Fourth Moment Identity as a Trace Formula

The identity `∑_{a,b} W(a,b)⁴ = q² · ∑_{u,v} δ(u,v)²` is a **categorical trace formula**:

- **LHS:** The trace of W⊗W (Schur product) — spectral side
- **RHS:** The trace of δ⊗δ — geometric side

This is the finite field analogue of the **Selberg trace formula** in harmonic analysis,
or the **Lefschetz trace formula** in algebraic geometry. The bridge between spectral
and geometric data is mediated by character orthogonality (a form of Yoneda).

---

## 3. Type Theory Patterns

### 3.1 Curry-Howard in Action

Every theorem in this formalization is a **type** (proposition), and every proof is a
**term** (program) inhabiting that type. Key examples:

| Lean Declaration | Curry-Howard Reading |
|---|---|
| `lemma delta_eq_lin_plus_const` | A function transforming algebraic identity witnesses |
| `theorem AB_implies_APN` | A program converting AB evidence into APN evidence |
| `theorem kasami_bridge` | A product type (conjunction) of three sub-programs |

### 3.2 Dependent Types

The formalization uses **dependent function types** (Π-types) extensively:

```lean
theorem triple_count_eq
    (hq : q = 2 ^ n) (hn : 1 ≤ n) ... (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card = 2 ^ (n - 1)
```

Here the type of the output (`(walshSupport W b).card = 2^(n-1)`) **depends on** the
input values `b`, `n`, `q`. This is a Π-type: `Π (b : ι), b ≠ 0 → ...`.

### 3.3 Universe Polymorphism

The variable declaration `{ι : Type*}` uses **universe polymorphism** — the proofs
work for index types at any universe level. This is the type-theoretic analogue of
"parametric polymorphism" in System F.

### 3.4 Propositions as Types, Proofs as Programs

The `IsAPN_abs` definition is a **Σ-type** (existential negation):
```lean
def IsAPN_abs : Prop := ∀ u : ι, u ≠ 0 → ∀ v : ι, δ u v ≤ 2
```

A proof of `IsAPN_abs δ` is a **certified program** that, given any nonzero u and any v,
produces a proof that δ(u,v) ≤ 2. The AB→APN theorem is a **compiler** from AB-programs
to APN-programs.

### 3.5 Inductive Types and Pattern Matching

The `rcases n with (_ | _ | n)` pattern in `half_sq_pow` is **structural recursion on ℕ**
— the type-theoretic eliminator for the inductive type `Nat`:
- Case `n = 0`: base case
- Case `n = 1`: another base case  
- Case `n = k + 2`: inductive step

This corresponds to the **recursor** `Nat.rec` in the type theory.

---

## 4. HoTT (Homotopy Type Theory) Connections

### 4.1 Propositions as (-1)-Types

In HoTT, propositions are **(-1)-truncated types** (mere propositions). All the `Prop`
declarations in this formalization (`IsAPN_abs`, `IsAB_abs`, etc.) live in the
(-1)-truncation — they have at most one inhabitant up to homotopy.

The proof irrelevance of Lean's `Prop` sort implements this: any two proofs of the same
proposition are **judgmentally equal**, corresponding to the contractibility of the
fiber in HoTT.

### 4.2 The Univalence Axiom and `kernel_iso_normalized`

The kernel isomorphism:
```
{x | Δ_u f(x) = 0} ≃ {y | Lnorm(y) = 0}
```

In HoTT, the **univalence axiom** states that equivalences between types are paths
between types: `(A ≃ B) ≃ (A = B)`. The kernel isomorphism would, under univalence,
give a **path** between the two kernel types, allowing us to transport properties
(like cardinality) across the equivalence.

In Lean, we achieve the same effect via `Finset.card_image_of_injective` — the
cardinality is invariant under injective maps, which is the truncated version of
transport along a path.

### 4.3 Higher Inductive Types and the Frobenius

The iterated Frobenius `frobIter k` can be viewed as a **loop** in the space of
endomorphisms of F. In HoTT:
- `frob2` is a **generator** of π₁(End(F))
- `frobIter k` is the k-fold concatenation of this loop
- The factorization `L₁ ∘ L₂ = L₀` is a **path** in the endomorphism space

The Galois group Gal(F/𝔽₂) ≅ ℤ/nℤ acts on F via the Frobenius, and this action
is the **fundamental group** of the classifying space BG acting on the fiber.

### 4.4 Truncation and Proof Irrelevance

The use of `Decidable` instances throughout (`[DecidableEq ι]`) corresponds to the
**decidability** of identity types — in HoTT terms, the type ι has decidable equality,
meaning the identity type `a =_ι b` is **decidable** (either inhabited or empty, and
we can algorithmically determine which).

---

## 5. Higher Category Theory & Higher Operads

### 5.1 The Walsh Transform as a 2-Morphism

In a **2-category** of finite abelian groups:
- **0-cells:** Finite fields F, index types ι
- **1-cells:** The Walsh transform W and differential table δ (as matrices/profunctors)
- **2-cells:** The fourth moment identity as a 2-morphism between W⊗W and q²·δ⊗δ

The Parseval identity is a **coherence condition** at the 2-categorical level — it
ensures that the Walsh transform is a **unitary 1-cell** (up to the factor q²).

### 5.2 The Factorization L₁ ∘ L₂ = L₀ as an Operad Composition

In the **operad of linearized polynomials** over 𝔽₂:
- **Colors:** Natural numbers (degrees)
- **Operations:** Linearized (additive) polynomials L : F → F  
- **Composition:** Function composition

The factorization `L₁ ∘ L₂ = L₀` is an **operadic composition**:
```
    L₁ (degree 2)
     |
    L₂ (degree 2^{k-1})
     |
  = L₀ (degree 2^k)
```

This is a **binary tree** in the operad, with L₁ as root and L₂ as leaf.

### 5.3 The E_∞ Structure of Characteristic 2

In characteristic 2, the identity `x + x = 0` gives every element an **involution**.
This is an **E₁-algebra structure** (associative up to homotopy). The Frobenius
endomorphism φ(x) = x² commutes with addition (`φ(x+y) = φ(x) + φ(y)` in char 2),
making F an **E_∞-algebra** in the category of 𝔽₂-vector spaces.

The AB and APN conditions are then **constraints on the E_∞ structure** — they say
that the multiplication (Gold function x^(2^k+1)) interacts with the additive
E_∞ structure in a controlled way.

### 5.4 Higher Operads and the Differential Table

The differential table `δ(u,v)` can be organized into a **colored operad**:
- **Input colors:** Elements u ∈ F* (nonzero differences)
- **Output colors:** Elements v ∈ F (output differences)
- **Operations:** Solution sets {x | f(x+u) + f(x) = v}
- **Composition:** Via the group structure of (F, +)

The APN condition `δ(u,v) ≤ 2` says that each operation has **arity ≤ 2** —
this is a **quadratic operad** constraint, closely related to Koszul duality
for quadratic operads.

---

## 6. Opetopes

### 6.1 Proof Trees as Opetopes

Each proof in the formalization has a tree structure that can be visualized as an
**opetope** — a higher-dimensional polytope encoding the composition pattern.

The proof of `kasami_bridge` has the shape:

```
        kasami_bridge (3-cell: conjunction)
       /        |           \
AB_implies_APN  triple_count_eq  triple_count_pairs
      |              |                |
  [sub-lemmas]   [Parseval+AB]    [Parseval+AB]
```

This is a **3-dimensional opetope**: a 3-cell (the conjunction `⟨_, _, _⟩`) whose
source is a pasting diagram of three 2-cells.

### 6.2 The Zoom Opetope

The normalization step creates a "zoom" pattern:
```
    Δ_u f(x) = 0          (problem at scale F)
         |  ≃               (opetopic face: substitution y = x/u)
    Lnorm(y) = 0           (problem at scale F, but normalized)
         |  ≤               (opetopic face: degree bound)
    2^k roots              (answer)
```

Each arrow is a **face** of the opetope, and the composition gives the final
bound. This is a **2-opetope** (a globular 2-cell with structured source).

### 6.3 The Factorization Opetope

The factorization `L₁ ∘ L₂ = L₀` is an opetopic composition:
```
    L₁ ● L₂ = L₀
```
where ● is the operadic composition. In opetopic notation, this is a
**corolla** (tree with one node) with two leaves, composed into a single operation.

---

## 7. Universal Arrows & Beautiful Patterns

### 7.1 Universal Property of the Kernel

The kernel `{x | Δ_u f(x) = 0}` is a **universal arrow** in the following sense:
it is the **equalizer** of two morphisms in the category of F-sets:

```
    F  ⇉  F
      Δ_u f
       0
```

The equalizer (kernel) is the universal object through which any map to F that
makes the two morphisms agree must factor. The normalization lemma shows this
equalizer is isomorphic to a simpler one.

### 7.2 The Parseval Identity as Adjunction

Parseval's identity `∑_a |W(a,b)|² = q²` expresses a **Plancherel theorem** —
the Walsh transform is a **unitary equivalence** (up to scaling). In categorical
terms, the Walsh transform functor is **self-adjoint**:

```
    Hom(W·f, g) ≅ Hom(f, W·g)
```

The fourth moment identity is then the **unit-counit equation** of this adjunction
applied twice.

### 7.3 Beautiful Pattern: The Forcing Argument 🌟

The most elegant part of the entire formalization is the **forcing argument** in
`AB_implies_APN`. Here is the beautiful logical structure:

1. **Global constraint:** `∑ δ² = 2q(q-1) + q²` (from the fourth moment)
2. **Pointwise lower bound:** `δ² ≥ 2δ` (from evenness)
3. **Row sum:** `∑_v δ(u,v) = q` (conservation law)
4. **Lower bound per row:** `∑_v δ(u,v)² ≥ 2q`
5. **Total rows:** `(q-1)` nontrivial rows, each contributing ≥ 2q
6. **Budget:** Total = `2q(q-1)` matches the lower bound exactly
7. **Forcing:** Equality everywhere ⟹ δ(u,v)² = 2δ(u,v) ⟹ δ ∈ {0, 2} ✓

This is a **budget argument** — the total budget is tight, so every individual
contribution must be at its minimum. It's the algebraic analogue of the
pigeonhole principle elevated to a spectral setting.

### 7.4 Beautiful Pattern: Characteristic 2 Self-Duality 🌟

In characteristic 2, `x + x = 0` means `-x = x`. Subtraction is addition.
Negation is identity. This creates a **self-dual** structure where:
- The additive group (F, +) is a vector space over 𝔽₂
- Every nonzero element has order 2
- The differential `f(x+u) + f(x)` is simultaneously a "forward difference" and
  a "backward difference"

The `CharTwo.neg_eq` and `CharTwo.sub_eq_add` lemmas capture this duality.
In the language of quadratic forms: char 2 is where **symmetric = alternating**,
and this self-duality is what makes the APN/AB theory so rich.

### 7.5 Beautiful Pattern: The Gold Function 🌟

The Gold function `f(x) = x^(2^k+1)` is beautiful because:
- Its exponent `2^k + 1` is the **sum of two Frobenius powers**: `x^(2^k) · x`
- Its derivative `Δ_u f(x)` is **linearized** — a polynomial where every term has
  degree a power of 2 (plus a constant)
- The normalized equation `y^(2^k) + y + 1 = 0` is an **Artin-Schreier equation**
  shifted by 1 — connecting APN theory to class field theory
- The factorization `L₁ ∘ L₂ = L₀` exploits the **telescoping** of Frobenius powers

### 7.6 Universal Arrow: The Walsh Transform as Left Adjoint

The Walsh transform can be viewed as the **left adjoint** to the "evaluation"
functor in the duality between F and its Pontryagin dual F̂:

```
    Walsh : Fun(F, ℂ) → Fun(F̂, ℂ)    (left adjoint)
    Eval  : Fun(F̂, ℂ) → Fun(F, ℂ)    (right adjoint)
```

The Parseval identity is the **unit** of this adjunction (η: Id → Eval ∘ Walsh),
and the inversion formula is the **counit** (ε: Walsh ∘ Eval → Id).

---

## 8. Lean Best Practices & Clean Code

### 8.1 Namespace Hygiene

✅ **Good:** The code uses `namespace FourierSpectralBridge` and `namespace KasamiFinal`
to prevent name collisions. Each file has its own logical namespace.

**Tip:** Always namespace your definitions. Bare names like `goldFun` could collide with
other formalizations. Better: `Gold.fun` or `APN.goldFun`.

### 8.2 Section Variables

✅ **Good:** The code uses `variable` declarations to avoid repeating type class
assumptions:
```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
```

⚠️ **Warning:** The linter flags unused section variables in some theorems. Use
`omit [DecidableEq ι] in theorem ...` to suppress when appropriate.

### 8.3 Noncomputable Sections

✅ **Good:** `noncomputable section` is used correctly in Normalization.lean and
Factorization.lean where classical reasoning is needed.

**Tip:** Mark individual definitions `noncomputable` rather than entire sections when
possible — it makes the computability boundary explicit.

### 8.4 Documentation Strings

✅ **Good:** Key lemmas have `/-- ... -/` doc strings explaining the mathematical content.

**Tip:** Every `def` and major `theorem` should have a doc string. Use `/-! ... -/`
for section-level documentation (already done well here).

### 8.5 Proof Style

**Tactic mode** is used throughout, which is appropriate for these algebraic proofs.

**Tips for cleaner proofs:**
- Avoid trailing semicolons after `ring` or `grind` — they're no-ops
- Replace `exact?` suggestions with the found term (already mostly done)
- Use `calc` blocks for chains of equalities/inequalities instead of nested `have`s
- Prefer `omega` over `nlinarith` for pure natural number goals when possible

### 8.6 Import Discipline

The current code uses `import Mathlib` everywhere, which imports the entire library
(~4M lines). For production code, prefer targeted imports:

```lean
-- Instead of:
import Mathlib
-- Prefer:
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
```

This improves build times and makes dependencies explicit. (See annotated files for
specific import suggestions.)

### 8.7 Naming Conventions

Follow Mathlib naming conventions:
- `camelCase` for definitions and lemmas
- Use `_of_` for implications: `APN_of_AB` rather than `AB_implies_APN`
- Use `_iff_` for biconditionals
- Use `_le_`, `_lt_`, `_eq_` for relations
- Prefix with the primary type: `WalshCoeff.support` rather than `walshSupport`

### 8.8 Error Handling

**Tip:** When a proof uses `simp_all +decide`, add a comment explaining what the
simp lemmas are doing. Future maintainers (including yourself) will thank you.

### 8.9 Modular File Structure

✅ **Excellent:** The code is split into focused files:
- `Normalization.lean` — kernel isomorphism (single responsibility)
- `Factorization.lean` — polynomial factorization (single responsibility)
- `Counting.lean` — combinatorial counting (single responsibility)
- `Kasami_Final_Theorem.lean` — integration (composition)

This follows the **Single Responsibility Principle** and makes each file
independently verifiable.

---

## 9. Functional Programming Principles

### 9.1 Referential Transparency

All definitions are **pure functions** — `goldFun`, `deltaGold`, `linPart`, `Lnorm`,
`L₀`, `L₁`, `L₂` have no side effects. Given the same inputs, they always return
the same outputs. This is enforced by Lean's type system.

### 9.2 Higher-Order Functions

The Walsh transform `W : ι → ι → ℤ` is a **curried** higher-order function. The
partial application `W a : ι → ℤ` is a "row" of the Walsh matrix. The definition
```lean
noncomputable def walshSupport (b : ι) : Finset ι :=
  Finset.univ.filter fun a => W a b ≠ 0
```
uses `filter` with a **lambda** (anonymous function) — classic FP pattern.

### 9.3 Algebraic Data Types

The `IsAB_abs` definition uses a **sum type** (disjunction):
```lean
W a b ^ 2 = 0 ∨ W a b ^ 2 = (2 : ℤ) ^ (n + 1)
```
This is an ADT with two constructors, and pattern matching on it (`cases hAB a b hb`)
is the eliminator.

### 9.4 Composition over Inheritance

The proof architecture uses **composition** rather than inheritance:
- `kasami_bridge` composes `AB_implies_APN`, `triple_count_eq`, `triple_count_pairs`
- `AB_implies_APN` composes `AB_fourth_eq_second_times_pow`, `sum_sq_ge_two_mul_sum_of_even`
- No type class hierarchy is extended — everything is composed from primitives

### 9.5 The Functor Pattern

`Finset.filter`, `Finset.sum`, `Finset.card` form a **functor-like** pipeline:
```
univ  →[filter p]→  S  →[card]→  ℕ
univ  →[map f]→  images  →[sum]→  total
```

This is the `map-filter-reduce` pattern from functional programming, applied to
finite sets with decidable predicates.

### 9.6 Monadic Proof Construction

The `refine' ⟨_, _, _⟩` pattern in `kasami_bridge` is essentially **monadic bind**
in the proof monad: "I need to produce a triple; give me three proof obligations."
Each obligation is then filled independently — this is the **applicative functor**
pattern.

---

## 10. Refactoring Suggestions

### 10.1 Extract the "Budget Argument" Pattern

The forcing argument in `AB_implies_APN` (§7.3) is a general-purpose proof technique.
Extract it as a standalone lemma:

```lean
/-- If ∑ f(i)² = 2 · ∑ f(i) and f(i)² ≥ 2·f(i) pointwise, then f(i)² = 2·f(i) everywhere. -/
lemma eq_of_sum_eq_of_pointwise_ge [Fintype ι] (f : ι → ℕ)
    (h_even : ∀ i, 2 ∣ f i)
    (h_sum : ∑ i, f i ^ 2 = 2 * ∑ i, f i) :
    ∀ i, f i ^ 2 = 2 * f i := ...
```

This would simplify `AB_implies_APN` and be reusable in other contexts.

### 10.2 Use Mathlib's `Polynomial.roots` API More Directly

The root-counting lemmas (`card_roots_Lnorm_le`, `card_roots_L₀_le`,
`card_roots_shifted_le`) all follow the same pattern: construct a polynomial,
bound its degree, apply `Polynomial.card_roots'`. This could be abstracted:

```lean
/-- Count roots of a polynomial over a finite field. -/
lemma card_roots_le_degree (p : Polynomial F) (hp : p ≠ 0) :
    (univ.filter fun x => p.eval x = 0).card ≤ p.natDegree := ...
```

Then each specific case becomes a one-liner.

### 10.3 Separate Pure Arithmetic from Algebraic Geometry

The arithmetic lemmas (`pow_sq_identity`, `pairs_to_final_const`, `half_sq_pow`,
`choose_pow_two_eq`) are independent of the APN/AB theory. Move them to a dedicated
`Arithmetic.lean` utility file for better separation of concerns.

### 10.4 Consider a Typeclass for APN/AB Functions

Instead of passing `W` and `δ` as function arguments everywhere, consider:

```lean
class CryptographicFunction (F : Type*) [Field F] [Fintype F] where
  f : F → F
  walsh : F → F → ℤ
  diff : F → F → ℕ
  parseval : ∀ b, ∑ a, walsh a b ^ 2 = (Fintype.card F : ℤ) ^ 2
  row_sum : ∀ u, u ≠ 0 → ∑ v, (diff u v : ℤ) = Fintype.card F
```

This would reduce parameter lists and enable dot notation: `cf.isAPN`, `cf.isAB`.

### 10.5 Use `Finset.card_filter_le_iff` for Root Bounds

Some root-counting proofs could be simplified using higher-level Mathlib API instead
of building the polynomial explicitly. Check if `Polynomial.card_rootSet_le_degree`
exists in your Mathlib version.

### 10.6 CLRS-Inspired: Precompute the Frobenius Table

For computational experiments (not proofs), precomputing a lookup table for Frobenius
powers — analogous to CLRS's precomputation in dynamic programming — would speed up
evaluation of `L₂(y) = ∑_{i=0}^{k-1} y^(2^i)`.

### 10.7 Replace `grind` with More Targeted Tactics

`grind` is powerful but opaque. Where possible, replace with:
- `ring` for ring equalities
- `omega` for linear arithmetic over ℕ/ℤ
- `simp [specific_lemmas]` for rewriting chains

This improves proof readability and robustness across Lean versions.

---

## Summary of Cross-Domain Connections

| Code Pattern | CLRS | Category Theory | Type Theory | HoTT |
|---|---|---|---|---|
| Split sum into trivial/nontrivial | Divide & Conquer (Ch. 4) | Coproduct decomposition | Sum type elimination | Pushout |
| Root count ≤ degree | Polynomial evaluation (Ch. 30) | Fiber cardinality of a morphism | Decidable equality on fibers | Truncation of path space |
| Fourth moment = q²·∑δ² | Matrix multiplication (Ch. 28) | Trace formula (2-morphism) | Dependent pair type | Loop space identity |
| Budget/forcing argument | Amortized analysis (Ch. 17) | Equalizer + universal property | Injectivity of constructors | Contractibility |
| File decomposition | Modular design (Ch. 1) | Functor composition | Module system | Fibration sequence |
| y = x/u substitution | Reduction (Ch. 34) | Natural isomorphism | Transport along path | Univalence |
| `filter + card` | Counting (App. C) | Image of a functor | Σ-type + truncation | Connected components |
| `L₁ ∘ L₂ = L₀` | Recursive decomposition (Ch. 4) | Factorization in End(F) | Function composition | Path concatenation |
