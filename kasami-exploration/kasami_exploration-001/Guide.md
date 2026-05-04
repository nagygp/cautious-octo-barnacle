# A Learner's Guide to Lean 4, Type Theory, and Category Theory

## Through the Lens of the Kasami–Bracken–McGuire Formalization

> *"The purpose of abstraction is not to be vague, but to create a new semantic level in which one can be absolutely precise."* — Edsger Dijkstra

---

## Table of Contents

1. [How to Read This Guide](#1-how-to-read-this-guide)
2. [Type Theory Foundations](#2-type-theory-foundations)
3. [Functional Programming Principles in Lean](#3-functional-programming-principles-in-lean)
4. [Category Theory Patterns](#4-category-theory-patterns)
5. [Homotopy Type Theory (HoTT) Connections](#5-homotopy-type-theory-hott-connections)
6. [Higher Category Theory and Higher Operads](#6-higher-category-theory-and-higher-operads)
7. [Opetopes and Universal Arrows](#7-opetopes-and-universal-arrows)
8. [Lean Best Practices](#8-lean-best-practices)
9. [The Art of Clean Lean Code](#9-the-art-of-clean-lean-code)
10. [Annotated Walkthrough of This Project](#10-annotated-walkthrough-of-this-project)
11. [Further Reading](#11-further-reading)

---

## 1. How to Read This Guide

This guide uses the Kasami/Bracken–McGuire formalization as a running example to teach:

- **Lean 4** as a programming language and proof assistant
- **Type theory** as the foundation beneath every definition and proof
- **Category theory** as the art of finding universal structure
- **HoTT, higher categories, and operads** as the frontier

Each section connects abstract theory to concrete code in this project. See `RequestProject/Patterns.lean` for a self-contained annotated example file.

---

## 2. Type Theory Foundations

### 2.1 Types as Propositions (Curry–Howard Correspondence)

The deepest idea in Lean: **types are propositions, terms are proofs**.

```lean
-- A type:              ℕ → ℕ → Prop
-- A term of that type: fun a b => a ≤ b
-- A proposition:       ∀ a b : ℕ, a ≤ b → a ≤ b + 1
-- A proof (= a term):  fun a b h => Nat.le_succ_of_le h
```

In this project, every `theorem` and `lemma` is just a function that *constructs* an inhabitant of a type:

```lean
-- From Counting.lean:
theorem triple_count_eq ... : (walshSupport W b).card = 2 ^ (n - 1) := by ...
```

Here the *type* is the equation `(walshSupport W b).card = 2 ^ (n - 1)`, and the proof after `:= by` constructs a *term* of that type. The `by` keyword enters "tactic mode" — an interactive way to build terms.

### 2.2 Dependent Types

Lean's type system is *dependently typed*: types can depend on values.

```lean
-- A dependent function type (Π-type):
-- The return type depends on the input value
variable (n : ℕ) : Vector ℝ n   -- a vector whose length is a *value*
```

In our project, the key abstraction uses dependent types heavily:

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ)    -- Walsh coefficients indexed by ι × ι
variable (δ : ι → ι → ℕ)    -- Differential counts indexed by ι × ι
```

The `{ι : Type*}` is a **universe-polymorphic implicit type** — it says "for any type `ι` in any universe." The square-bracket parameters `[Fintype ι]` are **type class instances** (more on this below).

### 2.3 The Four Universes

Lean has a hierarchy of type universes:

| Universe | Contains | Example |
|----------|----------|---------|
| `Prop`   | Propositions (proof-irrelevant) | `2 + 2 = 4` |
| `Type 0` (= `Type`) | Data types | `ℕ`, `ℤ`, `List ℕ` |
| `Type 1` | Types of types | `Type 0` itself |
| `Type u` | u-th universe | Parametric over levels |

**Proof irrelevance** in `Prop` means: if `p : Prop`, any two proofs `h₁ h₂ : p` are *definitionally equal*. This is why we can freely use `Classical.choice` without affecting computations.

### 2.4 Inductive Types: The Workhorse

Every data type in Lean is built from inductive definitions:

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

This is the Peano naturals. The recursor `Nat.rec` is the *universal property*: to define a function out of `ℕ`, give the zero case and the successor case. This is a **categorical initial algebra** (see §4).

---

## 3. Functional Programming Principles in Lean

### 3.1 Purity and Totality

Every Lean function is:
- **Pure**: no side effects (unless wrapped in a monad like `IO`)
- **Total**: must terminate on all inputs (the kernel checks this)

This is why Lean proofs are trustworthy — the kernel never accepts infinite loops as proofs.

### 3.2 Pattern Matching as Case Analysis

In our project, pattern matching drives case splits in proofs:

```lean
-- From Factorization.lean:
lemma frobIter_apply (x : F) : frobIter k F x = x ^ (2 ^ k) := by
  induction' k with k ih
  · aesop                    -- base case: k = 0
  · convert congr_arg ...    -- inductive step: k + 1
```

The `induction'` tactic *is* structural recursion: it pattern-matches on the natural number `k`.

### 3.3 Higher-Order Functions

Functions that take functions as arguments are everywhere:

```lean
-- Finset.filter: takes a predicate (a function to Prop) and filters
noncomputable def walshSupport (b : ι) : Finset ι :=
  Finset.univ.filter fun a => W a b ≠ 0
--                    ^^^^^^^^^^^^^^^^^^
--                    higher-order: a function passed to filter
```

```lean
-- Finset.sum: takes a function and sums its values
∑ a : ι, W a b ^ 2    -- sugar for Finset.sum Finset.univ (fun a => W a b ^ 2)
```

### 3.4 Composition and Pipelines

Lean encourages compositional thinking:

```lean
-- From Factorization.lean — the beautiful factorization identity:
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y
-- L₀ = L₁ ∘ L₂  — a factorization of operators!
```

This is the mathematical heart: the linearized polynomial `L₀(y) = y^(2^k) + y` factors as a composition `L₁ ∘ L₂` where `L₁` is the Artin–Schreier map and `L₂` is the partial Frobenius trace. **Factorization of morphisms is a categorical concept** (see §4.5).

### 3.5 The `noncomputable` Keyword

```lean
noncomputable def diffCount (f : F → F) (u v : F) : ℕ :=
  (Finset.univ.filter fun x => f (x + u) + f x = v).card
```

`noncomputable` means: this definition uses `Classical.choice` (via `DecidableEq` or `Fintype` instances that rely on classical logic). Lean can *reason* about it but can't *execute* it. This is a deliberate design: we separate the logic of correctness from computational efficiency.

---

## 4. Category Theory Patterns

### 4.1 What is a Category? (Informally)

A **category** consists of:
- **Objects** (types, sets, spaces, ...)
- **Morphisms** (functions, maps, transformations, ...)
- **Composition** that is associative with identity morphisms

In Lean/Mathlib, categories are encoded via type classes:

```lean
-- Mathlib's Category class (simplified)
class Category (C : Type*) where
  Hom : C → C → Type*           -- morphism type between objects
  id : (X : C) → Hom X X        -- identity morphism
  comp : Hom X Y → Hom Y Z → Hom X Z  -- composition
  -- + associativity and identity laws
```

### 4.2 Functors: Structure-Preserving Maps

A **functor** maps objects to objects and morphisms to morphisms, preserving composition and identities. In our project, the Frobenius endomorphism is a functor on the category of `F`-algebras:

```lean
-- The Frobenius is a ring homomorphism: it preserves + and ·
def frob2 : F →+* F := frobenius F 2
```

A ring homomorphism `F →+* F` is a functor from the one-object category defined by `F` (viewed as a ring) to itself — an **endofunctor**.

### 4.3 Natural Transformations: The "Right" Notion of Map Between Functors

A **natural transformation** `η : F ⟹ G` between functors is a family of morphisms `η_X : F(X) → G(X)` that commutes with every morphism in the source category.

In our project, the normalization lemma is secretly a natural isomorphism:

```lean
-- kernel_iso_normalized says:
--   deltaGold k F u x = 0  ↔  Lnorm k F (x * u⁻¹) = 0
```

The substitution `x ↦ x * u⁻¹` is a **natural bijection** between the kernel of `Δ_u f` and the roots of `Lnorm`. It's "natural" because it works uniformly for all `u ≠ 0`.

### 4.4 Universal Properties — The Crown Jewel

A **universal property** characterizes an object by its relationships to all other objects, rather than by its internal structure.

**Example: Products.** The product `A × B` is universal: for any type `C` with maps `f : C → A` and `g : C → B`, there is a unique map `⟨f, g⟩ : C → A × B`.

In our project, the abstract framework is a universal construction:

```lean
-- We abstract away from specific fields and characters:
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ)  -- any Walsh-like coefficients
variable (δ : ι → ι → ℕ)  -- any differential-like counts
```

This abstraction is the **universal arrow** pattern: instead of proving AB ⟹ APN for one specific field, we prove it for *any* structure satisfying the Fourier-analytic axioms. The concrete theorem is recovered by instantiating `ι` to a specific finite field.

### 4.5 Factorization Systems

The factorization `L₀ = L₁ ∘ L₂` from `Factorization.lean` is an instance of a **factorization system**: every morphism factors through an intermediate object.

```
              L₂
    F ───────────────► F
    │                  │
    │      L₀          │ L₁
    │                  │
    ▼                  ▼
    F ════════════════ F
```

The kernel bound follows: `ker(L₀) ⊆ L₂⁻¹(ker(L₁))`, so `|ker(L₀)| ≤ |ker(L₂)| · |ker(L₁)|`. This is a categorical argument — it works in any abelian category.

### 4.6 Type Classes as Functors

Lean's type class system is itself categorical. A type class like `Field F` is a **functor** from the category of types to the category of propositions (or structures):

```lean
[Field F]       -- F has field operations
[Fintype F]     -- F is finite
[CharP F 2]     -- F has characteristic 2
```

Type class inference is **functorial composition**: from `[Field F]` Lean automatically derives `[Ring F]`, `[AddCommGroup F]`, etc. This is a contravariant functor on the lattice of algebraic structures.

### 4.7 The Yoneda Lemma in Disguise

The Yoneda lemma says: an object is completely determined by its morphisms to/from all other objects. In Lean, this manifests as:

```lean
-- Extensionality: two functions are equal iff they agree on all inputs
funext : (∀ x, f x = g x) → f = g
```

This is the Yoneda lemma for the category `Type`: `Hom(A, -) ≅ A` naturally, so `f = g` iff they induce the same maps on all points.

---

## 5. Homotopy Type Theory (HoTT) Connections

### 5.1 What is HoTT?

**Homotopy Type Theory** interprets types as *spaces*, terms as *points*, and equalities as *paths*. Two proofs of the same proposition correspond to two paths — which may or may not be homotopic.

Lean 4 is *not* natively HoTT (it uses `Prop` with proof irrelevance), but many HoTT ideas appear:

### 5.2 Proof Irrelevance vs. Path Spaces

In HoTT, the type `a = b` is a *space* that can have interesting topology. In Lean's `Prop`:

```lean
-- All proofs of the same proposition are equal
-- (proof irrelevance = all path spaces are contractible)
example (h₁ h₂ : 2 + 2 = 4) : h₁ = h₂ := rfl
```

This is the HoTT axiom that `Prop` consists of **(-1)-types** (mere propositions / h-propositions): types with at most one inhabitant up to equality.

### 5.3 Truncation and Squashing

HoTT's **propositional truncation** `‖A‖` turns any type into a mere proposition. In Lean, this is `Nonempty`:

```lean
-- Nonempty A : Prop    — "A is inhabited" (forgets which inhabitant)
-- ‖A‖ in HoTT          — the propositional truncation of A
```

Our project uses `Classical.choice` freely, which corresponds to the HoTT axiom of **propositional resizing** + **choice**: from `Nonempty A` we can extract an actual `a : A`.

### 5.4 Equivalences and Isomorphisms

In HoTT, an **equivalence** `A ≃ B` is a function with a two-sided inverse up to homotopy. In Lean/Mathlib:

```lean
-- Equiv A B : a bijection between types
-- The kernel isomorphism in Normalization.lean is morally an equivalence:
kernel_deltaGold_eq_image :
    {x : F | deltaGold k F u x = 0} =
      (fun y => y * u) '' {y : F | Lnorm k F y = 0}
```

This says the solution set of `Δ_u f(x) = 0` is equivalent (as a set) to the roots of `Lnorm`, via the map `y ↦ y · u`. In HoTT language, these types are *equivalent*, not just *equal*.

### 5.5 The Univalence Principle

HoTT's **univalence axiom** says: equivalent types are equal (`(A ≃ B) ≃ (A = B)`). While Lean doesn't have univalence, Lean does have:

```lean
-- propext : (p ↔ q) → p = q    -- for Props
-- funext  : (∀ x, f x = g x) → f = g
-- Quotient.sound : for quotient types
```

These are "fragments" of univalence restricted to specific universes.

---

## 6. Higher Category Theory and Higher Operads

### 6.1 Why "Higher"?

In ordinary category theory, we have objects and morphisms. In **higher category theory**, we also have:
- **2-morphisms**: morphisms between morphisms (natural transformations)
- **3-morphisms**: morphisms between 2-morphisms
- **n-morphisms**: all the way up (or down)

### 6.2 The Proof-as-Morphism Tower

Our project secretly lives in a higher category:

| Level | Mathematical Object | Lean Encoding |
|-------|-------------------|---------------|
| 0-cells (objects) | Types `ι`, `ℤ`, `ℕ` | `Type*` |
| 1-cells (morphisms) | Functions `W : ι → ι → ℤ` | Function types |
| 2-cells | Proofs of equations between functions | `Prop` terms |
| 3-cells | Proof irrelevance (all proofs are equal) | `Prop` is an h-set |

The `kasami_bridge` theorem lives at level 2: it's a *morphism between statements* (combining three results into one).

### 6.3 Operads: Composing with Multiple Inputs

An **operad** is like a category, but morphisms can have multiple inputs:

```
     a₁  a₂  ...  aₙ
      \   |       /
       \  |      /
        ▼ ▼    ▼
     ┌─────────────┐
     │  operation   │
     └──────┬──────┘
            │
            ▼
            b
```

In our project, the Parseval identity is an operadic composition:

```lean
-- Parseval: ∑_a W(a,b)² = q²
-- This takes ALL Walsh coefficients W(a,b) for varying a
-- and produces a SINGLE number q²
-- This is a multi-input, single-output operation — an operad element!
```

The fourth moment identity is a *composition of operadic operations*:

```
  W(a,b)⁴ for all (a,b)     →     ∑∑ W⁴     →     q² · ∑∑ δ²
  (many inputs)                   (one value)       (factored form)
```

### 6.4 Higher Operads and the Proof Architecture

The proof of `AB_implies_APN` has a tree-shaped dependency structure:

```
                    AB_implies_APN
                   /       |        \
                  /        |         \
    AB_fourth_eq...  sum_sq_ge...  le_two_of_sq...
         |              |               |
       IsAB_abs    sq_ge_two_mul    (arithmetic)
```

This tree IS a higher operad element: each node is an operation that composes its children. The operad structure captures the *proof architecture* — how lemmas compose to build theorems.

### 6.5 ∞-Categories and the Proof-Relevant Future

In a (∞,1)-category, all k-morphisms for k ≥ 2 are invertible. This is exactly **proof irrelevance**: any two proofs of the same proposition are "the same" (connected by an invertible 2-morphism).

If Lean were HoTT-based, proofs would form an ∞-groupoid, and our formalization would live in an (∞,1)-topos. In current Lean, we get a truncated version of this.

---

## 7. Opetopes and Universal Arrows

### 7.1 What are Opetopes?

**Opetopes** (from "operation" + "polytope") are geometric shapes that describe higher-dimensional composition. They generalize:
- Points (0-opetopes)
- Arrows (1-opetopes)
- Globes/discs (2-opetopes)
- Trees and pasting diagrams (higher opetopes)

### 7.2 Opetopic Structure in Proofs

Each proof step in our formalization has an opetopic shape:

**The `kasami_bridge` theorem as a 2-opetope:**

```
  ┌──────────────────────────────────────────────┐
  │                kasami_bridge                  │
  │                                              │
  │   ╔══════════╗  ╔═══════════╗  ╔══════════╗  │
  │   ║AB→APN    ║  ║ support   ║  ║  pairs   ║  │
  │   ║(Task 2)  ║  ║ (Task 3a) ║  ║(Task 3b) ║  │
  │   ╚══════════╝  ╚═══════════╝  ╚══════════╝  │
  │        ↑              ↑             ↑         │
  │   [Walsh-Diff]   [Parseval]    [choose_eq]    │
  └──────────────────────────────────────────────┘
```

The outer rectangle is a 2-opetope: it has multiple input faces (the three tasks) and one output face (the combined theorem). This is the opetopic generalization of function composition.

### 7.3 Universal Arrows

A **universal arrow** from an object to a functor is the "most efficient" way to map into the functor's image. In our project:

**The abstract framework IS a universal arrow.** The abstraction:

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
```

creates a **universal construction**: instead of proving the theorem for `GF(2^n)` specifically, we prove it for the "free" finite type with zero. Any concrete finite field maps into this framework via a unique factorization:

```
  GF(2^n) ───────────────► (concrete theorem)
     │                          ↑
     │ universal                │ instantiate
     │ arrow                    │
     ▼                          │
  Abstract(ι, W, δ) ──────► (abstract theorem)
```

This is the **universal property of abstraction**: the abstract theorem is the "universal" version from which all concrete instances follow.

### 7.4 Adjunctions: The Pattern Behind Everything

An **adjunction** `F ⊣ G` between functors means: `Hom(FA, B) ≅ Hom(A, GB)` naturally. Adjunctions are ubiquitous:

- **Free ⊣ Forgetful**: Free algebras are left adjoint to forgetful functors
- **∃ ⊣ Pullback ⊣ ∀**: Quantifiers form adjoint triples
- **Abstract ⊣ Instantiate**: Our abstraction-instantiation pattern is adjoint!

In our project, the Parseval identity is an adjunction in disguise: it relates the "frequency domain" (Walsh coefficients) to the "spatial domain" (differential counts) — these two perspectives are adjoint functors on the category of functions over finite fields.

---

## 8. Lean Best Practices

### 8.1 Import Discipline

```lean
-- ❌ Bad: imports everything (slow compilation, hides dependencies)
import Mathlib

-- ✅ Good: import only what you need
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Card
```

**Why it matters:** Targeted imports make dependencies explicit, speed up compilation, and make the code more portable. See `Patterns.lean` for an example with targeted imports.

**Practical tip:** Start with `import Mathlib`, get your proof working, then use `#check` and `#print` to find which modules your lemmas come from, and narrow down.

### 8.2 Universe Polymorphism

```lean
-- ✅ Good: universe-polymorphic (works for any universe)
variable {ι : Type*}

-- ❌ Overly restrictive: locks to Type 0
variable {ι : Type}
```

### 8.3 Implicit vs. Explicit Arguments

```lean
-- {curly braces}: implicit, inferred by Lean
-- (parentheses): explicit, must be provided
-- [square brackets]: type class instances, auto-resolved

-- ✅ Good: make the type implicit, the value explicit
lemma my_lemma {n : ℕ} (hn : 1 ≤ n) : ...

-- ❌ Bad: making inferrable things explicit
lemma my_lemma (n : ℕ) (hn : 1 ≤ n) : ...  -- n is always clear from hn
```

### 8.4 Naming Conventions

Mathlib follows strict naming conventions:

| Pattern | Meaning | Example |
|---------|---------|---------|
| `X_of_Y` | X holds if Y holds | `le_two_of_sq_le_two_mul` |
| `X_iff_Y` | X is equivalent to Y | `kernel_iso_normalized` (uses ↔) |
| `X_eq_Y` | X equals Y | `triple_count_eq` |
| `X_le_Y` | X is at most Y | `card_roots_Lnorm_le` |

### 8.5 Section and Namespace Management

```lean
-- ✅ Good: use namespaces to avoid collisions
namespace KasamiFinal
  theorem kasami_bridge ... := ...
end KasamiFinal

-- ✅ Good: use sections to scope variables
section BridgeTheorems
  variable {ι : Type*} [Fintype ι]
  -- variables are in scope until `end`
end BridgeTheorems
```

### 8.6 The `noncomputable` Discipline

```lean
-- Mark definitions that use classical logic
noncomputable def diffCount ... := ...

-- Don't mark pure computations
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1  -- computable!
```

### 8.7 `set_option` Usage

```lean
-- ✅ Good: increase heartbeats for complex proofs
set_option maxHeartbeats 400000

-- ❌ Bad: disable linters to hide problems
-- set_option linter.unusedVariables false
```

---

## 9. The Art of Clean Lean Code

### 9.1 Proof Structure: Top-Down Decomposition

The project demonstrates excellent decomposition:

```
Kasami_Final_Theorem.lean     ← combines everything (3 lines of proof!)
  ├── Theorem3/Normalization.lean   ← kernel isomorphism
  ├── Theorem3/Factorization.lean   ← polynomial factorization
  └── Theorem23/Counting.lean       ← Walsh support counting
```

**Principle:** Each file should prove ONE main result with its helpers. The final theorem should be a short combination.

### 9.2 The Proof Sandwich

Good proofs follow a pattern:

```lean
theorem my_theorem (hypotheses) : conclusion := by
  -- 1. SETUP: introduce variables, unfold definitions
  -- 2. KEY STEP: the essential mathematical insight
  -- 3. CLEANUP: finish with arithmetic/automation
```

Example from the project:

```lean
theorem triple_count_eq ... := by
  -- SETUP: rewrite the Parseval sum using AB values
  have h_walshSupport : ∑ a, W a b ^ 2 = ∑ a ∈ walshSupport W b, 2^(n+1) := by ...
  -- KEY STEP: extract the cardinality
  -- CLEANUP: arithmetic
  rcases n with (_ | n) <;> simp_all +decide [pow_succ']
  nlinarith [pow_pos (zero_lt_two' ℤ) n]
```

### 9.3 Tactic Hygiene

```lean
-- ✅ Good: structured proof with named intermediates
have h_key : important_fact := by ...
exact final_step h_key

-- ❌ Bad: monolithic tactic block
simp_all +decide [everything, under, the, sun]; ring; omega; aesop
```

### 9.4 Documentation Patterns

```lean
/-! ## Section Header
  Explains the mathematical context and what follows.
-/

/-- **Theorem name.**
    One-line summary.
    
    Proof sketch: describe the key idea.
    Ref: citation. -/
theorem ... := by ...
```

### 9.5 Beautiful Patterns to Admire

#### The Factorization Diamond 💎

```lean
-- L₀ = L₁ ∘ L₂ is a thing of beauty:
-- L₀(y) = y^(2^k) + y           (the full operator)
-- L₁(y) = y² + y                (Artin-Schreier: simple, universal)
-- L₂(y) = ∑_{i<k} y^(2^i)      (partial Frobenius trace: builds up iteratively)
```

This factorization is *canonical* — it comes from the tower of Frobenius extensions. The Artin-Schreier map `L₁` is universal: it classifies all degree-2 extensions in characteristic 2.

#### The Parseval Pinch 📌

```lean
-- Parseval: ∑_a W(a,b)² = q²
-- AB:       W(a,b)² ∈ {0, 2^(n+1)}
-- Combined: |S_b| · 2^(n+1) = 2^(2n)
-- Result:   |S_b| = 2^(n-1)
```

Four lines of mathematical reasoning, perfectly captured in `triple_count_eq`. The Parseval identity is the *universal energy conservation law* for Fourier analysis.

#### The Forcing Argument 🔒

```lean
-- From AB_implies_APN:
-- Upper bound: ∑ δ² ≤ (known value)     (from fourth moment)
-- Lower bound: ∑ δ² ≥ 2·∑ δ            (from even-ness, δ² ≥ 2δ)
-- Equality forces: δ² = 2δ for each term
-- Therefore: δ ∈ {0, 2}                 (APN!)
```

This is a **squeezing argument**: trapped between matching bounds, every term must achieve equality. This pattern appears throughout mathematics (in convexity, entropy, information theory).

---

## 10. Annotated Walkthrough of This Project

### 10.1 File-by-File Summary

| File | Role | Key Theorem | Category Theory Pattern |
|------|------|-------------|------------------------|
| `Normalization.lean` | Substitution `y = x/u` | `kernel_iso_normalized` | Natural isomorphism |
| `Factorization.lean` | `L₀ = L₁ ∘ L₂` | `L₁_comp_L₂` | Factorization system |
| `Counting.lean` | Walsh-diff identity, AB⟹APN | `AB_implies_APN` | Universal property |
| `Kasami_Final_Theorem.lean` | Combines everything | `kasami_bridge` | Colimit / pushout |

### 10.2 The Proof Flow

```
    ┌─────────────────────────────────────────┐
    │           KASAMI BRIDGE                  │
    │                                          │
    │   Normalization ──► kernel_iso           │
    │        │                                 │
    │        ▼                                 │
    │   Factorization ──► root bound ≤ 2^k    │
    │        │                                 │
    │        ▼                                 │
    │   Walsh-Diff Identity (Task 1)           │
    │        │                                 │
    │        ▼                                 │
    │   AB ⟹ APN (Task 2) ◄── forcing arg    │
    │        │                                 │
    │        ▼                                 │
    │   Triple Count (Task 3) ◄── Parseval     │
    └─────────────────────────────────────────┘
```

### 10.3 Key Definitions Explained

```lean
-- Gold function: f(x) = x^(2^k + 1)
-- This is a "power map" — a morphism in the multiplicative group.
-- Its derivative has a beautiful linearized structure because
-- the Frobenius endomorphism x ↦ x^(2^k) is a RING HOMOMORPHISM
-- in characteristic p. This is the "miracle" of positive characteristic.
def goldFun (x : F) : F := x ^ goldExp k

-- The APN property: differential uniformity ≤ 2
-- This is a "local" condition: for each (u,v), the fiber is small.
-- In category theory, this is a condition on the FIBERS of a morphism.
def IsAPN (f : F → F) : Prop :=
  ∀ u : F, u ≠ 0 → ∀ v : F, diffCount f u v ≤ 2

-- The AB property: Walsh spectrum is "flat" (two-valued)
-- This is a "global" condition: the Fourier transform is controlled.
-- The AB⟹APN theorem is a LOCAL-GLOBAL PRINCIPLE:
-- global spectral flatness ⟹ local differential boundedness.
def IsAB_abs (n : ℕ) : Prop :=
  ∀ a : ι, ∀ b : ι, b ≠ 0 →
    W a b ^ 2 = 0 ∨ W a b ^ 2 = (2 : ℤ) ^ (n + 1)
```

---

## 11. Further Reading

### Type Theory and Lean
- **Theorem Proving in Lean 4** (official tutorial) — start here
- **Mathematics in Lean** (Mathlib tutorial) — for mathematical formalization
- **Functional Programming in Lean** (official guide) — for programming aspects

### Category Theory
- Saunders Mac Lane, *Categories for the Working Mathematician*
- Emily Riehl, *Category Theory in Context* (freely available online)
- Steve Awodey, *Category Theory* (gentler introduction)

### HoTT
- The HoTT Book, *Homotopy Type Theory: Univalent Foundations of Mathematics* (freely available)
- Egbert Rijke, *Introduction to Homotopy Type Theory*

### Higher Categories and Operads
- Tom Leinster, *Higher Operads, Higher Categories* (freely available on arXiv)
- Jacob Lurie, *Higher Topos Theory* (advanced, freely available)

### Cryptographic Functions (the math in this project)
- Lilya Budaghyan, *Construction and Analysis of Cryptographic Functions*
- Bracken–Byrne–Markin–McGuire, *Fourier Spectra of Binomial APN Functions*

---

*This guide was created to accompany the Kasami–Bracken–McGuire formalization project in Lean 4. See `RequestProject/Patterns.lean` for executable, annotated code examples.*
