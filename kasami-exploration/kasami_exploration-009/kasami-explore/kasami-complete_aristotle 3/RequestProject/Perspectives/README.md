# Perspectives on the Kasami-Gold APN Theorem

## Overview

These files explore different foundational perspectives on the Kasami-Gold
"AB ⟹ APN" theorem, formalized in Lean 4. Each file compiles without errors
or `sorry` statements.

## Files

### `TypeTheory.lean`
**Type-theoretic and functional programming perspective.**

- Curry-Howard correspondence: the theorem as a function type
- Dependent types: parameterized properties and predicates
- Proof irrelevance vs HoTT path spaces
- Universe polymorphism as naturality
- Constructive vs classical content
- Functional programming patterns (higher-order functions, composition, ADTs, totality)
- Lean best practices (naming, documentation, proof style, variable management)
- `#eval` for testing and exploration

### `CategoryTheory.lean`
**Category-theoretic perspective using Mathlib's `CategoryTheory` library.**

- The poset category of APN bounds
- The APN bound 2 as a universal arrow / initial object
- The "squeezing argument" as a limit computation
- Equalizers and the forcing fiber {0, 2}
- Functoriality of the Walsh and differential transforms
- The Frobenius as a natural endomorphism
- Adjunctions and the Fourier transform
- Monoidal structure and the convolution theorem
- The full categorical architecture diagram

### `HigherStructures.lean`
**Higher structures: HoTT, ∞-categories, operads, and opetopes.**

- HoTT truncation hierarchy and h-levels
- Why the Kasami proof lives in h-Prop (-1 truncated)
- Univalence vs propositional extensionality
- ∞-categories of finite fields and functions
- Stable ∞-categories and spectra
- The differential operad (formalized as `BoundedOperad`)
- APN as "binary operad" — arity ≤ 2
- Opetopic shapes for differential equations
- Higher Inductive Types (HITs) and opetopic type theory
- The squeezing lemma as a pullback
- Lean best practices for module organization and tactic selection

## Key Insights

| Perspective | What it reveals |
|------------|----------------|
| **Type Theory** | Proof = program; the theorem is a function |
| **Category Theory** | Universal bounds; naturality of identities |
| **HoTT** | Proof irrelevance; truncation levels |
| **∞-Categories** | Higher coherence (trivial here) |
| **Operads** | APN = binary operad; arity constraints |
| **Opetopes** | Solution sets as geometric shapes |

## Building

Each file can be built independently:
```
lake build RequestProject.Perspectives.TypeTheory
lake build RequestProject.Perspectives.CategoryTheory
lake build RequestProject.Perspectives.HigherStructures
```
