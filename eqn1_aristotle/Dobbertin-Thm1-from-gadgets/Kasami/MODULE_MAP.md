# Kasami — module map (building-block architecture)

A compositional re-presentation of the **permutation half** of Dobbertin's 1999
paper *"Kasami Power Functions, Permutation Polynomials and Cyclic Difference
Sets"*.  The idea: fix a few primitive **LEGO bricks** (the maps `L`, `F`, `C`),
add a small number of **combinators** that snap them together, and reach the
paper's results by pure composition.

Modules and declarations are named by **role / structural pattern**, not by the
paper's theorem numbers.  Import the whole toolkit with `import Kasami`.
Everything is `sorry`-free (standard axioms `propext`, `Classical.choice`,
`Quot.sound` only).

## The bricks — `Kasami/Gadgets/`

| Brick | Module (namespace `Kasami.Gadgets`) | Role |
| --- | --- | --- |
| **F** — Frobenius / doubling | `Gadgets/Frobenius.lean` | `frobenius`, `frobeniusPow` (`x ↦ x^{2^r}`), `doubling`; `frob_cycle`, `frobeniusPow_periodic`, `frobeniusPow_bijective`. |
| **L** — linearized trace loop | `Gadgets/TraceLoop.lean` | `traceLoop m x = ∑_{i<m} x^{2^i}`; `traceLoop_add` (additive), `traceLoop_frobenius` (equivariant), `traceLoop_sq` / `traceLoop_isBit` (idempotent bit). |
| **C** — cyclotomic-coset bookkeeping | `Gadgets/CyclotomicCoset.lean` | `mersenne_coprime`, `inv_mod_exists` (`(2^k−1)⁻¹ mod 2ⁿ−1`), `powMap_bijective` (`x ↦ xᵃ` a permutation iff `a ⟂ |F|−1`). |

Each brick depends only on `Mathlib`, so all three are reusable / upstreamable on
their own.

## The combinators — `Kasami/Combinators/`

| Combinator | Module (namespace `Kasami.Combinators`) | Role |
| --- | --- | --- |
| Artin–Schreier telescope (glue **L** to **F**) | `Combinators/ArtinSchreierTelescope.lean` | `traceLoop_artin_schreier` (`L(x²+x)=x^{2^k}+x`), `traceLoop_frobenius_invariant`, `traceLoop_artin_schreier_zero` (`L(t^{2^k}+t)=0`). |
| Linearized change of variable (basis change of the loop) | `Combinators/StepTrace.lean` | `stepTrace` (step-`2^k` trace `P`), `numeratorSum` (`S`), `numeratorSum_eq_stepTrace_frob` (`S=P^{2^k}`), `stepTrace_telescope`. |
| Categorical trace pattern | `Combinators/CategoricalTracePattern.lean` | `traceLoop_eq_algebraMap_trace`: **L is the field trace** `Algebra.trace 𝔽₂ L` — the one evaluation/coevaluation loop. |

## The assembly

| Module | Role |
| --- | --- |
| `Kasami/KasamiMap.lean` (`Kasami.kasamiMap`) | Snaps the bricks together: `kasamiMap = (S + α·L)·z^{coset}`, definitionally the paper's `qKasami`. |
| `Kasami/Results/PermutationCriterion.lean` | The headlines (namespace `Kasami`): `kasamiMap_isPermutation_iff` (**Theorem 1**), `traceFreeKasami_isPermutation_iff` (`α=0`, **Theorem 5**), `traceVersionKasami_isPermutation_iff` (`α=1`), `kasamiMap_one_isBit` (value-at-1 obstruction). |

## Relationship to the `Equation1/` engine

The heavy root-counting argument behind Theorem 1 (the two cases showing equation
(1) has at most one solution) is proven, `sorry`-free, in the `Equation1/` folder.
This `Kasami/` layer is its **readable, block-structured, reusable
re-presentation**: it names the primitive maps `L`, `F`, `C`, isolates the
combinators that wire them, and re-derives the headline permutation criteria as
compositions of those blocks.

## Scope

This toolkit covers the **permutation** half of the paper (Theorem 1 and its
trace-free / trace-version cases).  The **difference-set** half (autocorrelation,
2-rank, the §3–4 conjecture) needs two further primitives not built here — a
Fibonacci-style recursion block for the explicit inverse, and a
character/Fourier block `ψ = (−1)^{Tr}` — whose hard content (Gauss/Jacobi-sum
evaluation, recursion combinatorics) is not delivered by composition alone.
