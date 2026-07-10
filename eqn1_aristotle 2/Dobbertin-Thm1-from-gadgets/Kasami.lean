-- Primitive gadgets (the LEGO bricks).
import Kasami.Gadgets.Frobenius
import Kasami.Gadgets.TraceLoop
import Kasami.Gadgets.CyclotomicCoset
-- Combinators (how the bricks snap together).
import Kasami.Combinators.ArtinSchreierTelescope
import Kasami.Combinators.StepTrace
import Kasami.Combinators.CategoricalTracePattern
-- The assembled Kasami map and the headline results.
import Kasami.KasamiMap
import Kasami.Results.PermutationCriterion

/-!
# Kasami permutations from basic building blocks — theory root

A compositional toolkit for the *permutation half* of Dobbertin's 1999 paper
*"Kasami Power Functions, Permutation Polynomials and Cyclic Difference Sets"*.
Modules and declarations are named by **role / structural pattern**, not by the
paper's theorem numbers, and everything is `sorry`-free.

## The bricks (`Kasami/Gadgets/`)

| Brick | Module | Meaning |
| --- | --- | --- |
| **F** | `Gadgets/Frobenius` | the doubling map `φ : x ↦ x²` and its iterates `φ^r`; cycling, periodicity, bijectivity. |
| **L** | `Gadgets/TraceLoop` | the linearized trace loop `L_m(x) = ∑_{i<m} x^{2^i}`; additive, Frobenius-equivariant, idempotent bit. |
| **C** | `Gadgets/CyclotomicCoset` | exponent/coset arithmetic mod `2ⁿ−1`; `mersenne_coprime`, `inv_mod_exists`, `powMap_bijective`. |

## The combinators (`Kasami/Combinators/`)

| Combinator | Module | Meaning |
| --- | --- | --- |
| Artin–Schreier telescope | `Combinators/ArtinSchreierTelescope` | glue **L** to **F**: `L(x²+x) = x^{2^k}+x`, trace Frobenius-invariance, and `L(t^{2^k}+t)=0`. |
| Linearized change of variable | `Combinators/StepTrace` | the step-`2^k` trace `P` and numerator `S = P^{2^k}`, with its own telescope. |
| Categorical trace pattern | `Combinators/CategoricalTracePattern` | **L** *is* the field trace: `traceLoop = Algebra.trace 𝔽₂ L` (the evaluation/coevaluation loop). |

## The assembly (`Kasami/KasamiMap.lean`, `Kasami/Results/`)

* `KasamiMap` snaps the bricks together into `kasamiMap = ( S + α·L )·z^{coset}`,
  definitionally the paper's `qKasami`.
* `Results/PermutationCriterion` reaches the headline:
  - `kasamiMap_isPermutation_iff` — **Theorem 1**: `q_α` is a permutation iff
    `k' + α·n` is odd;
  - `traceFreeKasami_isPermutation_iff` (`α = 0`, **Theorem 5**) and
    `traceVersionKasami_isPermutation_iff` (`α = 1`) — the two named cases;
  - `kasamiMap_one_isBit` — the value-at-`1` parity obstruction.

The heavy root-counting engine those results compose over lives, proven, in the
`Equation1/` folder; this `Kasami/` layer is its readable, block-structured,
reusable re-presentation.  See `Kasami/MODULE_MAP.md`.
-/
