import KasamiPermutations2.FiniteField.Frobenius
import KasamiPermutations2.FiniteField.Trace
import KasamiPermutations2.NumberTheory.MersenneNumbers
import KasamiPermutations2.KasamiMap
import KasamiPermutations2.SpecialValues
import KasamiPermutations2.TraceFreeCriterion
import KasamiPermutations2.TraceVersionCriterion
import KasamiPermutations2.PermutationCriterion
import KasamiPermutations2.Equation1ProofSpace
import KasamiPermutations2.Equation1Classifier

/-!
# Kasami permutation criterion — library entry point

A self-contained formalisation, from the `Mathlib` foundations, of the opening of
Dobbertin's *Theorem 1* (Dobbertin 1999, "Kasami Power Functions, Permutation
Polynomials and Cyclic Difference Sets") — equation (1) and the permutation
criterion for the generalized Kasami map `q_α`, together with the derivation of
equation (2) from equation (1).

The modules are organised by **mathematical role** rather than by their numbering
in the paper:

| module | role |
|--------|------|
| `FiniteField/Frobenius` | the Frobenius endomorphism `x ↦ x^{p^r}` on a finite field |
| `FiniteField/Trace` | the additive (absolute) trace and its identities |
| `NumberTheory/MersenneNumbers` | coprimality / invertibility of `2^k − 1` mod `2ⁿ − 1` |
| `KasamiMap` | the definitions `Tr`, `qKasami` (`q_α`), `eqn1`, `ell`, `Qmap` |
| `SpecialValues` | the values `q_α(0)`, `q_α(1)` (the "only if" direction) |
| `TraceFreeCriterion` | criterion for the constant-bit map `q^{(ε)}` (paper: Theorem 5) |
| `TraceVersionCriterion` | criterion for the trace map `g = q₁` (paper: Theorem 8) |
| `PermutationCriterion` | the headline: `q_α` bijective ↔ parity; and (1) ⟹ (2) |
| `Equation1ProofSpace` | the Kasami-context groupoid and the analytic↔combinatorial parity bridge |
| `Equation1Classifier` | the engine-free necessary direction, the classifier equivalence `Context ≡ Discrete (ZMod 2)`, and the parity graph |

The paper ↔ library correspondence and the module dependency DAG are documented
in `docs/Kasami_Formalisation_Map.tex`; the structural-shortcut and redundancy
exploration is written up in `docs/Equation1_Shortcuts_and_Redundancies.md`, with
accompanying diagrams in `docs/Equation1_Structure_Diagrams.tex`.
-/
