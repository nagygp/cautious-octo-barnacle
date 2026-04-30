/-
# Formalization of Kasami (1971)

**T. Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
2nd Order Binary Reed-Muller Codes", Information and Control 18, 369-394 (1971).**

## Overview

This formalization captures the key definitions and theorems from Kasami's paper,
which derives explicit weight enumerator formulas for several families of subcodes
of the 2nd-order binary Reed-Muller codes.

## Structure

- `Kasami.Defs`: Core definitions including binary Gaussian binomial coefficients,
  code parameters `u₁` and `u₂`, Hamming weight, cyclic codes, and weight enumerators.

- `Kasami.Lemma1`: The foundational algebraic lemma about linear independence in
  polynomial residue classes modulo `f(X) = ∏(X - α^{u_i})`.

- `Kasami.WeightRestriction`: Theorem 1 (generalized BCH bound) and Theorem 2
  (weight restrictions for subcodes of Reed-Muller codes).

- `Kasami.WeightDistribution`: Lemma 3 (weight enumerator determination via Pless
  power moments), Theorem 3 and Theorem 4 (families of codes with equal weight
  enumerators).

- `Kasami.QuadraticForms`: Appendix I results - Lemma A1 (weight of trace of
  quadratic forms over GF(2^j)) and Theorem A1 (counting quadratic forms in
  canonical classes).

## Key Results

### Lemma 1 (§1)
For `v(X) = ∑ cᵢXᵘⁱ` and `R = {e | v(αᵉ) = 0}`, the residue class `Xᵉ mod f(X)`
is not in the span of `{Xʲ | j ∈ R}` whenever `e ∉ R`.

### Theorem 1 (§1)
A generalization of the BCH bound: under combinatorial conditions on the root set,
the number of nonzero terms in a codeword polynomial exceeds a specified sum.
The classical BCH bound is recovered as a special case (Remark 1).

### Theorem 3 (§2)
For `j | m` with `m/j` odd, codes `𝒜_{j₁}^{(u)}`, `𝒞_{j₂}^{(u)}`, `ℰ_{j₃}^{(u)}`
all share the same weight enumerator when `gcd(m, j₁) = gcd(m, j₂) = gcd(m, j₃) = j`.

### Theorem 4 (§2)
`ℰ_{j₁}^{(u)}` and `ℰ_j^{(u)}` have the same weight enumerators when `j = gcd(m, j₁)`.

### Theorem A1 (Appendix I)
The number of quadratic forms over `GF(2^j)` in the canonical class `P_{m̄,i}^{(1)}` is
`2^{i(i+1)j/2} · ∏_{t=0}^{2i-1}(2^{(m̄-t)j/2}-1) / ∏_{t=1}^{i}(2^{2jt}-1)`.
-/
import RequestProject.Kasami.Defs
import RequestProject.Kasami.Lemma1
import RequestProject.Kasami.WeightRestriction
import RequestProject.Kasami.WeightDistribution
import RequestProject.Kasami.QuadraticForms
