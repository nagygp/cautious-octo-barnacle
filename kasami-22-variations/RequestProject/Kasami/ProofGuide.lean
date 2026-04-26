/-
# Proof Writing Guide Application to Kasami P₃

This file documents how the Proof Writing Guide's approaches were applied
to explore variability and compose available components for the P₃ proof.

## Proof Design Space (from the Guide)

The P₃ proof was explored along the following axes:

### Decomposition: Many small lemmas
The monolithic `kasami_P3` was decomposed into:
- **Layer 1 (Algebra)**: `kasami_is_ab` — the Kasami function is Almost Bent
- **Layer 2 (Character sums)**: `ab_implies_vanishing` — AB ⟹ vanishing condition
- **Layer 3 (Counting)**: `tripleCount_from_vanishing` — vanishing ⟹ count formula

### Forward reasoning: Build up from foundations
Infrastructure was built bottom-up:
1. `Basic.lean`: F₂ⁿ, characteristic 2 arithmetic
2. `Trace.lean`: absolute trace Tr, surjectivity, kernel cardinality
3. `AdditiveCharacter.lean`: χ(x) = (-1)^Tr(x), orthogonality
4. `WalshHadamard.lean`: WHT, Parseval, inversion
5. `AlmostBent.lean`: AB definition, fourth moment
6. `FourthMoment.lean`: autocorrelation, Wiener-Khinchin identity
7. `DifferenceSet.lean`: Δ and character sums over Δ
8. `TripleCount.lean`: character-sum representation, P₃
9. `VanishingProof.lean`: split approach, g(b)=g(b+1), cardinality

### Calculation chains
Used extensively in:
- `tripleCount_charSum_eq`: Fubini + orthogonality chain
- `wht_parseval`: interchange of summation + orthogonality
- `ab_implies_vanishing_assembled`: split + zero term + vanishing

### Automation levels explored
- **High automation**: `simp +decide`, `aesop`, `grind` for routine steps
- **Medium**: `ring`, `omega`, `norm_num`, `push_cast` for arithmetic
- **Low**: manual `rw` chains for character sum manipulations

### Variability explored
Different proof strategies were attempted:
1. **Direct approach**: Trying to prove P₃ without going through AB
2. **Split approach**: Decomposing the spectral sum at a=0
3. **Fourth moment approach**: Using Wiener-Khinchin identity
4. **Autocorrelation approach**: Relating delta char sums to WHT

## Status of the P₃ proof

### Fully proved (sorry-free)
- Basic field infrastructure (`Basic.lean`)
- Trace theory (`Trace.lean`)
- Additive character orthogonality (`AdditiveCharacter.lean`)
- Walsh-Hadamard transform and Parseval (`WalshHadamard.lean`)
- Kasami exponent coprimality and permutation (`KasamiExponent.lean`)
- AB nonzero count and fourth moment (`AlmostBent.lean`, partial)
- Character-sum representation of triple count (`TripleCount.lean`, partial)
- P₃ from vanishing condition (`TripleCount.lean`)
- Dual P₃ ↔ P₃ equivalence (iteration 05)
- Gold case P₃ for k=1 (iteration 04)
- Autocorrelation infrastructure (`FourthMoment.lean`)
  - derivCount, derivCount_sum, derivCount_even
  - autocorr, autocorr_zero
  - wht_sq_as_autocorr (W² = Fourier of R)
  - fourth_moment_eq_autocorr_sq (Wiener-Khinchin)
  - ab_autocorr_sq_sum, ab_autocorr_sq_nonzero_sum
  - autocorr_abs_le, even_sum_sq_bound
- Derivative Parseval identity (`APNFromAB.lean`)
- Delta generator pairing, g(b)=g(b+1) (`VanishingProof.lean`)
- Delta set cardinality |Δ| = 2^{n-1} (`VanishingProof.lean`)
- Triple sum splitting (`VanishingProof.lean`)
- Assembly proof (modulo APN + vanishing hypotheses)

### Remaining sorry's (3 total)
1. `kasami_is_ab`: Deep algebraic result (Kasami 1971 / CCD 2000)
2. `ab_implies_vanishing`: Character sum vanishing for AB functions
3. `ab_implies_apn`: AB implies APN (fourth moment argument)

These correspond to deep results in Boolean function theory that are well-documented
in textbooks (Carlet 2021, Lidl-Niederreiter 1997) but require substantial
mathematical infrastructure not currently available in Mathlib:
- Linearized polynomial kernel dimension theory
- Quadratic form rank analysis over GF(2)
- Cross-correlation of m-sequences
-/
