# Kasami P₃ Formalization — Progress Summary

## What is P₃?

For the Kasami function `F(b) = b^{4^k - 2^k + 1}` over `𝔽_{2^n}` with `gcd(k,n) = 1` and `n` odd:

**P₃**: For all nonzero `v₁ ≠ v₂` in `𝔽_{2^n}`:
```
|{(x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0}| = 2^{2n-3}
```
where `Δ = {F(b) + F(b+1) + 1 : b ∈ 𝔽_{2^n}}`.

## Project Structure

### Core Theory (from the cautious-octo-barnacle repository, iteration 06)
- `Basic.lean` — F₂ⁿ = GaloisField 2 n, characteristic 2 arithmetic ✅
- `Trace.lean` — Absolute trace, surjectivity, kernel cardinality ✅
- `AdditiveCharacter.lean` — χ(x) = (-1)^Tr(x), orthogonality ✅
- `WalshHadamard.lean` — WHT, Parseval identity, inversion formula ✅
- `KasamiExponent.lean` — d = 4^k - 2^k + 1, coprimality, permutation ✅
- `AlmostBent.lean` — AB definition, fourth moment, nonzero count ⚠️ (1 sorry)
- `KasamiFunction.lean` — F(b) = b^d, derivatives ⚠️ (1 sorry)
- `DifferenceSet.lean` — Δ, character sums over Δ ✅
- `TripleCount.lean` — Character-sum representation, P₃ from vanishing ⚠️ (1 sorry)
- `KasamiP3.lean` — Assembly of P₃ ✅ (modulo imported sorry's)

### New Infrastructure (added using Proof Writing Guide approaches)
- `FourthMoment.lean` — Derivative distributions, autocorrelation, Wiener-Khinchin ✅
- `APNFromAB.lean` — Derivative Parseval identity ✅
- `VanishingProof.lean` — Split approach, g(b)=g(b+1), |Δ|=2^{n-1}, assembly ✅
- `ProofGuide.lean` — Documentation of proof strategies explored

## What Was Proved (sorry-free)

### Foundational Infrastructure (~1800 lines)
- All of `Basic.lean`, `Trace.lean`, `AdditiveCharacter.lean`, `WalshHadamard.lean`
- All of `KasamiExponent.lean`, `DifferenceSet.lean`
- Partial `AlmostBent.lean`: AB definition, nonzero count, fourth moment

### Key New Theorems
| Theorem | File | Description |
|---------|------|-------------|
| `derivCount_even` | FourthMoment | Solutions come in char-2 pairs |
| `wht_sq_as_autocorr` | FourthMoment | W²(a) = Fourier transform of autocorrelation |
| `fourth_moment_eq_autocorr_sq` | FourthMoment | Wiener-Khinchin identity |
| `ab_autocorr_sq_sum` | FourthMoment | AB autocorrelation sum = 2·(2ⁿ)² |
| `ab_autocorr_sq_nonzero_sum` | FourthMoment | Nonzero autocorrelation sum = (2ⁿ)² |
| `autocorr_abs_le` | FourthMoment | \|R(t)\| ≤ 2ⁿ |
| `even_sum_sq_bound` | FourthMoment | Distribution bound from evenness |
| `deriv_parseval` | APNFromAB | Parseval identity for derivatives |
| `deltaGen_paired` | VanishingProof | g(b) = g(b+1) in char 2 |
| `deltaGen_fiber_ge_two` | VanishingProof | Each Δ element has ≥2 preimages |
| `kasamiDelta_card` | VanishingProof | \|Δ\| = 2^{n-1} (from 2-to-1) |
| `deltaGen_two_to_one` | VanishingProof | g is 2-to-1 (from APN) |
| `triple_sum_split` | VanishingProof | Split at a=0 |
| `chi_triple_cancel` | VanishingProof | χ factor cancellation in char 2 |
| `ab_implies_vanishing_assembled` | VanishingProof | Full assembly (modulo 2 hypotheses) |

## Remaining Sorry's (3)

| Sorry | File | Difficulty | What's Needed |
|-------|------|-----------|---------------|
| `kasami_is_ab` | KasamiFunction.lean | Very Hard | Linearized polynomial kernel theory, quadratic form analysis over GF(2) |
| `ab_implies_vanishing` | TripleCount.lean | Hard | Nonzero spectral triple sum vanishing for AB functions |
| `ab_implies_apn` | AlmostBent.lean | Medium | Fourth moment argument (circular dependency issue) |

## Proof Writing Guide Approaches Used

Following the guide from `super-octo-dollop`:

1. **Decomposition**: Broke P₃ into 3 layers (algebra → character sums → counting)
2. **Forward reasoning**: Built infrastructure bottom-up from F₂ⁿ basics
3. **Calculation chains**: Used `calc` and `conv` for character sum manipulations
4. **Multiple proof styles**: Mixed tactic mode, term mode, and structured proofs
5. **Automation gradient**: From `decide`/`omega` to manual `rw` chains
6. **Composition**: Assembled proven components into higher-level results

## References
- Kasami (1971), *Information and Control* 18(4)
- Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1)
- Carlet (2021), *Boolean Functions for Cryptography and Coding Theory*, Ch. 6
