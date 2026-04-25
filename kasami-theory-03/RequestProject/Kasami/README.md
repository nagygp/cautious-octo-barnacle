# Kasami Function Formalization — Module Infrastructure

## Overview

This directory contains a Lean 4 formalization of the Kasami power function
and the proof infrastructure for the P₃ triple-intersection equidistribution
theorem, following [Kasami 1971], [Canteaut-Charpin-Dobbertin 2000], and
[Carlet 2021].

**Total**: 15 modules, ~1584 lines, 7 remaining sorries (down from 20).

## Module Dependency Graph

```
Basic.lean
  ├── Trace.lean
  │     └── AdditiveCharacter.lean
  │           └── WalshHadamard.lean
  │                 └── AlmostBent.lean
  │                       └── KasamiFunction.lean
  ├── KasamiExponent.lean
  │     └── KasamiFunction.lean
  │           └── DifferenceSet.lean
  │                 └── TripleCount.lean
  │                       └── KasamiP3.lean
  ├── APN.lean
  │     └── ABtoAPN.lean
  ├── AutoCorrelation.lean
  │     └── ABtoAPN.lean
  └── CrossCorrelation.lean
        └── SpectralBridge.lean
```

## Fully Proved Modules (sorry-free)

| Module | LOC | Description | Key Results |
|--------|-----|-------------|-------------|
| **Basic.lean** | 74 | `F2n n = GaloisField 2 n` | char-2 lemmas, cardinality, power map |
| **Trace.lean** | 118 | Absolute trace `Tr : F_{2^n} → F_2` | `tr2_sq`, `tr2_surjective`, `tr2_kernel_card`, `tr2_balanced` |
| **AdditiveCharacter.lean** | 117 | `χ(x) = (-1)^{Tr(x)}` | `chi_add`, `chi_orthogonality`, `chi_sum` |
| **WalshHadamard.lean** | 145 | Walsh-Hadamard transform | `wht_parseval`, `wht_inversion`, `wht_abs_le` |
| **DifferenceSet.lean** | 55 | Kasami difference set Δ | `kasami_P1`, `deltaCharSum` |
| **CrossCorrelation.lean** | 88 | Cross-correlation infrastructure | `weightedCharSum`, `autoCorr` |

## Partially Proved Modules

| Module | LOC | Proved | Sorry | Key Results |
|--------|-----|--------|-------|-------------|
| **AlmostBent.lean** | 92 | 4 | 1 | `ab_nonzero_count` ✓, `ab_fourth_moment` ✓, `ab_implies_apn` ✗ |
| **KasamiExponent.lean** | 119 | 6 | 0 | `kasamiExp_coprime` ✓, `kasamiExp_permutation` ✓ |
| **KasamiFunction.lean** | 63 | 3 | 1 | `kasamiF`, `kasami_is_ab` ✗ |
| **TripleCount.lean** | 118 | 2 | 1 | `tripleCount_charSum_eq` ✓, `tripleCount_from_vanishing` ✓, `ab_implies_vanishing` ✗ |
| **KasamiP3.lean** | 55 | 2 | 0 | `kasami_P3_from_constructed_chi` ✓ (uses sorry'd deps) |
| **APN.lean** | 137 | 6 | 1 | `deriv_count_even` ✓, `apn_deriv_zero_or_two` ✓, `apn_image_card` ✓ |
| **AutoCorrelation.lean** | 157 | 5 | 1 | `scaledWht_sq_eq_fourier_autoCorr` ✓, `wiener_khinchin` ✓, `scaledWht_power_shift` ✓ |
| **ABtoAPN.lean** | 109 | 4 | 1 | `apn_deltaGen_two_to_one` ✓, `apn_delta_card` ✓, `apn_weighted_eq_twice_delta` ✓ |
| **SpectralBridge.lean** | 151 | 6 | 1 | `ab_delta_card` ✓, `triple_sum_split` ✓, `weighted_eq_chi_autoCorr` ✓ |

## Remaining Sorries (7 total)

### Deep algebraic results (2)
| Sorry | Module | Description |
|-------|--------|-------------|
| `kasami_is_ab` | KasamiFunction.lean | The Kasami function is AB — Kasami (1971) / CCD (2000) |
| `ab_implies_apn` | AlmostBent.lean | AB ⟹ APN via fourth moment bound |

### Bridge theorems (2)
| Sorry | Module | Description |
|-------|--------|-------------|
| `ab_implies_vanishing` | TripleCount.lean | AB ⟹ AlmostBentVanishing |
| `nonzero_triple_sum_vanishes` | SpectralBridge.lean | ∑_{a≠0} vanishes for AB |

### Supporting infrastructure (3)
| Sorry | Module | Description |
|-------|--------|-------------|
| `fourth_moment_deriv_link` | ABtoAPN.lean | WHT fourth moment = 2^n · ∑ N_a(c)² |
| `scaledWht_ab_spectrum` | AutoCorrelation.lean | Scaled WHT has AB spectrum |
| `apn_fourth_moment` | APN.lean | Fourth moment formula for APN |

## Proof Architecture for Remaining Sorries

### Path to `ab_implies_vanishing`

The proof chain is:
```
kasami_is_ab ──→ ab_implies_apn ──→ ab_delta_card ─┐
                                                     ├→ triple_sum_split → ab_vanishing_value
nonzero_triple_sum_vanishes ─────────────────────────┘
```

The key vanishing result `nonzero_triple_sum_vanishes` requires:
```
scaledWht_ab_spectrum → autoCorr_one_ab → triple_weighted_eq_autoCorr → vanishing
```

### Path to `ab_implies_apn`

```
fourth_moment_deriv_link → (∑ W^4 = 2^n ∑ N² ) → ab_fourth_moment → APN bound
```

### Proof of `kasami_is_ab`

This is the deepest result, requiring:
- Cross-correlation theory of m-sequences
- Properties of the Kasami exponent modulo cyclotomic cosets
- Weil-type bounds for character sums over finite fields

## Mathlib Contribution Candidates

The following modules contain general-purpose results suitable for Mathlib:

1. **Trace.lean**: Specialization of `Algebra.trace` to `GaloisField 2 n / ZMod 2`
2. **AdditiveCharacter.lean**: Canonical additive character via trace, orthogonality
3. **WalshHadamard.lean**: WHT definition, Parseval, inversion
4. **APN.lean**: General APN function theory over F_{2^n}
5. **AutoCorrelation.lean**: Autocorrelation and Wiener-Khinchin identity

## Building

```
lake build RequestProject.Kasami.KasamiP3      # Main theorem
lake build RequestProject.Kasami.SpectralBridge # Bridge infrastructure
```
