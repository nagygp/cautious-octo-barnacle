# Kasami APN/AB Library — Refactored

Formalized proofs of cryptographic properties of Kasami power functions over finite fields of characteristic 2.

## Directory Structure

```
RequestProject/
├── Core/                    # General theory (Kasami-independent)
│   ├── CharTwo.lean         # Unified char-2 API (@[simp] lemmas)
│   ├── APN.lean             # APN definition, derivative image theory
│   ├── APNClass.lean        # Unified APN: two equivalent forms + bridge
│   ├── Character.lean       # Abstract character axioms
│   ├── Vanishing.lean       # Vanishing lemma for flat spectrum
│   ├── FourierInversion.lean # Fourier inversion (KR2)
│   └── ExpArith.lean        # Exponent arithmetic identities
│
├── Walsh/                   # Walsh transform theory
│   ├── Transform.lean       # Trace, sign character χ, Walsh definition
│   ├── Moments.lean         # Parseval, fourth moment, autocorrelation
│   ├── AB.lean              # AB definition, moment method proof
│   └── Divisibility.lean    # Quadratic Gauss sum divisibility
│
├── DempwolffMueller/        # Theorem 3.2 — permutation polynomials
│   ├── AutBase.lean         # Base automorphism theory
│   ├── FrobAlg.lean         # Frobenius algebra
│   ├── TraceNorm.lean       # Trace and norm maps
│   ├── ExpArith.lean        # DM-specific exponent arithmetic
│   ├── Lemma31.lean         # Lemma 3.1
│   ├── BareLemma31.lean     # Bare skeleton of Lemma 3.1
│   ├── AdjointBij.lean      # Adjoint bijectivity
│   ├── TruncTrace.lean      # Truncated trace: definition, kernel triviality
│   ├── DicksonPoly.lean     # Dickson polynomial: functional equation, injectivity
│   └── Thm32.lean           # Main bijectivity theorem (L·x^k is a permutation)
│
├── Kasami/                  # Kasami-specific theory
│   ├── Defs.lean            # Unified Kasami exponent + core definitions
│   ├── CharTwoBasics.lean   # Char-2 lemmas for collision analysis
│   ├── CrossForm.lean       # Cross form analysis, collision equation
│   ├── CrossPair.lean       # Cross pair proof
│   ├── MCM.lean             # Kasami MCM (multiplicative collision map)
│   ├── APN.lean             # Kasami APN theorem
│   ├── EvenK.lean           # Even-k extension via Frobenius twist
│   ├── AutocorrQuad.lean    # Autocorrelation quadratic substitution
│   ├── WalshDiv.lean        # Walsh divisibility for Kasami
│   ├── AB.lean              # Kasami AB theorem
│   └── TripleCount.lean     # Triple count bridge module
│
├── MTupleCount.lean         # General m-tuple count theorem
│
└── Tests/                   # Formal verification tests
    ├── StressTests.lean     # Comprehensive stress tests
    ├── LiteratureTests.lean # Literature consistency checks
    └── Verification.lean    # Axiom audit and signature checks
```

## Main Results

| Theorem | File | Statement |
|---------|------|-----------|
| **Kasami is APN** | `Kasami/APN.lean` | `kasami_is_apn` |
| **Kasami is APN (general)** | `Kasami/EvenK.lean` | `kasami_is_apn_general` |
| **Kasami is AB** | `Kasami/AB.lean` | `kasami_is_ab` |
| **m-Tuple Count** | `MTupleCount.lean` | `m_tuple_count` |
| **Triple Count** | `Kasami/TripleCount.lean` | `kasami_triple_count` |

## Verification

```bash
lake build                    # Full build (zero errors)
grep -rn "sorry" RequestProject/  # No sorry in any source file
```

All theorems depend only on standard Lean axioms:
`propext`, `Classical.choice`, `Quot.sound`.
