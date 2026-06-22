This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# RequestProject — self-contained Kasami APN & AB library

This project is a **single, self-contained module tree** for the two
first-principles results about the Kasami power map `x ↦ x ^ d(k)` over
`GF(2ⁿ)`, where `d(k) = 2^{2k} − 2^k + 1`:

* **Kasami is APN** (almost perfect nonlinear), and
* **Kasami is AB** (almost bent).

Everything needed for these two proofs — every connecting definition, lemma and
theorem — lives under `RequestProject/`. The tree imports only `Mathlib` and
other modules inside `RequestProject.*`; it has no other intra-project
dependencies, so it can be read, built, or lifted out on its own.

## Entry point

`RequestProject/Headlines.lean` is the one place to look. It
exposes the three headline names:

| Name                                      | Meaning                                             |
| ----------------------------------------- | --------------------------------------------------- |
| `Kasami.Headlines.kasami_is_apn`          | Kasami map is APN (every nonzero derivative ≤ 2-to-1) |
| `Kasami.Headlines.kasami_is_ab`           | Kasami map is AB (Walsh squares in `{0, 2^{n+1}}`)  |
| `Kasami.Headlines.kasami_is_apn_diffUnif` | APN restated as differential uniformity exactly 2   |

Standing hypotheses throughout: `1 ≤ k < n`, `gcd(k, n) = 1`, and `n` odd.

## Layered layout (low level → high level)

```
RequestProject/
  FiniteField/        — finite-field tower: trace, norm, Frobenius, exponent
                        arithmetic, Lemma 3.1 and the Dempwolff–Müller
                        permutation Theorem 3.2 (MCM permutation input)
    AutBase, FrobAlg, TraceNorm, ExpArith,
    Lemma31, BareLemma31Skeleton, AdjointBij, Thm32

  APN/                — APN/derivative vocabulary in characteristic two
    Defs, CharTwoBasics

  Walsh/              — Walsh/Fourier machinery and the moment method for AB
    Transform, Moments, WalshAB, WalshDivisibility

  Support/            — quadratic autocorrelation helper for the divisibility step
    AutocorrQuadratic

  Core/               — the Kasami collision analysis and AB/APN assembly
    KasamiAPN, KasamiEvenK, CrossFormAnalysis,
    KasamiMCM, KasamiWalshDiv, KasamiAB

  DiffUniformity/     — characteristic-free differential-uniformity foundation
                        and its bridge to the concrete Kasami APN predicate
    DifferentialUniformity, KasamiDiffUniformity

  Headlines.lean      — single discoverable entry point (aliases above)
```

## Dependency flow

```
FiniteField ─┐
APN ─────────┤
Walsh ───────┼─► Core ─► DiffUniformity ─┐
Support ─────┘                           ├─► Headlines
                          Core ──────────┘
```

All proofs are first-principles and `sorry`-free, depending only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
