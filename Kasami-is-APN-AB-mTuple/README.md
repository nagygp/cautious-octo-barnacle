This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Kasami APN/AB Formalization

Lean 4 formalization of structural results about the Kasami power function
`f(x) = x^d` on `GF(2ⁿ)`, where `d = 2^{2k} − 2^k + 1`.

All proofs are complete (**zero `sorry`**), using only standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

---

## Main Result: m-Tuple Count Theorem

The central theorem of this library is the **m-tuple count formula** for APN functions with flat derivative spectrum:

> **Theorem** (`MTupleCount.m_tuple_count`).
> Let `f : GF(2ⁿ) → GF(2ⁿ)` be APN (`n ≥ 3`), let `a ≠ 0`, and suppose the
> derivative image `Δf(a)` has flat spectrum. For any `m ≥ 2` and any coefficient
> tuple `c : Fin m → GF(2ⁿ)` with `cᵢ ≠ 0` for all `i`, the associated m-tuple
> count satisfies
>
> **`κₘ(Δf(a), c) = 2^{(m−1)n − m}`**

In Lean:

```lean
theorem m_tuple_count (n : ℕ) (hn : 3 ≤ n) (hcard : card 𝔽 = 2 ^ n)
    (m : ℕ) (hm : 2 ≤ m) (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0)
    (χ : Chi 𝔽) (hf : APN f) (c : Fin m → 𝔽)
    (hflat : FlatSpectrum χ (Δ f a)) (hc : ∀ i, c i ≠ 0) :
    κ m (Δ f a) c = 2 ^ ((m - 1) * n - m)
```

As a special case (`m = 3`), this gives the **triple count**: `κ₃ = 2^{2n − 3}`.

---

## Supporting Results

The m-tuple count theorem is established by composing three independent proof chains:

### 1. Kasami is APN
Each differential equation `f(x+a) + f(x) = b` has at most 2 solutions, proved via the Dempwolff–Müller bijectivity method.

> **Highlight: Frobenius Twist Extension** (`KasamiEvenK.kasami_is_apn_general`)
>
> The Dempwolff–Müller proof of Kasami APN requires `k` to be **odd**.
> `KasamiEvenK.lean` removes this restriction entirely via a Frobenius twist
> argument: the Kasami exponents for complementary parameters satisfy
>
> **`d_k ≡ d_{n−k} · 2^{2k}  (mod 2ⁿ − 1)`**
>
> so on `GF(2ⁿ)` the power maps `x^{d_k}` and `Frob_{2k}(x^{d_{n−k}})` coincide.
> Since the Frobenius automorphism is an additive bijection, APN is preserved
> under composition (`apn_comp_additive_bijective`), reducing the even-`k` case
> to the already-proved odd-`k` case with parameter `n − k`.
>
> The edge case `k = n − 1` (where `n − k = 1`) is handled by a self-contained
> proof of the **Gold APN theorem**: `x^{2^k+1}` is APN on `GF(2ⁿ)` when
> `gcd(k, n) = 1`, proved by showing the differential kernel is contained in
> `GF(2)` via Frobenius fixed-point analysis.
>
> The final result, `kasami_is_apn_general`, is the fully general statement:
> *x^d is APN on GF(2ⁿ) for all k with 1 < k < n, n odd, gcd(k,n) = 1* —
> with **no parity restriction** on k.

### 2. Kasami is AB (Almost Bent)
The Walsh spectrum of the Kasami function takes values in `{0, ±2^{(n+1)/2}}`, proved via Nyberg's moment method.

### 3. Fourier inversion + exponent arithmetic
Under the `Vanish` condition (derived from flat spectrum + nonzero coefficients),
Fourier inversion yields `|𝔽| · κ = |Δ|ᵐ`, and the APN identity `|Δ| = 2^{n−1}`
reduces this to `κ = 2^{(m−1)n − m}`.

---

## Module Dependency DAG

```
                    AutBase
                      │
                   FrobAlg
                    / | \
            TraceNorm  DM_ExpArith
               |      /
         BareLemma31Skeleton
               |
           Lemma31
               |
          AdjointBij
               |
             Thm32                Defs
               |                 / | \
          KasamiAPN    CharTwoBasics  WalshAB
               |          |    \       |
          KasamiEvenK    CrossFormAnalysis  WalshDivisibility
               |          |                  |
          KasamiMCM ← CrossPairProof   AutocorrQuadratic
               |                          |
          KasamiWalshDiv ─────────────────┘
               |
          KasamiAB

  CharTwo → APN → Character → Vanishing → FourierInversion → MTupleCount
                                                                 |
                      ExpArith ──────────────────────────────────┘
                                                                 |
          KasamiTripleCount ← KasamiAPN, KasamiEvenK, KasamiAB, MTupleCount
```

## File Descriptions

### Core definitions
| File | Lines | Description |
|------|-------|-------------|
| `Defs.lean` | 30 | Kasami exponent `d`, linearized poly `L`, cross form, norm `N`, `sVal` |
| `CharTwo.lean` | 36 | Char-2 arithmetic: `add_self_zero`, `neg_eq_self`, `sub_eq_add` |
| `Character.lean` | 45 | Additive character `Chi`, character sum `S`, orthogonality |

### Kasami APN proof chain (Dempwolff–Müller)
| File | Lines | Description |
|------|-------|-------------|
| `AutBase.lean` | 288 | Semilinear operators, additive polynomials, Singer action |
| `FrobAlg.lean` | 169 | Frobenius endomorphism: periodicity, additivity, trace |
| `TraceNorm.lean` | 140 | Frobenius sum (trace), norm, nondegeneracy |
| `DM_ExpArith.lean` | 90 | Exponent arithmetic for Dempwolff–Müller theory |
| `BareLemma31Skeleton.lean` | 219 | Lemma 3.1 for bare additive functions |
| `Lemma31.lean` | 132 | Abstract Lemma 3.1: injectivity ↔ bijectivity |
| `AdjointBij.lean` | 90 | Adjoint bijectivity for Theorem 3.2 |
| `Thm32.lean` | 475 | Theorem 3.2: `L_k(·) · (·)^{e'}` is bijective |
| `KasamiAPN.lean` | 370 | **Main**: Kasami is APN (odd k, 1 < k < n) |
| `KasamiEvenK.lean` | 238 | Extension to all k via Frobenius twist |
| `CharTwoBasics.lean` | 123 | Char-2 basics, `L_k` kernel, cross form triviality |
| `CrossFormAnalysis.lean` | 144 | Cross form analysis, collision equation |
| `KasamiMCM.lean` | 235 | MCM injectivity approach |
| `CrossPairProof.lean` | 152 | Cross-pair analysis → `kasami_apn` |

### Kasami AB proof chain (Nyberg moment method)
| File | Lines | Description |
|------|-------|-------------|
| `WalshAB.lean` | 596 | Walsh transform, Parseval, 4th moment, `ab_from_moments` |
| `WalshDivisibility.lean` | 95 | Quadratic Gauss sum divisibility |
| `AutocorrQuadratic.lean` | 122 | Gold function third-derivative vanishing |
| `KasamiWalshDiv.lean` | 100 | `2^{(n+1)/2} ∣ W` for Kasami via quadratic substitution |
| `KasamiAB.lean` | 85 | **Main**: `kasami_is_ab` |

### m-Tuple count and bridge
| File | Lines | Description |
|------|-------|-------------|
| `APN.lean` | 91 | APN definition, derivative image `Δ`, `\|Δ\| = 2^{n-1}` |
| `Vanishing.lean` | 70 | `FlatSpectrum` + nonzero coefficients ⟹ `Vanish` |
| `FourierInversion.lean` | 75 | Fourier inversion: `\|𝔽\| · κ = \|T\|ᵐ` under vanishing |
| `ExpArith.lean` | 43 | Pure arithmetic: `2ⁿ · κ = (2^{n-1})ᵐ ⟹ κ = ...` |
| `MTupleCount.lean` | 66 | ⭐ **Main result**: `m_tuple_count`, `triple_count` |
| `KasamiTripleCount.lean` | 65 | **Bridge**: `kasami_is_mtuple_apn`, `kasami_triple_count` |
