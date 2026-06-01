This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Kasami APN Formalization

A fully verified Lean 4 formalization of the **Kasami APN theorem** and its
supporting infrastructure, following Dempwolff & Müller's "Permutation
polynomials and translation planes of even order" (Adv. Geom. 2013).

## Main Results

The library proves three headline theorems, all sorry-free and depending only
on standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | File | Statement |
|---------|------|-----------|
| **Kasami APN (general)** | `RequestProject/KasamiEvenK.lean` | `kasami_is_apn_general`: x^d is APN on GF(2ⁿ) for all k with 1<k<n, n odd, gcd(k,n)=1 |
| **Kasami APN (odd k)** | `RequestProject/KasamiAPN.lean` | `kasami_is_apn`: x^d is APN when k is additionally odd |
| **Theorem 3.2** | `RequestProject/Thm32.lean` | `theorem_3_2`: L(X)·X^k is a permutation polynomial on GF(2ⁿ) |

where d = 2^{2k} − 2^k + 1 is the Kasami exponent.

## Library Structure

```
RequestProject/
├── AutBase.lean           # Semilinear operators, additive polynomials, support
├── FrobAlg.lean           # Frobenius algebra: cycling, periodicity, bijection
├── TraceNorm.lean         # Trace/norm theory: frobSum, adjoint identities
├── ExpArith.lean          # Exponent arithmetic: power maps, Mersenne GCD
├── Lemma31.lean           # Lemma 3.1 (LinearMap version)
├── BareLemma31Skeleton.lean # Lemma 3.1 (bare function version)
├── AdjointBij.lean        # Adjoint bijectivity transfer engine
├── Thm32.lean             # Theorem 3.2: permutation polynomial bijection
├── KasamiAPN.lean         # Kasami APN for odd k
└── KasamiEvenK.lean       # Extension to even k via Frobenius twist + Gold APN
```

### Dependency DAG

```
AutBase ← FrobAlg ← TraceNorm ←┐
              ↑                  │
          ExpArith               │
              ↑                  │
         Lemma31   BareLemma31 ──┤
              ↑         ↑        │
          AdjointBij ────────────┘
              ↑
           Thm32
              ↑
         KasamiAPN
              ↑
        KasamiEvenK
```

## Proof Architecture

The proof of Kasami APN follows a multi-layer DAG:

1. **Artin–Schreier identity**: L_k(x²+x) = x^{2^k}+x
2. **Key polynomial identity**: relates the Kasami differential to the truncated trace
3. **Gold coprimality**: gcd(2^k+1, 2^n−1) = 1
4. **Dickson polynomial injectivity**: via algebraic closure lifting
5. **Φ-map injectivity**: composition of truncated trace bijection with Gold power map
6. **Collision analysis**: Kasami differential collision forces x²+x = y²+y
7. **APN conclusion**: x+y ∈ {0,1} in char 2

The even-k extension uses a **Frobenius twist**: d_k ≡ d_{n-k}·2^{2k} (mod 2^n−1),
so APN of the odd parameter n−k transfers to the even parameter k.

## Earlier Work

The root-level `.lean` files (`MCMProof.lean`, `KasamiDAGLayers.lean`, etc.)
contain earlier partial approaches. The `RequestProject/` library supersedes
them with a complete, sorry-free proof.
