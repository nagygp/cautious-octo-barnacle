This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Kasami APN & Dempwolff–Müller Theorem 3.2

**Fully machine-verified Lean 4 formalization** of:

1. **Theorem 3.2** (Dempwolff–Müller): Permutation polynomials L(X)·X^k on GF(2ⁿ)
2. **Kasami APN Theorem**: The Kasami power function x^d is Almost Perfect Nonlinear
3. **Gold APN Theorem**: The Gold power function x^{2^k+1} is APN
4. **Kasami APN General**: Extension to **all** valid k (including even k)

All proofs depend only on standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

## What is proved

### Theorem 3.2 (Dempwolff–Müller)

Let F = GF(2ⁿ) with n odd. Let m be odd with 1 < m < n and gcd(m,n) = 1.
Let L(X) = ∑_{i=0}^{m-1} X^{2^i}. Set k = 2^{n-1} - 2^{m-1} - 1. Then:

- **`theorem_3_2`** / **`LxXk_bijective`**: L(X)·X^k is a permutation polynomial on F
- **`LxXk'_bijective`**: L(X)·X^{k'} is also a permutation polynomial when k·k' ≡ 2^{m-1} mod (2ⁿ-1)

### Kasami APN Theorem (Odd k)

Let F = GF(2ⁿ) with n odd. Let k be odd with 1 < k < n and gcd(k,n) = 1.
Then f(x) = x^d where d = 2^{2k} - 2^k + 1 is APN on F.

- **`kasami_is_apn`**: The main APN result for odd k

### Gold APN Theorem

Let F = GF(2ⁿ). Let gcd(k,n) = 1. Then x^{2^k+1} is APN on F.

- **`gold_is_apn`**: Gold APN via kernel triviality and the linear differential

### Kasami APN General (All k, including even)

Let F = GF(2ⁿ) with n odd. Let 1 < k < n with gcd(k,n) = 1.
Then f(x) = x^d where d = 2^{2k} - 2^k + 1 is APN on F.
**No parity restriction on k.**

- **`kasami_is_apn_general`**: The unified result

## How the proofs connect

### Odd k → Theorem 3.2

The Kasami APN proof for odd k uses Theorem 3.2 as its core engine through three layers:

1. **Key identity**: `(x+1)^d + x^d + 1 = L_k(x²+x)^{q+1} / (x²+x)^q`
2. **Decomposition**: Φ(u) = L_k(u)^{q+1}/u^q = (L_k(u)·u^{e'})^{q+1}
3. **Composition**: L_k(·)·(·)^{e'} bijective (Thm 3.2) ∘ y^{q+1} bijective (Gold)

### Even k → Frobenius Twist

For even k, the Kasami exponents satisfy the congruence:
```
d_k ≡ d_{n-k} · 2^{2k}  (mod 2ⁿ - 1)
```
Since n is odd and k is even, n-k is odd with gcd(n-k,n) = gcd(k,n) = 1.
The power function x^{d_k} = Frob_{2k}(x^{d_{n-k}}), and composing with
the additive bijection Frobenius preserves APN. Two sub-cases:

- **n-k ≥ 2**: Apply `kasami_is_apn` with parameter n-k (odd)
- **n-k = 1**: The Kasami exponent reduces to Gold (d₁ = 3), use `gold_is_apn`

## DAG structure

```
                    kasami_is_apn_general
                     /        |        \
              (k odd)    (k even,     (k even,
                |         n-k ≥ 2)    n-k = 1)
                |            |            |
          kasami_is_apn  kasami_is_apn  kasami_is_apn
              |           _even_k       _even_k_edge
              |              |              |
          [Thm 3.2]   kasami_apn_of    kasami_one_is_apn
                       _complement          |
                            |           gold_is_apn
                     apn_frob_twist         |
                            |        frob_fixed_implies_GF2
                apn_comp_additive         + gold_differential
                    _bijective            + gold_kernel_eq
                            |
                  frob_bijective ← iterateFrobenius (Mathlib)
                  frob_additive  ← add_pow_char_pow (Mathlib)
                  kasami_exp_congr_mod ← arithmetic identity
                  kasami_pow_frob_identity ← pow_eq_pow_of_mod_eq
```

## Project structure (11 files, 2377 lines, 0 sorries)

| File | Lines | Role |
|------|-------|------|
| `AutBase.lean` | 288 | Semilinear operators, additive polynomials, Lemma 4.2 |
| `FrobAlg.lean` | 169 | Frobenius cycling/periodicity, bijection transfer |
| `TraceNorm.lean` | 143 | Frobenius sums, trace properties, adjoint |
| `ExpArith.lean` | 91 | Power map bijectivity, Mersenne GCD |
| `Lemma31.lean` | 133 | Lemma 3.1: L·M injective ↔ L*·M⁻¹ injective |
| `BareLemma31Skeleton.lean` | 218 | Lemma 3.1 for bare additive functions |
| `AdjointBij.lean` | 89 | Adjoint bijectivity transfer engine |
| `Thm32.lean` | 488 | **Theorem 3.2**: all 12 layers of the permutation polynomial proof |
| `KasamiAPN.lean` | 404 | **Kasami APN** (odd k): key identity, Gold coprimality, main theorem |
| `KasamiEvenK.lean` | 330 | **Kasami APN General**: Frobenius twist, Gold APN, even k extension |
| `Main.lean` | 24 | Common imports |

## Full dependency DAG

```
Mathlib
  ├── AutBase ──── FrobAlg ──── TraceNorm ───┐
  │                   │                       │
  │                   └── ExpArith ──────────┤
  │                                           │
  │   BareLemma31Skeleton ── Lemma31 ────────┤
  │                           │               │
  │                           └── AdjointBij ─┤
  │                                           │
  │                                      Thm32 ← (Theorem 3.2)
  │                                           │
  │                                      KasamiAPN ← (Kasami APN, odd k)
  │                                           │
  │                                    KasamiEvenK ← (Kasami APN General)
  │                                       ↑
  │                    Gold APN + Frobenius twist + exponent congruence
```

## Key lemmas in `KasamiEvenK.lean`

| Lemma | Role |
|-------|------|
| `apn_comp_additive_bijective` | APN invariant under additive automorphisms |
| `frob_bijective` | Frobenius x ↦ x^{2^j} is bijective (via `iterateFrobenius`) |
| `frob_pow_card` | x^{2^n} = x on GF(2ⁿ) |
| `apn_frob_twist` | APN preserved under Frobenius twist |
| `kasami_exp_congr_mod` | d_k ≡ d_{n-k} · 2^{2k} (mod 2ⁿ-1) |
| `kasami_pow_frob_identity` | x^{d_k} = Frob_{2k}(x^{d_{n-k}}) on GF(2ⁿ) |
| `kasami_apn_of_complement` | APN for n-k implies APN for k |
| `frob_fixed_implies_GF2` | x^{2^k} = x with gcd(k,n)=1 ⟹ x ∈ {0,1} |
| `gold_differential` | (x+a)^{2^k+1} + x^{2^k+1} = affine in x |
| `gold_kernel_eq` | Gold kernel ↔ Frobenius fixed point |
| `gold_is_apn` | **Gold APN theorem** |
| `kasami_is_apn_even_k` | Kasami APN for even k, n-k ≥ 2 |
| `kasami_is_apn_even_k_edge` | Kasami APN for even k, n-k = 1 (Gold) |
| `kasami_is_apn_general` | **Unified Kasami APN** — all valid k |

## References

- U. Dempwolff, P. Müller, "Permutation polynomials and translation planes of even order",
  Adv. Geom. 2013.
- T. Kasami, "The weight enumerators for several classes of subcodes of the 2nd order
  binary Reed-Muller codes", Inform. Control, 1971.
- R. Gold, "Maximal recursive sequences with 3-valued recursive cross-correlation
  functions", IEEE Trans. Inform. Theory, 1968.

## Building

```
lake build
```

Requires Lean 4.28.0 with Mathlib v4.28.0.
