# Kasami Functions are Almost Bent (AB)

## Overview

This project formalizes the theorem that **Kasami functions are Almost Bent (AB)** over
finite fields of characteristic 2, following the proof approach from:

> T. Kasami, *"The Weight Enumerators for Several Classes of Subcodes of the 2nd Order
> Binary Reed-Muller Codes"*, Information and Control 18 (1971), 369-394.

## File Structure

- **`Defs.lean`**: Core definitions
  - `AbsoluteTrace`: The trace map Tr: F → GF(2) for finite extensions
  - `chi`: Additive character χ: GF(2) → ℤ mapping 0 ↦ 1, 1 ↦ -1
  - `WalshTransform`: W_f(a,b) = Σ_x (-1)^{Tr(b·f(x) + a·x)}
  - `IsAlmostBent`: AB property (three-valued Walsh spectrum)
  - `IsAPN`: Almost Perfect Nonlinear property
  - `kasamiExponent`: d = 2^(2k) - 2^k + 1
  - `kasamiFunction`: x ↦ x^d

- **`Helpers.lean`**: Helper lemmas for characteristic 2 fields and linearized polynomials
  - Characteristic 2 properties (negation, addition, Frobenius)
  - Linearized polynomial theory: L(y) = y^(2^(2k)) + y^(2^k) + y
  - Root counting for linearized polynomials

- **`KasamiAB.lean`**: Main theorem and proof structure
  - Number-theoretic properties of the Kasami exponent
  - APN property (reduces to `kasami_derivative_at_most_two`)
  - Walsh spectrum analysis
  - **Main theorem**: `kasami_is_AB`

## Proof Architecture

The main theorem `kasami_is_AB` is proved via the following decomposition:

```
kasami_is_AB
├── kasami_walsh_squared  [sorry — requires weight enumerator analysis]
│   (Kasami 1971, Theorem 3 + Corollary 2, page 18)
└── walsh_squared_to_three_valued  [✓ proved]
    (If W² ∈ {0, 2^(n+1)} then W ∈ {0, ±2^((n+1)/2)})
```

The APN property `kasami_is_APN` is proved using:
```
kasami_is_APN
└── kasami_derivative_at_most_two  [sorry — requires deep finite field algebra]
    (Kasami 1971, Lemma 1 / Theorem 1)
```

## Fully Proved Results

| Lemma | Description |
|-------|-------------|
| `kasami_exponent_pos` | d ≥ 1 for k ≥ 1 |
| `kasami_exponent_one` | d = 3 when k = 1 |
| `kasami_exponent_two` | d = 13 when k = 2 |
| `kasami_exponent_factor` | (2^k + 1) · d = 2^(3k) + 1 |
| `gcd_two_pow_sub_one` | gcd(2^a - 1, 2^b - 1) = 2^(gcd(a,b)) - 1 |
| `kasami_exponent_coprime` | gcd(d, 2^n - 1) = 1 when gcd(k,n) = 1 and n odd |
| `power_map_bijective` | x ↦ x^d is a bijection when gcd(d, |F|-1) = 1 |
| `walsh_squared_to_three_valued` | W² ∈ {0, 2^(n+1)} ⟹ W ∈ {0, ±2^((n+1)/2)} |
| `char2_neg_eq` | -x = x in char 2 |
| `char2_add_self` | x + x = 0 in char 2 |
| `char2_sub_eq_add` | x - y = x + y in char 2 |
| `frobenius_add_char2` | (x+y)^(2^k) = x^(2^k) + y^(2^k) |
| `gcd_two_mul_of_odd` | gcd(2k, n) = gcd(k, n) when n is odd |
| `linearized_kernel_additive` | ker(L) is an additive subgroup |
| `roots_linearized_simple` | |{y : y^(2^m) + y = 0}| = 2^gcd(m,n) |
| `linearized_kernel_subset_cube` | L(y) = 0 ⟹ y^(2^(3k)) + y = 0 |

## Remaining Sorry's

Three deep results remain unproved:

1. **`kasami_derivative_at_most_two`** (APN core): The equation (x+a)^d + x^d = b
   has at most 2 solutions. This requires showing that the derivative of the Kasami
   function factors through a linearized polynomial whose kernel has GF(2)-dimension ≤ 1,
   using the specific algebraic structure of d = 2^(2k) - 2^k + 1.

2. **`linearized_kernel_bound`**: Bounding the kernel of L(y) = y^(2^(2k)) + y^(2^k) + y
   to at most 2^(2·gcd(k,n)) elements. Requires the direct sum decomposition
   ker(σ³-1) = ker(σ-1) ⊕ ker(σ²+σ+1) where σ is the k-th Frobenius.

3. **`kasami_walsh_squared`** (Walsh spectrum): The Walsh transform squared takes only
   values 0 and 2^(n+1). This is the deepest result, corresponding to Kasami's Theorem 3
   and Corollary 2 (page 18). It requires the full weight enumerator analysis showing
   that the Kasami-function-generated code has the same weight distribution as the
   Gold-function-generated code.

These sorry's correspond to the deepest technical content of Kasami's 1971 paper and
would require substantial new formalization infrastructure (linearized polynomial theory,
Reed-Muller code weight enumerators, cyclotomic coset analysis) that is not currently
available in Mathlib.
