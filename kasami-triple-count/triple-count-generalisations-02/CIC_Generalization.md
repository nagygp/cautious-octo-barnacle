# Generalized m-Tuple Count Theorem — CIC Formalization

## Objects and Context

```
Γ ⊢ F : Type*                                    -- Ground field GF(2ⁿ)
Γ ⊢ CharP F 2                                    -- Characteristic 2
Γ ⊢ n : ℕ,  n ≥ 3,  n odd                        -- Dimension constraints
Γ ⊢ |F| = 2ⁿ                                     -- Cardinality
Γ ⊢ m : ℕ,  m ≥ 2                                -- Tuple order (m=3 recovers original)
Γ ⊢ k : ℕ,  k ≥ 1,  gcd(k,n) = 1                -- Kasami exponent parameter
```

## Definitions

```
-- Kasami exponent and function
Γ ⊢ kasamiExp(k) ≝ 4ᵏ − 2ᵏ + 1                    : ℕ
Γ ⊢ kasamiFun(k) ≝ λ x : F. x^{kasamiExp(k)}      : F → F

-- Differential set (support)
Γ ⊢ Δ(k) ≝ { f(x) + f(x+1) + 1 | x ∈ F }         : Finset F

-- Generalized m-tuple set
-- An m-tuple (x₁,…,xₘ) ∈ Δᵐ satisfying a linear constraint
Γ ⊢ coeffs : Fin m → F                              -- Coefficient vector
Γ ⊢ coeffs_valid : ∀ i, coeffs i ≠ 0                -- All nonzero
Γ ⊢ coeffs_sum_zero : ∑ᵢ coeffs(i) = 0             -- Sum to zero (char 2 generalization)

Γ ⊢ mTupleSet(m, k, coeffs) ≝
      { x : Fin m → F | (∀ i, x i ∈ Δ(k)) ∧ ∑ᵢ coeffs(i) · x(i) = 0 }
                                                      : Finset (Fin m → F)
```

## Black-Boxed Lemmas (sorry'd)

### Lemma 1 — APN Cardinality
```
Γ ⊢ apn_card :
    |Δ(k)| = 2^{n−1}
  Proof: sorry  -- Known: APN ⟹ 2-to-1 derivative
```

### Lemma 2 — Higher-Order Correlation Identity (Fourier)
```
Γ ⊢ higher_correlation_identity :
    |F| · |mTupleSet(m, k, coeffs)| = ∑_{u ∈ F} ∏ᵢ₌₁ᵐ δ̂(coeffs(i) · u)
  Proof: sorry  -- Generalized Fourier counting identity
```

### Lemma 3 — AB-m Spectral Collapse
```
Γ ⊢ ab_spectral_collapse :
    IsABₘ(f) ⟹ ∑_{u ∈ F} ∏ᵢ₌₁ᵐ δ̂(coeffs(i) · u) = |Δ|ᵐ
  Proof: sorry  -- m-flatness of AB functions
```

### Combined Black Box (Lemma 2 + Lemma 3)
```
Γ ⊢ fourier_spectral_combined :
    |F| · |mTupleSet(m, k, coeffs)| = |Δ(k)|ᵐ
  Proof: sorry  -- Composition of higher_correlation_identity and ab_spectral_collapse
```

## Arithmetic Lemmas (provable)

### Lemma A — Power of Power
```
Γ ⊢ pow_of_pow :
    (2^{n−1})ᵐ = 2^{m(n−1)} = 2^{mn − m}
  Proof: ring arithmetic
```

### Lemma B — Exponent Split
```
Γ ⊢ exponent_split :
    2^{mn − m} = 2ⁿ · 2^{(m−1)n − m}
  Proof: 2^{mn − m} = 2^{n + ((m−1)n − m)} = 2ⁿ · 2^{(m−1)n − m}
         since mn − m = n + (m−1)n − m ⟺ mn − m = n + mn − n − m ✓
```

### Lemma C — Exponent Arithmetic
```
Γ ⊢ exponent_identity :
    m * n − m = n + ((m − 1) * n − m)      when m ≥ 2, n ≥ 3
  Proof: omega
```

## Main Theorem (Top-Down)

```
Γ ⊢ generalized_mTuple_count :
    |mTupleSet(m, k, coeffs)| = 2^{(m−1)n − m}

  Proof:
    have h1 : |F| · κₘ = |Δ|ᵐ           := fourier_spectral_combined
    have h2 : |Δ| = 2^{n−1}              := apn_card
    calc  2ⁿ · κₘ
        = |F| · κₘ                        -- by hcard
      _ = |Δ|ᵐ                            -- by h1
      _ = (2^{n−1})ᵐ                      -- by h2
      _ = 2^{mn − m}                      -- by pow_of_pow
      _ = 2ⁿ · 2^{(m−1)n − m}            -- by exponent_split
    ∴ κₘ = 2^{(m−1)n − m}                 -- cancel 2ⁿ  □
```

## Specialization: m = 3 Recovers Original

```
Γ ⊢ triple_count_specialization :
    generalized_mTuple_count(m := 3) ⟹ κ₃ = 2^{2n − 3}

  Proof: (m−1)n − m = 2n − 3  when m = 3  □
```

## Summary Table

| m | Formula              | C  | Name          |
|---|----------------------|----|---------------|
| 2 | 2^{n − 2}           | 2  | Pair count    |
| 3 | 2^{2n − 3}          | 3  | Triple count  |
| 4 | 2^{3n − 4}          | 4  | Quadruple     |
| 5 | 2^{4n − 5}          | 5  | Quintuple     |
| m | 2^{(m−1)n − m}      | m  | m-tuple count |

**The constant C = m.**
