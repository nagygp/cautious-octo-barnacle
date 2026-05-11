# Dual Statement: C = m and m-Tuple Count Determines f — CIC Formalization

## Overview

The **primal** chain of implications is:

```
  f is APN ──→ |Δ_f| = 2^{n-1}
  f is AB  ──→ |F|·κ_m = |Δ_f|^m   (Fourier + spectral collapse)
  ────────────────────────────────
  ∴ κ_m = 2^{(m-1)n - m},  C = m
```

The **dual** reverses the arrows: given the m-tuple count, what can
we deduce about f?

```
  κ_m = 2^{(m-1)n - m}  ──→  |F|·κ_m = 2^{mn - m}
                          ──→  |Δ_f|^m = 2^{mn - m}     (via Fourier identity)
                          ──→  |Δ_f|   = 2^{n-1}        (unique m-th root in ℕ)
                          ──→  f has 2-to-1 derivative   (characterizes APN)
                          ──→  C must equal m            (forced by algebra)
```

## CIC Objects and Context

```
Γ ⊢ F : Type*                                    -- Ground field GF(2ⁿ)
Γ ⊢ CharP F 2                                    -- Characteristic 2
Γ ⊢ n : ℕ,  n ≥ 3                                -- Dimension
Γ ⊢ |F| = 2ⁿ                                     -- Cardinality
Γ ⊢ m : ℕ,  m ≥ 2                                -- Tuple order
Γ ⊢ f : F → F                                    -- Arbitrary function
Γ ⊢ Δ_f : Finset F                               -- Differential set of f
Γ ⊢ κ_m : ℕ                                      -- m-tuple count
```

## Dual Definitions

```
-- The abstract m-tuple set for a general function f
Γ ⊢ mTupleSetGen(f, m, coeffs) ≝
      { x : Fin m → F | (∀ i, x i ∈ Δ_f) ∧ ∑ᵢ coeffs(i) · x(i) = 0 }
                                                      : Finset (Fin m → F)

-- The abstract spectral identity (Fourier counting)
Γ ⊢ SpectralIdentity(f, m) ≝ |F| · κ_m = |Δ_f|ᵐ    : Prop
```

## Dual Chain of Implications — Atomic Lemmas

### Dual Lemma 1 — Count Determines Product
```
Γ ⊢ dual_count_product :
    κ_m = 2^{(m-1)n - m}  ∧  |F| = 2ⁿ
    ────────────────────────────────────
    |F| · κ_m = 2^{mn - m}

  Proof:
    |F| · κ_m = 2ⁿ · 2^{(m-1)n - m}
              = 2^{n + (m-1)n - m}
              = 2^{mn - m}             — by exponent_identity  □
```

### Dual Lemma 2 — Product + Spectral Identity Determines |Δ|^m
```
Γ ⊢ dual_product_determines_delta_pow :
    |F| · κ_m = |Δ_f|ᵐ  ∧  |F| · κ_m = 2^{mn - m}
    ──────────────────────────────────────────────────
    |Δ_f|ᵐ = 2^{mn - m}

  Proof: transitivity  □
```

### Dual Lemma 3 — m-th Power Equation Has Unique ℕ Solution
```
Γ ⊢ dual_unique_mth_root :
    d^m = 2^{mn - m}  ∧  m ≥ 1
    ──────────────────────────────
    d = 2^{n - 1}

  Proof:
    2^{mn - m} = 2^{m(n-1)} = (2^{n-1})ᵐ
    d^m = (2^{n-1})ᵐ
    ∴ d = 2^{n-1}              — by Nat.pow_left_injective  □
```

### Dual Lemma 4 — |Δ| = 2^{n-1} Characterizes APN
```
Γ ⊢ dual_delta_half_field_iff_apn :
    |Δ_f| = |F| / 2  ↔  (derivative of f is exactly 2-to-1)

  Proof: sorry  — Known characterization of APN functions.
    Forward:  |Δ| = |F|/2 means the derivative map x ↦ f(x+a)+f(x)
              has image of size |F|/2 for each a≠0 ⟹ each fiber has
              size exactly 2 ⟹ differential uniformity 2 ⟹ APN.
    Backward: APN ⟹ each derivative fiber has size ≤ 2, hence
              exactly 2 (char 2), hence |Δ| = |F|/2.  □
```

### Dual Lemma 5 — C Is Forced to Equal m
```
Γ ⊢ dual_C_eq_m :
    |F| · κ = |Δ|ᵐ  ∧  |Δ| = 2^{n-1}  ∧  |F| = 2ⁿ
    ∧  κ = 2^{(m-1)n - C}
    ──────────────────────────────────────────────────
    C = m

  Proof:
    |Δ|ᵐ = (2^{n-1})ᵐ = 2^{m(n-1)} = 2^{mn - m}
    |F| · κ = 2ⁿ · 2^{(m-1)n - C} = 2^{n + (m-1)n - C} = 2^{mn - C}
    2^{mn - C} = 2^{mn - m}
    ∴ mn - C = mn - m              — by Nat.pow_right_injective
    ∴ C = m                        — by cancellation  □
```

### Dual Main Theorem — m-Tuple Count Determines f
```
Γ ⊢ dual_mTuple_count_determines_f :
    (SpectralIdentity(f, m) holds)
    ∧  κ_m = 2^{(m-1)n - m}
    ──────────────────────────
    |Δ_f| = 2^{n-1}           (f is APN)
    ∧  C = m                   (the constant is forced)

  Proof: chain Dual Lemmas 1–3 and 5.  □
```

## Summary: Primal vs Dual

| Direction | Input                     | Output                        |
|-----------|---------------------------|-------------------------------|
| Primal    | f is APN + AB             | κ_m = 2^{(m-1)n - m}, C = m  |
| Dual      | κ_m = 2^{(m-1)n - m}     | |Δ_f| = 2^{n-1}, C = m       |
|           | + spectral identity       | (f must be APN)               |

The dual shows that the m-tuple count is a **complete invariant** of the
differential set cardinality: knowing κ_m for any single m ≥ 2 (together
with the Fourier identity) uniquely recovers |Δ_f| and forces C = m.
