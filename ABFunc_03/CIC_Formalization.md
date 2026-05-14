# Kasami Triple-Count Theorem — CIC Unicode Formalization

## 1. Setting

Let **𝔽** := GF(2ⁿ) be a finite field of characteristic 2 with |𝔽| = 2ⁿ.

**Parameters:**
- n ∈ ℕ, n ≥ 3, n odd
- k ∈ ℕ, k ≥ 1, gcd(k, n) = 1

## 2. Definitions in CIC

### Kasami Exponent
```
d : ℕ → ℕ
d(k) := 4ᵏ − 2ᵏ + 1
```

### Kasami Function
```
f : 𝔽 → 𝔽
f(x) := x^{d(k)}
```

### Differential Set
```
Δ : Finset 𝔽
Δ := { f(b) + f(b + 1) + 1 | b ∈ 𝔽 }
```

### Triple Set
```
𝒯 : 𝔽 → 𝔽 → Finset (𝔽 × 𝔽 × 𝔽)
𝒯(v₁, v₂) := { (x, y, z) ∈ Δ × Δ × Δ | v₁·x + v₂·y + (v₁ + v₂)·z = 0 }
```

### Additive Character
```
χ : 𝔽 → ℂ
χ := AddChar.FiniteField.primitiveChar_to_Complex 𝔽
```

### Fourier Transform of Δ
```
δ̂ : 𝔽 → ℂ
δ̂(a) := Σ_{x ∈ Δ} χ(a · x)
```

### Triple Spectral Sum
```
T : 𝔽 → 𝔽 → ℂ
T(v₁, v₂) := Σ_{a ∈ 𝔽} δ̂(v₁·a) · δ̂(v₂·a) · δ̂((v₁+v₂)·a)
```

## 3. The Main Theorem (CIC Type)

```
∀ (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2],
∀ (n k : ℕ),
  3 ≤ n →
  n % 2 = 1 →
  Fintype.card 𝔽 = 2^n →
  Nat.Coprime k n →
  ∀ (v₁ v₂ : 𝔽),
    v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
    |𝒯(v₁, v₂)| = 2^{2n − 3}
```

## 4. Proof Structure (CIC Term)

The proof term has the following logical structure:

```
kasami_triple_count :=
  λ 𝔽 n k hn hn_odd hcard hcoprime v₁ v₂ hv₁ hv₂ hne ⇒
    let hk : 1 ≤ k := coprime_implies_k_ge_1 hcoprime
    let κ := |𝒯(v₁, v₂)|

    -- Step 1: Combined Fourier-AB identity (black-boxed)
    let h_comb : |𝔽| · κ = |Δ|³ :=
      combined_identity 𝔽 k hn hk hn_odd hcard hcoprime v₁ v₂ hv₁ hv₂ hne

    -- Step 2: Delta cardinality from APN (proved from black-boxed APN)
    let h_delta : |Δ| = 2^{n−1} :=
      kasami_delta_card 𝔽 k hn hk hcard hcoprime

    -- Step 3: Algebraic chain (fully proved)
    let key : 2ⁿ · κ = 2ⁿ · 2^{2n−3} :=
      calc 2ⁿ · κ
          = |𝔽| · κ             -- hcard
        _ = |Δ|³                -- h_comb
        _ = (2^{n−1})³          -- h_delta
        _ = 2^{3n−3}            -- pow_cube
        _ = 2ⁿ · 2^{2n−3}      -- pow_split_3

    -- Step 4: Cancellation (fully proved)
    mul_left_cancel₀ (2ⁿ ≠ 0) key
```

## 5. Dependency Graph

```
                   kasami_triple_count
                   /                  \
          combined_identity      kasami_delta_card
          (BLACK BOX)           /              \
              |          delta_fiber_exact   delta_fiber_sum
              |          /           \           (PROVED)
              |  delta_fiber_le_two  delta_fiber_ge_two
              |      (PROVED         (PROVED from
              |    from kasami_apn)  derivative_symmetric)
              |          |
              |     kasami_apn
              |     (BLACK BOX)
              |
          combines:
          ├── Fourier identity
          │   (Σ_a χ orthogonality)
          └── AB spectral collapse
              (BLACK BOX: [BBMM, Thm 3])
```

## 6. What is Proved from Mathlib

| Result | Status | Method |
|--------|--------|--------|
| `char2_add_self` | ✅ Proved | `CharP.cast_eq_zero` + ring |
| `char2_add_one_twice` | ✅ Proved | From `char2_add_self` |
| `ne_add_one_char2` | ✅ Proved | `sub_eq_zero` |
| `derivative_symmetric` | ✅ Proved | `char2_add_one_twice` + ring |
| `delta_fiber_le_two` | ✅ Proved | From `kasami_apn` + rewrite |
| `delta_fiber_ge_two` | ✅ Proved | `derivative_symmetric` + `ne_add_one_char2` |
| `delta_fiber_exact` | ✅ Proved | `≤ 2` + `≥ 2` ⟹ `= 2` |
| `delta_fiber_sum` | ✅ Proved | Fiber partition of Finset.univ |
| `kasami_delta_card` | ✅ Proved | Fiber sum + exact fiber size |
| `pow_cube` | ✅ Proved | omega |
| `pow_split_3` | ✅ Proved | omega |
| `exp_split` | ✅ Proved | zify + linarith |
| `kasami_triple_count` | ✅ Proved | calc chain + cancel |
| `m_tuple_count` | ✅ Proved | calc chain + cancel |
| `triple_as_m3` | ✅ Proved | specialization |
| `ab_iff_kappa` | ✅ Proved | composition of forward + inverse |

## 7. What is Black-Boxed

| Result | Reference |
|--------|-----------|
| `kasami_apn` | [Bud, Thm 2.3] — APN property via linearized polynomial analysis |
| `combined_identity` | [BBMM, Thm 3] — Fourier identity + AB spectral collapse |
| `fourier_ab_m` | Generalization of combined_identity to m-tuples |
| `ab_forward` | Parseval/convolution + AB spectral flatness |
| `ab_inverse` | Moment–count bridge + Hausdorff moment uniqueness |

## 8. m-Tuple Generalization (CIC Type)

```
∀ (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2],
∀ (n k m : ℕ),
  3 ≤ n → n % 2 = 1 → 2 ≤ m →
  Fintype.card 𝔽 = 2^n →
  Nat.Coprime k n → 1 ≤ k →
  ∀ (coeffs : Fin m → 𝔽),
    (∀ i, coeffs i ≠ 0) →
    |𝒯ₘ(coeffs)| = 2^{(m−1)·n − m}
```

Specializations:
- m = 3: 2^{2n − 3}  (triple count)
- m = 4: 2^{3n − 4}  (quadruple count)
- m = 5: 2^{4n − 5}  (quintuple count)

## 9. Dual Characterization (CIC Type)

```
∀ (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2],
∀ (f : 𝔽 → 𝔽),
  IsAB(f) ⟺ (∀ m ≥ 2, κₘ(f) = 2^{(m−1)·n − m})
```

where:
- **IsAB(f)** := ∀ u ∈ 𝔽, |Ŵ_f(u)| ∈ {0, 2^{(n+1)/2}}
- **κₘ(f)** := |{ v ∈ 𝔽ᵐ | Σᵢ vᵢ = 0 }|

This is proved as a composition: the biconditional `ab_iff_kappa` combines
`ab_forward` (sorry'd) and `ab_inverse` (sorry'd), each of which relies on
deep spectral analysis (Parseval identity, Hausdorff moment uniqueness).

## 10. Why Full First-Principles Proof is Not Currently Achievable

The two black-boxed results require mathematical infrastructure not yet in Mathlib:

1. **APN (kasami_apn)**: Requires showing that x^d + (x+a)^d = b has ≤ 2
   solutions over GF(2ⁿ) when d = 4ᵏ − 2ᵏ + 1 and gcd(k,n) = 1. This
   involves:
   - Factoring the equation into a linearized polynomial L(x) = 0
   - Showing ker(L) has GF(2)-dimension ≤ 1
   - This uses the norm map N_{GF(2ⁿ)/GF(2ᵏ)} and its interaction with
     the Frobenius endomorphism

2. **AB Spectral Collapse (combined_identity)**: Requires computing the Walsh
   spectrum of x^d, showing |Ŵ(u)| ∈ {0, 2^{(n+1)/2}} for n odd. This uses:
   - Gauss sums over GF(2ⁿ)
   - The Stickelberger relation
   - The fact that for APN power functions with n odd, the Walsh transform
     has exactly the AB distribution

Both are well-established results from the 1990s–2000s literature on
cryptographic Boolean functions. The Lean 4 formalization of these would
require building significant finite field infrastructure (extension fields,
trace maps, Gauss sums) that goes beyond current Mathlib coverage.
