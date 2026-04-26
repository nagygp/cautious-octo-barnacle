# Analysis of `kasamiDiff_eq_implies_linearized`

## Summary

The original statement of `kasamiDiff_eq_implies_linearized` (as found in `kasami-09` and `kasami-17-CCD`) is **mathematically false** without additional hypotheses on the field size. A corrected version has been provided with the necessary `Nat.Coprime k n` hypothesis, but the proof of the corrected version remains open (sorry'd).

## The Bug: Missing Hypotheses

### Original (False) Statement
```lean
theorem kasamiDiff_eq_implies_linearized (k : ℕ) (hk : 0 < k)
    (y₁ y₂ : F) (heq : kasamiDiff k 1 y₁ = kasamiDiff k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0
```

### Counterexample
- **Field**: F₄ = GF(2,2) with elements {0, 1, α, α+1} where α²+α+1 = 0
- **Parameter**: k = 2, giving d = 4² - 2² + 1 = 13
- **Key fact**: Over F₄, |F₄*| = 3 and 13 ≡ 1 (mod 3), so x¹³ = x for all x
- **Consequence**: D₁(x^d) = (x+1)+x = 1 is constant, so the hypothesis holds for ALL pairs
- **Failure**: Take y₁ = α, y₂ = 0: z = α ≠ 0, z ≠ 1, and L₂(α) = α¹⁶+α⁴+α = α+α+α = α ≠ 0
- **All three disjuncts fail** → the theorem is false

### Root Cause
When n | k (here n=2, k=2), the exponent d ≡ 1 (mod 2ⁿ-1), making x^d the identity function. The hypothesis `Nat.Coprime k n` excludes this degenerate case.

### Corrected Statement
```lean
theorem kasamiDiff_eq_implies_linearized (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n)
    (y₁ y₂ : F) (heq : kasamiDiff' k 1 y₁ = kasamiDiff' k 1 y₂) :
    y₁ = y₂ ∨ y₁ = y₂ + 1 ∨ linPolyL k (y₁ + y₂) = 0
```

## What Has Been Proved

### Sorry-free results (in `KasamiKernel.lean`)
1. **`gold_second_deriv'`**: The second derivative of the Gold function x^(2^m+1) equals z^(2^m)+z
2. **`frob_cube_eq_mk_lk`**: z^(2^(3k))+z = L_k(z)^(2^k)+L_k(z) (key algebraic identity)
3. **`kasamiExp'_mul_identity`**: d*(2^k+1) = 2^(3k)+1 (number-theoretic identity)
4. **`kasamiDelta_two_to_one'`**: The 2-to-1 property follows from the (sorry'd) CCD factorization + kernel triviality

### Sorry-free infrastructure (in `Defs.lean` and `Kernel.lean`)
- Linearized polynomial definitions and properties
- Kernel dimension theory: `linPolyM_ker_card`, `linPolyL_ker_trivial_of_three_ndvd`, `linPolyL_ker_dim2_of_three_dvd`
- Frobenius fixed point theory

## What Remains

The corrected `kasamiDiff_eq_implies_linearized` (1 sorry) requires the full CCD factorization, which involves:

1. **Bilinear identity**: From Φ = 0 (second derivative vanishing), derive u^q·f + u·f^q = z^(q³)+z via the (q+1)-th power argument
2. **Polynomial factorization**: Show the second derivative D_z D_1(x^d) factors as z(z+1)·Q(x,z) where Q is linearized in x
3. **Solvability analysis**: Show Q(x,z) = 0 has solutions over F_{2^n} only when L_k(z) = 0

This is estimated at 500-1000 lines of new formalization and represents the deepest algebraic step in the Kasami theory.

## Impact on Downstream Results

The downstream theorems are structured to work with the corrected version:
- `kasamiDelta_two_to_one'` (proved modulo the sorry) uses the corrected CCD factorization + `linPolyL_ker_trivial_of_three_ndvd`
- The existing `kasami-14` project's `kasami_is_ab` and `ab_implies_vanishing` remain independent sorries
