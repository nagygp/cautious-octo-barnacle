# Linearized Polynomial Kernel Dimension Theory — Formalization Summary

## Overview

This module formalizes the theory of linearized polynomials over finite fields of characteristic 2,
with particular focus on kernel dimension analysis needed for the Kasami P₃ theorem.

## File Structure

### `RequestProject/LinearizedPoly/Defs.lean` — Core Definitions (sorry-free ✅)
- `frobIter` : Iterated Frobenius `x ↦ x^{2^k}`
- `IsLinearizedFn` : Predicate for additive (linearized) functions
- `artinSchreier` : The Artin–Schreier map `x ↦ x² + x`
- `linPolyL` : The operator `L_k(x) = x^{2^{2k}} + x^{2^k} + x`
- `linPolyM` : The operator `M_k(x) = x^{2^k} + x`
- **Key results**: additivity of all operators, kernel closure under addition,
  Artin–Schreier kernel = {0,1} with cardinality 2

### `RequestProject/LinearizedPoly/Kernel.lean` — Kernel Dimension Theory (sorry-free ✅)
- **Frobenius fixed-point theory**:
  - `frob_mod` : `x^{2^k} = x → x^{2^{k%n}} = x`
  - `frob_fixed_gcd` : `x^{2^k} = x ↔ x^{2^{gcd(k,n)}} = x`
  - `card_frob_fixed` : `|{x : x^{2^m} = x}| = 2^m` when `m | n`
- **M_k kernel**: `linPolyM_ker_card` : `|ker(M_k)| = 2^{gcd(k,n)}`
- **L_k kernel dimension bounds**:
  - `linPolyL_ker_card_le` : `|ker(L_k)| ≤ 2^{2k}`
  - `linPoly_ker_card_pow_two` : `|ker(L)| = 2^d` for some `d`
- **Complete L_k kernel classification** (`linPolyL_ker_card_classification`):
  When `gcd(k,n) = 1`:
  - If `3 ∤ n` : `|ker(L_k)| = 1` (trivial kernel)
  - If `3 | n` and `3 ∤ k` : `|ker(L_k)| = 4` (dimension 2 over GF(2))
  - `3 | n` and `3 | k` impossible since `gcd(k,n) = 1`
- **Subsidiary results**: `linPolyL_ker_nonzero_eq`, `linPolyL_ker_card_gcd`

### `RequestProject/LinearizedPoly/ArtinSchreier.lean` — Trace Connection (sorry-free ✅)
- `trace_frobenius` : `Tr(x²) = Tr(x)` (Frobenius commutes with trace)
- `artinSchreier_fiber` / `artinSchreier_fiber_card` : AS map is 2-to-1
- `artinSchreier_image_card` : `|Im(AS)| = |F|/2`
- `trace_ker_card` : `|ker(Tr)| = |F|/2`
- `artinSchreier_image_eq_trace_ker` : `Im(x ↦ x²+x) = ker(Tr)`

### `RequestProject/LinearizedPoly/KasamiKernel.lean` — Kasami Application (1 sorry)
- `kasamiExp` : The Kasami exponent `d = 4^k - 2^k + 1`
- `kasamiDiff_normalize` : `D_a G(x) = a^d · D_1(x/a)` ✅
- `kasamiDelta_periodic` : `δ(b) = δ(b+1)` ✅
- `kasamiDelta_two_to_one` : 2-to-1 property when `gcd(k,n) = 1, 3 ∤ n` ✅
- `kasamiDelta_image_card` : `|Δ_k| = 2^{n-1}` ✅
- `kasamiDiff_count_even` : Differential count is even ✅
- `kasami_apn` : APN property (count is 0 or 2) ✅
- ⚠️ `kasamiDiff_eq_implies_linearized` : **1 sorry** — The deep factorization
  connecting the Kasami derivative equation to the linearized polynomial L_k.

## Sorry Analysis

**Total sorry count: 1** (out of ~45 theorem statements)

The single remaining sorry is `kasamiDiff_eq_implies_linearized`, which states that
if two points have equal Kasami differentials, then either they differ by 0 or 1,
or their sum is in `ker(L_k)`. This is the Canteaut–Charpin–Dobbertin (2000)
factorization of the Kasami derivative through linearized polynomials.

All other theorems in the four files are fully proved and verified, depending only
on standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Mathematical References

- Lidl, Niederreiter, *Finite Fields* (1997), Chapter 3
- Kasami (1971), *Information and Control* 18(4)
- Canteaut, Charpin, Dobbertin (2000), *SIAM J. Discrete Math.* 13(1)
- Carlet (2021), *Boolean Functions for Cryptography and Coding Theory*
