# Gap Analysis: Connecting AB Functions to Machine-Verified Mathlib Proofs

## Executive Summary

This document identifies what was missing and what was built to connect the new AB function
conjectures (AB1–AB10) to machine-verified Mathlib-grounded proofs, including computable
AB/APN detection and testing.

---

## New Files Created

| File | Purpose |
|------|---------|
| `Detect/GF2n.lean` | Computable GF(2^n) arithmetic: XOR addition, polynomial multiplication, exponentiation, absolute trace |
| `Detect/APNDetector.lean` | Computable APN detector with differential uniformity computation and `#eval` tests |
| `Detect/ABDetector.lean` | Computable AB detector via Walsh spectrum computation and `#eval` tests |
| `Detect/Bridge.lean` | Machine-verified bridge: `native_decide` formal theorems connecting detectors to Lean propositions |

## Sorries Eliminated (4 total)

| File | Theorem | Status |
|------|---------|--------|
| `Foundation/CodeSubmodule.lean` | `dim_plus_codim` | ✅ Proved |
| `Foundation/CodeSubmodule.lean` | `double_orthogonal_eq` | ✅ Proved |
| `Foundation/CodeSubmodule.lean` | `evalMap_bijective` | ✅ Proved |
| `Foundation/GaussSumBridge.lean` | `project_gauss_eq_mathlib` | ✅ Proved |

---

## What Now Works

### ✅ Computable AB/APN Detection (`Detect/`)
- **`checkAPN n f`**: decides whether `f` is APN over GF(2^n) — fully `#eval`-friendly
- **`isAB n f`**: decides whether `f` is AB over GF(2^n) — computes the full Walsh transform using the absolute trace
- **`differentialUniformity n f`**: computes the exact differential uniformity
- **`walshSpectrumSq n f`**: computes the set of distinct |W_f(a,b)|² values
- **`abScan n`**: enumerates ALL APN/AB power maps over GF(2^n)
- **`abReport n d`**: full diagnostic report for a power map x^d

### ✅ Machine-Verified Results via `native_decide` (`Detect/Bridge.lean`)
These are **formal Lean theorems** (not just `#eval` outputs):

| Theorem | Statement | Axioms |
|---------|-----------|--------|
| `gold_apn_gf32` | x³ is APN over GF(2⁵) | `Lean.ofReduceBool`, `Lean.trustCompiler` |
| `gold_ab_gf32` | x³ is AB over GF(2⁵) | same |
| `gold_apn_gf8` | x³ is APN over GF(2³) | same |
| `gold_ab_gf8` | x³ is AB over GF(2³) | same |
| `kasami_apn_gf32` | x¹³ is APN over GF(2⁵) | same |
| `kasami_ab_gf32` | x¹³ is AB over GF(2⁵) | same |
| `welch_apn_gf32` | x⁷ is APN over GF(2⁵) | same |
| `welch_ab_gf32` | x⁷ is AB over GF(2⁵) | same |
| `inverse_apn_not_ab_gf32` | x³⁰ is APN but NOT AB over GF(2⁵) | same |
| `frobenius_not_apn_gf32` | x² is NOT APN over GF(2⁵) | same |
| `conjAB10_gf32` | x⁶ (S₃-transferred exponent) IS AB over GF(2⁵) | same |

### ✅ Computational Evidence for New AB Conjectures
- **Conjecture AB10** (x⁶): Computationally confirmed both APN and AB on GF(2⁵) ✓
- **Conjecture AB1** k=2 (x⁷ = Welch): Confirmed AB on GF(2⁵) ✓
- **Conjecture AB6** (x¹⁵ = Double-Gold): APN but NOT AB on GF(2⁵) — conjecture may be false or n=5 may be too small
- **Full scan of GF(2⁵)**: 20 of 25 APN exponents are AB; non-AB APN exponents are d ∈ {15, 23, 27, 29, 30}

### ✅ Fully Proved Mathlib-Grounded Results
- `evalMap_bijective`: GF(2)^n is self-dual via the standard bilinear form
- `dim_plus_codim`: dim(C) + dim(C⊥) = n for linear codes
- `double_orthogonal_eq`: C⊥⊥ = C for linear codes over GF(2)
- `project_gauss_eq_mathlib`: Project's Gauss sum equals Mathlib's `gaussSum`

---

## What Is Still Missing (Gaps)

### Gap 1: No Mathlib `GaloisField` ↔ Nat Isomorphism (Medium Impact)

**Problem**: Mathlib's `GaloisField 2 n` is defined as a splitting field
and is **noncomputable** (no `Fintype` instance). There is no computable
bijection to our `Nat`-based representation.

**Impact**: The `native_decide` proofs in `Detect/Bridge.lean` work on
our Nat-based model. To transfer them to `GaloisField`, we need an
isomorphism-invariance theorem for APN.

**What would fix it**:
- Prove "for any two fields of the same finite size and characteristic,
  the APN property of a power map is preserved under isomorphism"
- OR build a computable `GaloisField` in Mathlib (major project)
- OR use `(Fin n → ZMod 2)` as the canonical additive group, since
  `IsAPN` only uses the additive group structure, and this type already
  has `AddCommGroup`, `Fintype`, `DecidableEq` from Mathlib

### Gap 2: Walsh Transform Not Grounded in Mathlib Characters (Medium Impact)

**Problem**: The project's `WalshData`/`IsABWalsh` in `Conjectures/NewAB.lean`
is an abstract structure with integer coefficients. It is not connected to:
- Mathlib's `AddChar` (additive characters)
- The absolute trace function
- Our computable `walshCoeff` in `Detect/ABDetector.lean`

**Impact**: The AB conjectures (AB1–AB10) use `IsAPN` not `IsABWalsh`, so
this is less critical for them. But a full AB verification path needs it.

**What would fix it**: Define Walsh transform using `AddChar` from Mathlib,
connect `gf2nTrace` to `FiniteField.trace`, prove equivalence with `walshCoeff`.

### Gap 3: No Formal AB ⟹ APN Bridge (Low-Medium Impact)

**Problem**: For odd n, AB implies APN. This classical result is not proved.
The project's conjectures use `IsAPN` (weaker than AB), so this gap doesn't
block the conjectures but does block formal verification that AB-ness implies
APN-ness.

**What would fix it**: Prove via Parseval's identity + Welch bound.

### Gap 4: AB Conjectures Not Proved (Research-Level)

**Problem**: Conjectures AB1–AB10 are open mathematical conjectures.

**Status by conjecture**:
| # | Name | Computational Evidence | Theoretical Status |
|---|------|----------------------|-------------------|
| AB1 | Coulter-Matthews Boolean | k=2 is Welch (known AB) | Open for general k |
| AB2 | Ding-Helleseth Boolean | Kasami exponent (known AB) | Already known |
| AB3 | Helleseth-Rong Boolean | k=1 gives d=5 (known) | Open for k≥2 |
| AB4 | Log-Domain Gold | Index-level statement | Needs field lifting |
| AB5 | Frobenius-Twisted Kasami | Needs larger field test | Open |
| AB6 | Double-Gold | x¹⁵ NOT AB on GF(2⁵)! | Likely FALSE |
| AB7 | Kerdock Sufficiency | Structural | Open |
| AB8 | Homotopical Characterisation | Structural | Open |
| AB9 | Walsh Self-Dual AB | Existence claim | Trivially true (Gold works) |
| AB10 | S₃-Transferred | x⁶ IS AB on GF(2⁵)! | Encouraging evidence |

### Gap 5: 14 Remaining `sorry` Statements (Deep Results)

| File | Count | Nature |
|------|-------|--------|
| `Foundation/FunctorialDuality.lean` | 2 | Power sum bound, bent existence |
| `Foundation/GaussSumBridge.lean` | 5 | χ' primitive, Gauss norm², Kasami coprimality/permutation, moment bounds |
| `Spectral/WalshGauss.lean` | 5 | Kasami APN, Walsh bounds, three-valuedness |
| `Spectral/WalshDuality.lean` | 1 | spectrFlat → AB (needs Parseval) |
| `Conjectures/APN.lean` | 1 | APN differential image |

Most require deep algebraic coding theory not yet in Mathlib.

---

## Architecture Diagram

```
                    ┌──────────────────────┐
                    │  Conjectures/NewAB   │  AB1–AB10 conjectures
                    │  (uses IsAPN)        │  (stated, not proved)
                    └──────────┬───────────┘
                               │ imports
                    ┌──────────▼───────────┐
                    │  Conjectures/APN     │  IsAPN definition
                    │  differentialMap     │  (Mathlib AddCommGroup)
                    └──────────┬───────────┘
                               │
          ┌────────────────────┼────────────────────┐
          │                    │                    │
┌─────────▼────────┐ ┌────────▼─────────┐ ┌───────▼────────┐
│  Bridge/Duality  │ │  Spectral/*      │ │  Foundation/*  │
│  (topos theory)  │ │  (Walsh, Gauss)  │ │  (codes, topos)│
└──────────────────┘ └──────────────────┘ └────────────────┘
                               │
                    ┌──────────▼───────────┐
         NEW ──────▶│  Detect/            │  Computable detection
                    │  GF2n.lean          │  (Nat-based GF(2^n))
                    │  APNDetector.lean   │  (#eval friendly)
                    │  ABDetector.lean    │  (Walsh spectrum)
                    │  Bridge.lean        │  (native_decide proofs)
                    └─────────────────────┘
```

## Recommended Next Steps (Priority Order)

1. **Extend AB scan to GF(2⁷)** — validate/refute AB6 on larger field
2. **Build `AddCommGroup` on `Fin (2^n)` via XOR** — or use `(Fin n → ZMod 2)` directly with `IsAPN`
3. **Prove isomorphism-invariance of APN** — transfers `native_decide` results to abstract fields
4. **Ground Walsh transform in `AddChar`** — connects AB to Mathlib character theory
5. **Prove AB ⟹ APN** — standard Parseval + Welch bound argument
6. **Eliminate remaining `sorry` statements** — deep algebraic coding theory
