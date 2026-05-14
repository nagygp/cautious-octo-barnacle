# Mini AB-Topos Theory — A Learner's Guide

## What is this?

This is a **self-contained, fully machine-verified** formalization of the
core theory connecting spectral analysis, coding theory, and APN
cryptographic functions. Every theorem is proved — there are zero `sorry`
statements and no custom axioms.

The formalization is organized into 5 chapters that build from the simplest
definitions to deep structural theorems.

---

## How to read this (suggested order)

### Chapter 1: Spectral Foundations
**File**: `Chapter1_SpectralFoundations.lean`

**What you learn**: The basic building blocks of the theory.

| Concept | What it is | Analogy |
|---------|-----------|---------|
| `SpectralObject` | A finite set with a ℂ-valued "spectrum" | A signal with frequency components |
| `IsBent` | All nonzero spectral values have the same magnitude | A perfectly flat frequency response |
| `IsThreeValued` | Spectrum ∈ {0, +c, −c} | The signature of AB (Almost-Bent) functions |
| `spectralDiversity` | Number of distinct nonzero magnitudes | Measures "spectral noise" |

**Key result**: `bent_diversity_eq_one` — the **KEY LEMMA** of the entire theory.
If a spectrum is bent at level c > 0 with at least one nonzero value,
its diversity is exactly 1. This single lemma powers everything that follows.

---

### Chapter 2: Spectral Rigidity
**File**: `Chapter2_SpectralRigidity.lean`

**What you learn**: How bentness forces structural rigidity.

| Concept | What it is |
|---------|-----------|
| `HomotopySpectralObject` | Spectrum + "homotopy group sizes" πₖ |
| `IsDiscrete` | πₖ = 1 for all k ≥ 1 (maximally simple) |
| `IsKBent` | Bent + trivial homotopy up to level k |
| `postnikovConstruction` | Builds πₖ from the spectrum: π₀ = \|carrier\|, πₖ = diversity |

**The logical chain**:
```
Bent spectrum
    │ (KEY LEMMA from Ch. 1)
    ▼
diversity = 1
    │ (Postnikov construction)
    ▼
πₖ = 1 for all k ≥ 1
    │
    ▼
SPECTRAL RIGIDITY (discreteness)
```

**Main theorem**: `bent_implies_discrete` — bent spectra are necessarily discrete.
This is *derived*, not assumed!

**Converse**: `silence_constraint` — two distinct nonzero magnitudes force
diversity > 1, which prevents discreteness.

---

### Chapter 3: Binary Codes and m-Tuple Counts
**File**: `Chapter3_CodingTheory.lean`

**What you learn**: The coding-theory side of the bridge.

| Concept | What it is |
|---------|-----------|
| `BinaryCode` | A set of binary vectors closed under addition |
| `hammingWeight` | Number of nonzero coordinates |
| `weightDistribution` | How many codewords of each weight |
| `mTupleCount` | Number of m-tuples summing to zero |

**Main theorem**: `mTupleCount_eq_card_pow` — for any binary linear code C
and m ≥ 1:

    κ_m(C) = |C|^{m−1}

This is proved by induction using the GF(2) property that −x = x.

**Corollary**: `mtuple_rigidity_from_card` — the m-tuple count depends
*only* on |C|. Two codes with the same cardinality have identical
m-tuple counts, regardless of any other structural differences.

---

### Chapter 4: APN Functions and the Cardinality Theorem
**File**: `Chapter4_APNCardinality.lean`

**What you learn**: Cryptographic functions and their differential structure.

| Concept | What it is |
|---------|-----------|
| `differentialMap` | D_a(f)(x) = f(x+a) + f(x) |
| `IsAPN` | At most 2 solutions to every differential equation |
| `differentialSet` | Δ(f) = {f(x) + f(x+1) + 1 : x ∈ 𝔽} |

**Key insight**: In characteristic 2, the differential has a pairing symmetry:
D_a(f)(x) = D_a(f)(x + a). This means solutions always come in pairs of size 2.

**Main theorem**: `apn_differentialSet_card` — for APN f over GF(2ⁿ):

    |Δ(f)| = 2^{n−1}

**Bonus**: `primal_dual_equivalence` — the m-tuple count and differential
set size determine each other:

    κ = 2^{(m−1)n − m}  ⟺  δ = 2^{n−1}

---

### Chapter 5: The Rosetta Stone
**File**: `Chapter5_RosettaStone.lean`

**What you learn**: How spectral theory, coding theory, and homotopy theory
are all measuring the **same thing**.

The **spectral power sum** S_m = Σ ‖W(v)‖^{2m} is the "classical" quantity.
For a bent spectrum:

    S_m = |support| · c^{2m}

Dividing by c^{2m} gives the **spectral invariant** = |support|, which is
a purely combinatorial number.

**The Rosetta Stone Theorem** (`spectral_topos_isomorphism`):
For a bent spectrum at level c > 0:

| World | Invariant | Value |
|-------|-----------|-------|
| **Spectral** | S_m / c^{2m} | = |support| |
| **Coding** | κ_m^{1/(m-1)} | = |C| (when |C| = |support|) |
| **Homotopy** | diversity | = 1 (bent ⟹ discrete) |

All three frameworks extract the same number: the spectral support size.

---

## Mathematical Soundness

### What's verified
- **Zero sorry**: Every theorem has a complete machine-checked proof
- **Standard axioms only**: `propext`, `Classical.choice`, `Quot.sound`
  (the standard Lean 4 / Mathlib axioms)
- **No custom axioms**: No `axiom` declarations anywhere
- **No contradictions**: The axiom audit at the end of Chapter 5 confirms
  all theorems depend only on standard axioms

### What's grounded in mathematics
- **Spectral objects**: Standard definitions from harmonic analysis
- **Bentness**: Standard definition from Boolean function theory
- **Binary codes**: Standard definitions from coding theory
- **APN functions**: Standard definition from cryptography (Nyberg 1994)
- **Differential pairing**: Uses characteristic-2 arithmetic (x + x = 0)
- **m-tuple count formula**: Proved by induction using GF(2) linearity
- **Primal-dual equivalence**: Pure number theory (divisibility of powers of 2)

### The Postnikov construction
The "homotopy spectral object" and "Postnikov construction" are
*inspired by* algebraic topology but are defined purely combinatorially:
- πₖ for k ≥ 1 is defined as the spectral diversity
- Discreteness (πₖ = 1) is *derived* from bentness, not assumed

This is mathematically sound: the definitions are well-formed, and all
theorems about them are fully proved. The connection to actual homotopy
theory is an *analogy*, not a formal claim.

---

## Dependency Graph

```
Chapter 1 (Foundations)
    │
    ├──▶ Chapter 2 (Rigidity)
    │         │
    │         ├──▶ Chapter 5 (Rosetta Stone)
    │         │         ▲
    │         │         │
    ├─────────┼─────────┤
    │         │         │
    │    Chapter 3      │
    │   (Coding Theory) │
    │                   │
    └──── Chapter 4 ────┘
        (APN Functions)
```

Chapters 3 and 4 are independent of each other and of Chapter 2.
Chapter 5 brings everything together.

---

## Line Counts

| File | Lines | Sorry | Description |
|------|-------|-------|-------------|
| Chapter1_SpectralFoundations.lean | 262 | 0 | Spectral objects, bentness, diversity |
| Chapter2_SpectralRigidity.lean | 306 | 0 | Postnikov, rigidity, silence constraint |
| Chapter3_CodingTheory.lean | 213 | 0 | Binary codes, m-tuple counts |
| Chapter4_APNCardinality.lean | 270 | 0 | APN functions, KR₁ theorem |
| Chapter5_RosettaStone.lean | 284 | 0 | Rosetta Stone bridge |
| **Total** | **1335** | **0** | |

Compare to the original project: ~8000 lines with 14 sorry statements.
This mini version distills the proven, mathematically sound core.
