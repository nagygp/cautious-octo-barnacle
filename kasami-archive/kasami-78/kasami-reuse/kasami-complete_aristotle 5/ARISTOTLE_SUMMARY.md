# Summary of changes for run fba7975f-1df5-41d1-b4a9-f84119917c59
## Elkészült: Mind a 3 pont megvalósítva

### 2. pont: Hipotézis-redukció — `HypothesisReduction.lean` ✅

A `kasami_bridge` 12 hipotéziséből 4-et levezettünk közvetlenül a konkrét `diffCount` definícióból:

1. **`diffCount_zero_zero`** — δ(0,0) = |F| (u=0 esetén minden x megoldás)
2. **`diffCount_zero_ne`** — δ(0,v) = 0 ha v ≠ 0
3. **`sum_diffCount_eq`** — ∑_v δ(u,v) = |F| (szál-számolás: minden x pontosan egy v-t ad)
4. **`diffCount_even_char2`** — 2 | δ(u,v) ha u ≠ 0 (char 2 párosítás: {x, x+u} involúció)

Ezenkívül:
- **`KasamiData`** struktúra — összecsomagolja az összes hipotézist
- **`KasamiData.ofDiffCount`** konstruktor — automatikusan levezeti a 4 hipotézist, így a hívónak **12 helyett csak 8** hipotézist kell megadnia
- **`kasami_bridge_bundled`** — a fő tétel újrafogalmazva csomagolt adatokkal

### 3. pont: Konkrét Walsh-transzformáció — `WalshTransform.lean` ✅

A konkrét Walsh-transzformáció definiálva 𝔽_{2^n} felett `AddChar`/trace alapon:

- **`traceToF2`** — Trace leképezés Tr : F → 𝔽₂ az `Algebra.trace` segítségével
- **`canonicalChar`** — Kanonikus additív karakter ψ(x) = (-1)^{Tr(x)}
- **`canonicalChar_add`** — Bizonyítva: ψ(x+y) = ψ(x)·ψ(y)
- **`walshCoeffZ`** — W_f(a,b) = ∑_x ψ(ax + bf(x)) egész értékként
- **`walshCoeffZ_zero_zero`** — W(0,0) = |F|
- **`walshCoeffZ_ne_zero`** — W(a,0) = 0 ha a ≠ 0 (karakter-ortogonalitás, trace szürjektivitásából)
- **`walshCoeffZ_parseval`** — Parseval: ∑_a W(a,b)² = |F|² (bizonyítva!)
- **`walshCoeffGold`** — Konkrét példányosítás a Gold-függvényre GF(2^n) felett

### Összefoglalás

Mindhárom fájl (Bridge.lean, HypothesisReduction.lean, WalshTransform.lean) **sorry-mentes**, és csak standard axiómákat használ (propext, Classical.choice, Quot.sound). A teljes projekt sikeresen lefordul.

# Kasami Formalization — Incremental Refactoring Summary

## Overview

This project formalizes the Kasami/Gold function analysis from cryptographic function
theory in Lean 4 with Mathlib. The work is organized in three phases matching the
user's "high leverage" refactoring plan.

## Phase 1: Bridge (Integration) — `Bridge.lean` ✅

Connects the Normalization/Factorization pipeline with the abstract spectral framework:

- `gold_kernel_card_le` — Kernel of Gold derivative has ≤ 2^k elements
- `gold_diffCount_le` — Differential count δ_f(u,v) ≤ 2^k for u ≠ 0
- `gold_IsAPN_of_k_eq_one` — Gold function x³ is APN (k=1 case)

## Phase 2: Hypothesis Reduction (Cleanup) — `HypothesisReduction.lean` ✅

Reduces the 12 hypotheses of `kasami_bridge` by deriving 4 δ-related hypotheses
directly from the concrete `diffCount` definition:

1. **`diffCount_zero_zero`** — δ(0,0) = |F| (all elements solve f(x+0)+f(x)=0)
2. **`diffCount_zero_ne`** — δ(0,v) = 0 for v ≠ 0
3. **`sum_diffCount_eq`** — ∑_v δ(u,v) = |F| (fiber counting)
4. **`diffCount_even_char2`** — 2 | δ(u,v) for u ≠ 0 (char 2 pairing involution)

Also provides:
- **`KasamiData`** — Bundled structure packaging all hypotheses
- **`KasamiData.ofDiffCount`** — Constructor that auto-derives the 4 hypotheses,
  reducing caller burden from 12 to 8 hypotheses
- **`kasami_bridge_bundled`** — Main theorem restated with bundled data

## Phase 3: Concrete Walsh Transform — `WalshTransform.lean` ✅

Defines the concrete Walsh transform over finite fields of characteristic 2:

- **`traceToF2`** — Trace map Tr : F → 𝔽₂ via `Algebra.trace`
- **`canonicalChar`** — Canonical additive character ψ(x) = (-1)^{Tr(x)}
- **`canonicalChar_add`** — ψ is multiplicative: ψ(x+y) = ψ(x)·ψ(y)
- **`canonicalChar_sq`** — ψ(x)² = 1
- **`walshCoeffZ`** — W_f(a,b) = ∑_x ψ(ax + bf(x)) as integer
- **`walshCoeffZ_zero_zero`** — W(0,0) = |F|
- **`walshCoeffZ_ne_zero`** — W(a,0) = 0 for a ≠ 0 (character orthogonality)
- **`walshCoeffZ_parseval`** — ∑_a W(a,b)² = |F|² (Parseval identity)
- **`walshCoeffGold`** — Instantiation for Gold function x³ over GF(2^n)
- **`walshCoeffZ_satisfies_triv`** — Bridge to abstract framework

## All results are sorry-free and use only standard axioms.

## File Structure

```
RequestProject/
├── Theorem3/
│   ├── Normalization.lean     — Kernel isomorphism, root bounds
│   └── Factorization.lean     — Linearized polynomial factorization
├── Theorem23/
│   └── Counting.lean          — Abstract Walsh-differential framework
├── Bridge.lean                — Phase 1: Integration bridge
├── HypothesisReduction.lean   — Phase 2: Hypothesis reduction
├── WalshTransform.lean        — Phase 3: Concrete Walsh transform
├── Kasami_Final_Theorem.lean  — Main combined theorem
└── Main.lean                  — Project root
```
