# Summary of changes for run 99db2212-09f2-44a7-895a-03cf04ee40d1
# Analysis: Completing Kasami Formalization Versions

## Overview

I analyzed the formalization attempts in `kasami-64`, `kasami-65`, `kasami-66`, and `kasami-67` from the [cautious-octo-barnacle](https://github.com/attilavjda/cautious-octo-barnacle) repository.

**Key finding:** `kasami-67` does not exist in the repository.

## Results by Version

### kasami-64 and kasami-65: Already Complete
Both have **0 sorries** and compile with only standard axioms. Their main theorems take the Almost Bent (AB) property as a hypothesis, which cannot be discharged from any existing proven lemma in the repository. kasami-65 is the stronger version — it corrects a mathematical error in kasami-64's formula (the original T₃ = 2^{2n-3} is wrong; the correct formula is T₃ = 2^{2n-3} - 2^{n-2}).

### kasami-66: Partially Completed — Mathematical Errors Discovered

kasami-66 originally had **6 sorries** across 4 theorems. I discovered that **2 of these 4 theorems are mathematically false**:

- `gold_walsh_third_moment_zero` claimed ∑ W(a)³ = 0 — **FALSE** (correct value: 2^{2n+1})
- `gold_P3_ordered` claimed goldTripleCount = 2^{2n-1} — **FALSE** (correct value: 2^{2n-1} + 2^n)

These have been commented out with explanations of the correct values.

**Successfully proved the 2 correct theorems:**

- ✅ **`gold_walsh_sq_spectrum`** — The AB property: W(a)² ∈ {0, 2^{n+1}}
- ✅ **`gold_walsh_at_zero`** — Balancedness: W(0) = 0

Both are proved from first principles via a **radical factorization technique** in the new file `RequestProject/WalshRadical.lean`, which establishes the key identity:

> **W(a)² = |F| · (1 + (-1)^{Tr(1+a)})**

This identity is derived by expanding W(a)², substituting z = x+y, and showing that the inner character sum vanishes for z ∉ {0, 1} (the radical of the polar form). The proof reuses proven lemmas from within kasami-66 itself (polar expansion, kernel bounds, trace adjoint, Frobenius injectivity).

## New File Created

**`RequestProject/WalshRadical.lean`** — 11 fully proved theorems (0 sorries, standard axioms only):
- Character multiplicativity, trace lemmas, unweighted kernel characterization
- Polar form identity, inner sum vanishing/evaluation
- The key Walsh² identity and its consequences (AB property, balancedness)

## Project Status

All `.lean` files compile successfully with **zero sorries** in executable code and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Full analysis is in `ANALYSIS.md`.