# Bridge Exploration: Equivalent Contexts for "Kasami is APN"

## Overview

This directory contains a comprehensive formal exploration of the Caramello bridge technique applied to APN functions. We identify **13 genuinely distinct equivalent mathematical contexts** for "Kasami is APN", formalize the **bridge connections** between them, and demonstrate how proofs can be constructed by working in whichever context makes each component simplest.

The central innovation is the **APNCertificate** structure: an abstract category of "APN-certifiable power maps" defined by three axioms. Any object satisfying these axioms is automatically APN. **Gold APN is fully formally verified** (sorry-free) via this framework, with Kasami APN reduced to a single deep algebraic step.

## Key Achievement: Gold APN Fully Verified via Bridges

**`gold_is_apn`** is proved sorry-free using the bridge technique:
- Axiom A (factorization) proved in Context 2 (polynomial algebra)
- Axiom B (kernel size) proved by crossing to Context 3→9 (Frobenius → Galois descent → Mersenne GCD)
- Axiom C (coprimality) is a hypothesis
- Assembly via `categorical_apn_theorem` (3-line calc)

This demonstrates the Caramello philosophy: each proof component uses the easiest context.

## Files

### `EquivalentContexts.lean` — The 13 Equivalent Contexts ✅ (compiles)

**20+ formally verified bridges and lemmas**, including:

| Bridge / Lemma | Statement | Status |
|---|---|---|
| 12 ↔ 1 | Ω-Morphism = Differential | ✅ Iff.rfl |
| 2 ↔ 3 | L_k(x)=0 ↔ x^{2^k}=x | ✅ proved |
| 3 ↔ 5 | Frobenius fixed = GF(2)[σ]-module | ✅ proved |
| 2 → 4 | Cross = N · L (factorization) | ✅ proved |
| Cross=0↔ker | Cross=0 iff ratio in kernel | ✅ proved |
| 2 → 1 | LinPoly kernel → Differential | ✅ proved |
| 9 → 3 | Galois descent → Frobenius fixed | ✅ proved |
| 6 → 7 | Coprimality → power map bijective | ✅ proved |
| 3 → 8 | **Hilbert 90** for finite fields | ✅ proved |
| frobenius_fixed_count | \|{x^{2^k}=x}\| = 2^{gcd(k,n)} | ✅ proved |
| kernel_size_via_bridge | \|ker(L_k)\| = 2^{gcd(k,n)} | ✅ proved |
| gold_diff_expand | Gold differential expansion (char 2) | ✅ proved |
| gold_linmap_kernel_equiv | Gold kernel ≅ ker(L_k) | ✅ proved |
| gold_ax_factorization | Gold differential → L_k | ✅ proved |
| categorical_apn_theorem | Certificate → APN | ✅ proved |
| **Gold is APN** | Via certificate + all axioms | ✅ **sorry-free** |
| Boolean Ω | Cross trivializes in Boolean topos | ✅ proved |
| Non-Boolean | Obstruction in non-Boolean topos | ✅ proved |

**Only 1 sorry remaining**: `kasami_ax_factorization` (the deep Kasami differential → L_k factorization).

### `APNCategoryBridge.lean` — The Abstract APN Category ✅ (compiles)

Imports and builds on EquivalentContexts.lean. Provides the categorical framework:

- **APNCert**: Structure with 3 axioms (factorization, kernel bound, coprimality)
- **apn_from_cert**: Categorical APN theorem (sorry-free)
- **goldCert**: Gold certificate (sorry-free — all 3 axioms verified)
- **kasamiCert**: Kasami certificate (1 sorry — kasami_diff_reduces)
- **gold_is_apn**: Gold is APN (sorry-free via bridge)
- **kasami_is_apn**: Kasami is APN (1 sorry)
- **linPoly_kernel_trivial**: ker = {0,1} when gcd(k,n)=1 (sorry-free via bridge chain)
- **Ω-generalization**: Extension to non-Boolean Heyting algebras with proved obstruction
- Detailed bridge diagram explaining how each axiom is proved in a different context

### `CyclotomicBridge.lean` — Cyclotomic Polynomial Bridge ✅ (compiles)

Bridge: d = Φ₃(2^k) connects Kasami to cyclotomic polynomial theory.

### `SpectralDualBridge.lean` — Walsh/Fourier Dual Bridge ✅ (compiles)

The spectral characterization: APN ↔ Walsh coefficient bound.

## Architecture: The Bridge Technique in Action

### How it works (demonstrated with Gold APN)

```
     gold_is_apn (PROVED, sorry-free)
         |
    apn_from_cert (categorical theorem, PROVED)
    /         |         \
 Axiom A    Axiom B     Axiom C
 (PROVED)   (PROVED)    (hypothesis)
    |         |
 Context 2  Context 2 ←bridge→ Context 3 ←bridge→ Context 9
 (Gold diff  (L_k(x)=0          (x^{2^k}=x         (Frobenius
  expansion)  ↔ Frob fixed)      fixed count)        via Mersenne GCD)
```

Each axiom is proved in a **different equivalent context** — the one where it's simplest:
- Axiom A uses char 2 polynomial expansion (Context 2)
- Axiom B crosses bridges 2↔3→9 to use number theory (Mersenne GCD)
- Axiom C is a pure arithmetic hypothesis

### The Bridge Map

```
  ┌─── (1) Differential ───┐
  │          ↕ ✅           │
  │    (2) LinPoly Kernel   │
  │    ✅ ↕       ↕ ✅      │
  │  (3) Frob  (4) Norm-Tr  │
  │   Fixed   ✅ ↕          │
  │  ✅ ↕    (8) Hilbert 90 │
  │  (9) Galois  ✅         │
  │   Descent               │
  │          ↕              │
  │   (5) GF(2)[σ]-module   │
  └──── ✅ ─┬───────────────┘
            ↕
  ┌── (6) Cyclotomic ──┐
  │       ✅ ↕          │
  │  (7) Mult. Order ✅ │
  └─────────┬───────────┘
            ↕
  ┌── (12) Ω-Morphism ─┐
  │       ✅ ↕          │
  │  (13) Non-Boolean ✅│
  └─────────────────────┘
```

## Connection to Caramello's Program

The APNCertificate IS a bridge object in Caramello's sense:

- **T₁** = "Theory of power functions with bounded differentials"
- **T₂** = "Theory of linearized polynomials with small kernels"
- **The bridge**: Cross-term factorization Cross(s,P) = N_k(s) · L_k(P/s)
- **Morita invariant**: "|ker(L_k)| ≤ 2" ↔ "differential uniformity ≤ 2"

The Ω-generalization (Context 13) shows this bridge is **specific to Boolean toposes** — in non-Boolean settings, the cross term doesn't trivialize. This is the topos-theoretic boundary of the theorem.

### Lean's type theory as a topos

The foundational fact that Lean's `Prop` IS the subobject classifier Ω (proved in `RequestProject/Foundations/PropAsOmega.lean`) means the bridge technique is **native** to Lean. Moving between contexts is moving between equivalent formulations within the same topos, using Lean's own internal logic. The bridges are formally verified equivalences, not informal mathematical analogies.
