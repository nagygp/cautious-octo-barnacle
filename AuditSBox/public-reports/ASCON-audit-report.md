# Public Audit Report — ASCON S-Box

**Subject:** the 5-bit ASCON substitution box (Dobraunig–Eichlseder–Mendel–
Schläffer; NIST Lightweight Cryptography winner)
**Method:** machine-checked exhaustive verification (Lean 4 + Mathlib,
`native_decide`)
**Machine-verifiable evidence:** [`../outputs-example/ASCON/`](../outputs-example/ASCON/)
(`Evidence.lean`, `Certificate.md`, `README.md`)

---

## 1. Executive summary

The ASCON S-box is a **sound, lightweight 5-bit S-box** of the Keccak-χ family.
For a 5-bit map its metrics (δ = 8, NL = 8, β = 16) are exactly what one expects
from a low-degree, hardware-cheap, χ-style nonlinear layer: each individual
S-box gives modest standalone resistance, and the cipher recovers full security
through many rounds and a strong linear layer. Every metric below is **proven by
exhaustive machine-checked enumeration**.

**Verdict: ★★☆☆☆** as a standalone S-box (differential bias 2⁻², i.e. 2 bits per
application). This is normal and by design for a lightweight 5-bit S-box — the
rating reflects the per-S-box bias, not a flaw, and must be read together with
ASCON's round count and diffusion.

## 2. The S-box

A 5-bit permutation on GF(2)⁵ (32 elements), an affine-equivalent of the
Keccak χ map. The 32-entry lookup table is reproduced verbatim in the evidence
files.

## 3. Verified security metrics

| Metric | Value | What it means |
|---|---|---|
| Bijective (permutation) | ✓ | The S-box is invertible. |
| Differential uniformity **δ** | **8** | Max DDT entry. Best differential probability is δ/2⁵ = 2⁻². |
| Nonlinearity **NL** | **8** | Distance to the nearest affine function. |
| Max Walsh magnitude **\|W\|** | **16** | Linear-approximation bound; NL = (2⁵ − \|W\|)/2 = 8. |
| Boomerang uniformity **β** | **16** | Max BCT entry (β ≥ δ). |
| Derivative image bound | ≥ 4 | Any nonzero input difference produces ≥ ⌈32/8⌉ = 4 distinct output differences. |
| Differential security | 2 bits | −log₂(δ/2⁵) per S-box invocation. |

## 4. What the numbers mean for an attacker

- **Differential cryptanalysis (δ = 8).** The best single-S-box differential
  holds with probability 8/32 = 2⁻². On its own this is weak, but ASCON applies
  the S-box across many rounds, so trail probabilities multiply down rapidly.
- **Linear cryptanalysis (NL = 8, \|W\| = 16).** Typical for a low-algebraic-
  degree 5-bit S-box chosen for cheap hardware/bitsliced implementation.
- **Boomerang attacks (β = 16).** In line with the differential profile.

These are the per-S-box numbers; ASCON's overall security argument rests on
composing them over its full permutation, which this S-box-level report does not
attempt to evaluate.

## 5. How to verify

```bash
# from the project root
lake build
```

If the build succeeds, every theorem in
[`../outputs-example/ASCON/Evidence.lean`](../outputs-example/ASCON/Evidence.lean)
is proven by the Lean kernel via exhaustive enumeration over all 32 × 32 input
pairs. Trust assumptions: Lean's standard axioms plus the compiled-evaluation
axioms (`Lean.ofReduceBool` / `Lean.trustCompiler`).

## 6. Scope and limitations

This certifies the **S-box in isolation**. A 5-bit S-box necessarily has higher
δ and lower NL than an 8-bit one (the metric ceilings scale with width), so the
two-star rating is *not* comparable to AES on equal footing — a lightweight
cipher deliberately trades per-S-box strength for cheap hardware and recovers
security over many rounds. This report does not evaluate the full ASCON
permutation, its implementation, or its mode of use.

---
*Produced with the `AuditSBox` toolkit (Lean 4 + Mathlib). Reproducible
evidence: [`../outputs-example/ASCON/`](../outputs-example/ASCON/).*
