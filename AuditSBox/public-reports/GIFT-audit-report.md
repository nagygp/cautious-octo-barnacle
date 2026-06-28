# Public Audit Report — GIFT S-Box

**Subject:** the 4-bit GIFT substitution box (Banik–Pandey–Peyrin–Sasaki–Sim–
Todo, CHES 2017; used in GIFT-64 / GIFT-128 and GIFT-COFB)
**Method:** machine-checked exhaustive verification (Lean 4 + Mathlib,
`native_decide`)
**Machine-verifiable evidence:** [`../outputs-example/GIFT/`](../outputs-example/GIFT/)
(`Evidence.lean`, `Certificate.md`, `README.md`)

---

## 1. Executive summary

The GIFT S-box is an **ultra-lightweight 4-bit S-box** optimized for the
smallest possible hardware footprint. Judged purely in isolation it is the
weakest of the three ciphers in this portfolio (δ = 6, NL = 4), which is an
explicit design trade-off: GIFT spends its security budget on a very cheap S-box
plus a carefully chosen bit-permutation linear layer and a high round count.
Every metric below is **proven by exhaustive machine-checked enumeration**.

**Verdict: ★☆☆☆☆** as a standalone S-box (differential bias δ/2⁴ = 6/16, about
1.42 bits per application). This low standalone rating is expected for an
ultra-lightweight design and must be read together with GIFT's diffusion and
round count, not as a defect.

## 2. The S-box

A 4-bit permutation on GF(2)⁴ (16 elements). The 16-entry lookup table is
`#[1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]` (reproduced in the
evidence files).

## 3. Verified security metrics

| Metric | Value | What it means |
|---|---|---|
| Bijective (permutation) | ✓ | The S-box is invertible. |
| Differential uniformity **δ** | **6** | Max DDT entry. Best differential probability is δ/2⁴ = 6/16 = 0.375. |
| Nonlinearity **NL** | **4** | Distance to the nearest affine function. |
| Max Walsh magnitude **\|W\|** | **8** | Linear-approximation bound; NL = (2⁴ − \|W\|)/2 = 4. |
| Boomerang uniformity **β** | **16** | Max BCT entry (β ≥ δ). |
| Derivative image bound | ≥ 3 | Any nonzero input difference produces ≥ ⌈16/6⌉ = 3 distinct output differences. |
| Differential security | ≈ 1.42 bits | −log₂(δ/2⁴) per S-box invocation. |

Note that δ = 6 is **above** the optimum δ = 4 for a 4-bit permutation: GIFT
deliberately accepts a weaker S-box than the best possible 4-bit map (e.g.
PRESENT achieves δ = 4) in exchange for a smaller circuit.

## 4. What the numbers mean for an attacker

- **Differential cryptanalysis (δ = 6).** A single-S-box differential can hold
  with probability up to 6/16. GIFT compensates with its bit-permutation layer
  and many rounds, so that long trails still have negligible probability.
- **Linear cryptanalysis (NL = 4, \|W\| = 8).** Modest, as expected for a 4-bit
  S-box chosen for minimal area.
- **Boomerang attacks (β = 16).** The boomerang profile is correspondingly loose
  at the S-box level.

## 5. How to verify

```bash
# from the project root
lake build
```

If the build succeeds, every theorem in
[`../outputs-example/GIFT/Evidence.lean`](../outputs-example/GIFT/Evidence.lean)
is proven by the Lean kernel via exhaustive enumeration over all 16 × 16 input
pairs. Trust assumptions: Lean's standard axioms plus the compiled-evaluation
axioms (`Lean.ofReduceBool` / `Lean.trustCompiler`).

## 6. Scope and limitations

This certifies the **S-box in isolation**. GIFT's security argument is a
*whole-cipher* one — cheap S-box plus strong linear layer plus high round count
— so a one-star S-box rating is a statement about the component, not the cipher.
This report does not evaluate the full GIFT cipher, its implementation, or its
mode of use.

---
*Produced with the `AuditSBox` toolkit (Lean 4 + Mathlib). Reproducible
evidence: [`../outputs-example/GIFT/`](../outputs-example/GIFT/).*
