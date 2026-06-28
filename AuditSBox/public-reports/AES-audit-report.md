# Public Audit Report — AES (Rijndael) S-Box

**Subject:** the 8-bit AES / Rijndael substitution box (FIPS 197;
Daemen–Rijmen, 1998)
**Method:** machine-checked exhaustive verification (Lean 4 + Mathlib,
`native_decide`)
**Machine-verifiable evidence:** [`../outputs-example/AES/`](../outputs-example/AES/)
(`Evidence.lean`, `Certificate.md`, `README.md`)

---

## 1. Executive summary

The AES S-box is, by these metrics, a **best-in-class 8-bit S-box**. It attains
the best known differential uniformity (δ = 4) and the maximum possible
nonlinearity (NL = 112) for an 8-bit permutation, and a low boomerang
uniformity (β = 6). Every one of these properties is **proven by exhaustive
machine-checked enumeration**, not merely measured — anyone can re-run the build
and obtain the same theorems.

**Verdict: ★★★★☆** (strong; the only thing keeping it from five stars is that
δ = 4 rather than the theoretical optimum δ = 2, which no 8-bit permutation is
known to reach).

## 2. The S-box

An 8-bit permutation on GF(2)⁸ (256 elements), built as multiplicative
inversion in GF(2⁸) (with 0 ↦ 0) followed by a GF(2)-affine map:
`S(x) = A·x⁻¹ + c`, with `c = 0x63`. The 256-entry lookup table is reproduced
verbatim in the evidence files.

## 3. Verified security metrics

| Metric | Value | What it means |
|---|---|---|
| Bijective (permutation) | ✓ | The S-box is invertible. |
| Differential uniformity **δ** | **4** | Max DDT entry. Best probability of a differential is δ/2⁸ = 2⁻⁶. |
| Nonlinearity **NL** | **112** | Distance to the nearest affine function. This is the maximum for 8-bit S-boxes. |
| Max Walsh magnitude **\|W\|** | **32** | Linear-approximation bound; NL = (2⁸ − \|W\|)/2 = 112. |
| Boomerang uniformity **β** | **6** | Max BCT entry. Always β ≥ δ; here only slightly above. |
| Derivative image bound | ≥ 64 | Any nonzero input difference produces ≥ ⌈256/4⌉ = 64 distinct output differences. |
| Differential security | 6 bits | −log₂(δ/2⁸) per S-box invocation. |

Each value is **tight**, and that tightness is also proven: the certificate
verifies both that δ ≤ 4 *and* that δ ≰ 2 (so δ = 4 exactly), and likewise that
\|W\| ≤ 32 but \|W\| ≰ 31 (so \|W\| = 32 exactly).

## 4. What the numbers mean for an attacker

- **Differential cryptanalysis (δ = 4).** An attacker chooses an input
  difference and predicts an output difference; the best single-S-box success
  probability is 4/256 = 2⁻⁶. Lower is better; 4 is the best achieved by any
  known 8-bit permutation.
- **Linear cryptanalysis (NL = 112).** The S-box is maximally far from every
  linear/affine approximation an attacker could use. 112 is the ceiling for
  8-bit S-boxes.
- **Boomerang attacks (β = 6).** Boomerang-style differentials are also tightly
  constrained; β = 6 is close to the differential floor.

These reproduce the long-established public values for AES; the contribution of
this report is that they are now re-checkable theorems.

## 5. How to verify

```bash
# from the project root
lake build
```

If the build succeeds, every theorem in
[`../outputs-example/AES/Evidence.lean`](../outputs-example/AES/Evidence.lean)
(bijectivity, δ ≤ 4 and tight, \|W\| ≤ 32, β ≤ 6) is proven by the Lean kernel.
The proofs use only `native_decide`, i.e. exhaustive enumeration over all
256 × 256 input pairs; the only trust assumptions are Lean's standard axioms
plus the compiled-evaluation axioms (`Lean.ofReduceBool` / `Lean.trustCompiler`).

## 6. Scope and limitations

This certifies the **S-box in isolation** — its differential, linear, and
boomerang profile. It does not certify the full AES cipher, its implementation,
key schedule, side-channel resistance, or protocol usage. A strong S-box is
necessary but not sufficient for a secure cipher.

---
*Produced with the `AuditSBox` toolkit (Lean 4 + Mathlib). Reproducible
evidence: [`../outputs-example/AES/`](../outputs-example/AES/).*
