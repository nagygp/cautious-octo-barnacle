# 20 New AB & APN Function Conjectures

## Overview

This document summarises 20 new conjectures (10 AB, 10 APN) generated using insights from the topos-theoretic AB/APN framework formalised in this project. All conjectures are formalised in Lean 4 and type-check successfully with zero `sorry`.

---

## Methods

Each conjecture is motivated by one of four structural techniques:

| Method | Description | Conjectures |
|--------|-------------|-------------|
| **Bridge Transfer** | The Bridge Theorem transfers PN counting signatures from GF(p) to GF(2). We "binarise" specific PN exponents to obtain candidate AB/APN power maps. | AB1–AB3, APN1–APN3 |
| **Exp ↔ Log Conjugation** | The discrete log map conjugates multiplicative power maps to additive maps on indices. We apply nonlinear perturbations in the log domain (quadratic, Frobenius, composition) and lift back. | AB4–AB6, APN4–APN6 |
| **Spectral/Kerdock Construction** | The Kerdock correspondence and Pless moment decomposition constrain APN functions. We conjecture sufficiency conditions and even-dimensional generalisations. | AB7–AB8, APN7–APN8 |
| **Isotopy/Lifting** | CCZ-isotopy from known sporadic examples, Walsh self-duality, and representation-theoretic transfer from non-abelian groups. | AB9–AB10, APN9–APN10 |

---

## 10 AB Conjectures (`NewABConjectures.lean`)

| # | Name | Exponent / Construction | Source Insight |
|---|------|------------------------|----------------|
| AB1 | Coulter–Matthews Boolean Relative | x^{2^k + 2^{⌊k/2⌋} + 1} | Binarise CM exponent (3^k+1)/2 via Bridge Theorem |
| AB2 | Ding–Helleseth Boolean Relative | x^{2^{2k} + 2^k + 1} | Binarise DH exponent; structurally = Kasami |
| AB3 | Helleseth–Rong Boolean Relative | x^{2^k + 3} (k ≥ 2) | Binarise HR exponent 3^k + 2 |
| AB4 | Log-Domain Gold + Carry | i ↦ (2^k+1)i + ⌊i²/(2^n-1)⌋ | Quadratic perturbation in log domain |
| AB5 | Frobenius-Twisted Kasami | x^{2·(2^{2k} - 2^k + 1)} | Frobenius x↦x² composed with Kasami in log domain |
| AB6 | Double-Gold Composition | x^{(2^j+1)(2^k+1)} | Gold∘Gold via exp–log bridge |
| AB7 | Kerdock Sufficiency | Spectral signature constraint | Converse of Kerdock correspondence |
| AB8 | Homotopical Characterisation | Postnikov tower discrete ⟺ AB | Converse of `bent_implies_discrete` |
| AB9 | Walsh Self-Dual AB | Existence for each odd n ≥ 5 | Self-duality of bridge fixed point |
| AB10 | S₃-Transferred AB | x^6 | Representation theory of S₃ via pipeline theorem |

---

## 10 APN Conjectures (`NewAPNConjectures.lean`)

| # | Name | Exponent / Construction | Source Insight |
|---|------|------------------------|----------------|
| APN1 | CM Transfer (Even Dim) | x^{2^k + 2^{⌊k/2⌋} + 1} on GF(2^{2m}) | Bridge Theorem to even dimension |
| APN2 | Frobenius-Chain DO | x^{2^s+1} + x^{2^{2s}+2^s} + x^{2^{3s}+2^{2s}} | 3-term Dembowski–Ostrom polynomial |
| APN3 | Dual Inverse (Even Dim) | x^{2^n-2} + x^{2^n-1} | Trace-corrected inverse via dual Heyting algebra |
| APN4 | Log-Quadratic Gold | i ↦ (2^k+1)i + i² (mod 2^n-1) | Quadratic perturbation in log domain |
| APN5 | Log-Inverse | i ↦ i⁻¹ (mod 2^n-1) for Mersenne primes | Compositional inverse in log domain |
| APN6 | Even-Dim Niho Transfer | x^{2^m + 2^{m/2} - 1} on GF(2^{2m}) | Niho exponent transferred to even dimension |
| APN7 | 5-Weight Kerdock | 5-weight code characterisation | Even-dim analogue of 3-weight Kerdock |
| APN8 | 5-Moment Sufficiency | Pless moments determine APN | Extended Pless moment decomposition |
| APN9 | Sporadic APN Lifting | Non-power APN for all even n ≥ 8 | Lifting Dillon–McGuire from dimension 6 |
| APN10 | Boolean Relative Existence | ∃ APN on GF(2^n) for all even n ≥ 6 | Strongest form of Bridge Theorem prediction |

---

## Key Design Principles

1. **Even-dimension focus for APN**: Conjectures APN1, APN2, APN3, APN6, APN7, APN9, APN10 specifically target even dimensions, where the APN classification is most open (no AB bridge, no sporadic examples beyond n = 6).

2. **Non-power functions**: APN2, APN4, APN5, APN9 propose non-power-map APN functions, addressing the possibility that new APN functions may lie outside the power-map paradigm.

3. **Bridge Theorem consistency**: All conjectures are verified to be consistent with the Bridge Theorem's predicted counting signature 2^{(m-1)n - m}, as proved by `ab_conjectures_bridge_consistent` and `apn_new_conjectures_bridge_compatible`.

4. **Formal well-formedness**: Every conjecture type-checks as a well-formed `Prop` in Lean 4, confirmed by `ab_conjectures_well_formed` and `apn_new_conjectures_well_formed`.

---

## Files

| File | Contents |
|------|----------|
| `NewABConjectures.lean` | 10 AB conjectures + structural verification theorems |
| `NewAPNConjectures.lean` | 10 APN conjectures + structural verification theorems |
| `NEW_CONJECTURES_SUMMARY.md` | This summary |
