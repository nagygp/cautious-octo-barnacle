# Roadmap: What's Needed to Complete the Kasami-is-AB Formalization

## Executive Summary

Your proposed chain **trace ↔ additive characters → Walsh = trace-sum form → |W|² expansion → orthogonality → contraction** is essentially correct, but you already have most of it formalized. The real gaps are narrower and deeper than "Level 2 harmonic analysis." Here's a precise diagnosis.

---

## What You Already Have (Done ✔)

### Level 1: Algebraic Infrastructure ✔
| Component | File | Status |
|-----------|------|--------|
| Absolute trace Tr : F_{2^n} → F_2 | `Kasami/Trace.lean` | ✔ Proved |
| Tr(x^{2^k}) = Tr(x) (Frobenius invariance) | `Kasami/Trace.lean` | ✔ Proved |
| Trace surjectivity, kernel card = 2^{n-1} | `Kasami/Trace.lean` | ✔ Proved |
| Frobenius adjoint Tr(cy^{2^k}) = Tr(c^{2^j}y) | `Kasami/FrobeniusAdjoint.lean` | ✔ Proved |
| Trace nondegeneracy | `Kasami/FrobeniusAdjoint.lean` | ✔ Proved |
| Kasami exponent d = 4^k - 2^k + 1 | `Kasami/KasamiExponent.lean` | ✔ Proved |
| d·(2^k+1) = 2^{3k}+1 | `Kasami/QuadFormBridge.lean` | ✔ Proved |

### Your Proposed Chain — Status

| Step | Status | Location |
|------|--------|----------|
| **trace ↔ additive characters** | ✔ DONE | `Kasami/AdditiveCharacter.lean`: χ(x) = (-1)^{Tr(x)}, χ(x+y) = χ(x)·χ(y) |
| **Walsh = trace-sum form** | ✔ DONE | `Kasami/WalshHadamard.lean`: W_f(a) = ∑_x χ(ax + f(x)) |
| **\|W\|² expansion** | ✔ DONE | `Kasami/WalshHadamard.lean`: `wht_parseval` ∑_a W_f(a)² = (2^n)² |
| **Orthogonality** | ✔ DONE | `Kasami/AdditiveCharacter.lean`: `chi_orthogonality` ∑_x χ(ax) = 0 for a≠0 |
| **Contraction (Wiener-Khinchin)** | ✔ DONE | `Kasami/FourthMoment.lean`: ∑_a W_f(a)⁴ = 2^n · ∑_t R(t)² |

You also have:
- WHT inversion formula ✔
- WHT² = Fourier transform of autocorrelation ✔  
- AB fourth moment identity ✔
- AB ↔ spectrum characterization ✔

**So Level 2 "harmonic analysis" is actually ~90% done, not "PARTIAL."**

---

## What's Actually Missing: 3 Specific Gaps

### Gap 1: Gauss Sum Evaluation for GF(2) Quadratic Forms ❌
**File:** `Kasami/KasamiABProof.lean`, theorem `gf2_gauss_sum_sq'`

**What it says:** For a GF(2)-quadratic form Q of rank r on F_{2^n}:  
S(Q)² = 2^{2n-r}

**What you have:** The framework in `QuadFormGF2/GaussSum.lean` already proves:
- S(Q)² = |V| · |rad(Q)| when Q vanishes on rad(Q) ✔
- S(Q) = 0 when Q doesn't vanish on rad(Q) ✔

**What's missing:** The connection between |rad(Q)| and the rank r. Specifically:
- |rad(Q)| = 2^{n-r} where r = rank of the associated bilinear form
- For the Gold quadratic form Q_a(x) = Tr(ax^{2^k+1}), the radical has exactly 2 elements (proved as `radical_linearized_poly_card` ← **sorry**)

**Textbook reference:** 
- **Lidl & Niederreiter, *Finite Fields* (1997)**, Theorem 6.26–6.27: Gauss sums of quadratic forms over finite fields
- **MacWilliams & Sloane, *Theory of Error-Correcting Codes* (1977)**, Chapter 15 §5: "Quadratic forms and self-dual codes"  
- **Carlet, *Boolean Functions for Cryptography and Coding Theory* (2021)**, §4.2: Exponential sums of quadratic forms

### Gap 2: Radical Cardinality = 2 ❌
**File:** `Kasami/RadicalCard.lean`, theorem `radical_linearized_poly_card`

**What it says:** The kernel of P(z) = a^{2^k}·z^{2^{2k}} + a·z has exactly 2 elements when a ≠ 0, n odd, gcd(k,n) = 1.

**What you have:**
- `coprime_2k_of_odd`: gcd(2k,n) = 1 ✔
- `mersenne_coprime`: gcd(2^a-1, 2^b-1) = 1 when gcd(a,b) = 1 ✔  
- `pow_bijective_of_coprime_order`: z ↦ z^d bijective when gcd(d, |F|-1) = 1 ✔

**What's missing:** The key step: P(z) = a·(a^{2^k-1}·z^{2^{2k}-1} + 1)·z = 0. For z≠0 this gives z^{2^{2k}-1} = a^{1-2^k}. Since gcd(2k,n) = 1 ⟹ gcd(2^{2k}-1, 2^n-1) = 1 (by Mersenne coprimality), the map z ↦ z^{2^{2k}-1} is a bijection on F_{2^n}^*, giving exactly 1 nonzero solution.

**Textbook reference:**
- **Lidl & Niederreiter, *Finite Fields***, §3.4: Linearized polynomials and their kernels
- **Carlet, *Boolean Functions***, Proposition 6.14: Kernel analysis of x^{2^{2k}} + x

### Gap 3: CCD Kernel Step / Derivative Triple Product ❌
**Files:** `Kasami/KasamiNormIdentity.lean` (`ccd_kernel_step'`), `Kasami/ABVanishing.lean` (`deriv_triple_product_vanishes'`), `Kasami/TripleCount.lean` (`ab_implies_vanishing`)

These are the "deep spectral" results needed for the APN direction of the proof. They are **not needed for kasami_is_ab** if you take the direct Gauss sum route (Gaps 1-2 suffice).

---

## Would Your Proposed Chain Suffice?

**For `kasami_is_ab` (the main theorem): Almost.**

Your chain covers Level 2 harmonic analysis, which is already done. What remains is:

1. **Radical cardinality = 2** (Gap 2) — this is pure algebra, not harmonic analysis
2. **Gauss sum² = |V|·|rad|** (Gap 1) — this IS in your `QuadFormGF2/GaussSum.lean` already  
3. **Connecting the pieces** (Gap 1 + Gap 2 → `kasami_wht_sq_values'`)

So the answer is: **your chain is correct but already built.** The remaining work is:
- One linearized polynomial kernel count (algebra, not harmonic analysis)
- One assembly lemma connecting existing pieces

**For the APN-direction results**: Gap 3 is genuinely hard and needs the derivative/autocorrelation machinery (which you have) plus a deep spectral cancellation argument. This direction is **not needed** for the AB theorem itself.

---

## Which Textbooks Cover What

### For the Radical Count (Gap 2) — Pure Algebra

| Book | Chapter | Content |
|------|---------|---------|
| **Lidl & Niederreiter, *Finite Fields*** | Ch. 3 §4 | Linearized polynomials, kernel dimension = gcd |
| **Lidl & Niederreiter** | Ch. 2 §3 | Trace, Frobenius, adjoint (you have this) |
| **Carlet, *Boolean Functions*** | Ch. 6 §4 | Gold function analysis, radical of B_a |

**Key result:** For a linearized polynomial L(z) = ∑ c_i z^{2^i} over GF(2^n), the kernel is a GF(2)-vector space. Its dimension equals the degree of gcd(L, x^{2^n} - x) as a linearized polynomial. This is in Lidl-Niederreiter Theorem 3.62.

### For the Gauss Sum Evaluation (Gap 1) — Quadratic Form Theory

| Book | Chapter | Content |
|------|---------|---------|
| **MacWilliams & Sloane, *Theory of Error-Correcting Codes*** | Ch. 15 §5 | Self-dual codes, quadratic forms over GF(2), weight distributions via Gauss sums |
| **Carlet, *Boolean Functions*** | Ch. 4 §2 | S(Q)² = 2^{2n-r}, rank theory |
| **Lidl & Niederreiter** | Ch. 6 §2 | Exponential sums, character sums, Gauss sums |

**You already have the key theorem** (`expSum_sq_eq_card_mul_radical_card` in `QuadFormGF2/GaussSum.lean`). You just need to specialize it.

### For the Full "Harmonic Analysis" Layer — Which You Already Have

| Book | Chapter | Content |
|------|---------|---------|
| **Carlet, *Boolean Functions*** | Ch. 4 §1 | Walsh-Hadamard transform, Parseval |
| **Carlet** | Ch. 6 §2 | Fourth moment, Wiener-Khinchin |
| **Ceccherini-Silberstein, Scarabotti, Tolli, *Harmonic Analysis on Finite Groups*** | Ch. 1-3 | General Fourier analysis on finite abelian groups |
| **Terras, *Fourier Analysis on Finite Groups*** | Ch. 1-2 | Character theory, orthogonality |

These books cover what you've already formalized in `WalshHadamard.lean`, `AdditiveCharacter.lean`, and `FourthMoment.lean`.

---

## Recommended Next Steps (Priority Order)

### Step 1: Prove `radical_linearized_poly_card` (Gap 2)
This is the most tractable remaining sorry. The proof is:
1. Factor P(z) = a · z · (a^{2^k-1} · z^{2^{2k}-1} + 1) (need char 2: -a = a)
2. For z = 0: always a solution ✔
3. For z ≠ 0: need z^{2^{2k}-1} = a^{1-2^k}, which has exactly 1 solution because gcd(2^{2k}-1, 2^n-1) = 1 (by `mersenne_coprime` + `coprime_2k_of_odd`)

### Step 2: Connect `expSum_sq_eq_card_mul_radical_card` to `gf2_gauss_sum_sq'`
Specialize the abstract quadratic form Gauss sum result to the Gold quadratic form Q_a.

### Step 3: Prove `kasami_wht_sq_values'`
This assembles everything: WHT of Kasami = Gauss sum of Gold (via CCD) → |radical| = 2 → rank = n-1 → S(Q)² = 2^{n+1} or 0.

---

## Summary

```
Your proposed chain:                Already formalized?
─────────────────────               ──────────────────
trace                               ✔ Trace.lean
  ↕                                 
additive characters                 ✔ AdditiveCharacter.lean
  ↕
Walsh = trace-sum form              ✔ WalshHadamard.lean
  ↕
|W|² expansion (Parseval)           ✔ WalshHadamard.lean
  ↕
orthogonality                       ✔ AdditiveCharacter.lean
  ↕
contraction (Wiener-Khinchin)       ✔ FourthMoment.lean

What's ACTUALLY missing:
─────────────────────────
radical_linearized_poly_card        ❌ (algebra, not harmonic analysis)
gf2_gauss_sum_sq' specialization    ❌ (connecting existing pieces)
kasami_wht_sq_values' assembly      ❌ (final assembly)
```

**Bottom line:** The harmonic analysis layer IS built. The gap is in the algebra (linearized polynomial kernel count) and in connecting the already-proved abstract Gauss sum theorem to the specific Gold quadratic form. Two targeted proofs would close the main theorem.
