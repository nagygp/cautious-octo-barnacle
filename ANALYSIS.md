# Analysis: Kasami P₃ and Dual P₃ Formalization

## 1. Executive Summary

The repository contains **six iterations** (`kasami-theory-01` through `kasami-theory-06`) of attempts to formalize the Kasami P₃ triple-intersection equidistribution theorem and its dual in Lean 4. **The theory is NOT complete.** Across all iterations, there are critical `sorry`-marked gaps that prevent full verification of P₃ in its general form. The Gold case (k=1) *is* fully proved in iteration 04. The dual P₃ ↔ P₃ equivalence *is* fully proved in iteration 05. But the general Kasami case has deep unresolved sorries in every iteration.

---

## 2. What P₃ and Its Dual Are

**P₃ (combinatorial):** For `gcd(k,n) = 1`, `n` odd, and all nonzero `v₁ ≠ v₂` in `𝔽_{2^n}`:

```
|{ (x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0 }| = 2^{2n−3}
```

where `Δ = { b^d + (b+1)^d + 1 : b ∈ 𝔽_{2^n} }` and `d = 4^k − 2^k + 1` is the Kasami exponent.

**Dual P₃ (spectral):** The Fourier-analytic reformulation via Pontryagin duality:

```
∑_{ψ ∈ 𝔽̂} Ŝ_ψ(v₁) · Ŝ_ψ(v₂) · Ŝ_ψ(v₁+v₂) = 2^{3n−3}
```

The equivalence P₃ ↔ Dual P₃ is proved in iteration 05 (`DualP3.lean`). The factor connecting them is simply `|𝔽| = 2^n`.

---

## 3. What IS Fully Proved (sorry-free)

### Iteration 04: Gold Case P₃ (k = 1)
- **`gold_P3`** in `GoldP3.lean` — fully verified, 0 sorry, standard axioms only
- For k=1: `Δ = ker(Tr)`, Walsh spectrum analysis via trace annihilator

### Iteration 05: Dual P₃ Equivalence
- **`spectral_eq_count_mul_card`** — the connecting identity between combinatorial and spectral formulations
- **`P3_iff_DualP3`** — full equivalence proof, 0 sorry

### Common Infrastructure (proved across iterations 03/04/06)
| Module | Key Results Proved |
|--------|--------------------|
| Basic.lean | `F2n n = GaloisField 2 n`, char-2 arithmetic |
| Trace.lean | `tr2_sq`, `tr2_surjective`, `tr2_kernel_card`, `tr2_balanced` |
| AdditiveCharacter.lean | `chi_add`, `chi_orthogonality`, `chi_sum` |
| WalshHadamard.lean | Parseval's identity, inversion formula, convolution theorem |
| KasamiExponent.lean | `kasamiExp_coprime`, `kasamiExp_permutation` |
| DifferenceSet.lean | P₁, `deltaCharSum` |
| TripleCount.lean | `tripleCount_charSum_eq`, `tripleCount_from_vanishing` |
| SpectralIdentity.lean | Spectral identity, ratio reduction |
| APN.lean | `deriv_count_even`, `apn_deriv_zero_or_two`, `apn_image_card` |
| ABtoAPN.lean | `apn_deltaGen_two_to_one`, `apn_delta_card` |
| AutoCorrelation.lean | Wiener-Khinchin identity, `scaledWht_power_shift` |
| LinearizedPoly.lean | Artin-Schreier map, kernel analysis |

---

## 4. What Is Still Missing (sorry'd)

The remaining sorries fall into a clear dependency chain. Here they are in logical order:

### Level 0: The Deepest Result
| Sorry | Location | Description |
|-------|----------|-------------|
| **`kasami_is_ab`** | KasamiFunction.lean | The Kasami function `x ↦ x^{4^k-2^k+1}` is Almost Bent (AB) when gcd(k,n)=1 and n is odd |

This is the theorem of Kasami (1971), refined by Canteaut-Charpin-Dobbertin (2000). It requires:
- **Linearized polynomial theory over finite fields** — kernel dimension analysis of `L(x) = x^{2^{2k}} + x^{2^k} + x` over `GF(2^n)`
- **Quadratic form theory over GF(2)** — rank of the quadratic form `Q(x) = Tr(ax^d)`, Gauss sum evaluation
- **Cyclotomic coset analysis** — bounding radical dimension from `gcd(k,n) = 1`

### Level 1: Bridge Theorems
| Sorry | Location | Description |
|-------|----------|-------------|
| **`ab_implies_apn`** | AlmostBent.lean | AB ⟹ APN via fourth moment bound |
| **`ab_implies_vanishing`** | TripleCount.lean | AB ⟹ `AlmostBentVanishing` |
| **`nonzero_triple_sum_vanishes`** | SpectralBridge.lean | ∑_{a≠0} spectral terms vanish for AB |

### Level 2: Supporting Infrastructure
| Sorry | Location | Description |
|-------|----------|-------------|
| **`fourth_moment_deriv_link`** | ABtoAPN.lean | WHT⁴ = 2^n · ∑ N_a(c)² |
| **`scaledWht_ab_spectrum`** | AutoCorrelation.lean | Scaled WHT inherits AB spectrum |
| **`apn_fourth_moment`** | APN.lean | Fourth moment formula for APN functions |

### Level 3: Quadratic Form Theory (Iteration 01)
| Sorry | Location | Description |
|-------|----------|-------------|
| **`radicalDim`** (definition) | QuadraticGF2.lean | Radical dimension of quadratic forms over GF(2) |
| **`gaussSum2_rank_formula_even/odd`** | QuadraticGF2.lean | Gauss sum = ±2^{n−r/2} based on rank parity |
| **`kasamiDerivative_factorization`** | KasamiWalshSpectrum.lean | Derivative factorizes as linearized polynomial |
| **`walsh_as_gaussSum`** | KasamiWalshSpectrum.lean | Walsh coefficient = Gauss sum of quadratic form |
| **`kasami_radical_bound`** | KasamiWalshSpectrum.lean | Radical dim ≤ 1 from gcd(k,n)=1 |

---

## 5. What Is Available in Mathlib

### Present in Mathlib
| Component | Mathlib Location | Status |
|-----------|-----------------|--------|
| `GaloisField 2 n` | `Mathlib.FieldTheory.Finite.GaloisField` | ✅ Full definition and basic API |
| `Algebra.trace` | `Mathlib.RingTheory.Trace.Basic` | ✅ General trace for ring extensions |
| `AddChar` | `Mathlib.Algebra.Group.AddChar` | ✅ Additive characters (basic structure) |
| `gaussSum` | `Mathlib.NumberTheory.GaussSum` | ✅ Gauss sums for multiplicative × additive characters |
| `QuadraticForm` | `Mathlib.LinearAlgebra.QuadraticForm.Basic` | ✅ General quadratic forms over modules |
| Finite field cardinality | `Mathlib.FieldTheory.Finite.Basic` | ✅ `Fintype.card F = p ^ n` |
| Polynomial API | Various | ✅ Extensive |

### NOT in Mathlib (must be built from scratch)
| Component | What's Needed | Difficulty |
|-----------|---------------|-----------|
| **Walsh-Hadamard transform** | Definition, Parseval, inversion, convolution theorem | Medium — the iterations have working versions |
| **Additive character orthogonality** | `∑_ψ ψ(s) = |G| if s=0, else 0` — specifically for the full dual group | Medium — Mathlib has `AddChar` but lacks the complete orthogonality sum over all characters of a finite field |
| **Linearized polynomials over GF(2^n)** | `L(x) = ∑ aᵢ x^{2^i}` is GF(2)-linear, kernel dimension theory | Hard — not in Mathlib at all |
| **Quadratic forms over GF(2)** | Rank analysis, Arf invariant, Gauss sum evaluation for char-2 quadratic forms | Hard — Mathlib's `QuadraticForm` is general but lacks char-2 specific rank/Gauss sum results |
| **APN / Almost Bent function theory** | Definitions, fourth moment identities, spectral characterizations | Hard — entirely missing from Mathlib |
| **Cyclotomic coset theory** | Cosets of powers of 2 modulo 2^n − 1, dimension bounds from gcd conditions | Medium-Hard |
| **Trace specialization to GF(2^n)/GF(2)** | `Tr(x²) = Tr(x)`, surjectivity, balanced fibers, kernel cardinality | Medium — the iterations have working versions |
| **Cross-correlation of m-sequences** | Fundamental to proving `kasami_is_ab` | Very Hard — deep coding theory, not in Mathlib |

---

## 6. External Resources and References

### Primary Mathematical References

1. **Kasami, T. (1971)** — "The weight enumerators for several classes of subcodes of the 2nd order binary Reed-Muller codes." *Information and Control*, 18(4), 369–394.
   - Original proof that the Kasami exponent yields a three-valued Walsh spectrum.

2. **Canteaut, A., Charpin, P., and Dobbertin, H. (2000)** — "Weight divisibility of cyclic codes, highly nonlinear functions on F_{2^m}, and crosscorrelation of maximum-length sequences." *SIAM Journal on Discrete Mathematics*, 13(1), 105–138.
   - Modern proof of the AB property via quadratic form rank analysis.

3. **Carlet, C. (2021)** — *Boolean Functions for Cryptography and Coding Theory.* Cambridge University Press.
   - Chapter 6 covers APN/AB theory, Walsh spectrum, and the connection to P₃. The most complete modern reference.

4. **Gold, R. (1968)** — "Maximal recursive sequences with 3-valued recursive cross-correlation functions." *IEEE Trans. IT*, 14(1), 154–156.
   - The k=1 special case (Gold functions).

5. **Lidl, R. and Niederreiter, H. (1997)** — *Finite Fields.* Cambridge University Press.
   - Standard reference for linearized polynomials (Chapter 3), trace functions, and quadratic forms over finite fields.

6. **Dillon, J. F. and Dobbertin, H. (2004)** — "New cyclic difference sets with Singer parameters." *Finite Fields Appl.*, 10(3), 342–389.
   - P₃-type results for Kasami difference sets.

### Online Resources

7. **Pott, A. (2004)** — "Nonlinear functions in Abelian groups and relative difference sets." *Discrete Applied Mathematics*, 138(1-2), 177–193.
   - Survey connecting APN/AB to difference sets and the spectral approach.

8. **Budaghyan, L. (2014)** — *Construction and Analysis of Cryptographic Functions.* Springer.
   - Modern treatment of power functions over GF(2^n), APN classification.

### Existing Formal Libraries (NOT in Mathlib)

There are **no known external Lean 4 libraries** that formalize:
- Walsh-Hadamard transforms over finite fields
- APN/AB function theory
- Linearized polynomial kernel theory
- Kasami exponent spectral analysis
- P₃ or related difference set properties

Other proof assistants:
- **No known Coq, Isabelle/HOL, or HOL Light formalizations** of the Kasami AB theorem or P₃ exist in public repositories. The closest related work:
  - The **Flocq** library (Coq) has some finite field arithmetic but no spectral/coding theory.
  - **Isabelle AFP** has finite field basics and some coding theory (`Error_Correcting_Codes`) but nothing approaching Kasami theory.
  - **Mathcomp** (Coq) has extensive finite field and polynomial theory that could serve as a foundation, but no APN/AB formalization exists.

---

## 7. Modules That Need to Be Built

To fully prove `kasami_P3` (general case) and close all sorries, the following modules need to be constructed **from scratch** (none exist in Mathlib or known external libraries):

### Tier 1: Foundational (estimated 500-800 lines each)

1. **`LinearizedPoly.lean`** — Comprehensive linearized polynomial theory
   - Definition: `L(x) = ∑ᵢ aᵢ · x^{p^i}` is `GF(p)`-linear
   - Kernel dimension theory: `dim_{GF(p)} ker(L) ≤ deg(L)` (as a p-polynomial)
   - Kernel of `L_k(x) = x^{2^{2k}} + x^{2^k} + x` over `GF(2^n)`
   - GCD condition: `gcd(k,n) = 1 ⟹ dim ker(L_k) = 1`
   - Connection to the Kasami derivative factorization

2. **`QuadraticFormGF2.lean`** — Quadratic forms in characteristic 2
   - Rank and radical of a quadratic form `Q: GF(2)^n → GF(2)`
   - Arf invariant
   - Gauss sum evaluation: `∑_x (-1)^{Q(x)} = ±2^{n - rank(Q)/2}`
   - The quadratic form `Q_a(x) = Tr(a · x^d)` for the Kasami exponent

3. **`FourthMoment.lean`** — Fourth moment identity
   - `∑_a W_f(a)^4 = 2^n · ∑_{a,c} N_a(c)^2` (connecting spectral and differential sides)
   - APN ⟹ specific fourth moment value
   - AB ⟹ APN (the bridge)

### Tier 2: Connecting Theory (estimated 300-500 lines each)

4. **`ABVanishing.lean`** — The vanishing theorem
   - AB spectrum ⟹ autocorrelation structure
   - Autocorrelation ⟹ vanishing of nonzero triple spectral sums
   - Complete proof of `ab_implies_vanishing`

5. **`KasamiAB.lean`** — The deep AB theorem
   - Kasami derivative factorization as linearized polynomial
   - Walsh coefficient = Gauss sum of quadratic form
   - Radical dimension bound from `gcd(k,n) = 1`
   - Three-valued spectrum ⟹ AB
   - Complete proof of `kasami_is_ab`

### Tier 3: Integration (estimated 100-200 lines)

6. **`KasamiP3Complete.lean`** — Assembly
   - `kasami_is_ab` + `ab_implies_vanishing` + `tripleCount_from_vanishing` = `kasami_P3`
   - `P3_iff_DualP3` + `kasami_P3` = `DualP3_holds`

### Estimated Total Effort
- **2,000–4,000 lines** of new Lean 4 code
- The hardest part is Tier 1, particularly the linearized polynomial kernel dimension theory and the char-2 quadratic form Gauss sum evaluation, as these require substantial algebraic infrastructure that has no Lean 4 precedent.

---

## 8. Conclusion

**The fragments in the kasami-theory folders do NOT contain all required modules.** The existing code provides an excellent skeleton (~1,600 lines of working infrastructure per best iteration) but has 7+ deep sorries blocking full verification. These sorries correspond to mathematical results that are:

1. **Not available in Mathlib** — Walsh-Hadamard transforms, APN/AB theory, linearized polynomials, char-2 quadratic form Gauss sums
2. **Not available in any known formal library** — No Lean, Coq, Isabelle, or HOL formalization of the Kasami AB theorem exists publicly
3. **Well-documented in textbooks** — Carlet (2021), Lidl-Niederreiter (1997), and the original papers by Kasami (1971) and Canteaut-Charpin-Dobbertin (2000) contain complete proofs

The Gold case (k=1) is fully proved in iteration 04 and serves as a proof-of-concept. The general case requires formalizing linearized polynomial kernel theory and quadratic form rank analysis from scratch — estimated at several months of focused formalization work.
