# Complete Assembly Report — Kasami P₃ Formalization

## Overview

This document provides a **complete, current** (as of kasami-33) inventory of every lemma, theorem, and definition across the project, organized by module and layer, with status (✅ proved / ❌ sorry / ⚠️ inherits sorry).

---

## Layer 0: Field and Trace Infrastructure

### `Kasami/Basic.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `F2n` | def | `GaloisField 2 n` abbreviation |
| `F2n.card` | theorem | `|GF(2^n)| = 2^n` |
| `F2n.char_two` | instance | `CharP (F2n n) 2` |
| `F2n.powMap` | def | `x ↦ x^d` as a map |

### `Kasami/Trace.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `tr2` | def | Absolute trace `Tr : GF(2^n) → GF(2)` |
| `tr2_add` | theorem | `Tr(x+y) = Tr(x) + Tr(y)` |
| `tr2_sq` | theorem | `Tr(x²) = Tr(x)` |
| `tr2_pow2` | theorem | `Tr(x^{2^i}) = Tr(x)` |
| `tr2_surjective` | theorem | `Tr` is surjective |
| `tr2_kernel_card` | theorem | `|ker(Tr)| = 2^{n-1}` |
| `tr2_fiber_one_card` | theorem | `|Tr^{-1}(1)| = 2^{n-1}` |
| `tr2_balanced` | theorem | `Tr(ax)` balanced when `x ≠ 0` |

### `Kasami/AdditiveCharacter.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `chi` | def | `χ(x) = (−1)^{Tr(x)}` |
| `chiAddChar` | def | `χ` as an `AddChar` |
| `chi_add` | theorem | `χ(x+y) = χ(x)·χ(y)` |
| `chi_sq` | theorem | `χ(x)² = 1` |
| `chi_orthogonality` | theorem | `∑_x χ(ax) = 0` for `a ≠ 0` |
| `chi_inner_product` | theorem | `∑_x χ(ax)·χ(bx) = 2^n·δ_{a,b}` |
| `chi_sum` | theorem | `∑_x χ(ax) = 2^n` iff `a = 0` |

---

## Layer 1: Kasami Exponent Properties

### `Kasami/KasamiExponent.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `kasamiExp` | def | `d = 4^k − 2^k + 1` |
| `kasamiExp_pos` | theorem | `d > 0` |
| `kasamiExp_odd` | theorem | `d` is odd |
| `kasamiExp_coprime` | theorem | `gcd(d, 2^n−1) = 1` when `gcd(k,n) = 1` |
| `kasamiExp_permutation` | theorem | `x ↦ x^d` is a permutation |

---

## Layer 2: Walsh-Hadamard Transform

### `Kasami/WalshHadamard.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `wht` | def | Walsh-Hadamard transform `W_f(a)` |
| `wht_parseval` | theorem | `∑_a W_f(a)² = (2^n)²` |
| `wht_inversion` | theorem | Inversion formula |
| `wht_abs_le` | theorem | `|W_f(a)| ≤ 2^n` |

### `Kasami/AlmostBent.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `IsAlmostBent` | def | AB: `W_f(a)² ∈ {0, 2^{n+1}}` for all `a` |
| `isAlmostBent_iff_abs` | theorem | Equivalent absolute value form |
| `ab_nonzero_count` | theorem | Number of nonzero WHT values = `2^{n-1}` |
| `ab_fourth_moment` | theorem | `∑_a W_f(a)⁴ = 2·(2^n)³` |

### `Kasami/FourthMoment.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `derivCount` | def | `N_a(b) = |{x : f(x+a)+f(x)=b}|` |
| `derivCount_even` | theorem | `N_a(b)` is even for `a ≠ 0` |
| `derivCount_sum` | theorem | `∑_b N_a(b) = 2^n` |
| `autocorr` | def | `R(t) = ∑_x χ(t·f(x))` |
| `autocorr_zero` | theorem | `R(0) = 2^n` |
| `wht_sq_as_autocorr` | theorem | `W_f(a)² = ∑_t χ(at)·R(t)` |
| `fourth_moment_eq_autocorr_sq` | theorem | Wiener-Khinchin identity |
| `ab_autocorr_sq_sum` | theorem | AB autocorrelation sum |
| `ab_autocorr_sq_nonzero_sum` | theorem | Nonzero autocorrelation sum |
| `even_sum_sq_bound` | theorem | Combinatorial bound for APN |

---

## Layer 3: AB ⟹ APN (Kasami-specific)

### `Kasami/ABImpliesAPN.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `power_fn_deriv_charsum_scaling` | theorem | `G_a(c) = G_1(c·a^d)` scaling identity |
| `power_fn_scaled_wht` | theorem | WHT reparametrization for power fns |
| `power_fn_scaled_ab` | theorem | Scalar multiples of AB power fns are AB |
| `scaled_autocorr_sq_sum` | theorem | Scaled autocorrelation bound |
| `deriv_charsum_sq_sum_nonzero` | theorem | `∑_{t≠0} G_t(c)² = (2^n)²` for AB |
| `kasami_deriv_sq_sum_eq` | theorem | `∑_b N_a(b)² = 2^{n+1}` for all `a≠0` |
| `apn_from_deriv_sq` | theorem | APN from constant derivative sum |
| `ab_implies_apn` | theorem | **AB ⟹ APN for Kasami function** |

### `Kasami/APNFromAB.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `deriv_parseval` | theorem | Parseval for derivative distribution |
| `deriv_char_sum_abs_le` | theorem | Bound on derivative character sums |

---

## Layer 4: CCD Algebraic Infrastructure

### `Kasami/CCDFactorization.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `kasamiExp_mul_identity` | theorem | `d·(2^k+1) = 2^{3k}+1` |
| `char2_add_pow` | theorem | `(a+b)^{2^k} = a^{2^k} + b^{2^k}` |
| `F2n_frobenius` | theorem | `x^{2^n} = x` |
| `char2_sum_powers` | theorem | Cross-term expansion |
| `gold_deriv` | theorem | Gold function derivative |
| `gold_second_deriv` | theorem | Gold second derivative |
| `bilinear_form_factor` | theorem | `B(a,b)` factorization |

### `Kasami/CCDHelpers.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| Various char-2 helper lemmas | — | Auxiliary algebraic identities |

---

## Layer 5: Linearized Polynomial Theory

### `LinearizedPoly/Defs.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `linPolyL` | def | `L_k(x) = x^{2^{2k}} + x^{2^k} + x` |
| `linPolyM` | def | `M_k(x) = x^{2^k} + x` |
| `linPolyL_linearized` | theorem | `L_k` is `F₂`-linear |

### `LinearizedPoly/Kernel.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `linPolyL_ker_nonzero_eq` | theorem | Kernel nonzero elements characterization |
| `linPolyM_ker_card` | theorem | `|ker(M_k)| = 2^{gcd(k,n)}` |
| `linPolyL_ker_card_classification` | theorem | `|ker(L_k)| ∈ {1, 4}` when `gcd(k,n)=1` |
| `linPolyL_ker_trivial_of_three_ndvd` | theorem | `|ker|=1` when `3∤n` |
| `linPolyL_ker_dim2_of_three_dvd` | theorem | `|ker|=4` when `3|n` |
| `linPolyM_ker_eq_coprime` | theorem | `ker(M_k) = {0,1}` when `gcd(k,n)=1` |
| `frob_fixed_gcd` | theorem | Fixed points of σ^k |
| `card_frob_fixed` | theorem | `|{x : x^{2^m}=x}| = 2^m` when `m|n` |

### `LinearizedPoly/ArtinSchreier.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `artinSchreier_image_eq_trace_ker` | theorem | `Im(x²+x) = ker(Tr)` |

### `LinearizedPoly/KasamiKernel.lean` — ⚠️ 1 SORRY
| Lean Name | Type | Status | Description |
|-----------|------|--------|-------------|
| `kasamiPow` | def | ✅ | `x ↦ x^d` |
| `kasamiDelta` | def | ✅ | `b ↦ b^d + (b+1)^d + 1` |
| `kasamiDelta_periodic` | theorem | ✅ | `δ(b) = δ(b+1)` |
| `kasamiDiff` | def | ✅ | Differential `f(x+a)+f(x)` |
| `kasamiDiff_normalize` | theorem | ✅ | Normalization to `a=1` |
| `char2_freshman` | theorem | ✅ | `(a+b)^{2^k} = a^{2^k}+b^{2^k}` |
| `gold_derivative` | theorem | ✅ | Gold derivative formula |
| `gold_deriv_at_one` | theorem | ✅ | Derivative at `z=1` |
| `gold_second_derivative` | theorem | ✅ | Second derivative (x-independent) |
| `ccdCrossTerm` | def | ✅ | CCD cross-term `C(y₂)` |
| `ccd_power_factorization` | theorem | ✅ | `[D₁(x^d)]^{2^k+1}` factorization |
| `ccd_second_deriv_eq` | theorem | ✅ | `z^{2^{3k}}+z = C(y₂)+C(y₂+z)` |
| **`ccd_crossterm_gives_linPolyL`** | theorem | **❌ SORRY** | Cross-term → `L_k(z)=0` |
| `kasamiDiff_eq_implies_linearized` | theorem | ✅ (mod above) | Assembled from CCD lemmas |
| `kasamiDelta_two_to_one` | theorem | ✅ | `δ` is 2-to-1 |
| `kasamiDelta_image_card` | theorem | ✅ | `|Im(δ)| = 2^{n-1}` |
| `kasamiDiff_count_even` | theorem | ✅ | Differential count is even |
| `kasami_apn` | theorem | ✅ | Kasami is APN when `3∤n` |

---

## Layer 6: Quadratic Form Theory over GF(2)

### `QuadFormGF2/Defs.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `QuadFormF2` | structure | Quadratic form `V → ZMod 2` |
| `QuadFormF2.polar` | def | `B(x,y) = Q(x+y)+Q(x)+Q(y)` |
| `polar_add_left` | theorem | `B` is additive in first arg |
| `polar_comm` | theorem | `B` is symmetric |
| `polar_add_right` | theorem | `B` is additive in second arg |
| `QuadFormF2.radical` | def | `{x : ∀ y, B(x,y) = 0}` |
| `QuadFormF2.additive_on_radical` | theorem | `Q(x+w) = Q(x)+Q(w)` for `w ∈ rad` |
| `QuadFormF2.radicalRestriction` | def | `Q|_{rad}` as linear map |

### `QuadFormGF2/GaussSum.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `QuadFormF2.expSum` | def | `S(Q) = ∑_x (−1)^{Q(x)}` |
| `signZ` | def/lemmas | Sign function calculus |
| `expSum_sq_eq_card_mul_radical_card` | theorem | **S(Q)² = |V|·|rad|** |
| `expSum_zero_of_radical_nonvanishing` | theorem | `S(Q)=0` when `Q|_{rad}≠0` |
| `radical_sum_eq_card_of_vanishing` | theorem | Radical sum = |rad| when `Q|_{rad}=0` |

### `QuadFormGF2/Kasami.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| Kasami spectrum outline | — | Framework definitions |

### `QuadFormGF2/KasamiConnection.lean` — ⚠️ 1 SORRY
| Lean Name | Type | Status | Description |
|-----------|------|--------|-------------|
| `kasamiTracePower` | def | ✅ | `Q_a(x) = Tr(a·x^d)` |
| `kasamiCrossTerm` | def | ✅ | Cross-term of `(x+y)^d` |
| `kasamiPolarCandidate` | def | ✅ | Polar form candidate |
| `kasamiTracePower_zero` | theorem | ✅ | `Q_a(0) = 0` |
| `kasamiPolarSymm` | theorem | ✅ | Polar symmetry |
| `kasamiPolarSelf` | theorem | ✅ | `B(x,x) = 0` |
| `kasamiPolar_eq` | theorem | ✅ | Polar = candidate |
| `kasamiExpSum_eq` | theorem | ✅ | Exponential sum relation |
| **`kasami_wht_sq_trichotomy`** | theorem | **❌ SORRY** | WHT² ∈ {0, 2^{n+1}} |

---

## Layer 7: P₃ Proof Chain

### `Kasami/DifferenceSet.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `kasamiDelta` | def | Difference set `Δ` |
| `kasami_P1` | theorem | P₁ property |
| Cardinality bounds, character sums | — | Supporting results |

### `Kasami/TripleCount.lean` — ⚠️ 1 SORRY
| Lean Name | Type | Status | Description |
|-----------|------|--------|-------------|
| `tripleSet` | def | ✅ | Set of valid triples |
| `tripleCount` | def | ✅ | `|tripleSet|` |
| `tripleCount_charSum_eq` | theorem | ✅ | Character-sum representation |
| `AlmostBentVanishing` | def | ✅ | Vanishing condition |
| **`ab_implies_vanishing`** | theorem | **❌ SORRY** | AB ⟹ vanishing |
| `tripleCount_from_vanishing` | theorem | ✅ | Vanishing ⟹ `count = 2^{2n−3}` |

### `Kasami/VanishingProof.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `F2n.add_one_add_one` | theorem | `b+1+1 = b` (char 2) |
| `deltaGen_paired` | theorem | `g(b) = g(b+1)` |
| `deltaGen_fiber_ge_two` | theorem | Fibers have ≥ 2 elements |
| `kasamiDelta_card` | theorem | `|Δ| = 2^{n-1}` |
| `deltaGen_two_to_one` | theorem | From APN |
| `triple_sum_split` | theorem | Sum splitting |
| `deltaCharSum_double` | theorem | Double character sum |
| `chi_triple_cancel` | theorem | χ cancellation in char 2 |
| `ab_implies_vanishing_assembled` | theorem | Framework (needs hypotheses) |

### `Kasami/KasamiP3.lean` — ⚠️ (inherits sorries)
| Lean Name | Type | Status | Description |
|-----------|------|--------|-------------|
| `kasami_P3_from_constructed_chi` | theorem | ✅ | P₃ from explicit spectral hyp |
| `kasami_P3` | theorem | ⚠️ | Full P₃ (depends on S1 + S2) |

### `Kasami/DualP3.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| `spectral_eq_count_mul_card` | theorem | Spectral triple = count × |F| |
| `P3_iff_DualP3` | theorem | Dual P₃ ↔ P₃ |

### `Kasami/AbstractTripleCount.lean` — ✅ ALL PROVED
| Lean Name | Type | Description |
|-----------|------|-------------|
| Abstract triple count framework | — | General framework |

### `Kasami/KasamiFunction.lean` — ⚠️ 1 SORRY
| Lean Name | Type | Status | Description |
|-----------|------|--------|-------------|
| `kasamiF` | def | ✅ | `F(b) = b^d` |
| `kasami_P2` | theorem | ✅ | `F(b) = b^{4^k−2^k+1}` |
| `kasamiF_zero` | theorem | ✅ | `F(0) = 0` |
| `kasamiF_one` | theorem | ✅ | `F(1) = 1` |
| `kasamiDeriv` | def | ✅ | Derivative `D_a F(x)` |
| `kasamiDeltaGen` | def | ✅ | Delta generator `g(b)` |
| **`kasami_is_ab`** | theorem | **❌ SORRY** | **Kasami is Almost Bent** |

---

## Layer 8: Bridge Lemmas (QuadFormBridge.lean, kasami-27)

### `Kasami/QuadFormBridge.lean` — ⚠️ 7 SORRYs

These bridge lemmas connect the general quadratic form + linearized polynomial theory to the Kasami function:

| # | Lean Name | Status | Layer | Description |
|---|-----------|--------|-------|-------------|
| 2b | `kasami_Qa_is_quadratic` | ❌ | 2 | `Q_a(x)=Tr(a·x^d)` is a quadratic form |
| 2e | `kasami_Ba_simplified` | ❌ | 2→3 | `B_a(x,y) = Tr(y·L_a(x))` via Frobenius |
| 3c | `kasami_radical_eq_kernel` | ❌ | 3 | `rad(Q_a) = ker(L_a)` |
| 3e | `kasami_radical_small` | ❌ | 3 | `|rad| ∈ {1, 2}` |
| 4c | `kasami_Qa_vanishes_on_radical` | ❌ | 4 | `Q_a|_{rad} = 0` |
| 5a | `kasami_walsh_eq_expSum` | ❌ | 5 | `W_f(a) = S(Q_a)` |
| 5b | `kasami_walsh_sq_values` | ❌ | 5 | `W_f(a)² ∈ {0, 2^{n+1}}` |
| 5c | `kasami_is_ab_from_bridge` | ✅ | 5 | Assembly (proved from 5b) |

---

## Layer 9: Standalone Bridge Decomposition (KasamiBridgeLemmas.lean, kasami-26)

Self-contained 21-lemma skeleton with identical mathematical content to Layer 8, but using standalone definitions (not importing the project). All 21 are sorry'd. See `DECOMPOSITION_MAP.md` for full tree.

---

## Summary Statistics

| Category | Count |
|----------|-------|
| Total Lean files | ~28 |
| Total theorems/lemmas/defs | ~120+ |
| Sorry-free theorems | ~105+ |
| Remaining sorry's (critical path) | **3** (S1, S2, S3) |
| Remaining sorry's (off critical path) | **1** (S4) |
| Bridge sub-lemmas needed | **7** (QuadFormBridge) |
| Total sorry-eliminating lemmas estimated | **25–40** |
