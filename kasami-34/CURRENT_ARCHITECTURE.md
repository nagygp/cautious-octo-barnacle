# Kasami P₃ Formalization — Current Architecture

## 1. Goal

Prove in Lean 4 that for the **Kasami power function** `f(x) = x^d` on `GF(2^n)` with
`d = 2^{2k} − 2^k + 1`, `gcd(k,n) = 1`, `n` odd, `n ≥ 3`:

> **P₃**: The number of triples `(x,y,z) ∈ Δ³` satisfying
> `v₁·x + v₂·y + (v₁+v₂)·z = 0` is exactly `2^{2n−3}`,
> where `Δ = { b^d + (b+1)^d + 1 : b ∈ GF(2^n) }`.

This is equivalent to the **dual (spectral) P₃**:
`∑_ψ Ŝ_ψ(v₁)·Ŝ_ψ(v₂)·Ŝ_ψ(v₁+v₂) = 2^{3n−3}`.

---

## 2. Module Map (Most Recent: kasami-33)

```
RequestProject/
├── Main.lean                            ← Root imports, options
├── Kasami/
│   ├── Basic.lean                       ← F2n = GF(2^n), char-2 arith       ✅ sorry-free
│   ├── Trace.lean                       ← Tr : GF(2^n)→GF(2), surjectivity  ✅ sorry-free
│   ├── AdditiveCharacter.lean           ← χ(x)=(−1)^Tr(x), orthogonality    ✅ sorry-free
│   ├── WalshHadamard.lean               ← WHT, Parseval, inversion           ✅ sorry-free
│   ├── KasamiExponent.lean              ← d=4^k−2^k+1, coprimality, perm    ✅ sorry-free
│   ├── AlmostBent.lean                  ← IsAlmostBent def, 4th moment       ✅ sorry-free
│   ├── KasamiFunction.lean              ← kasamiF, kasami_is_ab              ⚠️  1 SORRY
│   ├── ABImpliesAPN.lean                ← AB⟹APN for Kasami (power fn)      ✅ sorry-free
│   ├── DifferenceSet.lean               ← Δ, character sums on Δ             ✅ sorry-free
│   ├── TripleCount.lean                 ← Character-sum representation,       ⚠️  1 SORRY
│   │                                       ab_implies_vanishing
│   ├── AbstractTripleCount.lean         ← Abstract triple count framework    ✅ sorry-free
│   ├── FourthMoment.lean                ← Autocorrelation, Wiener-Khinchin   ✅ sorry-free
│   ├── APNFromAB.lean                   ← Derivative Parseval, bounds        ✅ sorry-free
│   ├── VanishingProof.lean              ← g(b)=g(b+1), |Δ|=2^{n-1}, split  ✅ sorry-free
│   ├── KasamiP3.lean                    ← P₃ final assembly                  ✅ (inherits sorries)
│   ├── DualP3.lean                      ← Dual P₃ ↔ P₃ equivalence          ✅ sorry-free
│   ├── CCDHelpers.lean                  ← Char-2 helpers (freshman, gold)    ✅ sorry-free
│   ├── CCDFactorization.lean            ← d·(2^k+1)=2^{3k}+1, Frobenius    ✅ sorry-free
│   └── QuadFormBridge.lean              ← Bridge lemmas Q→WHT (kasami-27)    ⚠️  7 SORRYs
├── LinearizedPoly/
│   ├── Defs.lean                        ← φ, linPolyL, linPolyM defs        ✅ sorry-free
│   ├── Kernel.lean                      ← Kernel dimension classification    ✅ sorry-free
│   ├── ArtinSchreier.lean               ← x²+x, Im = ker(Tr)               ✅ sorry-free
│   └── KasamiKernel.lean               ← Derivative↔linearized poly         ⚠️  1 SORRY
└── QuadFormGF2/
    ├── Defs.lean                        ← QuadFormF2, polar, radical         ✅ sorry-free
    ├── GaussSum.lean                    ← S(Q)²=|V|·|rad|, vanishing        ✅ sorry-free
    ├── Kasami.lean                      ← Kasami spectrum outline            ✅ sorry-free
    └── KasamiConnection.lean            ← WHT↔QuadForm connection            ⚠️  1 SORRY
```

### Additional Files (from kasami-26, kasami-28)

```
KasamiBridgeLemmas.lean                  ← Standalone 21-lemma bridge         ⚠️  21 SORRYs
                                            decomposition (self-contained)
KasamiAB.lean                            ← Alternative standalone skeleton    ⚠️  (kasami-28)
```

---

## 3. The Four Top-Level Sorry's

These are the 4 sorry's in the **main proof chain** (kasami-33):

| # | Theorem | File | Description |
|---|---------|------|-------------|
| **S1** | `kasami_is_ab` | `Kasami/KasamiFunction.lean` | The Kasami function is Almost Bent |
| **S2** | `ab_implies_vanishing` | `Kasami/TripleCount.lean` | AB ⟹ spectral triple product vanishing |
| **S3** | `ccd_crossterm_gives_linPolyL` | `LinearizedPoly/KasamiKernel.lean` | CCD cross-term factorization |
| **S4** | `kasami_wht_sq_trichotomy` | `QuadFormGF2/KasamiConnection.lean` | WHT² trichotomy (redundant with S1) |

### Dependency Chain

```
S3: ccd_crossterm_gives_linPolyL
  └──→ kasamiDiff_eq_implies_linearized (proved modulo S3)
         └──→ kasamiDelta_two_to_one, kasami_apn (proved from above)

S1: kasami_is_ab
  ├──→ ab_implies_apn  ✅ (proved in ABImpliesAPN.lean)
  └──→ S2: ab_implies_vanishing ──→ kasami_P3 ✅ (proved modulo S1+S2)

S4: kasami_wht_sq_trichotomy
  └──→ (standalone, redundant with S1; not on critical path)
```

---

## 4. What Is Fully Proved (sorry-free)

### Infrastructure (Layers 0–1)
- **Field/Trace**: `F2n.card`, `tr2`, `tr2_add`, `tr2_sq`, `tr2_pow2`, `tr2_surjective`, `tr2_kernel_card`, `tr2_fiber_one_card`, `tr2_balanced`
- **Additive Character**: `chi`, `chiAddChar`, `chi_add`, `chi_sq`, `chi_orthogonality`, `chi_inner_product`, `chi_sum`
- **Kasami Exponent**: `kasamiExp`, `kasamiExp_odd`, `kasamiExp_coprime`, `kasamiExp_permutation`

### Walsh-Hadamard Theory
- `wht`, `wht_parseval`, `wht_inversion`, `wht_abs_le`

### Almost Bent Theory
- `IsAlmostBent` definition, `ab_nonzero_count`, `ab_fourth_moment`

### AB ⟹ APN (for Kasami power function)
- `power_fn_deriv_charsum_scaling`, `power_fn_scaled_wht`, `power_fn_scaled_ab`
- `deriv_charsum_sq_sum_nonzero`, `kasami_deriv_sq_sum_eq`, `apn_from_deriv_sq`
- **`ab_implies_apn`** ✅

### Derivative/Autocorrelation
- `derivCount`, `derivCount_even`, `autocorr`, `autocorr_zero`
- `wht_sq_as_autocorr`, `fourth_moment_eq_autocorr_sq`
- `ab_autocorr_sq_sum`, `ab_autocorr_sq_nonzero_sum`, `even_sum_sq_bound`

### CCD Factorization
- `kasamiExp_mul_identity`, `char2_add_pow`, `F2n_frobenius`
- `char2_sum_powers`, `gold_deriv`, `gold_second_deriv`, `bilinear_form_factor`

### CCD Kernel Lemmas (all proved)
- `char2_freshman`, `gold_derivative`, `gold_deriv_at_one`, `gold_second_derivative`
- `ccd_power_factorization`, `ccd_second_deriv_eq`

### Linearized Polynomial Kernel
- `linPolyL`, `linPolyM`, `linPolyL_linearized`
- `linPolyM_ker_card`, `linPolyL_ker_card_classification`
- `linPolyL_ker_trivial_of_three_ndvd`, `linPolyL_ker_dim2_of_three_dvd`
- `linPolyM_ker_eq_coprime`, `frob_fixed_gcd`, `card_frob_fixed`
- `kasamiDelta_two_to_one`, `kasami_apn` (when 3∤n)

### Quadratic Form over GF(2)
- `QuadFormF2` structure, `polar`, `radical`, `radicalRestriction`
- `polar_add_left`, `polar_comm`, `polar_add_right`
- `additive_on_radical`, `expSum`, `signZ`
- **`expSum_sq_eq_card_mul_radical_card`** ✅
- `expSum_zero_of_radical_nonvanishing`, `radical_sum_eq_card_of_vanishing`

### P₃ Chain
- `tripleCount_charSum_eq`, `tripleCount_from_vanishing`
- `kasami_P3_from_constructed_chi`, `kasami_P3` (inherits sorries)
- `spectral_eq_count_mul_card`, `P3_iff_DualP3`
- `kasamiDelta`, `kasami_P1`, cardinality bounds, character sums
- `deltaGen_paired`, `deltaGen_fiber_ge_two`, `kasamiDelta_card`
- `deltaGen_two_to_one`, `triple_sum_split`, `deltaCharSum_double`
- `chi_triple_cancel`, `ab_implies_vanishing_assembled`

### Artin-Schreier
- `artinSchreier_image_eq_trace_ker`

---

## 5. Proof Strategy (Quadratic Form Route for S1)

The proof of `kasami_is_ab` follows the **Canteaut–Charpin–Dobbertin (CCD)** quadratic form route:

```
Layer 0: Field/Trace infrastructure          ← ✅ FULLY PROVED
    ↓
Layer 1: Kasami exponent properties          ← ✅ FULLY PROVED
    ↓
Layer 2: Quadratic form Q_a, bilinear B_a    ← ❌ BRIDGE LEMMAS SORRY'D
    ↓
Layer 3: Linearized polynomial kernel        ← ✅ PROVED (general theory)
    ↓                                          ❌ BRIDGE to Layer 2 sorry'd
Layer 4: GF(2) Gauss sum evaluation          ← ✅ FULLY PROVED (general theory)
    ↓                                          ❌ BRIDGE to Layer 3 sorry'd
Layer 5: Assembly (WHT ↔ QuadForm bridge)    ← ❌ ASSEMBLY SORRY'D
```

The general-purpose infrastructure (Layers 0, 1, 3-general, 4-general) is complete.
The gaps are all **bridge lemmas** that connect the general theory to the specific Kasami function.

---

## 6. Cross-Reference to Previous Sessions

| Session | Key Focus | Key Output |
|---------|-----------|------------|
| kasami-23 | Initial assembly | Full module structure, most infrastructure |
| kasami-24 | AB modularization | `KASAMI_AB_MODULARIZATION.md` |
| kasami-25 | Assembly audit | `ASSEMBLY_REPORT.md` with lemma-by-lemma status |
| kasami-26 | Bridge decomposition | `KasamiBridgeLemmas.lean` (21 sub-lemmas) |
| kasami-27 | Architecture | `QuadFormBridge.lean` (7 bridge lemmas in project) |
| kasami-28 | Standalone AB | `KasamiAB.lean` alternative |
| kasami-29 | Category theory analysis | `PROOF_ARCHITECTURE.md`, `KasamiConnection.lean` |
| kasami-30 | AB⟹APN | Proved `ab_implies_apn` for power functions |
| kasami-31 | AB⟹APN decomposition | `ABImpliesAPNDecomposition.lean` |
| kasami-32 | (cleanup) | — |
| kasami-33 | CCD kernel, AB⟹APN | Proved 6/7 CCD sub-lemmas, proved `ab_implies_apn` |

---

## 7. Completion Estimate

- **Lines of sorry-free Lean**: ~3000+
- **Remaining sorry's on critical path**: 3 (S1, S2, S3)
- **Remaining sorry's off critical path**: 1 (S4, redundant)
- **Bridge sub-lemmas needed for S1**: 7 (in QuadFormBridge.lean)
- **Sub-lemmas needed for S3**: ~3–5
- **Sub-lemmas needed for S2**: ~5–8
- **Total remaining lemmas**: ~25–40
- **Estimated completion**: ~80% of proof chain
