# P₃ Formalization — Completeness Analysis and Decomposition

## Status Summary

The P₃ formalization is **structurally complete** — the full proof chain from
hypotheses to the P₃ count `2^{2n-3}` is formalized, with 4 remaining sorry's
corresponding to deep mathematical results.

### What Was Done in This Session

**Proved: `ab_implies_apn` (AB ⟹ APN for the Kasami function)**

The original `ab_implies_apn` was stated for a general AB function `f`, but
the proof requires the power function structure of the Kasami function. We:

1. Created `Kasami/ABImpliesAPN.lean` with 7 helper lemmas:
   - `power_fn_deriv_charsum_scaling` ✅ — Scaling identity G_a(c) = G_1(c·a^d)
   - `power_fn_scaled_wht` ✅ — WHT reparametrization for power functions
   - `power_fn_scaled_ab` ✅ — Scalar multiples of AB power functions are AB
   - `deriv_charsum_sq_sum_nonzero` ✅ — ∑_{t≠0} G_t(c)² = (2^n)² for AB
   - `kasami_deriv_sq_sum_eq` ✅ — ∑_b N_a(b)² = 2^{n+1} for all a≠0
   - `apn_from_deriv_sq` ✅ — APN from constant derivative sum
   - `ab_implies_apn` ✅ — Final assembly: Kasami AB ⟹ APN

2. Modified `Kasami/VanishingProof.lean` to use the proved `ab_implies_apn`
   directly, removing the `hapn` hypothesis from `ab_implies_vanishing_assembled`.

**Partially proved: `kasamiDiff_eq_implies_linearized` (Derivative ↔ Linearized Poly)**

Decomposed into 7 helper lemmas (in `LinearizedPoly/KasamiKernel.lean`):
- `char2_freshman` ✅ — Freshman's dream
- `gold_derivative` ✅ — Gold derivative formula
- `gold_deriv_at_one` ✅ — Gold derivative at z=1
- `gold_second_derivative` ✅ — Gold second derivative is x-independent
- `ccd_power_factorization` ✅ — CCD power factorization [D₁(x^d)]^{2^k+1}
- `ccd_second_deriv_eq` ✅ — z^{2^{3k}} + z = C(y₂) + C(y₂+z)
- `ccd_crossterm_gives_linPolyL` ❌ — The deepest algebraic step

The main theorem `kasamiDiff_eq_implies_linearized` is proved modulo
`ccd_crossterm_gives_linPolyL`.

---

## Remaining Sorry's (4)

### 1. `kasami_is_ab` (KasamiFunction.lean:62)
**The Kasami function is Almost Bent.**

This is the deepest result, requiring:
- Constructing Q_a(x) = Tr(a·x^d) as a quadratic form over F₂
- Showing B_a has rank n-1 or n via linearized polynomial kernel analysis
- Applying the Gauss sum formula S(Q)² = |V|·|rad|
- Connecting back to the WHT values

**Decomposition strategy**: The infrastructure for this is partially in place:
- `QuadFormGF2/Defs.lean`: QuadFormF2 structure ✅
- `QuadFormGF2/GaussSum.lean`: expSum_sq_eq_card_mul_radical_card ✅
- `QuadFormGF2/KasamiConnection.lean`: Bridge definitions (kasamiTracePower, kasamiPolarCandidate) ✅
- Missing: Showing B_a is biadditive, computing the radical, connecting to linPolyL kernel

**Estimated sub-lemmas needed**: ~10-15 more lemmas

### 2. `ab_implies_vanishing` (TripleCount.lean:120)
**AB ⟹ spectral vanishing for the triple product.**

This requires showing that for AB Kasami function:
∑_{a≠0} S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂)) = 0

The assembly framework is in VanishingProof.lean (`ab_implies_vanishing_assembled`),
which reduces this to proving the "nonzero sum vanishing" (`hvanish`).

**Decomposition**: The nonzero sum vanishing requires relating S_Δ(c) to
G_1(c) via the 2-to-1 property, then showing the triple product of G_1
values vanishes. This involves deep character sum identities.

**Estimated sub-lemmas needed**: ~8-12 more lemmas

### 3. `ccd_crossterm_gives_linPolyL` (KasamiKernel.lean:176)
**The cross-term difference factors through linPolyL.**

This is the deepest algebraic step of the CCD (Canteaut-Charpin-Dobbertin) proof.
From z^{2^{3k}} + z = C(y₂) + C(y₂+z), together with the original differential
equation, it concludes linPolyL k z = 0.

**Key insight**: (L_k(z))^{2^k} + L_k(z) = z^{2^{3k}} + z (easily verified algebraically).
So z^{2^{3k}} + z = M_k(L_k(z)) where M_k(t) = t^{2^k} + t.
The CCD proof then shows that C(y₂) + C(y₂+z) also equals M_k(L_k(z)),
and uses the structure of C to conclude L_k(z) = 0.

**Decomposition strategy**:
1. Prove z^{2^{3k}} + z = M_k(L_k(z)) (algebraic identity)
2. Show C(y₂) + C(y₂+z) = M_k(something) using the differential equation
3. Conclude L_k(z) = 0 from the injectivity properties of M_k

**Estimated sub-lemmas needed**: ~5-8 more lemmas

### 4. `kasami_wht_sq_trichotomy` (KasamiConnection.lean:182)
**WHT spectrum trichotomy for the Kasami quadratic form.**

This is closely related to `kasami_is_ab` — both state that the Walsh/exponential
sum squared is in {0, 2^{n+1}}.

**Note**: This sorry is in a standalone file (`QuadFormGF2/KasamiConnection.lean`)
and is NOT on the critical path for P₃. It was added as an independent formalization
of the same result via the quadratic form route. Proving `kasami_is_ab` would make
this redundant.

---

## Dependency Chain

```
ccd_crossterm_gives_linPolyL  ←  deepest algebraic step
        ↓
kasamiDiff_eq_implies_linearized  ←  now proved modulo above
        ↓
(feeds into kasami_apn, kasamiDelta_two_to_one in KasamiKernel.lean)

kasami_is_ab  ←  the main deep theorem
        ↓
ab_implies_apn  ✅  (PROVED)
ab_implies_vanishing  ←  needs kasami_is_ab + vanishing
        ↓
kasami_P3  ←  the P₃ theorem (proved modulo above)
```

## What Is Fully Proved (sorry-free)

- All of Layers 0-1: Field/Trace infrastructure, Kasami exponent properties
- Walsh-Hadamard transform: definition, Parseval, inversion, bounds
- AB definition and fourth moment formula
- **AB ⟹ APN for the Kasami function** (NEW)
- Derivative distribution: evenness, Parseval identity, autocorrelation
- CCD factorization identities (d·(2^k+1) = 2^{3k}+1, Freshman's dream)
- Gold derivative formulas (3 lemmas, NEW)
- CCD power factorization and second derivative (2 lemmas, NEW)
- Linearized polynomial kernel theory (kernel dimension bounds)
- Quadratic form theory over F₂ (radical, Gauss sum S(Q)²)
- Difference set Δ: definition, character sums
- Triple count character-sum representation
- Triple count from vanishing
- P₃ assembly (modulo kasami_is_ab + ab_implies_vanishing)
- Dual P₃ ↔ P₃ equivalence
- Delta pairing g(b)=g(b+1), cardinality
- Artin-Schreier map analysis

## Conclusion

The formalization is approximately **80% complete** for the P₃ theorem.
The remaining 4 sorry's correspond to deep mathematical results that require
substantial additional algebraic infrastructure (~25-40 more lemmas total).
The critical bottleneck is `kasami_is_ab`, which requires building the full
bridge between the quadratic form theory and the Kasami function.
