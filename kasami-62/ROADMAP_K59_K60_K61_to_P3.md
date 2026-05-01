# Roadmap: kasami-59 / 60 / 61 → P₃ Proof

## 1. Inventory of Modules

### kasami-59 (two variants: k-59a, k-59b — nearly identical)

| File | What it provides | Sorry count | Status |
|------|-----------------|-------------|--------|
| `KasamiDefs.lean` | Core defs: `kasamiExp`, `frobIter`, `linPolyL`, `linPolyM`, `kerL`, `frobFixedPts`, `linPolyLA`, `kerDimLA`, `radical`, `polarForm`, `walshHT`, `walshHTSq` | **0** | ✅ Fully proved |
| `KasamiPhase1.lean` | Kernel ⊆ Frobenius fixed points: `linearized_kernel_subset_cube`, `kerL_subset_frobFixed`, Frobenius GCD → GF(2): `frobFixed_subset_gf2`, `mk_ker_eq_F2` | **0** | ✅ Fully proved |
| `CCDCounting.lean` | `frobenius_gcd_fixed`, `ccd_kernel_bound` (ker(L_k) ⊆ GF(2^gcd(3k,n))), `ccd_kernel_card_le_two`, `ccd_kasami` (main CCD), `gcd_3k_2k1_dvd_three`, `gcd_3k_n_eq_one` | **0** | ✅ Fully proved |
| `KasamiPhase2.lean` | Trace-Frobenius invariance, L_k linearity, polar form symmetry, radical closure, `linPolyLA_add` | **1** | `radical_eq_ker_LA` — sorry |
| `KasamiPhase3.lean` | WHT vanishing/peak, kernel-dim membership, `kasami_wht_sq_value`, `kasami_is_AB` | **4** (k-59a) / **3** (k-59b) | `wht_vanishing`, `wht_peak`, `kerDimLA_mem` — sorry; top-level theorems derived from these |
| `Mathlib/QuadraticFourier.lean` | `walsh_int_values`, `walsh_spectrum_values` (W²=2^(n+1) ⟹ W=±2^((n+1)/2)) | **0** | ✅ Fully proved |

#### k-59a vs k-59b differences
- k-59a has an extra sorry for `linPolyLA_ker_subset_cube` (leaf lemma in Phase 3).
- k-59b removes that leaf lemma and reorganises the Phase 3 skeleton slightly.
- All other files are identical.

---

### kasami-60 (two variants: k60a, k60b)

#### k60a — Gold exponent radical-kernel bridge

| File | What it provides | Sorry count | Status |
|------|-----------------|-------------|--------|
| `KasamiDefs.lean` | Gold exponent defs: `goldExp`, `goldQ`, `polar`, `goldB`, `goldL`, `goldRadical`, `goldKerL`, `fieldTr` | **0** | ✅ Fully proved |
| `GoldRadicalKernel.lean` | `char2_add_pow`, `gold_polar_expand`, `trace_frob_inv`, `pow_finrank_eq`, `trace_nondeg`, `gold_bridge`, `gold_radical_eq_ker` | **1** | `trace_adj` (trace adjoint identity) — sorry |

> **Note:** k60a is the **Gold** (d = 2^k + 1) analogue, not the Kasami (d = 2^{2k} − 2^k + 1) exponent. It proves `goldRadical = goldKerL` for the Gold case, modulo the trace adjoint identity.

#### k60b — Full Kasami AB pipeline (identical structure to k-59a)

| File | What it provides | Sorry count | Status |
|------|-----------------|-------------|--------|
| `KasamiDefs.lean` | Same as k-59a | **0** | ✅ |
| `KasamiPhase1.lean` | Same as k-59a | **0** | ✅ |
| `CCDCounting.lean` | Same as k-59a | **0** | ✅ |
| `KasamiPhase2.lean` | Same as k-59a | **1** | `radical_eq_ker_LA` — sorry |
| `KasamiPhase3.lean` | Same structure, but adds helper lemmas for kernel bound (`gcd_k_n_of_gcd_3k_n`, `ker_element_norm_eq`, `ker_frobenius_identity`) | **2** | `wht_vanishing`, `wht_peak` partially handled; `u_eq_of_lin_indep` — sorry |
| `Mathlib/QuadraticFourier.lean` | Same as k-59a | **0** | ✅ |

---

### kasami-61 (two variants: k-61-a, k-61-b — identical)

| File | What it provides | Sorry count | Status |
|------|-----------------|-------------|--------|
| `Defs.lean` | `kasamiExp(Z)`, `trGF2`, `chiGF2`, `walshSum`, `IsAlmostBent`, `kasamiFun`, `linearizedOp`, `polarForm`, `traceBilinForm`, `radical` | **0** | ✅ Fully proved |
| `KasamiAB.lean` | `kasamiExpZ_pos`, `kasamiExp_eq`, `kasamiExp_odd`, Phase 1 Frobenius linearity, `linearizedOp_add`, `radical_eq_ker_linearizedOp` (proved from two sorry'd lemmas) | **6** | See below |

#### kasami-61 sorry inventory (both a and b identical)

| Lemma | Location | Mathematical content | Difficulty |
|-------|----------|---------------------|------------|
| `traceBilin_eq_trace_linearizedOp` | KasamiAB:77 | B_a(x,y) = Tr(x · L_a(y)) — the adjoint identity | Hard |
| `trace_nondegenerate` | KasamiAB:80 | Tr(x·z) = 0 ∀x ⟹ z = 0 — trace non-degeneracy | Medium |
| `ker_linearizedOp_card_le` | KasamiAB:101 | |ker(L_a)| ≤ 2 — kernel dimension bound | Hard |
| `radical_ncard_le` | KasamiAB:105 | |rad(Q_a)| ≤ 2 — follows from above two | Easy (once above proved) |
| `walshSum_sq_eq` | KasamiAB:114 | W² ∈ {0, 2^n, 2^(n+1)} — quadratic form spectrum | Hard |
| `kasami_is_AB` | KasamiAB:124 | Main theorem: Kasami is AB | Medium (assembly) |

---

## 2. Summary: What Is Proved vs What Remains

### Fully proved (sorry-free) across k-59/60/61

| Component | Where |
|-----------|-------|
| Kasami exponent definitions & basic properties | All `KasamiDefs.lean` / `Defs.lean` |
| Frobenius iterate algebra (additivity, char 2) | `KasamiDefs.lean`, `KasamiPhase1.lean` |
| ker(L_k) ⊆ GF(2^{3k})-fixed points | `KasamiPhase1.lean` (all variants) |
| Frobenius-GCD fixed point theorem | `CCDCounting.lean` |
| CCD kernel bound: ker(L_k) ⊆ GF(2^{gcd(3k,n)}) | `CCDCounting.lean` |
| CCD counting: |ker(L_k)| ≤ 2 when gcd(k,n)=1, n=2k+1 | `CCDCounting.lean` |
| gcd(3k, 2k+1) ∣ 3 | `CCDCounting.lean` |
| Walsh integer square-root lemma (W²=2^{n+1} ⟹ W=±2^{(n+1)/2}) | `QuadraticFourier.lean` |
| Trace Frobenius invariance Tr(x^{2^k}) = Tr(x) | `KasamiPhase2.lean` |
| L_k additivity, polar form symmetry | `KasamiPhase2.lean` |
| Gold radical = kernel (modulo trace adjoint) | `GoldRadicalKernel.lean` (k60a) |

### Remaining sorries (unique mathematical gaps)

| # | Sorry | Appears in | P₃ critical path? |
|---|-------|-----------|-------------------|
| S1 | **`radical_eq_ker_LA`** — Radical of Q_a = kernel of L_a (Kasami exponent) | k-59a/b Phase2, k-60b Phase2 | ✅ Yes — feeds SORRY #1 |
| S2 | **`traceBilin_eq_trace_linearizedOp`** — B_a(x,y) = Tr(x · L_a(y)) | k-61a/b KasamiAB | ✅ Yes — equivalent to S1 |
| S3 | **`trace_nondegenerate`** — Trace non-degeneracy | k-61a/b KasamiAB | ✅ Yes — needed for S1/S2 |
| S4 | **`trace_adj`** — Trace adjoint: Tr(u·v^{2^j}) = Tr(u^{2^{n-j}}·v) | k60a GoldRadicalKernel | ⚠️ Indirect (Gold, not Kasami) |
| S5 | **`wht_vanishing`** — WHT vanishing when radical is trivial | k-59a/b Phase3, k-60b Phase3 | ✅ Yes |
| S6 | **`wht_peak`** — WHT peak value = 2^{n+1} when radical nontrivial | k-59a/b Phase3, k-60b Phase3 | ✅ Yes |
| S7 | **`kerDimLA_mem`** — ker dimension ∈ {0, 1} (or {1, 2} for card) | k-59a/b Phase3, k-60b Phase3 | ✅ Yes |
| S8 | **`ker_linearizedOp_card_le`** — |ker(L_a)| ≤ 2 | k-61a/b KasamiAB | ✅ Yes (= S7) |
| S9 | **`walshSum_sq_eq`** — W² ∈ {0, 2^n, 2^{n+1}} | k-61a/b KasamiAB | ✅ Yes (= S5 + S6) |
| S10 | **`kasami_is_AB`** — Main AB theorem | k-61a/b KasamiAB | ✅ Yes — **this IS P₃ SORRY #1** |
| S11 | **`u_eq_of_lin_indep`** — Linear independence helper | k-60b Phase3 | ✅ Yes (sub-lemma for S7) |

### Deduplication

Many sorries are the same mathematical fact in different formalisations:

- **S1 ≈ S2**: Both are "radical = kernel" via the trace-adjoint identity
- **S5 + S6 ≈ S9**: Walsh spectrum characterisation
- **S7 ≈ S8**: Kernel cardinality bound
- **S10**: Assembly of all the above

**Unique mathematical gaps reduce to 4:**

| Gap | Math | Which sorries |
|-----|------|--------------|
| **GAP A** | Trace adjoint identity: Tr(a · polar(x,y)) = Tr(x · L_a(y)) | S1, S2, S4 |
| **GAP B** | Trace non-degeneracy: Tr(x·z)=0 ∀x ⟹ z=0 | S3 |
| **GAP C** | Kernel dimension: |ker(L_a)| ≤ 2 for a≠0 | S7, S8, S11 |
| **GAP D** | Walsh–quadratic form connection: W² = 2^n · |rad| | S5, S6, S9 |

---

## 3. Mapping to P₃ Proof (from P3_COMPLETENESS_ANALYSIS.md)

The P₃ theorem depends on:

```
kasami_P3
  ├── kasami_is_ab          [P₃ SORRY #1]
  ├── ab_implies_vanishing   [P₃ SORRY #2]
  └── tripleCount_from_vanishing  ✅
```

### P₃ SORRY #1: `kasami_is_ab` — Can k-59/60/61 close this?

**Current coverage from k-59/60/61:**

```
kasami_is_ab  (= S10)
  ├── radical_eq_ker_LA        (= S1/S2)  ← GAP A + GAP B
  │     ├── traceBilin_eq_trace_linearizedOp  ← GAP A (trace adjoint)
  │     └── trace_nondegenerate               ← GAP B
  ├── ker_card_le_two          (= S7/S8)  ← GAP C
  │     └── CCD counting argument           ✅ PROVED (CCDCounting.lean)
  │         ├── linearized_kernel_subset_cube ✅ PROVED (KasamiPhase1.lean)
  │         ├── frobenius_gcd_fixed           ✅ PROVED (CCDCounting.lean)
  │         └── gcd_3k_n_eq_one               ✅ PROVED (CCDCounting.lean)
  └── walsh_sq_from_radical    (= S5/S6)  ← GAP D
        └── Gauss sum / quadratic form theory  ← NOT FORMALISED
```

**Assessment:** k-59/60/61 provide the **bottom half** of the `kasami_is_ab` proof:
- ✅ The CCD counting argument (ker(L_k) ⊆ small subfield) is **fully proved**.
- ✅ The Frobenius algebra (linearity, kernel inclusion) is **fully proved**.
- ✅ The Walsh integer square-root lemma is **fully proved**.
- ❌ The **trace adjoint identity** (GAP A) remains unproved everywhere.
- ❌ **Trace non-degeneracy** (GAP B) remains unproved (but is a well-known Mathlib-adjacent fact).
- ❌ The **Walsh ↔ radical cardinality** bridge (GAP D) remains unproved.
- ⚠️ **Kernel bound** (GAP C): The CCD counting in `CCDCounting.lean` proves |ker(L_k)| ≤ 2, but this is for the *linearized polynomial* L_k(z) = z^{2^{2k}} + z^{2^k} + z, **not** the *operator* L_a(y) = a·y^{2^{2k}} + a^{2^k}·y^{2^k} + a^{2^{2k}}·y. The bridge from L_a to L_k (via substitution z = a·y or similar) is **not formalised**.

### P₃ SORRY #2: `ab_implies_vanishing`

**Not addressed by k-59/60/61 at all.** This requires:
- Expressing S_Δ(c) in terms of WHT
- Triple-sum evaluation using AB spectrum + Parseval
- Approximately 8–12 additional lemmas

### P₃ SORRY #3: `ccd_crossterm_gives_linPolyL`

**Partially addressed.** The CCD counting argument in `CCDCounting.lean` provides the kernel bound, which is the deepest part. But the *cross-term decomposition* itself (showing polar form = trace of linearized poly) is exactly GAP A.

### P₃ SORRY #4: `kasami_wht_sq_trichotomy`

**Redundant** with P₃ SORRY #1 (once `kasami_is_ab` is proved, this follows).

---

## 4. What k-59/60/61 Contribute to P₃ (Summary)

| P₃ Component | Contribution from k-59/60/61 | Gap remaining |
|--------------|------------------------------|---------------|
| CCD counting (ker ≤ 2) | ✅ **Fully proved** in CCDCounting.lean | Bridge L_a ↔ L_k |
| Frobenius fixed-point theory | ✅ **Fully proved** in KasamiPhase1.lean | — |
| Walsh integer square-root | ✅ **Fully proved** in QuadraticFourier.lean | — |
| Trace Frobenius invariance | ✅ **Fully proved** in KasamiPhase2.lean | — |
| L_k / L_a linearity | ✅ **Fully proved** in KasamiPhase2.lean, KasamiAB.lean | — |
| Polar form symmetry | ✅ **Fully proved** in KasamiPhase2.lean | — |
| Radical = ker(L_a) | ❌ Sorry (GAP A + B) | Trace adjoint + non-degeneracy |
| |ker(L_a)| ≤ 2 | ⚠️ Partially (L_k done, L_a not) | L_a ↔ L_k bridge |
| W² ↔ |rad| connection | ❌ Sorry (GAP D) | Quadratic form Gauss sum |
| AB ⟹ spectral vanishing | ❌ Not addressed | Entirely missing |
| kasami_is_AB assembly | ❌ Sorry | Depends on all above |

---

## 5. Proof Sketch: Closing the Gaps

### GAP A — Trace Adjoint Identity

**Goal:** `Tr(a · ((x+y)^d + x^d + y^d)) = Tr(x · L_a(y))`

**Sketch:** Expand `(x+y)^d` for `d = 2^{2k} − 2^k + 1` using Freshman's dream. The cross-terms reduce to:
```
a · (x^{2^{2k}} · y + x · y^{2^{2k}} + x^{2^k} · y^{2^{2k}-2^k+1-2^k} + ...)
```
Apply trace-Frobenius `Tr(u^{2^j}) = Tr(u)` repeatedly to rewrite each term as `Tr(x · (something involving a, y))`. The "something" collects into `L_a(y)`.

**Key ingredients already proved:** `trace_frobenius_invariant` (KasamiPhase2), Frobenius additivity (KasamiDefs).

**Missing:** The actual multinomial expansion of `(x+y)^d` for the specific Kasami exponent, and the trace-adjoint regrouping.

### GAP B — Trace Non-degeneracy

**Goal:** `∀ x, Tr(x · z) = 0 → z = 0`

**Sketch:** This is equivalent to the non-degeneracy of the trace bilinear form for separable extensions. In Mathlib, this should follow from `Algebra.traceForm_nondegenerate` for `GF(2^n) / GF(2)`. The k60a file already has `trace_nondeg` proved (using `Algebra.trace_ne_zero`), so this is portable.

**Status in k60a:** Actually proved! The `GoldRadicalKernel.lean` file has:
```lean
lemma trace_nondeg (z : F) (hz : ∀ x : F, fieldTr (x * z) = 0) : z = 0
```
This is **proved** (no sorry). Can be directly reused.

### GAP C — Kernel Bound L_a ↔ L_k Bridge

**Goal:** Show |ker(L_a)| ≤ 2 from |ker(L_k)| ≤ 2.

**Sketch:** For the Kasami *operator* L_a(y) = a·y^{2^{2k}} + a^{2^k}·y^{2^k} + a^{2^{2k}}·y, when a ≠ 0, the substitution w = a·y (or a change of variable using a^{-1}) relates ker(L_a) to ker(L_k) up to scaling. Specifically, L_a(y) = 0 implies a certain polynomial in y vanishes, and after dividing by a (using a ≠ 0), one obtains an equation in the form of L_k applied to a related variable. The kernel of L_a has the same cardinality as ker(L_k) (they are related by an invertible linear change of variable).

### GAP D — Walsh ↔ Radical Connection

**Goal:** W_f(b)² = 2^n · |rad(Q_b)| (or a variant).

**Sketch:** This is the classical result from quadratic form theory over GF(2):
1. Q_b(x) = Tr(b·x^d) is a quadratic form on GF(2^n) viewed as GF(2)^n.
2. The Gauss sum of Q_b satisfies: (∑ (-1)^{Q_b(x)})² = 2^n · |rad(Q_b)|.
3. The left side is exactly W_f(b)² (for the power function f(x) = x^d, evaluated at the point b with the "linear part" absorbed).

**This requires:** Formalizing the Gauss sum identity for quadratic forms over GF(2). This is substantial new infrastructure not present in any of k-59/60/61.

---

## 6. Recommended Next Steps (Priority Order)

1. **Port `trace_nondeg` from k60a** → closes GAP B everywhere.
2. **Prove GAP A (trace adjoint)** → closes S1, S2, S4; unlocks radical = kernel.
3. **Formalise L_a ↔ L_k bridge** → closes GAP C using the already-proved CCD counting.
4. **Formalise Gauss sum for quadratic forms over GF(2)** → closes GAP D.
5. **Assemble `kasami_is_AB`** → closes P₃ SORRY #1.
6. **Prove `ab_implies_vanishing`** → closes P₃ SORRY #2.
7. **Final assembly of `kasami_P3`**.

**Estimated remaining work:** ~25–35 additional lemmas across GAPs A–D + P₃ SORRY #2.

---

## 7. Module Dependency Graph

```
                    ┌──────────────────┐
                    │   kasami_P3      │  (P₃ theorem)
                    └──────┬───────────┘
                           │
              ┌────────────┼────────────────┐
              ▼            ▼                ▼
      kasami_is_ab   ab_implies_vanishing  tripleCount_from_vanishing
      [P₃ SORRY #1]  [P₃ SORRY #2]        [✅ PROVED]
              │
    ┌─────────┼──────────────┐
    ▼         ▼              ▼
radical=ker  ker_card≤2   W²=2ⁿ·|rad|
 [GAP A+B]   [GAP C]      [GAP D]
    │         │
    │    ┌────┴────┐
    │    ▼         ▼
    │  L_a↔L_k   CCD counting
    │  [MISSING]  [✅ k-59/60]
    │              │
    │         ┌────┴─────────────┐
    │         ▼                  ▼
    │   ker⊆GF(2^{3k})    gcd(3k,n)|3
    │   [✅ Phase1]        [✅ CCDCounting]
    │
    ├──► trace_adjoint [GAP A — MISSING]
    └──► trace_nondeg  [GAP B — ✅ in k60a]
```

**Legend:** ✅ = proved in k-59/60/61, ❌/MISSING = sorry, GAP X = unique mathematical gap.
