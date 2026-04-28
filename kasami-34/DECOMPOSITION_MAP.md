# Decomposition Map — Remaining Sorry's and Sub-Lemma Tree

## Overview

This document provides a **complete decomposition tree** for every remaining sorry,
breaking each into the smallest provable sub-lemmas, with difficulty estimates and
dependency ordering.

---

## Master Dependency Graph

```
┌─────────────────────────────────────────────────────────────────────┐
│                           kasami_P3                                  │
│                     (Kasami/KasamiP3.lean)                           │
└───────────────┬──────────────────────┬──────────────────────────────┘
                │                      │
    ┌───────────▼───────────┐  ┌───────▼────────────────────┐
    │   kasami_is_ab (S1)   │  │ ab_implies_vanishing (S2)  │
    │  KasamiFunction.lean  │  │    TripleCount.lean        │
    └───────────┬───────────┘  └───────┬────────────────────┘
                │                      │
    ┌───────────▼───────────────────────▼──────────────────┐
    │              ab_implies_apn  ✅ PROVED               │
    │              (ABImpliesAPN.lean)                      │
    └─────────────────────────────────────────────────────┘

                    ┌──────────────────────────────┐
                    │ ccd_crossterm_gives_linPolyL  │
                    │        (S3)                    │
                    │   KasamiKernel.lean           │
                    └───────────┬──────────────────┘
                                │
                    ┌───────────▼──────────────────┐
                    │ kasamiDelta_two_to_one ✅     │
                    │ kasami_apn  ✅                │
                    └──────────────────────────────┘

                    ┌──────────────────────────────┐
                    │ kasami_wht_sq_trichotomy (S4) │
                    │  KasamiConnection.lean        │
                    │  (REDUNDANT with S1)          │
                    └──────────────────────────────┘
```

---

## S1: `kasami_is_ab` — The Kasami Function is Almost Bent

**Location**: `Kasami/KasamiFunction.lean:62`
**Statement**: For `gcd(k,n)=1`, `n` odd, `k≠0`, `n≠0`:
`IsAlmostBent (kasamiF n k)`, i.e., `∀ a, wht(kasamiF n k)(a)² ∈ {0, 2^{n+1}}`

**Strategy**: Quadratic Form Route (CCD). Decomposed into 7 bridge lemmas (QuadFormBridge.lean).

### Full Decomposition Tree for S1

```
kasami_is_ab
  └── kasami_is_ab_from_bridge ✅ (trivial assembly)
        └── kasami_walsh_sq_values [S1.7]
              ├── kasami_walsh_eq_expSum [S1.6]
              │     └── (definitional: wht = ∑ χ(a·x^d) = S(Q_a))
              ├── kasami_Qa_vanishes_on_radical [S1.5]
              │     └── (uses kernel structure from S1.3)
              ├── expSum_sq_eq_card_mul_radical_card ✅ (GaussSum.lean)
              └── kasami_radical_small [S1.4]
                    ├── kasami_radical_eq_kernel [S1.3]
                    │     ├── kasami_Ba_simplified [S1.2]
                    │     │     ├── kasami_Qa_is_quadratic [S1.1]
                    │     │     │     ├── kasami_cross_terms [S1.1a]
                    │     │     │     ├── Ba_add_right [S1.1b]
                    │     │     │     ├── Ba_symm [S1.1c]
                    │     │     │     └── Qa_smul [S1.1d]
                    │     │     ├── trace_frob_eq [S1.2a] ← tr2_pow2 ✅
                    │     │     ├── add_pow_two_pow [S1.2b] ← char2_add_pow ✅
                    │     │     └── frob_card_eq_id [S1.2c] ← F2n_frobenius ✅
                    │     └── tr2_surjective ✅
                    └── linPolyL_ker_card_classification ✅ (Kernel.lean)
```

### Sub-Lemma Details for S1

#### S1.1: `kasami_Qa_is_quadratic` — Q_a is a quadratic form
**Difficulty**: Hard
**Estimated sub-lemmas**: 4

| ID | Sub-lemma | Statement | Difficulty | Approach |
|----|-----------|-----------|------------|----------|
| S1.1a | `kasami_cross_terms` | `(x+y)^d + x^d + y^d = ∑ mixed terms` | Hard | Expand binomial in char 2; use `d = 2^{2k}−2^k+1` structure. The key fact is `(x+y)^{2^i} = x^{2^i} + y^{2^i}` (Freshman's dream, already proved). Need multinomial expansion for the three-term product `(x+y)·(x+y)^{2^k}·(x+y)^{2^{2k}} = (x+y)·(x^{2^k}+y^{2^k})·(x^{2^{2k}}+y^{2^{2k}})`. |
| S1.1b | `Ba_add_right` | `B_a(x, y₁+y₂) = B_a(x,y₁) + B_a(x,y₂)` | Medium | Follows from S1.1a: each mixed term is of the form `x^{2^i}·y^{2^j}`, which is additive in `y`. |
| S1.1c | `Ba_symm` | `B_a(x,y) = B_a(y,x)` | Medium | Follows from S1.1a: the cross terms come in symmetric pairs. |
| S1.1d | `Qa_smul` | `Q_a(c·x) = c·Q_a(x)` for `c ∈ F₂` | Easy | Just check `c=0` and `c=1`. |

**Mathematical detail for S1.1a**: Since `d = 2^{2k} − 2^k + 1`, we can write `x^d = x · x^{2^{2k}−2^k} = x · (x^{2^k−1})^{2^k} · x^0`... Actually, the cleaner way:
- `x^d = x · (x^{2^k})^{2^k−1}` is complicated.
- Better: `(x+y)^d = (x+y) · (x+y)^{2^{2k}} · (x+y)^{−2^k}` ... no, not right.
- The correct expansion uses `d = 2^{2k} − 2^k + 1` to get:
  ```
  (x+y)^d = (x+y)^{2^{2k}} · (x+y)^{−2^k} · (x+y)
           = (x^{2^{2k}} + y^{2^{2k}}) · inv(...) · (x+y)
  ```
  This doesn't work cleanly.
- **Better approach**: Use the factorization `d = 1 + 2^k(2^k − 1)`, so:
  ```
  x^d = x · x^{2^k(2^k−1)} = x · (x^{2^k})^{2^k−1}
  ```
  Then cross terms of `(x+y)^d + x^d + y^d` in char 2:
  ```
  = (x+y)·((x+y)^{2^k})^{2^k−1} + x·(x^{2^k})^{2^k−1} + y·(y^{2^k})^{2^k−1}
  ```
- **Cleanest approach**: Factor as `d·1 = (2^k+1)(2^k−1) + 2 = ...`. Actually, note:
  `d = 2^{2k} − 2^k + 1`, and `d(2^k+1) = 2^{3k}+1` (already proved as `kasamiExp_mul_identity`).
  So `x^{d(2^k+1)} = x^{2^{3k}+1} = x · x^{2^{3k}}`.
  The cross terms in `(x+y)^d` can be determined by the fact that in char 2, the multinomial expansion of a product of Frobenius-shifted terms has only degree-2 cross terms (products of exactly 2 of the three factors), giving 6 terms that pair into 3 symmetric pairs.

#### S1.2: `kasami_Ba_simplified` — B_a = Tr(y · L_a(x))
**Difficulty**: Hard
**Estimated sub-lemmas**: 3 (all essentially proved in existing infrastructure)

| ID | Sub-lemma | Statement | Difficulty | Status |
|----|-----------|-----------|------------|--------|
| S1.2a | `trace_frob_eq` | `Tr(x^{2^i}) = Tr(x)` | Easy | Equivalent to `tr2_pow2` ✅ |
| S1.2b | `add_pow_two_pow` | `(x+y)^{2^i} = x^{2^i} + y^{2^i}` | Easy | Equivalent to `char2_add_pow` ✅ |
| S1.2c | `frob_card_eq_id` | `x^{2^n} = x` | Easy | Equivalent to `F2n_frobenius` ✅ |

**Proof**: From S1.1a, we have `B_a(x,y) = Tr(a · (cross terms))`. Each cross term is of the form `x^{2^i} · y^{2^j}`. Apply `Tr(z^{2^i}) = Tr(z)` to absorb Frobenius powers, then factor out `y` to get `Tr(y · (a^{2^{2k}}·x^{2^{2k}} + a^{2^k}·x^{2^k} + a·x + ...))`. The resulting coefficient of `y` is exactly `L_a(x)` after applying `x^{2^n} = x` to reduce indices mod `n`.

**Key insight**: The cross terms from `(x+y)^d + x^d + y^d` for `d = 2^{2k}−2^k+1` are:
```
a·(x^{2^{2k}}·y + x·y^{2^{2k}}) + a·(x^{2^k}·y^{2^{2k}−2^k} + ...) + ...
```
After applying `Tr(z^{2^i}) = Tr(z)`, these collapse to `Tr(y · L_a(x))` where:
```
L_a(x) = a·x^{2^{2k}} + a^{2^k}·x^{2^k} + a^{2^{2k}}·x
```
Note: The exact form of `L_a` depends on the pairing between the project's `linPolyL` definition and the bridge expansion. Check that `linPolyL k (a*x)` matches.

#### S1.3: `kasami_radical_eq_kernel` — rad(Q_a) = ker(L_a)
**Difficulty**: Medium
**Estimated sub-lemmas**: 0 (direct from S1.2 + `tr2_surjective`)

**Proof**: `x ∈ rad(B_a)` iff `∀ y, B_a(x,y) = 0` iff `∀ y, Tr(y · L_a(x)) = 0` (by S1.2). Since `Tr` is surjective, `y · L_a(x)` ranges over all elements as `y` varies, so `Tr(y · L_a(x)) = 0` for all `y` iff `L_a(x) = 0`. Thus `rad = ker(L_a)`.

The non-degeneracy argument: if `L_a(x) ≠ 0`, pick `y = c / L_a(x)` where `Tr(c) = 1` (exists by surjectivity) to get `Tr(y · L_a(x)) = Tr(c) = 1 ≠ 0`.

#### S1.4: `kasami_radical_small` — |rad| ∈ {1, 2}
**Difficulty**: Medium
**Estimated sub-lemmas**: 1–2

**Proof**: By S1.3, `|rad(Q_a)| = |ker(L_a)|`. By `linPolyL_ker_card_classification`, `|ker(L_k)| ∈ {1, 4}` when `gcd(k,n)=1`. However, the radical is `ker(L_a(a·-))` (the kernel of `x ↦ L_k(a·x)`), and the map `x ↦ a·x` is a bijection since `a ≠ 0`. So `|ker(L_a(a·-))| = |ker(L_k)|`.

**Issue**: There's a potential mismatch between `|ker(L_k)| ∈ {1,4}` (from Kernel.lean) and the claimed `|rad| ∈ {1,2}`. This needs careful reconciliation:
- If `|ker(L_k)| = 1`, then `|rad| = 1` (radical is trivial, rank = n).
- If `|ker(L_k)| = 4`, then `|rad| = 4` (radical has dim 2, rank = n−2).

Wait — this contradicts the "rank ∈ {n−1, n}" claim. Let me re-examine.

**Correction**: The `linPolyL` in the project is `L_k(x) = x^{2^{2k}} + x^{2^k} + x`, which has kernel cardinality in `{1, 4}` when `gcd(k,n)=1` (dimension 0 or 2 over GF(2)). But the bilinear form `B_a(x,y) = Tr(y · L_a(x))` has a different kernel — it's `{x : L_a(x) = 0}` intersected with {x : Q_a(x) = 0}, but the **radical** is just `{x : ∀ y, B(x,y) = 0} = ker(L_a)`.

So actually:
- `|ker(L_k)| = 1` ⟹ radical trivial, `S(Q)² = 2^n · 1 = 2^n` → `S(Q) = ±2^{n/2}` (but n is odd, so this gives non-integer)
- `|ker(L_k)| = 4` ⟹ `|rad| = 4`, `S(Q)² = 2^n · 4 = 2^{n+2}` → `S(Q) = ±2^{(n+2)/2}`

Hmm, this doesn't match the expected `{0, ±2^{(n+1)/2}}` for AB. Let me reconsider.

**Re-examination**: The issue is that `linPolyL` as defined in the project may differ from the `L_a` needed for the bilinear form. The `linPolyL k x` in the project is the *generic* linearized polynomial for the Kasami kernel analysis, while the bilinear form uses a *scaled* version `L_a(x) = a·x^{2^{2k}} + a^{2^k}·x^{2^k} + a^{2^{2k}}·x` (with coefficients depending on `a`).

The key observation: for `a ≠ 0`, the kernel of `L_a` is related to `ker(linPolyL)` by the bijection `x ↦ a^{-1}·x` (or similar), but the exact relation depends on the precise definitions.

**Alternative**: The KasamiBridgeLemmas.lean (kasami-26) claims `|ker(L_a)| ∈ {1, 2}`, which would give:
- `|ker| = 1`: `S² = 2^m · 1 = 2^m`, rank = m is odd → S = 0 (by the Gauss sum odd-rank vanishing)
- `|ker| = 2`: `S² = 2^m · 2 = 2^{m+1}`, rank = m−1 = 2k is even → `S = ±2^{(m+1)/2} = ±2^{k+1}`

This matches the expected AB spectrum `{0, ±2^{k+1}}` when `m = 2k+1`.

So the kernel cardinality `{1, 2}` in the bridge file uses a different normalization than `linPolyL_ker_card_classification`'s `{1, 4}`. Reconciling these requires understanding:
- `linPolyL k x = x^{2^{2k}} + x^{2^k} + x` has ker ∈ {1, 4}
- The bilinear form's `L_a` is not exactly `linPolyL` but a scaled version
- The scaling changes the kernel cardinality

**Sub-lemma needed**:

| ID | Sub-lemma | Statement | Difficulty |
|----|-----------|-----------|------------|
| S1.4a | `kernel_La_vs_linPolyL` | Relate `ker(L_a)` to `ker(linPolyL k ∘ (a·-))` or similar | Medium |
| S1.4b | `radical_card_values` | `|rad(Q_a)| ∈ {1, 2^{gcd(k,n)}}` | Medium |

#### S1.5: `kasami_Qa_vanishes_on_radical` — Q_a|_{rad} = 0
**Difficulty**: Hard
**Estimated sub-lemmas**: 2–3

| ID | Sub-lemma | Statement | Difficulty | Approach |
|----|-----------|-----------|------------|----------|
| S1.5a | `radical_trivial_case` | If `|rad|=1`, Q vanishes trivially (Q(0)=0) | Easy | |
| S1.5b | `radical_generator_trace_zero` | If `x₀ ∈ ker(L_a)\{0}`, then `Tr(a·x₀^d) = 0` | Hard | Uses the algebraic relation from `L_a(x₀) = 0`. If `L_a(x₀) = 0`, write `x₀^{2^{2k}} = f(x₀, x₀^{2^k}, a)`, substitute into `x₀^d = x₀ · (x₀^{2^k})^{2^k−1}`, simplify using Frobenius properties, and show the result lies in `Im(Frob − id) = ker(Tr)`. |
| S1.5c | `Q_linear_on_radical` | `Q_a|_{rad}` is linear (from QuadFormF2 theory) | Easy | Already proved as `radicalRestriction` in `QuadFormGF2/Defs.lean` ✅ |

**Mathematical detail for S1.5b**: If `L_a(x₀) = 0`, i.e., `a·x₀^{2^{2k}} + a^{2^k}·x₀^{2^k} + a^{2^{2k}}·x₀ = 0`, then:
- `Tr(a·x₀^d) = Tr(a·x₀^{2^{2k}−2^k+1})`.
- Using `L_a(x₀) = 0` to express `x₀^{2^{2k}}` in terms of lower Frobenius powers.
- After substitution and simplification, `a·x₀^d` can be written as `z^2 + z` for some `z` (i.e., in the Artin-Schreier image).
- By `artinSchreier_image_eq_trace_ker`, `Tr(z^2 + z) = 0`.

#### S1.6: `kasami_walsh_eq_expSum` — W_f(a) = S(Q_a)
**Difficulty**: Easy–Medium
**Estimated sub-lemmas**: 1

**Proof**: By definition:
- `wht(kasamiF n k)(a) = ∑_x χ(a·x + kasamiF(x)) = ∑_x (-1)^{Tr(a·x + x^d)}`
- Wait, the WHT definition in the project may use a different convention. Check:
  - If `wht f a = ∑_x (-1)^{Tr(a·x^d)}` (when `f(x)=x^d`), this is directly `S(Q_a)`.
  - If `wht f a = ∑_x (-1)^{Tr(a·x + f(x))}` (standard convention), this is `S(Q_{1,a})` where `Q_{1,a}(x) = Tr(x^d + a·x)`.

**Key sub-lemma**: The shift by the linear term `a·x` can be absorbed by completing the square. For power functions with odd exponent `d`, the substitution `x → x + c` where `c` solves `d·c^{d-1} = a` reduces the affine form to a pure quadratic form.

| ID | Sub-lemma | Statement | Difficulty |
|----|-----------|-----------|------------|
| S1.6a | `wht_as_quadform_expSum` | `wht(f)(a) = ∑_x signZ(Q_a(x))` for appropriate Q_a | Medium |

#### S1.7: `kasami_walsh_sq_values` — W_f(a)² ∈ {0, 2^{n+1}}
**Difficulty**: Medium (assembly from S1.3–S1.6)
**Estimated sub-lemmas**: 0 (pure assembly)

**Proof**:
1. `W_f(a) = S(Q_a)` (by S1.6)
2. `S(Q_a)² = 2^n · |rad(Q_a)|` (by `expSum_sq_eq_card_mul_radical_card`) when `Q_a|_{rad} = 0` (by S1.5)
3. `|rad(Q_a)| ∈ {1, 2}` (by S1.4):
   - If `|rad| = 1`: `S² = 2^n`, but since `n` is odd, `S = 0` (by Gauss sum odd-rank vanishing)
   - If `|rad| = 2`: `S² = 2^{n+1}`
4. Therefore `W_f(a)² ∈ {0, 2^{n+1}}`.

### S1 Proving Order (Bottom-Up)

```
Phase 1 (char-2 algebra):
  S1.1a → S1.1b, S1.1c, S1.1d  (all independent after S1.1a)

Phase 2 (bridge construction):
  S1.1 (S1.1a–d) → S1.2  (needs S1.1a + Frobenius identities)

Phase 3 (kernel connection):
  S1.2 → S1.3  (+ tr2_surjective)
  S1.3 → S1.4  (+ linPolyL_ker_card_classification)

Phase 4 (vanishing on radical):
  S1.3 → S1.5  (independent of S1.4)

Phase 5 (WHT connection):
  S1.2 → S1.6  (independent of S1.3–S1.5)

Phase 6 (assembly):
  S1.4 + S1.5 + S1.6 → S1.7 → kasami_is_ab
```

---

## S2: `ab_implies_vanishing` — AB ⟹ Spectral Triple Product Vanishing

**Location**: `Kasami/TripleCount.lean:120`
**Statement**: If Kasami is AB, then `AlmostBentVanishing n k`:
`∑_{a≠0} S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂)) = (2^n − 2) · 2^{2n}`

**Depends on**: S1 (`kasami_is_ab`) + `ab_implies_apn` ✅

### Decomposition Tree for S2

```
ab_implies_vanishing
  ├── ab_implies_vanishing_assembled ✅ (VanishingProof.lean)
  │     (framework proved; needs hvanish hypothesis)
  └── hvanish: ∑_{a≠0} S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂)) = target
        ├── S_Δ_relation [S2.1]
        │     └── S_Δ(c) relates to G₁(c) via 2-to-1 property
        ├── wht_cube_sum_ab [S2.2]
        │     └── ∑_{a≠0} G₁(av₁)·G₁(av₂)·G₁(a(v₁+v₂))
        │           computed using AB spectrum
        ├── triple_product_vanishing_from_fourth_moment [S2.3]
        │     └── Key: use ∑_a W⁴ = 2·(2^n)³ to control triple products
        └── spectral_assembly [S2.4]
```

### Sub-Lemma Details for S2

| ID | Sub-lemma | Statement | Difficulty | Approach |
|----|-----------|-----------|------------|----------|
| S2.1 | `delta_charsum_as_wht` | `S_Δ(c) = ∑_{b∈Δ} χ(cb) = ... = (G₁(c) + ε) / 2` or similar relation to WHT | Hard | Use the 2-to-1 property of `δ`: each element of `Δ` is hit by exactly 2 values of `b`, giving `S_Δ(c) = (1/2)·∑_b χ(c·g(b))`. Then relate `∑_b χ(c·g(b))` to `W_f` via the definition `g(b) = f(b) + f(b+1) + 1`. |
| S2.2 | `wht_triple_sum_vanishing` | `∑_{a≠0} W(av₁)·W(av₂)·W(a(v₁+v₂)) = ...` for AB functions | Very Hard | This is the deepest spectral identity. For AB functions, `W(a)² ∈ {0, 2^{n+1}}`, so `W(a) ∈ {0, ±2^{(n+1)/2}}`. The triple product involves a third moment of the spectrum. Standard approach: use Parseval + fourth moment + moment constraints to determine the triple sum. |
| S2.3 | `delta_sum_vs_wht_sum` | Convert triple sum over `Δ` to triple sum over WHT | Medium | Algebraic conversion using S2.1. |
| S2.4 | `vanishing_assembly` | Assemble S2.1–S2.3 into `ab_implies_vanishing` | Medium | |

**Alternative approach for S2** (may be simpler):
Instead of going through `S_Δ` ↔ WHT, use the **direct character-sum method**:
1. The triple count equals `(1/2^n) · ∑_{a} S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))`.
2. The `a=0` term contributes `|Δ|³ = 2^{3(n-1)}`.
3. For `a≠0`, `S_Δ(c) = (1/2)(∑_b χ(c·f(b)) + ∑_b χ(c·(f(b)+1)))` from the 2-to-1 property.
4. This relates to `W_f` through convolution identities.
5. The AB condition forces the `a≠0` contribution to equal the required value.

| ID | Sub-lemma | Statement | Difficulty |
|----|-----------|-----------|------------|
| S2.5 | `charsum_delta_expansion` | `S_Δ(c) = (1 + χ(c))/2 · W_f(1,c)` or similar | Hard |
| S2.6 | `cube_product_ab_spectrum` | For AB `f`: `∑_{a≠0} W(av₁)²·W(av₂)·W(a(v₁+v₂)) = ...` | Very Hard |
| S2.7 | `moment_constraint_triple` | Third spectral moment from AB + Parseval | Hard |

### S2 Proving Order

```
Phase 1: S2.1 or S2.5 (S_Δ ↔ WHT relation)
Phase 2: S2.2 or S2.6 (spectral triple sum, the core)
Phase 3: S2.3, S2.4 (assembly)
```

---

## S3: `ccd_crossterm_gives_linPolyL` — CCD Cross-Term Factorization

**Location**: `LinearizedPoly/KasamiKernel.lean:176`
**Statement**: From `z^{2^{3k}} + z = C(y₂) + C(y₂+z)` and the original differential equation, conclude `linPolyL k z = 0`.

**Context**: This is the deepest step of the Canteaut-Charpin-Dobbertin (2000) proof. It's on the critical path for `kasami_apn` (when `3|n`), but **not** strictly needed for `kasami_is_ab` via the quadratic form route.

### Decomposition Tree for S3

```
ccd_crossterm_gives_linPolyL
  ├── z_pow_3k_plus_z_eq_Mk_Lk [S3.1]
  │     └── z^{2^{3k}} + z = M_k(L_k(z))
  ├── C_diff_factors_through_Mk [S3.2]
  │     └── C(y₂) + C(y₂+z) factors through M_k
  ├── Mk_injectivity_on_image [S3.3]
  │     └── If M_k(u) = M_k(v), then u = v or u = v+1
  └── Lk_zero_conclusion [S3.4]
        └── From M_k(L_k(z)) = M_k(something), conclude L_k(z) = 0
```

### Sub-Lemma Details for S3

| ID | Sub-lemma | Statement | Difficulty | Approach |
|----|-----------|-----------|------------|----------|
| S3.1 | `z_pow_3k_plus_z_eq_Mk_Lk` | `z^{2^{3k}} + z = (L_k(z))^{2^k} + L_k(z)` | Medium | Algebraic verification. Expand `L_k(z) = z^{2^{2k}} + z^{2^k} + z`, then `M_k(L_k(z)) = L_k(z)^{2^k} + L_k(z)`. Compute: `L_k(z)^{2^k} = z^{2^{3k}} + z^{2^{2k}} + z^{2^k}` (Freshman's dream). So `M_k(L_k(z)) = (z^{2^{3k}} + z^{2^{2k}} + z^{2^k}) + (z^{2^{2k}} + z^{2^k} + z) = z^{2^{3k}} + z` ✓ |
| S3.2 | `C_diff_as_Mk` | `C(y₂) + C(y₂+z)` can be expressed as `M_k(w)` for some specific `w` | Hard | `C(t) = t^{2^{2k}+2^k} + t^{2^k+1} + t^{2^{2k}+1}` (ccdCrossTerm). The difference `C(y₂+z) + C(y₂)` expands using bilinearity of each term. Each term like `(y₂+z)^{2^{2k}+2^k} + y₂^{2^{2k}+2^k}` can be expanded using char-2 Frobenius. After collecting terms, show the result equals `M_k(w)` for a suitable `w` involving `y₂, z` and their Frobenius images. |
| S3.3 | `Mk_fiber_structure` | If `M_k(u) = M_k(v)`, then `M_k(u+v) = 0`, so `u+v ∈ ker(M_k) = GF(2^{gcd(k,n)}) ∩ F₂ = {0,1}` when `gcd(k,n)=1` | Medium | Uses `linPolyM_ker_eq_coprime`: `ker(M_k) = {0,1}` when `gcd(k,n)=1`. |
| S3.4 | `Lk_zero_from_Mk_eq` | From `M_k(L_k(z)) = M_k(w)` and the specific form of `w`, deduce `L_k(z) = 0` | Hard | By S3.3, `L_k(z) + w ∈ {0, 1}`. Then use the original differential equation constraints to rule out `L_k(z) + w = 1`, leaving `L_k(z) = w`. Then show `w = 0` from the constraints, giving `L_k(z) = 0`. |

### S3 Proving Order

```
Phase 1: S3.1 (algebraic identity, independent)
Phase 2: S3.2 (hardest sub-lemma, independent of S3.1)
Phase 3: S3.3 (uses ker(M_k) classification ✅)
Phase 4: S3.4 (assembly from S3.1–S3.3)
```

---

## S4: `kasami_wht_sq_trichotomy` — WHT² Trichotomy (Redundant)

**Location**: `QuadFormGF2/KasamiConnection.lean:183`
**Statement**: `wht(kasamiF n k)(a)² ∈ {0, 2^{n+1}}`

**Note**: This is mathematically identical to S1.7 (`kasami_walsh_sq_values`), formulated in a different file with slightly different type signatures. **Proving S1 automatically proves S4** since `kasami_is_ab` implies this trichotomy.

### Decomposition

Once S1 is proved, S4 follows trivially:
```
kasami_wht_sq_trichotomy
  └── kasami_is_ab ✅ (after S1 is proved)
        └── unfold IsAlmostBent, apply to specific `a`
```

No additional sub-lemmas needed beyond those for S1.

---

## Complete Sub-Lemma Inventory

### Summary Table

| Sorry | Sub-lemmas | Total est. | Priority |
|-------|------------|------------|----------|
| S1 (`kasami_is_ab`) | S1.1a–d, S1.2, S1.3, S1.4, S1.5a–b, S1.6, S1.7 | ~12 | **Critical** |
| S2 (`ab_implies_vanishing`) | S2.1–S2.7 | ~7 | **Critical** |
| S3 (`ccd_crossterm_gives_linPolyL`) | S3.1–S3.4 | ~4 | Useful |
| S4 (`kasami_wht_sq_trichotomy`) | (follows from S1) | 0 | Redundant |
| **Total** | | **~23** | |

### Difficulty Rankings

| Difficulty | Sub-lemmas |
|------------|------------|
| **Very Hard** | S2.2 (wht_triple_sum_vanishing), S2.6 (cube_product_ab_spectrum) |
| **Hard** | S1.1a (kasami_cross_terms), S1.2 (Ba_simplified), S1.5b (radical_generator_trace_zero), S2.1 (delta_charsum_as_wht), S3.2 (C_diff_as_Mk), S3.4 (Lk_zero_from_Mk_eq) |
| **Medium** | S1.1b, S1.1c, S1.3, S1.4, S1.6, S2.3, S2.4, S3.1, S3.3 |
| **Easy** | S1.1d (Qa_smul), S1.5a (radical_trivial_case), S1.7 (assembly) |

### Recommended Attack Order

```
Batch 1 (Foundation, parallel):
  ├── S3.1: z^{2^{3k}}+z = M_k(L_k(z))        [independent]
  ├── S1.1a: kasami_cross_terms                   [independent]
  └── S1.1d: Qa_smul                              [independent]

Batch 2 (From S1.1a, parallel):
  ├── S1.1b: Ba_add_right
  ├── S1.1c: Ba_symm
  └── S1.2: kasami_Ba_simplified

Batch 3 (From S1.2):
  ├── S1.3: radical_eq_kernel                      [parallel with S1.6]
  └── S1.6: walsh_eq_expSum                        [parallel with S1.3]

Batch 4 (From S1.3, parallel):
  ├── S1.4: radical_small
  └── S1.5: Qa_vanishes_on_radical

Batch 5 (Assembly):
  └── S1.7: walsh_sq_values → kasami_is_ab (S1 done!)

Batch 6 (S3, from S3.1):
  ├── S3.2: C_diff_as_Mk
  ├── S3.3: Mk_fiber_structure
  └── S3.4: Lk_zero_conclusion → S3 done!

Batch 7 (S2, depends on S1):
  ├── S2.1: delta_charsum_as_wht
  ├── S2.2: wht_triple_sum_vanishing (HARDEST)
  └── S2.3–S2.4: assembly → S2 done!

Final: kasami_P3 compiles sorry-free!
```

---

## Cross-Reference: Existing Infrastructure Available for Each Sub-Lemma

| Sub-lemma | Available Infrastructure |
|-----------|------------------------|
| S1.1a | `char2_add_pow` ✅, `char2_sum_powers` ✅ |
| S1.1b–c | `QuadFormF2.polar_add_left/right` ✅, `polar_comm` ✅ |
| S1.2 | `tr2_pow2` ✅, `F2n_frobenius` ✅, `linPolyL` def ✅ |
| S1.3 | `tr2_surjective` ✅ |
| S1.4 | `linPolyL_ker_card_classification` ✅ |
| S1.5 | `radicalRestriction` ✅, `artinSchreier_image_eq_trace_ker` ✅ |
| S1.6 | `wht` def ✅, `kasamiTracePower` ✅, `kasamiExpSum_eq` ✅ |
| S1.7 | `expSum_sq_eq_card_mul_radical_card` ✅ |
| S2.1 | `kasamiDelta_card` ✅, `deltaGen_paired` ✅, `deltaCharSum_double` ✅ |
| S2.2 | `ab_fourth_moment` ✅, `wht_parseval` ✅ |
| S3.1 | `linPolyL` def ✅, `linPolyM` def ✅, `char2_add_pow` ✅ |
| S3.3 | `linPolyM_ker_eq_coprime` ✅ |

---

## Appendix: KasamiBridgeLemmas.lean (kasami-26) ↔ QuadFormBridge.lean (kasami-27) Correspondence

| KasamiBridgeLemmas (26) | QuadFormBridge (27) | This decomposition |
|--------------------------|---------------------|-------------------|
| `add_pow_two_pow` | (part of S1.1) | S1.2b |
| `kasami_cross_terms` | (part of S1.1) | S1.1a |
| `Ba_add_right` | (part of S1.1) | S1.1b |
| `Ba_symm` | (part of S1.1) | S1.1c |
| `Qa_smul` | (part of S1.1) | S1.1d |
| `trace_frob_eq` | (part of S1.2) | S1.2a |
| `trace_sq_eq` | (part of S1.2) | S1.2a (special case) |
| `frob_card_eq_id` | (part of S1.2) | S1.2c |
| `La_additive` | (part of S1.2) | S1.2 (intermediate) |
| `Ba_eq_trace_La` | `kasami_Ba_simplified` | S1.2 |
| `kerLa_add_mem` | (part of S1.3) | S1.3 |
| `kerLa_card_le` | (part of S1.4) | S1.4 |
| `kerLa_card_dichotomy` | `kasami_radical_small` | S1.4 |
| `radical_eq_kerLa` | `kasami_radical_eq_kernel` | S1.3 |
| `expSum_sq_eq` | (already proved) | ✅ |
| `rank_parity_cases` | (part of S1.7) | S1.7 |
| `gauss_sum_odd_rank` | (part of S1.7) | S1.7 |
| `gauss_sum_even_rank` | (part of S1.7) | S1.7 |
| `kasami_expSum_values` | (part of S1.7) | S1.7 |
| `two_pow_sq` | (arithmetic) | trivial |
| `wht_eq_expSum` | `kasami_walsh_eq_expSum` | S1.6 |
