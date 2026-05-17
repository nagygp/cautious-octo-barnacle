# Modularizing the Proof that the Kasami Function is Almost Bent

## Background

The **Kasami function** is $f(x) = x^d$ on $\operatorname{GF}(2^n)$ where $d = 2^{2k} - 2^k + 1$, with $\gcd(k, n) = 1$ and $n$ odd.

A function $f : \operatorname{GF}(2^n) \to \operatorname{GF}(2^n)$ is **Almost Bent (AB)** if its Walsh–Hadamard transform
$$W_f(a, b) = \sum_{x \in \operatorname{GF}(2^n)} (-1)^{\operatorname{Tr}(ax^d + bx)}$$
takes values only in $\{0, \pm 2^{(n+1)/2}\}$ for all $(a,b)$ with $a \ne 0$.

---

## The Standard Proof Architecture (Quadratic-Form Route)

The classical proof (Canteaut–Charpin–Dobbertin, also in Carlet's monograph) proceeds via:

1. **Reduce Walsh transform to exponential sum of a quadratic form.**
   For each $a \ne 0$, the map $Q_a(x) = \operatorname{Tr}(a \cdot x^d)$ is a quadratic form $\operatorname{GF}(2)^n \to \operatorname{GF}(2)$.
   The Walsh transform $W_f(a,b)$ equals a sign-change of the exponential sum of a related quadratic form.

2. **Determine the rank of the associated bilinear form.**
   The bilinear form $B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)$ has rank either $n-1$ or $n$.
   This is proved by analyzing the kernel of $B_a$: it equals the set of solutions to a linearized polynomial equation, whose solution space is controlled by $\gcd(k,n) = 1$.

3. **Apply the Gauss-sum formula for quadratic forms over $\operatorname{GF}(2)$.**
   For a quadratic form of rank $r$ on $\operatorname{GF}(2)^n$, the exponential sum satisfies $S(Q)^2 = 2^n \cdot 2^{n-r}$ (when $Q$ vanishes on the radical). Since rank $\in \{n-1, n\}$, we get $S(Q)^2 \in \{0, 2^{n+1}\}$, hence $W_f(a,b) \in \{0, \pm 2^{(n+1)/2}\}$.

---

## Tiny Components / Lemmas Needed

Below is a complete breakdown into small, independently provable lemmas. Each is tagged with its approximate difficulty and what it depends on.

### Layer 0: Field and Trace Infrastructure

These set up the working environment. Mathlib has `GaloisField p n`, `Algebra.trace`, `frobenius`, and `AddChar`, but several connective lemmas are missing.

| # | Lemma | Statement (informal) | Difficulty | Mathlib coverage |
|---|-------|----------------------|------------|-----------------|
| 0a | `galoisField_card` | $\|{\operatorname{GF}(2^n)}\| = 2^n$ | Easy | `GaloisField.card` exists ✓ |
| 0b | `trace_is_GF2_valued` | $\operatorname{Tr} : \operatorname{GF}(2^n) \to \operatorname{GF}(2)$ | Easy | `Algebra.trace` exists, but casting to `ZMod 2` needs wrapping |
| 0c | `trace_additive` | $\operatorname{Tr}(x+y) = \operatorname{Tr}(x) + \operatorname{Tr}(y)$ | Easy | Follows from `map_add` on `Algebra.trace` ✓ |
| 0d | `trace_frobenius` | $\operatorname{Tr}(x^{2^i}) = \operatorname{Tr}(x)$ | Medium | Needs `Algebra.trace` + Frobenius properties |
| 0e | `trace_surjective` | $\operatorname{Tr}$ is surjective onto $\operatorname{GF}(2)$ | Medium | Standard, may need building |
| 0f | `addChar_from_trace` | The map $\chi(x) = (-1)^{\operatorname{Tr}(x)}$ is a nontrivial additive character | Medium | `AddChar` exists but this specific construction needs work |

### Layer 1: Kasami Exponent Basics

| # | Lemma | Statement (informal) | Difficulty |
|---|-------|----------------------|------------|
| 1a | `kasami_exp_def` | $d = 2^{2k} - 2^k + 1$ | Trivial (definition) |
| 1b | `kasami_exp_odd` | $d$ is odd | Easy (since $2^{2k} - 2^k$ is even) |
| 1c | `kasami_gcd` | $\gcd(d, 2^n - 1) = 1$ when $\gcd(k, n) = 1$ and $n$ odd | Medium |
| 1d | `kasami_is_permutation` | $x \mapsto x^d$ is a permutation of $\operatorname{GF}(2^n)^*$ | Medium (follows from 1c) |

### Layer 2: The Quadratic Form $Q_a$

| # | Lemma | Statement (informal) | Difficulty |
|---|-------|----------------------|------------|
| 2a | `Qa_def` | $Q_a(x) = \operatorname{Tr}(a \cdot x^d)$ is well-defined as a map $\operatorname{GF}(2^n) \to \operatorname{GF}(2)$ | Easy |
| 2b | `Qa_is_quadratic` | $Q_a$ is a quadratic form (i.e., $Q_a(\lambda x) = \lambda^2 Q_a(x)$ and $B_a$ is bilinear) — but over $\operatorname{GF}(2)$, $\lambda^2 = \lambda$, so this reduces to: $B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)$ is $\operatorname{GF}(2)$-bilinear | Hard |
| 2c | `Ba_explicit` | $B_a(x,y) = \operatorname{Tr}\bigl(a \cdot [(x+y)^d + x^d + y^d]\bigr)$ | Easy (definition + trace linearity) |
| 2d | `kasami_power_expansion` | $(x+y)^d + x^d + y^d = \sum_{\text{mixed terms}} (\ldots)$ — specifically for $d = 2^{2k} - 2^k + 1$: $(x+y)^d + x^d + y^d = x^{2^{2k}} y + x y^{2^{2k}} + x^{2^k} y^{2^{2k}-2^k} + \ldots$ (the cross terms) | Hard |
| 2e | `Ba_simplified` | Using trace-Frobenius ($\operatorname{Tr}(z^{2^i}) = \operatorname{Tr}(z)$), simplify $B_a(x,y)$ to $\operatorname{Tr}(y \cdot L_a(x))$ where $L_a$ is a linearized polynomial | Hard |

### Layer 3: Linearized Polynomial and Kernel Analysis

| # | Lemma | Statement (informal) | Difficulty |
|---|-------|----------------------|------------|
| 3a | `La_def` | $L_a(x) = a^{2^{2k}} x^{2^{2k}} + a x + a^{2^k} x^{2^k}$ (or equivalent form after Frobenius simplification) | Medium |
| 3b | `La_is_linearized` | $L_a$ is $\operatorname{GF}(2)$-linear (i.e., $L_a(x+y) = L_a(x) + L_a(y)$) | Medium |
| 3c | `radical_eq_kernel_La` | $\operatorname{rad}(B_a) = \ker(L_a)$ (since $B_a(x,y) = \operatorname{Tr}(y \cdot L_a(x))$ and $\operatorname{Tr}$ is surjective) | Medium |
| 3d | `kernel_La_bound` | $\dim_{\operatorname{GF}(2)} \ker(L_a) \le 1$ when $\gcd(k,n)=1$ and $a \ne 0$ | **Hard** (key lemma) |
| 3e | `rank_Ba` | $\operatorname{rank}(B_a) \in \{n-1, n\}$ | Medium (follows from 3c + 3d) |

**Lemma 3d** is the technical heart. It requires showing that the equation $L_a(x) = 0$ (for $a \ne 0$) has at most $2$ solutions in $\operatorname{GF}(2^n)$. The sub-decomposition:

| # | Sub-lemma for 3d | Statement | Difficulty |
|---|-------------------|-----------|------------|
| 3d-i | `La_zero_implies_linearized` | If $L_a(x) = 0$ and $x \ne 0$, then $t = x^{2^k - 1}$ satisfies $t^{2^k+1} + t + 1 = 0$ (after dividing by appropriate powers) | Hard |
| 3d-ii | `linearized_poly_solutions` | The equation $t^{2^k+1} + t + 1 = 0$ over $\operatorname{GF}(2^n)$: the number of solutions is related to $\gcd(k,n)$ | Hard |
| 3d-iii | `gcd_condition_implies_no_solution` | When $\gcd(k,n)=1$ and $n$ is odd, $t^{2^k+1} + t + 1 = 0$ has no solution in $\operatorname{GF}(2^n)$ (or at most one), giving $\ker L_a \subseteq \{0\}$ or $\dim \le 1$ | **Very Hard** |

### Layer 4: Gauss Sum for GF(2) Quadratic Forms

| # | Lemma | Statement (informal) | Difficulty |
|---|-------|----------------------|------------|
| 4a | `expSum_def` | $S(Q) = \sum_{x \in V} (-1)^{Q(x)}$ for $Q : V \to \operatorname{GF}(2)$ | Easy (definition) |
| 4b | `expSum_sq_rank` | $S(Q)^2 = 2^n \cdot |\operatorname{rad}(Q)|$ when $Q$ vanishes on $\operatorname{rad}(B)$ | Hard (but user says this is done) |
| 4c | `Qa_vanishes_on_radical` | $Q_a$ vanishes on $\operatorname{rad}(B_a)$ | Medium-Hard |

**For 4c:** If $\operatorname{rad}(B_a) = \{0\}$ this is trivial. If $\operatorname{rad}(B_a)$ has dimension 1, one needs to check $Q_a(x_0) = 0$ for the generator $x_0$ of the radical. This uses the specific structure of the Kasami exponent.

### Layer 5: Putting It Together

| # | Lemma | Statement (informal) | Difficulty |
|---|-------|----------------------|------------|
| 5a | `walsh_eq_expSum` | $W_f(a,b) = \pm S(Q_{a,b})$ for appropriate quadratic form $Q_{a,b}(x) = Q_a(x) + \operatorname{Tr}(bx)$ | Medium |
| 5b | `walsh_sq_values` | $W_f(a,b)^2 \in \{0, 2^{n+1}\}$ (combining rank $\in \{n-1,n\}$ with Gauss sum formula) | Medium |
| 5c | `kasami_is_ab` | The Kasami function is Almost Bent | Easy (follows from 5b) |

---

## Three Alternative Modularization Strategies

### Strategy A: "Quadratic Form Route" (Classical, as above)

```
Layer 0: Field/Trace infrastructure
    ↓
Layer 1: Kasami exponent properties
    ↓
Layer 2: Quadratic form Q_a and bilinear form B_a
    ↓
Layer 3: Linearized polynomial kernel analysis  ←── hardest part
    ↓
Layer 4: GF(2) Gauss sum evaluation
    ↓
Layer 5: Assembly
```

**Pros:** Most natural; follows standard textbook proofs (Carlet, Cusick–Dobbertin).
**Cons:** Layer 3 requires substantial algebraic manipulation in characteristic 2.
**File structure:**
- `FieldTrace.lean` — Layers 0
- `KasamiExponent.lean` — Layer 1
- `KasamiQuadForm.lean` — Layer 2
- `LinearizedKernel.lean` — Layer 3
- `GF2GaussSum.lean` — Layer 4
- `KasamiAB.lean` — Layer 5

### Strategy B: "Direct Walsh Transform Calculation"

Instead of the quadratic form route, directly compute $W_f(a,b)^{2}$ by expanding and manipulating character sums.

```
Step 1: W_f(a,b)² = Σ_{x,y} χ(a(x^d + y^d) + b(x+y))
Step 2: Substitution y → x+z, getting Σ_x Σ_z χ(a·[(x+z)^d + x^d] + bz)
Step 3: Inner sum over x is an exponential sum of a quadratic form in x (for fixed z)
Step 4: Evaluate using character sum identities
```

**Pros:** Avoids formalizing abstract quadratic form theory; works directly with character sums.
**Cons:** More computation-heavy; the key difficulty (linearized polynomial kernel) reappears anyway.
**File structure:**
- `FieldTrace.lean`
- `KasamiExponent.lean`
- `CharacterSums.lean` — General character sum identities
- `WalshSquared.lean` — Direct $W^2$ computation
- `LinearizedKernel.lean` — Still needed for the inner sum evaluation
- `KasamiAB.lean`

### Strategy C: "Difference-Set / Divisibility Route"

Use the fact that $f$ is AB iff the equation $f(x+a) + f(x) = b$ has 0 or 2 solutions for all $a \ne 0, b$.

```
Step 1: Define "differential uniformity" δ(f) and AB ≡ δ(f) ≤ 2 (for odd n)
Step 2: Study the equation x^d + (x+1)^d = c (WLOG a=1 by permutation property)
Step 3: Substitution t = x/(x+1), reduce to t^{2^k+1} + t + 1 = ... 
Step 4: Count solutions using the linearized polynomial theory
```

**Pros:** More elementary (no quadratic forms or Gauss sums needed); the AB ↔ differential uniformity 2 equivalence is itself useful.
**Cons:** The equivalence "AB ↔ differentially 2-uniform" itself needs proof (which requires character sum theory). So this route either assumes that equivalence or needs even more infrastructure.
**File structure:**
- `FieldTrace.lean`
- `KasamiExponent.lean`
- `DifferentialUniformity.lean` — Definition and basic properties
- `ABiffDU2.lean` — AB ↔ differentially 2-uniform (needs character sums!)
- `KasamiDU2.lean` — Kasami is differentially 2-uniform
- `LinearizedKernel.lean`
- `KasamiAB.lean`

---

## Recommended Approach

**Strategy A** is the most direct for proving AB specifically and matches the infrastructure you described. The critical path is:

```
                    trace_frobenius (0d)
                          ↓
kasami_gcd (1c) → kasami_power_expansion (2d) → Ba_simplified (2e) → radical_eq_kernel_La (3c)
                                                                            ↓
                                                    kernel_La_bound (3d) ← linearized_poly_solutions (3d-ii)
                                                            ↓
                                                      rank_Ba (3e)
                                                            ↓
                    expSum_sq_rank (4b) + Qa_vanishes_on_radical (4c)
                                                            ↓
                                                    walsh_sq_values (5b)
                                                            ↓
                                                     kasami_is_ab (5c)
```

The **single hardest lemma** is `kernel_La_bound` (3d) / `gcd_condition_implies_no_solution` (3d-iii). Everything else is either infrastructure or relatively straightforward assembly.

---

## Mathlib Gaps to Be Aware Of

1. **No `GF(2)`-specific quadratic form theory.** Mathlib's `QuadraticForm` is over general rings/modules. You need to build the characteristic-2 specialization (where $Q(x+y) + Q(x) + Q(y) = B(x,y)$ replaces the usual polarization identity).

2. **No exponential sums / Walsh transforms.** These must be built from `AddChar` and `Finset.sum`.

3. **No linearized polynomial theory.** The theory of $\operatorname{GF}(q)$-linear maps of the form $L(x) = \sum a_i x^{q^i}$ is absent. You need kernel dimension bounds.

4. **Frobenius and trace interaction.** `Algebra.trace` exists and `frobenius` exists, but the key identity $\operatorname{Tr}(x^{2^i}) = \operatorname{Tr}(x)$ needs to be built (it follows from the Frobenius being a Galois automorphism and trace being the sum of Galois conjugates).

5. **`GaloisField` API.** The `GaloisField p n` type exists but has a thin API. You'll need to establish basic facts like every element satisfying $x^{2^n} = x$.

---

## Estimated Lemma Count and Effort

| Layer | Lemmas | Estimated Difficulty |
|-------|--------|---------------------|
| 0: Field/Trace | 6 | Moderate (API wrapping) |
| 1: Kasami exponent | 4 | Easy–Medium |
| 2: Quadratic form | 5 | Medium–Hard |
| 3: Kernel analysis | 5 + 3 sub-lemmas | **Hard** |
| 4: Gauss sum | 3 | Medium (partly done) |
| 5: Assembly | 3 | Easy–Medium |
| **Total** | **~29 lemmas** | |

The proof requires approximately **25–30 lemmas** in total, with the kernel analysis (Layer 3) being the critical bottleneck requiring the most mathematical sophistication.
