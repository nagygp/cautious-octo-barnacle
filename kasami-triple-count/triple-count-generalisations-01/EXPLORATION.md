# Generalizations of the Kasami Triple-Count Theorem

## The Established Result

For the Kasami function $f(x) = x^{4^k - 2^k + 1}$ over $\mathrm{GF}(2^n)$ with $\gcd(k,n)=1$, $n$ odd, $n \geq 3$:

$$|\{(x,y,z) \in \Delta^3 : v_1 x + v_2 y + (v_1+v_2)z = 0\}| = 2^{2n-3}$$

The proof decomposes into three independent facts:
1. **APN property** ⟹ $|\Delta| = 2^{n-1}$ (the derivative is 2-to-1)
2. **Fourier identity** ⟹ $|F| \cdot \kappa = \sum_a \hat\delta(v_1 a)\hat\delta(v_2 a)\hat\delta((v_1+v_2)a)$
3. **AB spectral collapse** ⟹ the Fourier sum equals $|\Delta|^3$

Combining: $\kappa = |\Delta|^3 / |F| = 2^{3(n-1)} / 2^n = 2^{2n-3}$.

---

## Axis 1: Other APN+AB Function Families (Same Exponent Formula)

The proof *only* uses two properties of the Kasami function: that it is **APN** (Almost Perfect Nonlinear) and **AB** (Almost Bent). Any function that is both APN and AB over $\mathrm{GF}(2^n)$ ($n$ odd) will satisfy the same triple-count formula $2^{2n-3}$.

The known APN+AB families over $\mathrm{GF}(2^n)$ ($n$ odd) are:

| Family | Exponent $d$ | Conditions |
|--------|-------------|------------|
| **Gold** | $2^k + 1$ | $\gcd(k,n) = 1$ |
| **Kasami** | $4^k - 2^k + 1$ | $\gcd(k,n) = 1$ |
| **Welch** | $2^t + 3$ | $n = 2t+1$ |
| **Niho** | $2^t + 2^{t/2} - 1$ (t even) or $2^t + 2^{(3t+1)/2} - 1$ (t odd) | $n = 2t+1$ |
| **Inverse** | $2^{2t} - 1$ | $n = 2t+1$ |
| **Dobbertin** | $2^{4t} + 2^{3t} + 2^{2t} + 2^t - 1$ | $n = 5t$ |

**Conjecture (now theorem for all AB functions):** For ANY AB function $f$ over $\mathrm{GF}(2^n)$, $n$ odd, with differential set $\Delta$, and distinct nonzero $v_1, v_2$:
$$|\{(x,y,z) \in \Delta^3 : v_1 x + v_2 y + (v_1+v_2)z = 0\}| = 2^{2n-3}$$

This is formalized in `KasamiGeneralizations.lean` as `ab_triple_count`.

---

## Axis 2: k-Tuple Generalization (Higher Moments)

Instead of triples, consider **$m$-tuples** $(x_1, \ldots, x_m) \in \Delta^m$ satisfying a linear constraint $\sum_{i=1}^m c_i x_i = 0$ with all partial sums of $c_i$ nonzero.

The Fourier identity generalizes to:
$$|F| \cdot \kappa_m = \sum_{a \in F} \prod_{i=1}^m \hat\delta(c_i a)$$

For AB functions, the Walsh spectrum satisfies $|\hat\delta(a)|^2 \in \{0, 2^n\}$ for $a \neq 0$. This means:
- **$m$ even:** $\sum_a \prod \hat\delta(c_i a) = |\Delta|^m$ when the constraint is "generic"
  - ⟹ $\kappa_m = 2^{m(n-1) - n} = 2^{(m-1)n - m}$
- **$m$ odd:** Same formula under AB, since the odd moment also collapses

**Conjecture (m-tuple count for AB functions):**
$$\kappa_m = 2^{(m-1)n - m}$$

For $m=3$: $\kappa_3 = 2^{2n-3}$ ✓ (our theorem)  
For $m=4$: $\kappa_4 = 2^{3n-4}$  
For $m=5$: $\kappa_5 = 2^{4n-5}$  

This is formalized as `ab_mtuple_count_conjecture`.

---

## Axis 3: APN but Non-AB Functions (Even $n$)

When $n$ is even, APN functions exist but are **not** AB. The Walsh spectrum is no longer flat, and the triple count changes. The spectral sum becomes:

$$\sum_a \hat\delta(v_1 a)\hat\delta(v_2 a)\hat\delta((v_1+v_2)a) \neq |\Delta|^3$$

For the Kasami function with $n$ even, the Walsh spectrum takes values in $\{0, \pm 2^{(n+1)/2}\}$ (Gold) or more complex distributions. The triple count depends on the specific spectral distribution.

**Conjecture (APN, non-AB triple count):** For APN functions over $\mathrm{GF}(2^n)$ with $n$ even, the triple count depends on the **third moment** of the Walsh spectrum:
$$\kappa = \frac{1}{2^n} \sum_{a \in F} \hat\delta(v_1 a)\hat\delta(v_2 a)\hat\delta((v_1+v_2)a)$$

This is NOT a clean power of 2 in general. Characterizing when it is (and what it equals) is an open problem.

---

## Axis 4: Higher Differential Uniformity

The APN condition means the derivative equation $f(x+a) + f(x) = b$ has at most 2 solutions for every $a \neq 0$. If we relax this to **$\delta$-uniform** (at most $\delta$ solutions), then $|\Delta|$ changes:

- $\delta$-uniform ⟹ $|\Delta| \geq 2^n / \delta$
- The derivative is at most $\delta$-to-1 rather than 2-to-1

For a $\delta$-uniform function that is also "spectrally nice" (analogous to AB but for higher uniformity), we get:
$$\kappa = \frac{|\Delta|^3}{|F|}$$

**Conjecture ($\delta$-uniform triple count):** For a $\delta$-uniform, spectrally-flat function:
$$\kappa = \frac{(2^n/\delta)^3}{2^n} = \frac{2^{2n}}{\delta^3}$$

For $\delta = 2$ (APN+AB): $\kappa = 2^{2n}/8 = 2^{2n-3}$ ✓

---

## Axis 5: Odd Characteristic (Planar/PN Functions)

In odd characteristic $p$, the analog of APN is the **PN (Perfect Nonlinear)** or **planar** condition: the derivative $f(x+a) - f(x)$ is a bijection for every $a \neq 0$. Here $|\Delta| = p^n$ (the whole field).

Known PN functions over $\mathrm{GF}(p^n)$:
- $f(x) = x^2$ (always PN in odd char)
- $f(x) = x^{p^k + 1}$ (Dembowski-Ostrom, conditions on $k,n,p$)
- Coulter-Matthews: $x^{(3^k+1)/2}$ over $\mathrm{GF}(3^n)$

For PN functions, the triple count becomes:
$$\kappa = \frac{|\Delta|^3}{|F|} = \frac{(p^n)^3}{p^n} = p^{2n}$$

**Theorem (PN triple count):** For a PN function over $\mathrm{GF}(p^n)$, $p$ odd:
$$|\{(x,y,z) \in \Delta^3 : c_1 x + c_2 y + c_3 z = 0\}| = p^{2n}$$

This is formalized as `pn_triple_count`.

---

## Axis 6: Category-Theoretic / Structural View

The proof has a **functorial** structure that suggests higher abstraction:

### The Proof as a Diagram
```
  Function f  ─────► Differential Set Δ  ─────► Walsh Spectrum {δ̂(a)}
       │                    │                           │
  (APN property)      (|Δ| = 2^{n-1})          (AB: flat spectrum)
       │                    │                           │
       └──────────► Fourier Identity ◄──────────────────┘
                         │
                    Triple Count κ = 2^{2n-3}
```

### Abstract Framework

Define a **counting functor** $\mathcal{C}$ from the category of:
- **Objects:** Pairs $(F, f)$ where $F$ is a finite field and $f: F \to F$ is a power map
- **Morphisms:** Field embeddings compatible with the power map

to the category of:
- **Objects:** Natural numbers (the tuple counts)
- **Morphisms:** Divisibility relations

The key insight: the counting functor **factors through** the Walsh spectrum:

$$\mathcal{C} = \text{Count} \circ \text{Fourier} \circ \text{Differential}$$

Each factor is independently abstractable:
1. **Differential functor:** $(F,f) \mapsto \Delta_f$ — depends only on APN/PN property
2. **Fourier functor:** $\Delta \mapsto \{\hat\delta(a)\}$ — character theory
3. **Count functor:** spectrum $\mapsto \kappa$ — arithmetic

### Higher-Dimensional Analogs

1. **Multivariate functions:** $f: F^m \to F$, differential sets in $F^m$
2. **Matrix constraints:** Replace linear constraint with matrix equation $Ax = 0$
3. **Higher-order derivatives:** Use $k$-th order differentials instead of first-order

---

## Axis 7: Connections to Other Areas

### Coding Theory
- The Walsh spectrum of $f$ determines the weight distribution of the associated cyclic code
- The triple count relates to the **third-order weight enumerator**
- AB ⟹ the code has optimal minimum distance (related to BCH bound)

### Combinatorial Designs
- APN functions yield **difference sets** in certain groups
- The triple count is related to the **$\lambda$ parameter** of the design
- AB functions give optimal designs (Menon difference sets)

### Algebraic Geometry
- Power functions $x^d$ correspond to **Artin-Schreier curves** $y^p - y = x^d$
- The Walsh spectrum encodes the **number of rational points** on these curves
- The Weil bound gives $|\hat\delta(a)| \leq (d-1)\sqrt{|F|}$, and AB is the case of equality

---

## Summary of Formalized Conjectures

| # | Conjecture | File | Status |
|---|-----------|------|--------|
| 1 | AB triple count (all AB functions) | `KasamiGeneralizations.lean` | Theorem (from axiomatized AB property) |
| 2 | Gold triple count | `KasamiGeneralizations.lean` | Theorem (instance of AB) |
| 3 | m-tuple count for AB | `KasamiGeneralizations.lean` | Conjecture |
| 4 | PN triple count (odd char) | `KasamiGeneralizations.lean` | Theorem (from axiomatized PN property) |
| 5 | Welch triple count | `KasamiGeneralizations.lean` | Theorem (instance of AB) |
| 6 | Dobbertin triple count | `KasamiGeneralizations.lean` | Theorem (instance of AB) |

---

## Suggested Research Program

1. **Immediate:** Prove the $m$-tuple count conjecture for $m=4$ (quadruples) by analyzing the fourth moment of the AB spectrum.
2. **Short-term:** Characterize triple counts for APN-but-not-AB functions (even $n$). Start with Gold function for $n=4,6,8$.
3. **Medium-term:** Develop the category-theoretic framework and prove functoriality of the counting map.
4. **Long-term:** Connect to algebraic geometry via Weil conjectures — the triple count should relate to point counts on certain varieties over finite fields.
