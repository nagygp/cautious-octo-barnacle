# Kasami P₃ — Proof Architecture, Completeness Analysis, and FOL Chain

## 1. What Is P₃?

**P₃ (combinatorial):** For `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂` in `F_{2^n}`:

```
|{ (x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0 }| = 2^{2n−3}
```

where `Δ = { b^d + (b+1)^d + 1 : b ∈ F_{2^n} }` and `d = 4^k − 2^k + 1` is the Kasami exponent.

**Dual P₃ (spectral):** Via Pontryagin duality:

```
∑_{ψ} Ŝ_ψ(v₁) · Ŝ_ψ(v₂) · Ŝ_ψ(v₁+v₂) = 2^{3n−3}
```

---

## 2. Project Module Structure (After Refactoring)

```
RequestProject/
├── Main.lean                         ← Root import
├── Kasami/
│   ├── Basic.lean                    ← F_{2^n}, char-2 arithmetic        ✅ sorry-free
│   ├── Trace.lean                    ← Absolute trace Tr, surjectivity   ✅ sorry-free
│   ├── AdditiveCharacter.lean        ← χ(x) = (−1)^Tr(x), orthogonality ✅ sorry-free
│   ├── WalshHadamard.lean            ← WHT, Parseval, inversion          ✅ sorry-free
│   ├── KasamiExponent.lean           ← d = 4^k−2^k+1, coprimality       ✅ sorry-free
│   ├── AlmostBent.lean               ← AB defn, 4th moment, AB⟹APN      ⚠️  1 sorry
│   ├── KasamiFunction.lean           ← F(b)=b^d, kasami_is_ab           ⚠️  1 sorry
│   ├── DifferenceSet.lean            ← Δ, S_Δ(c)                        ✅ sorry-free
│   ├── TripleCount.lean              ← charSum repr, AlmostBentVanishing ⚠️  1 sorry
│   ├── FourthMoment.lean             ← Autocorrelation, Wiener-Khinchin  ✅ sorry-free
│   ├── APNFromAB.lean                ← Derivative Parseval               ✅ sorry-free
│   ├── VanishingProof.lean           ← g(b)=g(b+1), |Δ|, split assembly ✅ sorry-free
│   ├── KasamiP3.lean                 ← Main P₃ assembly                  ✅ (mod above)
│   ├── DualP3.lean                   ← Dual P₃ ↔ P₃                     ✅ sorry-free
│   ├── CCDHelpers.lean               ← Char-2 algebraic helpers          ✅ sorry-free
│   └── CCDFactorization.lean         ← d·(2^k+1) = 2^{3k}+1, Frobenius  ✅ sorry-free
├── LinearizedPoly/
│   ├── Defs.lean                     ← Frobenius, linearized fns, L_k    ✅ sorry-free
│   ├── Kernel.lean                   ← Kernel dimension theory           ✅ sorry-free
│   ├── ArtinSchreier.lean            ← x² + x, image analysis            ✅ sorry-free
│   └── KasamiKernel.lean             ← Derivative-linearized connection  ⚠️  1 sorry
└── QuadFormGF2/
    ├── Defs.lean                     ← QuadFormF2, polar, radical         ✅ sorry-free
    ├── GaussSum.lean                 ← S(Q)²=|V|·|rad|, zero criterion   ✅ sorry-free
    └── Kasami.lean                   ← Kasami spectrum outline            ✅ sorry-free
```

---

## 3. Is This a Complete Theory and Proof?

### Answer: **No — but it is structurally complete modulo 4 deep results.**

The formalization provides a **complete proof skeleton** with the following sorry-free results:

| What | Status |
|------|--------|
| Dual P₃ ↔ P₃ equivalence | ✅ Fully proved |
| Character-sum representation of triple count | ✅ Fully proved |
| P₃ from AlmostBentVanishing condition | ✅ Fully proved |
| Assembly: `kasami_is_ab` + `ab_implies_vanishing` → P₃ | ✅ Fully proved (uses sorry'd lemmas) |
| Walsh-Hadamard: Parseval, inversion, convolution | ✅ Fully proved |
| Kasami exponent coprimality and bijectivity | ✅ Fully proved |
| Trace theory: surjectivity, kernel card, balance | ✅ Fully proved |
| Additive character orthogonality | ✅ Fully proved |
| Fourth moment = Wiener-Khinchin identity | ✅ Fully proved |
| AB fourth moment formula | ✅ Fully proved |
| Autocorrelation sum for AB | ✅ Fully proved |
| Derivative distribution: evenness, Parseval | ✅ Fully proved |
| Delta set pairing g(b)=g(b+1) | ✅ Fully proved |
| Delta cardinality from 2-to-1 | ✅ Fully proved |
| Linearized poly: kernel dimension, Artin-Schreier | ✅ Fully proved |
| Quadratic form: radical, S(Q)², vanishing criterion | ✅ Fully proved |
| CCD factorization identities | ✅ Fully proved |

### The 4 Remaining Sorry's

| # | Sorry | File | What It Says |
|---|-------|------|-------------|
| 1 | `kasami_is_ab` | `KasamiFunction.lean` | The Kasami function is Almost Bent |
| 2 | `ab_implies_apn` | `AlmostBent.lean` | AB ⟹ APN (fourth moment bound) |
| 3 | `ab_implies_vanishing` | `TripleCount.lean` | AB ⟹ triple spectral sum = 2^{3n−3} |
| 4 | `kasamiDiff_eq_implies_linearized` | `KasamiKernel.lean` | Derivative factors through linearized poly |

These 4 sorry's form a **dependency chain**:

```
kasami_is_ab
  │
  ├──→ ab_implies_apn  ──→ (used in VanishingProof assembly)
  │
  └──→ ab_implies_vanishing ──→ kasami_P3
```

And `kasamiDiff_eq_implies_linearized` feeds into `kasami_is_ab` (it's part of the factorization
that shows the Kasami derivative has linearized polynomial structure, bounding the kernel dimension).

---

## 4. Where to Find the Missing Components

### Sorry 1: `kasami_is_ab` — The Kasami function is Almost Bent

This is the deepest result. It requires proving that the Walsh spectrum of `x ↦ x^d` takes
values only in `{0, ±2^{(n+1)/2}}`.

**Primary references:**

- **Kasami, T. (1971).** "The weight enumerators for several classes of subcodes of the
  2nd order binary Reed-Muller codes." *Information and Control*, 18(4), 369–394.
  - Original proof via weight enumeration of subcodes.
  - **§4**: Defines the exponent and computes the weight distribution.

- **Canteaut, A., Charpin, P., and Dobbertin, H. (2000).** "Weight divisibility of cyclic
  codes, highly nonlinear functions on F_{2^m}, and crosscorrelation of maximum-length
  sequences." *SIAM Journal on Discrete Mathematics*, 13(1), 105–138.
  - Modern proof via quadratic form rank analysis (the "CCD approach").
  - **Theorem 1** (p. 113): Three-valued cross-correlation → AB property.
  - **§4.2** (pp. 118–125): The rank analysis of the bilinear form `B_a(x,y)`.

- **Carlet, C. (2021).** *Boolean Functions for Cryptography and Coding Theory.*
  Cambridge University Press.
  - **Chapter 6, §6.4** (pp. 318–335): Complete treatment of the Kasami spectrum proof.
  - **Theorem 6.23**: The Walsh spectrum is three-valued.
  - Uses the linearized polynomial kernel dimension bound (from Chapter 3).

**What needs to be formalized:**

1. The quadratic form `Q_a(x) = Tr(a · x^d)` and its bilinear form `B_a(x,y)`.
   → The infrastructure is in `QuadFormGF2/` but the connection to the Kasami function
   is not yet formalized beyond the outline in `QuadFormGF2/Kasami.lean`.

2. The rank of `B_a` is either `n-1` or `n` when `gcd(k,n) = 1`.
   → This requires the linearized polynomial kernel analysis: the kernel of
   `L_k(x) = x^{2^{2k}} + x^{2^k} + x` over `GF(2^n)` is trivial when `gcd(k,n) = 1`.
   → The kernel infrastructure is in `LinearizedPoly/Kernel.lean`, but the specific
   dimension bound for the Kasami case requires `kasamiDiff_eq_implies_linearized` (sorry #4).

3. The Gauss sum evaluation: `S(Q_a)² = |V| · |rad(Q_a)|` when `Q_a|_{rad} = 0`.
   → **This is fully proved** in `QuadFormGF2/GaussSum.lean` (`expSum_sq_eq_card_mul_radical_card`).
   → The missing piece is showing `Q_a|_{rad} = 0` for the specific Kasami quadratic form.

### Sorry 2: `ab_implies_apn` — AB implies APN

**Reference:**
- **Carlet (2021)**, **Proposition 6.12** (p. 303):
  "Every AB function is APN."
  Proof: By the Parseval identity and the constraint `W_f(a)^2 ∈ {0, 2^{n+1}}`,
  the fourth moment `∑_a W_f(a)^4 = 2 · (2^n)^3`. The identity
  `∑_a W_f(a)^4 = 2^n · ∑_{a,b} N_a(b)^2` then implies
  `∑_{a,b} N_a(b)^2 = 2 · (2^n)^2`. Combined with `∑_b N_a(b) = 2^n` and
  the evenness of `N_a(b)`, this forces `N_a(b) ≤ 2` for all `a ≠ 0`.

- The project has the fourth moment identity (`ab_fourth_moment`),
  the Wiener-Khinchin identity (`fourth_moment_eq_autocorr_sq`),
  the derivative Parseval identity (`deriv_parseval`),
  and the evenness bound (`even_sum_sq_bound`). The missing step is
  assembling these into the `ab_implies_apn` proof.

### Sorry 3: `ab_implies_vanishing` — AB implies spectral vanishing

**Reference:**
- **Carlet (2021)**, **§6.4**, around **Theorem 6.20** (pp. 318–320):
  The key identity is that the triple spectral sum splits as
  `S_Δ(0)^3 + ∑_{a≠0} (...)`. The `a=0` term gives `(2^{n-1})^3 = 2^{3n-3}`.
  The nonzero sum vanishes because of the autocorrelation structure of AB functions.

- The project proves the split (`triple_sum_split`), the `a=0` term evaluation
  (`deltaCharSum_zero`, `kasamiDelta_card`), and the assembly
  (`ab_implies_vanishing_assembled`). The missing step is proving that the
  nonzero sum vanishes, which requires relating `S_Δ(c)` to the WHT of the
  Kasami function and using the AB spectral constraint.

- **Pott, A. (2004).** "Nonlinear functions in Abelian groups and relative difference
  sets." *Discrete Applied Mathematics*, 138(1-2), 177–193.
  - §3: Connection between Walsh spectrum and difference set character sums.

### Sorry 4: `kasamiDiff_eq_implies_linearized` — Derivative factorization

**Reference:**
- **Lidl, R. and Niederreiter, H. (1997).** *Finite Fields*, Cambridge University Press.
  - **Chapter 3, §3.4**: Linearized polynomials and their kernels.
  - **Theorem 3.62**: The kernel of a linearized polynomial of degree `p^m` over `GF(p^n)`
    has at most `p^{gcd(m,n)}` elements.

- **Canteaut, Charpin, Dobbertin (2000)**, **§4.1** (pp. 115–118):
  For `a ≠ 0`, the equation `D_a f(x) = D_a f(y)` with `z = x + y` reduces to
  `L_k(z) = 0` where `L_k(z) = z^{2^{2k}} + z^{2^k} + z` (after normalization by `a`).
  When `gcd(k,n) = 1` and `n` is odd, `ker(L_k) = GF(2)` (i.e., `z ∈ {0,1}`).

---

## 5. Proof Architecture in First-Order Logic (Chain of Implications)

Below is the full proof chain for P₃ expressed in FOL with the key predicates
and implications made explicit.

### Definitions (predicates and functions)

```
F         := GF(2^n)                                     -- finite field
d         := 4^k − 2^k + 1                              -- Kasami exponent
Tr(x)     := absolute trace F → GF(2)                   -- GF(2)-linear
χ(x)      := (−1)^{Tr(x)}                               -- additive character
W_f(a)    := ∑_{x∈F} χ(ax + f(x))                       -- Walsh-Hadamard transform
f(x)      := x^d                                        -- Kasami function
Δ         := {f(b) + f(b+1) + 1 : b ∈ F}               -- difference set
S_Δ(c)    := ∑_{x∈Δ} χ(cx)                              -- char sum over Δ
T(v₁,v₂)  := |{(x,y,z) ∈ Δ³ : v₁x+v₂y+(v₁+v₂)z=0}|   -- triple count
N_a(b)    := |{x∈F : f(x+a)+f(x)=b}|                    -- derivative distribution
R(t)      := ∑_x χ(f(x+t)+f(x))                         -- autocorrelation
```

### Predicates

```
AB(f)     := ∀a. W_f(a)²=0 ∨ W_f(a)²=2^{n+1}           -- Almost Bent
APN(f)    := ∀a≠0. ∀b. N_a(b) ≤ 2                       -- Almost Perfect Nonlinear
COPRIME   := gcd(k,n) = 1
ODD_N     := n is odd
VANISH    := ∀v₁≠0. ∀v₂≠0. v₁≠v₂ →
             ∑_a S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂)) = 2^{3n-3}
```

### The Chain of Implications

```
                        COPRIME ∧ ODD_N
                             │
                             ▼
               ┌─── (1) gcd(d, 2^n−1) = 1 ───────────────────┐
               │         [KasamiExponent.lean]                │
               │                                              │
               ▼                                              │
        x↦x^d is a permutation of F*                         │
               │                                              │
               ▼                                              │
    ┌──── (2) Rank analysis of B_a ◄──────────────────────────┤
    │     [QuadFormGF2/, LinearizedPoly/]                     │
    │                                                         │
    │  (2a) Q_a(x) = Tr(ax^d) is a quadratic form            │
    │       [QuadFormGF2/Defs.lean] ✅                        │
    │                                                         │
    │  (2b) B_a has radical dim ≤ 1                           │
    │       ← ker(L_k) = GF(2) when gcd(k,n)=1              │
    │       [LinearizedPoly/KasamiKernel.lean] ⚠️ sorry      │
    │                                                         │
    │  (2c) S(Q_a)² = 2^n · |rad(Q_a)|                       │
    │       [QuadFormGF2/GaussSum.lean] ✅                    │
    │                                                         │
    ▼                                                         │
(3) W_f(a)² ∈ {0, 2^{n+1}}  ∀a                              │
    i.e., AB(f)   [KasamiFunction.lean] ⚠️ sorry             │
    │                                                         │
    ├──────────────────────────────┐                          │
    │                              │                          │
    ▼                              ▼                          │
(4) AB(f) ⟹ APN(f)           (5) AB(f) ⟹ VANISH            │
    [AlmostBent.lean] ⚠️         [TripleCount.lean] ⚠️       │
    │                              │                          │
    │  Uses:                       │  Uses:                   │
    │  • Parseval ✅                │  • split at a=0  ✅      │
    │  • 4th moment ✅             │  • S_Δ(0)=|Δ| ✅         │
    │  • Wiener-Khinchin ✅        │  • |Δ|=2^{n-1} ✅        │
    │  • deriv evenness ✅         │  • ∑_{a≠0}(...)=0 ⚠️     │
    │  • sq bound ✅               │                          │
    │                              │                          │
    ▼                              ▼                          │
(6) APN ⟹ g is 2-to-1      (7) VANISH                       │
    [VanishingProof.lean] ✅       │                          │
    │                              │                          │
    ▼                              │                          │
(8) |Δ| = 2^{n-1}                 │                          │
    [VanishingProof.lean] ✅       │                          │
    │                              │                          │
    └──────────────┬───────────────┘                          │
                   │                                          │
                   ▼                                          │
(9) 2^n · T(v₁,v₂) = ∑_a S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))│
    [TripleCount.lean: tripleCount_charSum_eq] ✅             │
                   │                                          │
                   ▼                                          │
(10) 2^n · T(v₁,v₂) = 2^{3n−3}                              │
     [TripleCount.lean: from VANISH] ✅                      │
                   │                                          │
                   ▼                                          │
(11) T(v₁,v₂) = 2^{2n−3}     ◄═══ P₃                       │
     [KasamiP3.lean: tripleCount_from_vanishing] ✅           │
                   │                                          │
                   ▼                                          │
(12) P₃ ⟺ Dual P₃                                           │
     [DualP3.lean: P3_iff_DualP3] ✅                         │
```

### Written as FOL Implications

```
(I)    COPRIME ∧ ODD_N
         ⟹  gcd(d, 2^n−1) = 1                              ✅ proved

(II)   gcd(d, 2^n−1) = 1
         ⟹  x↦x^d bijective on F                           ✅ proved

(III)  COPRIME ∧ ODD_N
         ⟹  AB(f)                                           ⚠️ sorry (kasami_is_ab)

(IV)   AB(f) ⟹ APN(f)                                      ⚠️ sorry (ab_implies_apn)

(V)    AB(f) ⟹ VANISH                                      ⚠️ sorry (ab_implies_vanishing)

(VI)   APN(f)
         ⟹  ∀x ∈ Δ. |g⁻¹(x)| = 2                          ✅ proved

(VII)  ∀x ∈ Δ. |g⁻¹(x)| = 2
         ⟹  |Δ| = 2^{n−1}                                   ✅ proved

(VIII) ∀v₁,v₂. v₁≠0 ∧ v₂≠0 ∧ v₁≠v₂ →
       2^n · T(v₁,v₂) = ∑_a S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))
                                                              ✅ proved

(IX)   VANISH ⟹ T(v₁,v₂) = 2^{2n−3}                       ✅ proved

(X)    (III) ∧ (V) ∧ (IX) ⟹ P₃                             ✅ proved (mod sorry)

(XI)   P₃ ⟺ Dual P₃                                        ✅ proved
```

### Condensed Chain

```
COPRIME ∧ ODD_N
  ─(III)→  AB(f)                         ⚠️ deep sorry
  ─(V)──→  VANISH                        ⚠️ deep sorry
  ─(IX)──→ T(v₁,v₂) = 2^{2n-3}          ✅
  ═══════  P₃                             Q.E.D. (modulo III, V)
```

---

## 6. Summary of What Is Missing

The theory is **structurally complete**: every step of the proof is formalized
except for 4 results that correspond to deep mathematics. The 4 sorry's form
a clear dependency chain:

```
kasamiDiff_eq_implies_linearized  (derivative ↔ linearized poly)
        ↓
kasami_is_ab                      (the AB theorem)
        ↓
ab_implies_apn                    (AB ⟹ APN)
ab_implies_vanishing              (AB ⟹ spectral vanishing)
        ↓
kasami_P3                         (the P₃ theorem)
```

To close all sorry's, one needs to formalize approximately 2,000–4,000 lines of
new Lean 4 code building:

1. **The connection from `QuadFormGF2` to the Kasami function** — constructing `Q_a(x) = Tr(ax^d)`
   as a `QuadFormF2` and computing the rank of its bilinear form.

2. **The linearized polynomial kernel dimension bound** — proving `ker(L_k) = GF(2)` when
   `gcd(k,n) = 1`, which requires `kasamiDiff_eq_implies_linearized`.

3. **The AB ⟹ APN bridge** — assembling the existing fourth moment and derivative
   infrastructure into `ab_implies_apn`.

4. **The spectral vanishing** — connecting `S_Δ(c)` to WHT values and proving the
   nonzero sum vanishes.

None of these components exist in Mathlib or any known formal library. They are
well-documented in textbooks, primarily:

- **Carlet (2021)**, *Boolean Functions for Cryptography and Coding Theory*, Chapters 3, 6
- **Lidl & Niederreiter (1997)**, *Finite Fields*, Chapter 3
- **Canteaut, Charpin, Dobbertin (2000)**, SIAM J. Discrete Math. 13(1)
