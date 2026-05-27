# Formalization Roadmap — Dempwolff & Müller (2013)

## Current Status

| Section | Result | File | Status |
|---------|--------|------|--------|
| §2 | Proposition 2.1(a) | `Prop21.lean` | ✅ Complete (0 sorry) |
| §3 | Lemma 3.1 | `Lemma31.lean` | ✅ Complete (0 sorry) |
| §3 | Theorem 3.2 (k part) | `Thm32.lean` | ✅ Complete (0 sorry) |
| §3 | Theorem 3.2 (k′ part) | `Thm32.lean` + `Thm32Kprime.lean` | ⚠️ 6 sorries remain |
| §3 | Theorem 3.3 | — | ❌ Not started |
| §3 | Theorem 3.4 | — | ❌ Not started |
| §3 | Proposition 3.5 | — | ❌ Not started |
| §4 | Automorphisms | — | ❌ Not started |
| §5 | Isomorphisms | — | ❌ Not started |
| §6 | Symplectic spreads | — | ❌ Not started |

---

## Part A — Future Directions for Completing Section 3

### A1. Complete Theorem 3.2 (k′ part)

Remaining sorries in `Thm32Kprime.lean`:

| Layer | Lemma | Description |
|-------|-------|-------------|
| B | `truncTrace_adj_trace_prop` | Tr(L(w)·z) = Tr(w·L*(z)) — adjoint property via Frobenius shift |
| E | `LadjXe_bijective` | Frobenius composition: L*(x)·x^{k·2^{n-m+1}} is bijective |
| F | `adjoint_swap_bijective` | Specialized Lemma 3.1 instance for power maps |
| G | `exp_k'_eq_on_units` | Exponent identification l′ ≡ k′ (mod 2ⁿ−1) |
| H | `LxXk'_bijective_v2` | Main conclusion for k′ |

And `LxXk'_bijective` in `Thm32.lean` (depends on H above).

### A2. Formalize Theorem 3.3 (Twisted Kantor–Williams Polynomials)

**Statement:** Given divisor chain d₁ | d₂ | ⋯ | dₕ | n with n/d₁ odd,
coefficients cᵢ ∈ F*_{dᵢ} with partial sums nonzero, and ℓ with
gcd(2^{d₁}−1, 2^ℓ+1) = 1, the polynomial L(X)·X is a permutation
polynomial on F_n = GF(2ⁿ).

**Proof method:** Induction on h, applying trace maps T_{n:dₕ} and using
the base case h = 1 which reduces to coprimality of 2^ℓ+1 and 2^{d₁}−1.

**Suggested decomposition:**
- Trace map composition: T_{n:dᵢ}(z) = T_{dₕ:dᵢ}(T_{n:dₕ}(z))
- Base case h = 1: injectivity from coprimality
- Inductive step: T_{n:dₕ} reduction
- Assembly

### A3. Formalize Theorem 3.4 (Simple Construction)

**Statement:** If L(X)·Xᵏ is a permutation polynomial on GF(qⁿ) and
b is a multiple of N = (qⁿ−1)/(q−1) with gcd(bℓ+1, q−1) = 1,
then L(X)·X^{k+b} is also a permutation polynomial.

**Proof method:** Factor P′(z) = P(z^{1+bℓ}) using (k+1, q−1) = 1.

### A4. Formalize Proposition 3.5 (Same Translation Plane)

**Statement:** L(X)·Xᵏ and L(X)·X^{k+b} from Theorem 3.4 define the
same translation plane (i.e., identical spread sets).

**Proof method:** Show x ∘ y = x^{1+bℓ} · y directly.

---

## Part B — Extension Layers for the Rest of the Paper (DAG Modules)

The dependency DAG is structured as follows. Each layer depends only on
layers above it (and Mathlib). The root dependencies are on Mathlib's
finite field theory, linear algebra, and group theory.

```
Mathlib
  │
  ├── Prop21.lean (§2)
  │
  ├── Lemma31.lean (§3)
  │
  ├── Thm32.lean (§3)
  │     └── Thm32Kprime.lean (§3)
  │
  ├── [A2] Thm33.lean (§3) ──────────────────────────┐
  │                                                    │
  ├── [A3] Thm34.lean (§3) ──┐                        │
  │                           │                        │
  │                    [A4] Prop35.lean (§3)            │
  │                                                    │
  ├── [B1] AutBase.lean ◄─────── FIRST LAYER           │
  │     │   (Singer groups, T_r(a), spi, Lemmas 4.1-4.2)
  │     │                                              │
  │     ├── [B2] AutKernel.lean                        │
  │     │   │   (Lemmas 4.3, 4.4, 4.5)                │
  │     │   │                                          │
  │     │   ├── [B3] AutGeneral.lean                   │
  │     │   │   │   (Prop 4.6, Lemma 4.7)              │
  │     │   │   │                                      │
  │     │   │   ├── [B4] AutTypeI.lean ◄── Thm32.lean  │
  │     │   │   │   │   (Lemma 4.9, Theorem 4.8)      │
  │     │   │   │   │                                  │
  │     │   │   │   ├── [B6a] IsoTypeI.lean            │
  │     │   │   │   │   (Theorem 5.1)                  │
  │     │   │   │   │                                  │
  │     │   │   │   └── [B7a] SymplTypeI.lean          │
  │     │   │   │       (Prop 6.2)                     │
  │     │   │   │                                      │
  │     │   │   └── [B5] AutTypeII.lean ◄── Thm33.lean │
  │     │   │       │   (Lemmas 4.11, 4.12, Thm 4.10) │
  │     │   │       │                                  │
  │     │   │       ├── [B6b] IsoTypeII.lean           │
  │     │   │       │   (Theorem 5.2, Lemma 5.3)       │
  │     │   │       │                                  │
  │     │   │       └── [B7b] SymplTypeII.lean         │
  │     │   │           (Prop 6.3)                     │
  │     │   │                                          │
  │     │   └── [B6c] IsoTypeIvsII.lean                │
  │     │       │   (Theorem 5.4)  ◄── B4, B5         │
  │     │       │                                      │
  │     │       └── [B7c] Lemma61.lean                 │
  │     │           (Lemma 6.1 — adjoint of T_k(b))   │
  │     │                                              │
  │     └───────────────────────────────────────────────┘
  │
```

### Layer B1 — `AutBase.lean` ← **FIRST LAYER** (to be formalized now)

**Dependencies:** Mathlib (finite fields, linear algebra)

**Contents:**
- **Definition** `semilinearOp r a : F → F` := x ↦ a · x^{p^r}  (the operator T_r(a))
- **Properties:** linearity, composition, invertibility
- **Definition** `support L` := {i | coefficient aᵢ ≠ 0} for additive L(X) = Σ aᵢ X^{p^i}
- **Lemma 4.1** (Singer groups):
  - (a) {T_0(a) | a ∈ F*} is a Singer group; normalizer = {T_i(a)}
  - (b) Singer groups are conjugate
  - (c) Irreducible operator ↔ unique Singer group
- **Lemma 4.2** (Support under conjugation):
  spi(T_s(a) · L · T_t(b)⁻¹) = {i + r | i ∈ spi(L)}, r = s − t (mod n)

### Layer B2 — `AutKernel.lean`

**Dependencies:** B1, Prop21

**Contents:**
- **Lemma 4.3:** Kernel of the translation plane ≅ GF(p^r), r = gcd{i−j | i,j ∈ spi(L)}
- **Lemma 4.4:** τ_{a,b,α} ∈ G iff a^{α_i} · a^{−pⁱ} · b = aᵢ for all i
- **Lemma 4.5:** For non-desarguesian A:
  - (a) S is a Sylow p-subgroup of G_{0,∞}
  - (b) Normalizer elements have semilinear form
  - (c) G = N_{G_{0,∞}}(S)

### Layer B3 — `AutGeneral.lean`

**Dependencies:** B2

**Contents:**
- **Proposition 4.6:** If A is not a semifield plane:
  - (a) G_{0,∞} = G̃
  - (b) S is normal Sylow p-subgroup of G
  - (c) G = G_{{0,∞}}
- **Lemma 4.7:** For non-desarguesian semifield planes, L(X) or L⁻¹(X) has ≤ 2 terms

### Layer B4 — `AutTypeI.lean`

**Dependencies:** B3, Thm32

**Contents:**
- **Lemma 4.9:** Properties of L⁻¹(X) for type I:
  - L⁻¹(X) ∈ GF(2)[X]
  - (a) L⁻¹ is not sum of 1 or 2 monomials
  - (b) spi(L⁻¹) ≠ {i+r | 0 ≤ i < m′} for any r, m′
- **Theorem 4.8:** Kernel ≅ GF(2), G = G_{0,∞} = Z ⋊ {τ_{1,1,α}} ≅ C_{2ⁿ−1} · Cₙ

### Layer B5 — `AutTypeII.lean`

**Dependencies:** B3, Thm33

**Contents:**
- **Lemma 4.11:** Trace identity for nested subfields
- **Lemma 4.12:** Inverse polynomial structure for type II
- **Theorem 4.10:** Automorphism group of type II planes

### Layer B6a — `IsoTypeI.lean`

**Dependencies:** B4

**Contents:**
- **Theorem 5.1:**
  - (a) A_{n,m} ≅ A_{n,m′} (or A*_{n,m} ≅ A*_{n,m′}) iff m = m′
  - (b) A_{n,m} ≇ A*_{n,m′} for all m, m′

### Layer B6b — `IsoTypeII.lean`

**Dependencies:** B5

**Contents:**
- **Lemma 5.3:** Normalizer constraint s = t
- **Theorem 5.2:** Classification of isomorphisms between type II planes

### Layer B6c — `IsoTypeIvsII.lean`

**Dependencies:** B4, B5

**Contents:**
- **Theorem 5.4:**
  - (a) Type I ≇ Type II
  - (b) Types I, II ≇ generalized twisted field, nearfield, André, or Kantor–Williams planes

### Layer B7a — `SymplTypeI.lean`

**Dependencies:** B4, Lemma61

**Contents:**
- **Proposition 6.2:** Type I spread is not symplectic (A_{n,m} ≇ dual spread plane)

### Layer B7b — `SymplTypeII.lean`

**Dependencies:** B5, Lemma61

**Contents:**
- **Proposition 6.3:** Type II spread is not symplectic

### Layer B7c — `Lemma61.lean`

**Dependencies:** B1

**Contents:**
- **Lemma 6.1:**
  - (a) T_k(b)* = T_{−k}(b^{2^{−k}})
  - (b) Symplectic spread condition N(x)*A = A*N(x)
