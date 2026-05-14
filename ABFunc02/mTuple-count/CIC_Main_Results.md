# Main Results in CIC (Unicode)

Proofs derived from two black-boxed known results.

---

## Universes & Primitive Notions

```
𝕌 : Type                          — universe of types
ℕ : 𝕌                             — natural numbers
```

---

## Context (Γ)

```
Γ ≔
  F : 𝕌,
  _ : Field F,  _ : Fintype F,  _ : DecidableEq F,  _ : CharP F 2,
  n : ℕ,   h_n≥3 : 3 ≤ n,   h_nodd : n mod 2 = 1,
  h_card : |F| = 2ⁿ,
  f : F → F,
  m : ℕ,   h_m≥2 : 2 ≤ m,
  coeffs : Fin m → F,   h_nz : ∀ i, coeffs i ≠ 0
```

---

## Definitions

```
Δ(f) ≝ { f(x) + f(x + 1) + 1 | x ∈ F }  :  Finset F

κ(f, m, coeffs) ≝ |{ x⃗ : Fin m → F | (∀ i, x⃗ᵢ ∈ Δ(f)) ∧ Σᵢ coeffsᵢ · x⃗ᵢ = 0 }|  :  ℕ
```

---

## Black-Boxed Known Results (Axiomatised)

### ■ KR₁ — APN Cardinality

```
KR₁ : Γ ⊢  |Δ(f)| = 2ⁿ⁻¹
```

*Justification:* f is APN ⟹ x ↦ f(x+1) + f(x) is 2-to-1 ⟹ |im| = |F|/2 = 2ⁿ⁻¹.

### ■ KR₂ — Fourier + AB Spectral Collapse

```
KR₂ : Γ ⊢  |F| · κ(f, m, coeffs) = |Δ(f)|ᵐ
```

*Justification:* Fourier counting identity + AB spectral flatness of Kasami functions.

---

## Proved Arithmetic Lemmas

### Lemma α — Power of power

```
α  :  ∀ n m : ℕ,  1 ≤ n  →  (2ⁿ⁻¹)ᵐ = 2^(m·(n−1))
```

**Proof.**  `(2ⁿ⁻¹)ᵐ = 2^((n−1)·m) = 2^(m·(n−1))`  by `pow_mul` and commutativity.  ∎

### Lemma β — Exponent identity

```
β  :  ∀ n m : ℕ,  3 ≤ n → 2 ≤ m  →  m·(n − 1) = n + ((m−1)·n − m)
```

**Proof.**  Linear arithmetic over ℕ (valid since (m−1)·n ≥ m when m ≥ 2, n ≥ 3).  ∎

### Lemma γ — Exponent split

```
γ  :  ∀ n m : ℕ,  3 ≤ n → 2 ≤ m  →  2^(m·(n−1)) = 2ⁿ · 2^((m−1)·n − m)
```

**Proof.**  `2^(m(n−1))  =  2^(n + ((m−1)n − m))  =  2ⁿ · 2^((m−1)n − m)` by `pow_add` and β.  ∎

---

## ════════════════════════════════════════════
## PRIMAL THEOREM
## ════════════════════════════════════════════

### Theorem P — Generalized m-Tuple Count

```
P  :  Γ ⊢  κ(f, m, coeffs) = 2^((m−1)·n − m)
```

**Proof.**

```
  2ⁿ · κ
    = |F| · κ                      — by h_card
    = |Δ(f)|ᵐ                     — by KR₂
    = (2ⁿ⁻¹)ᵐ                    — by KR₁
    = 2^(m·(n−1))                  — by α
    = 2ⁿ · 2^((m−1)·n − m)        — by γ

  2ⁿ ≠ 0,  so cancel:  κ = 2^((m−1)·n − m).                             ∎
```

### Corollary P₃ — Triple count (m = 3)

```
P₃  :  Γ[m≔3] ⊢  κ(f, 3, coeffs) = 2^(2n − 3)
```

*Proof:* Instantiate P at m = 3.  ∎

### Corollary P₄ — Quadruple count (m = 4)

```
P₄  :  Γ[m≔4] ⊢  κ(f, 4, coeffs) = 2^(3n − 4)
```

*Proof:* Instantiate P at m = 4.  ∎

### Corollary P₅ — Quintuple count (m = 5)

```
P₅  :  Γ[m≔5] ⊢  κ(f, 5, coeffs) = 2^(4n − 5)
```

*Proof:* Instantiate P at m = 5.  ∎

### Observation — C = m

In the formula `κ = 2^((m−1)n − C)`, the constant is **C = m** (definitional / `rfl`).

---

## ════════════════════════════════════════════
## DUAL THEOREM
## ════════════════════════════════════════════

*Direction reversed:* the m-tuple count **determines** |Δ(f)| and forces C = m.

### Dual context (Γ')

```
Γ' ≔
  n m : ℕ,   3 ≤ n,   2 ≤ m,
  δ κ : ℕ,
  KR₂' : 2ⁿ · κ = δᵐ,                       — spectral identity (black-boxed)
  h_κ  : κ = 2^((m−1)·n − m)                 — observed count
```

### Dual Lemma D₁ — Count determines product

```
D₁  :  Γ' ⊢  2ⁿ · κ = 2^(m·n − m)
```

**Proof.**  `2ⁿ · 2^((m−1)n − m) = 2^(n + (m−1)n − m) = 2^(mn − m)` by pow_add and β.  ∎

### Dual Lemma D₂ — Product + spectral ⟹ δᵐ

```
D₂  :  Γ' ⊢  δᵐ = 2^(m·n − m)
```

**Proof.**  Substitute D₁ into KR₂':  `δᵐ = 2ⁿ · κ = 2^(mn − m)`.  ∎

### Dual Lemma D₃ — Unique m-th root

```
D₃  :  ∀ d n m : ℕ,  1 ≤ n → m ≠ 0 → dᵐ = 2^(m·n − m)  →  d = 2ⁿ⁻¹
```

**Proof.**
```
  2^(mn − m)  =  2^(m·(n−1))  =  (2ⁿ⁻¹)ᵐ      — factoring
  dᵐ = (2ⁿ⁻¹)ᵐ  ⟹  d = 2ⁿ⁻¹                  — ℕ powers are injective     ∎
```

### Dual Lemma D₄ — C is forced

```
D₄  :  Γ',  C : ℕ,  C ≤ (m−1)·n,  κ = 2^((m−1)·n − C),  δ = 2ⁿ⁻¹
       ⊢  C = m
```

**Proof.**
```
  2^(n + (m−1)n − C)  =  2ⁿ · κ  =  δᵐ  =  (2ⁿ⁻¹)ᵐ  =  2^(m·(n−1))
  ⟹  n + (m−1)n − C = m(n−1)          — 2-power injectivity
  ⟹  C = m                             — ℕ arithmetic                        ∎
```

### Theorem D — Dual Main Theorem

```
D  :  Γ' ⊢  δ = 2ⁿ⁻¹  ∧  (∀ C ≤ (m−1)·n, κ = 2^((m−1)·n − C) → C = m)
```

**Proof.**  Part 1: chain D₁ → D₂ → D₃.  Part 2: apply D₄ with Part 1.  ∎

---

## ════════════════════════════════════════════
## BIDIRECTIONAL EQUIVALENCE
## ════════════════════════════════════════════

### Theorem E — Primal ↔ Dual

```
E  :  ∀ n m δ κ : ℕ,  3 ≤ n → 2 ≤ m → 2ⁿ · κ = δᵐ
      ⊢   κ = 2^((m−1)·n − m)  ↔  δ = 2ⁿ⁻¹
```

**Proof.**
- (⟹)  Dual theorem D (Part 1).
- (⟸)  Primal computation: substitute δ = 2ⁿ⁻¹ into KR₂', expand, cancel 2ⁿ.  ∎

---

## Dependency Diagram

```
        KR₁ (|Δ|=2ⁿ⁻¹)          KR₂ (|F|·κ=|Δ|ᵐ)
        ─────────┐              ─────────┐
                 │                       │
                 ▼                       ▼
  α ──→ γ ──→  PRIMAL (P): κ = 2^((m−1)n − m)
                 ║
                 ║  instantiate
                 ╠══→ P₃ (m=3): κ = 2^(2n−3)
                 ╠══→ P₄ (m=4): κ = 2^(3n−4)
                 ╚══→ P₅ (m=5): κ = 2^(4n−5)


        KR₂' (spectral)  +  h_κ (observed count)
        ─────────────────────────┐
                                 │
          D₁ ──→ D₂ ──→ D₃ ──→ DUAL (D): δ = 2ⁿ⁻¹ ∧ C = m
                                 │
                                 ▼
               EQUIVALENCE (E): κ = 2^((m−1)n − m)  ⟺  δ = 2ⁿ⁻¹
```

---

## Summary Table

| Result | Statement | Status | Black boxes used |
|--------|-----------|--------|-----------------|
| **P** | κ = 2^((m−1)n − m) | ✅ Proved | KR₁, KR₂ |
| **P₃** | κ₃ = 2^(2n−3) | ✅ Corollary of P | — |
| **P₄** | κ₄ = 2^(3n−4) | ✅ Corollary of P | — |
| **P₅** | κ₅ = 2^(4n−5) | ✅ Corollary of P | — |
| **D** | δ = 2ⁿ⁻¹ ∧ C = m | ✅ Proved | KR₂' |
| **E** | κ-formula ⟺ δ-formula | ✅ Proved | KR₂' |
| **KR₁** | \|Δ(f)\| = 2ⁿ⁻¹ | ⬜ Black-boxed | (APN property of f) |
| **KR₂** | \|F\|·κ = \|Δ\|ᵐ | ⬜ Black-boxed | (Fourier + AB spectral) |
| **C = m** | Constant in exponent | ✅ Definitional | — |
