import Mathlib

/-!
# Dobbertin, Theorem 1 — step (1) ⟹ (2): definitions

Elementary definitions for the opening step of the proof of Theorem 1 in

> H. Dobbertin, *Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets*, NATO Sci. Ser. C **542**, 1999, pp. 133–158.

Throughout, `F = 𝔽_{2ⁿ}` is a finite field of characteristic `2`.  Equation (1)
of the paper, cleared of denominators, reads

```
   c · x^{2^k+1} = ∑_{i=1}^{k'} x^{2^{ik}} + α · Tr(x)                (1)
```

and the linearized equation (2) is `ℓ(x) = 0` where

```
   ℓ(x) = c^{2^k} · x^{2^{2k}} + x^{2^k} + c · x + 1.                 (2)
```

All definitions here depend only on `Mathlib`.
-/

namespace Dobbertin.Step1

open Finset

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Absolute **trace** `Tr(x) = ∑_{i<n} x^{2^i}`. -/
def trace (n : ℕ) (x : F) : F := ∑ i ∈ range n, x ^ (2 ^ i)

/-- **Numerator sum** `S(x) = ∑_{i=1}^{k'} x^{2^{ik}}` (the right side of (1)
without the trace term). -/
def numeratorSum (k k' : ℕ) (x : F) : F := ∑ i ∈ Icc 1 k', x ^ (2 ^ (i * k))

/-- **Partial trace** `P(x) = ∑_{j<k'} x^{2^{jk}}`: the length-`k'` linearized
polynomial for the Frobenius step `x ↦ x^{2^k}`.  It satisfies `S = P^{2^k}`. -/
def partialTrace (k k' : ℕ) (x : F) : F := ∑ j ∈ range k', x ^ (2 ^ (j * k))

/-- **Equation (1)** of the paper, cleared of denominators:
`c · x^{2^k+1} = S(x) + α · Tr(x)`. -/
def equation1 (n k k' α : ℕ) (c x : F) : Prop :=
  c * x ^ (2 ^ k + 1) = numeratorSum k k' x + (α : F) * trace n x

/-- The **linearized polynomial** `ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1`
of equation (2). -/
def linearized (k : ℕ) (c x : F) : F :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

end Dobbertin.Step1
