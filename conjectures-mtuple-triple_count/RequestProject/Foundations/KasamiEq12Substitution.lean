import RequestProject.Foundations.GoldQuadratic
import RequestProject.APN.Defs
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-1: the eq. (12) substitution

This module is the **first from-scratch foundational module of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15).

Equation (12) rewrites the Kasami cross-correlation as a GF(4)-coset average of
*Gold* (quadratic) Gauss sums after the field substitution `x = u^{2^k+1}`.  Its
irreducible *algebraic* substrate is the monomial identity that this substitution
turns the Kasami power into the Gold power `2^{3k}+1`:

```
   (u^{2^k+1})^{d k} = u^{2^{3k}+1},          (kasami_pow_substitution)
```

where `d k = 2^{2k} − 2^k + 1` is the Kasami exponent.  It rests on the exponent
identity

```
   (2^k + 1) · d k = 2^{3k} + 1,              (kasami_exp_mul_nat)
```

the natural-number form of the project's `kasami_exponent_factor`.

Because the right-hand exponent `2^{3k}+1` is a *Gold* exponent, the substituted
Kasami monomial `λ·(u^{2^k+1})^{d k}` is literally `λ·u^{2^{3k}+1}`, a Gold
quadratic monomial (`kasamiAux_isQuadraticForm` with the second coefficient `0`),
which is exactly the term whose Gauss sum the rank-evaluation step of (DD) must
pin.  `kasami_substituted_isQuadraticForm` records this directly.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure finite-field exponent
algebra; it introduces no hypotheses.  The remaining deep cores of (DD) — that
`u ↦ u^{2^k+1}` *realizes* the GF(4)-coset average (the bijectivity / `1/3`
counting on the substitution side), and the rank evaluation pinning each Gold
Gauss-sum term to `{0, ±2^{(n+1)/2}}` — are addressed by the later modules of
§15.

## Sources

Dillon–Dobbertin, *New cyclic difference sets with Singer parameters* (Finite
Fields Appl. 2004), eq. (12); Lidl–Niederreiter, *Finite Fields*, Ch. 6.
-/

namespace Vanish.Foundations

open Finset BigOperators CollisionAnalysis

/-! ## 1. The exponent identity behind the substitution -/

/-- **The Kasami/Gold exponent identity (natural numbers).**
`(2^k + 1) · d k = 2^{3k} + 1`, the natural-number form of
`kasami_exponent_factor`.  This is the arithmetic backbone of equation (12)'s
substitution: it converts the non-quadratic Kasami exponent into the Gold
exponent `2^{3k}+1`. -/
theorem kasami_exp_mul_nat (k : ℕ) :
    (2 ^ k + 1) * d k = 2 ^ (3 * k) + 1 := by
  have hle : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : (2 ^ (2 * k) - 2 ^ k + 1) * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
    have e2 : (2 : ℤ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
    have e3 : (2 : ℤ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
    zify [hle]; rw [e2, e3]; ring
  rw [mul_comm]; simpa [d] using key

/-! ## 2. The monomial substitution identity over the field -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
/-- **The eq. (12) substitution at the monomial level.**  Substituting
`x = u^{2^k+1}` into the Kasami power `x^{d k}` gives the Gold power `u^{2^{3k}+1}`:

```
   (u^{2^k+1})^{d k} = u^{2^{3k}+1}.
```

Pure exponent algebra: `(u^a)^b = u^{a·b}` and the identity `kasami_exp_mul_nat`. -/
theorem kasami_pow_substitution (k : ℕ) (u : F) :
    (u ^ (2 ^ k + 1)) ^ d k = u ^ (2 ^ (3 * k) + 1) := by
  rw [← pow_mul, kasami_exp_mul_nat]

/-- **The substituted Kasami monomial is a Gold quadratic form.**  After the
substitution `x = u^{2^k+1}`, the linear Kasami term `λ·x^{d k}` is
`λ·u^{2^{3k}+1}`, a Gold quadratic monomial — exactly the form whose Gauss sum
the rank-evaluation step of (DD) pins.  (It is `kasamiAux_isQuadraticForm` with
the second coefficient set to `0`, equivalently `goldForm_isQuadraticForm`.) -/
theorem kasami_substituted_isQuadraticForm (k : ℕ) (lam : F) :
    IsQuadraticForm (fun u : F => lam * (u ^ (2 ^ k + 1)) ^ d k) := by
  have h : (fun u : F => lam * (u ^ (2 ^ k + 1)) ^ d k)
      = fun u : F => lam * u ^ (2 ^ (3 * k) + 1) := by
    funext u; rw [kasami_pow_substitution]
  rw [h]; exact goldForm_isQuadraticForm (3 * k) lam

end Vanish.Foundations
