import RequestProject.Foundations.KasamiAxKatzAK2
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-9: the digit-sum complement balance

This module is a **further from-scratch foundational rung of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on the binary-digit-sum toolkit of `KasamiAxKatzAK2.lean`.

The two cores of (A) are the Gross–Koblitz `𝔭`-form valuation
`v₂(g(ω^{-s})) = s₂(e s)` and the McEliece digit-sum lower bound
`(n+1)/2 ≤ s₂(e s)`.  Underneath the Gross–Koblitz valuation lies one purely
combinatorial *balance* identity, the deepest/simplest level closest to Mathlib:
the binary digit sum and its `n`-bit **complement** add up to `n`,

```
   s₂(a) + s₂(2ⁿ − 1 − a) = n            (for a ≤ 2ⁿ − 1).
```

This is the combinatorial shadow of the **Gauss-sum magnitude relation**
`g(χ,ψ)·g(χ⁻¹,ψ⁻¹) = ±q` (`gaussSum_mul_gaussSum_eq_card`): the conjugate Gauss
sum is indexed by the complementary exponent, and the two `2`-adic valuations
(digit sums) must sum to `n = v₂(q)`.  Combined with the McEliece lower bound it
shows the bound for `a` is exactly the upper bound `s₂(2ⁿ−1−a) ≤ (n−1)/2` for the
complement.

## Results

* `binDigitSum_add_compl` — `s₂(a) + s₂(2ⁿ − 1 − a) = n` for `a ≤ 2ⁿ − 1`.
* `binDigitSum_compl` — `s₂(2ⁿ − 1 − a) = n − s₂(a)`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure `Nat` digit arithmetic; it
introduces no new hypotheses.  The remaining content — the *value* of the
valuation (the Gross–Koblitz `p`-adic Γ formula) and the McEliece lower bound —
are the carried cores of (A).

## Sources

Gross–Koblitz, *Gauss sums and the p-adic Γ-function* (Ann. Math. 1979);
McEliece, *Weight congruences for p-ary cyclic codes* (1972); Ireland–Rosen,
Ch. 14; Lidl–Niederreiter, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

/-
**The digit-sum complement balance.**  For `a ≤ 2ⁿ − 1`, the binary digit sum
of `a` and that of its `n`-bit complement `2ⁿ − 1 − a` add up to `n`: flipping each
of the `n` bits of `a` turns each `1` into a `0` and vice versa, so the two
populations of set bits partition the `n` positions.  This is the combinatorial
shadow of the Gauss-sum magnitude relation `g(χ)·g(χ̄) = ±q`.
-/
theorem binDigitSum_add_compl (n a : ℕ) (ha : a ≤ 2 ^ n - 1) :
    binDigitSum a + binDigitSum (2 ^ n - 1 - a) = n := by
  induction' n with n ih generalizing a <;> simp_all +decide [ Nat.pow_succ' ];
  rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩;
  · rw [ show 2 * 2 ^ n - 1 - 2 * b = 2 * ( 2 ^ n - 1 - b ) + 1 from ?_, binDigitSum_two_mul_add_one ];
    · linarith [ ih b ( by omega ), binDigitSum_two_mul b ];
    · grind;
  · convert congr_arg ( · + 1 ) ( ih b ( by omega ) ) using 1;
    rw [ show 2 * 2 ^ n - 1 - ( 2 * b + 1 ) = 2 * ( 2 ^ n - 1 - b ) by omega, Vanish.Foundations.binDigitSum_two_mul_add_one, Vanish.Foundations.binDigitSum_two_mul ] ; ring

/-- **The complement digit sum.**  `s₂(2ⁿ − 1 − a) = n − s₂(a)` for `a ≤ 2ⁿ − 1`. -/
theorem binDigitSum_compl (n a : ℕ) (ha : a ≤ 2 ^ n - 1) :
    binDigitSum (2 ^ n - 1 - a) = n - binDigitSum a := by
  have h := binDigitSum_add_compl n a ha
  omega

end Vanish.Foundations