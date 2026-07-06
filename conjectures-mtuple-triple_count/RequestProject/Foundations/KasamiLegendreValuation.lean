import RequestProject.Foundations.KasamiAxKatz
import RequestProject.Foundations.KasamiAxKatzAK2
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-1: the digit-sum ⟺ valuation dictionary

This module is the **first from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of
`Docs/VanishFutureDirections.md`, §15).

The Gross–Koblitz / Stickelberger valuation formula computes the `2`-adic
valuation of a Gauss sum (equivalently of a `p`-adic Γ-value) as a binary
digit sum.  The `p = 2` number-theoretic substrate — **Legendre's formula**
`v₂(n!) = n − s₂(n)` and **Kummer's theorem** for binomial coefficients — is
already in the project (`padicValNat_two_factorial`, `padicValNat_two_choose`,
both in `KasamiAxKatz.lean`).

This module adds the small **dictionary** turning those identities into the exact
shape the McEliece / Canteaut–Charpin–Dobbertin digit-sum *lower* bound of (A) is
phrased in:

* the additive form `s₂(n) + v₂(n!) = n`
  (`binDigitSum_add_padicValNat_two_factorial`);
* the digit-sum recovery `s₂(n) = n − v₂(n!)`
  (`binDigitSum_eq_sub_padicValNat_factorial`);
* the equivalence between a digit-sum *lower* bound and a factorial-valuation
  *upper* bound, `b ≤ s₂(n) ↔ v₂(n!) ≤ n − b`
  (`binDigitSum_ge_iff_padicValNat_le`) — the precise translation used to read off
  the `(n+1)/2 ≤ s₂(e s)` digit-sum lower bound of (A) from the competing
  valuation.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It introduces no new hypotheses: it is
pure number theory built on the project's existing Legendre/Kummer layer, in the
project's `binDigitSum` vocabulary.

## Sources

Legendre's formula / Kummer's theorem; Ireland–Rosen, *A Classical Introduction
to Modern Number Theory*, Ch. 1; McEliece, *Weight congruences for p-ary cyclic
codes* (1972); Gross–Koblitz (Ann. Math. 1979).
-/

namespace Vanish.Foundations

open Finset BigOperators

/-! ## 1. The additive form of Legendre's formula -/

/-- **Additive form of Legendre's formula.**  `s₂(n) + v₂(n!) = n`, from
`padicValNat_two_factorial` and `binDigitSum_le_self`. -/
theorem binDigitSum_add_padicValNat_two_factorial (n : ℕ) :
    binDigitSum n + padicValNat 2 (Nat.factorial n) = n := by
  rw [padicValNat_two_factorial]
  have hle : binDigitSum n ≤ n := binDigitSum_le_self n
  omega

/-- **Digit-sum recovery.**  `s₂(n) = n − v₂(n!)`. -/
theorem binDigitSum_eq_sub_padicValNat_factorial (n : ℕ) :
    binDigitSum n = n - padicValNat 2 (Nat.factorial n) := by
  have h := binDigitSum_add_padicValNat_two_factorial n
  omega

/-! ## 2. Digit-sum lower bound ⟺ factorial-valuation upper bound -/

/-- **A digit-sum lower bound is a factorial-valuation upper bound.**  For
`b ≤ n`, the McEliece / Canteaut–Charpin–Dobbertin digit-sum *lower* bound
`b ≤ s₂(n)` is equivalent to the factorial-valuation *upper* bound
`v₂(n!) ≤ n − b`.  This is the precise translation used to read off the
digit-sum lower bound of direction (A) from the competing valuation. -/
theorem binDigitSum_ge_iff_padicValNat_le {b n : ℕ} (hb : b ≤ n) :
    b ≤ binDigitSum n ↔ padicValNat 2 (Nat.factorial n) ≤ n - b := by
  have h := binDigitSum_add_padicValNat_two_factorial n
  have hle : binDigitSum n ≤ n := binDigitSum_le_self n
  omega

end Vanish.Foundations
