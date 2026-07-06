import RequestProject.Foundations.KasamiGoldRadical
import RequestProject.Foundations.KasamiGoldRadicalGcd
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-4d: radical = Frobenius fixed set

This module is a **further from-scratch foundational rung of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), wiring DD-fp-4c
(`KasamiGoldRadicalGcd.lean`, the Frobenius fixed-point gcd count) into DD-fp-4
(`KasamiGoldRadical.lean`, the rank-1 ⇒ spectrum reduction).

The two rungs already in place are:

* `frobeniusFixed_card_eq_two_of_coprime` — in `GF(2ⁿ)`, the Frobenius fixed set
  `{u | u^{2^a} = u}` has exactly `2` elements when `gcd(a,n) = 1`; and
* `kasamiAux_radical_two_spectrum` — if the auxiliary Gold form has a two-element
  radical, its Gauss sum lies in `{0, ±2^{(n+1)/2}}`.

The bridge between them is the **identification of the radical with a Frobenius
fixed set**: for the Kasami parameters the auxiliary Gold-form radical *is* the
fixed set of a Frobenius power `φ^{a'}` with `gcd(a', n) = 1`.  That identification
is the trace-substitution content (`h12`), carried here as the hypothesis
`hident`; this module proves it discharges the remaining `|radical| = 2` premise
and hence pins each equation-(12) term to the AB value set:

```
   radical Q = {u | u^{2^{a'}} = u}   ∧   gcd(a', n) = 1
        ⟹   |radical Q| = 2   ⟹   S(Q) ∈ {0, ±2^{(n+1)/2}}.
```

## Results

* `radical_card_two_of_frobenius_ident` — from the Frobenius identification and
  `gcd(a', n) = 1`, the radical has exactly two elements.
* `kasamiAux_radical_frobenius_spectrum` — the auxiliary Gold-form Gauss sum lies
  in `{0, ±2^{(n+1)/2}}` once the radical is identified with a coprime Frobenius
  fixed set.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the gcd-count ⇒ rank-1 ⇒ spectrum
wiring; the identification of the auxiliary Gold-form radical *with* a coprime
Frobenius fixed set for the Kasami parameters (the trace-substitution `h12`) is the
carried core.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4; Lidl–Niederreiter, *Finite Fields*,
Ch. 2–3, 6 (subfields, linearized polynomials, quadratic forms).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **The radical has two elements, from the Frobenius identification.**  If the
radical of a quadratic form coincides with the Frobenius fixed set
`{u | u^{2^{a'}} = u}` and `gcd(a', n) = 1`, then `|radical Q| = 2` by the
gcd-count `frobeniusFixed_card_eq_two_of_coprime`. -/
theorem radical_card_two_of_frobenius_ident {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) {Q : F → F} (a' : ℕ) (hgcd : Nat.gcd a' n = 1)
    (hident : radical Q = univ.filter (fun u : F => u ^ (2 ^ a') = u)) :
    (radical Q).card = 2 := by
  rw [hident]
  exact frobeniusFixed_card_eq_two_of_coprime hn hcard a' hgcd

/-- **The auxiliary Gold-form spectrum, from the Frobenius identification.**  If the
radical of the Appendix-A.4 auxiliary Gold form `λ x^{2^{3k}+1} + a x^{2^k+1}`
coincides with a coprime Frobenius fixed set, then (for `n` odd) its Gauss sum lies
in `{0, ±2^{(n+1)/2}}`.  This combines the gcd-count `|radical| = 2`
(`radical_card_two_of_frobenius_ident`) with the rank-1 ⇒ spectrum reduction
(`kasamiAux_radical_two_spectrum`). -/
theorem kasamiAux_radical_frobenius_spectrum {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (hnodd : Odd n) (k : ℕ) (lam a : F)
    (a' : ℕ) (hgcd : Nat.gcd a' n = 1)
    (hident : radical (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
        = univ.filter (fun u : F => u ^ (2 ^ a') = u)) :
    quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1)) = 0
      ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
          = 2 ^ ((n + 1) / 2)
      ∨ quadGaussSum (fun x : F => lam * x ^ (2 ^ (3 * k) + 1) + a * x ^ (2 ^ k + 1))
          = -2 ^ ((n + 1) / 2) :=
  kasamiAux_radical_two_spectrum hcard hnodd k lam a
    (radical_card_two_of_frobenius_ident hn hcard a' hgcd hident)

end Vanish.Foundations
