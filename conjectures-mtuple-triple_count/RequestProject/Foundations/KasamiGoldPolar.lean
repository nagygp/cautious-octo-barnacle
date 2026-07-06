import RequestProject.Foundations.GoldQuadratic
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-4a: the explicit Gold polar form

This module is a **further from-scratch foundational rung of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), refining DD-fp-4 (`KasamiGoldRadical.lean`).

The roadmap notes that DD-fp-4 itself splits into "radical = kernel of the polar
map; polar map = a linearized polynomial; its rank via gcd of exponents".  The
size-2 radical hypothesis `hrad` carried in `KasamiGoldRadical.lean` is the
*output* of that gcd computation; the first concrete step towards it is to write
the polar (bilinear) form of a Gold monomial **explicitly** as a linearized
expression, so that the radical becomes the trace-trivial kernel of an explicit
`F₂`-linear map.

In characteristic `2`, Freshman's dream makes `y ↦ y^{2^j}` additive, so the
polar form of the Gold monomial `Q(y) = λ·y^{2^j+1}` is the bilinear form

```
   B(x, u) = λ·(x^{2^j}·u + x·u^{2^j}),
```

a linearized polynomial in `u` for each fixed `x`.  The radical is then the
trace-trivial kernel `{ u | ∀ x, Tr(B(x,u)) = 0 }` of this explicit form
(`goldForm_mem_radical`), and the auxiliary equation-(12) form
`λ x^{2^{3k}+1} + a x^{2^k+1}` has the sum polar form `kasamiAux_polar` — the
explicit linearized object whose gcd-of-exponents rank computation is the
remaining DD-fp-4 core.

## Results

* `goldForm_polar` — the explicit Gold polar form
  `B(x,u) = λ(x^{2^j} u + x u^{2^j})`.
* `goldForm_mem_radical` — the radical as the trace-trivial kernel of `B`.
* `kasamiAux_polar` — the polar form of the auxiliary sum-of-Gold form.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure characteristic-2 polynomial
algebra (`add_pow_char_pow` / Freshman's dream) plus the definitions of `polar`
and `radical`; it introduces no new hypotheses.  The remaining DD-fp-4 content —
that this explicit linearized map has a one-dimensional kernel for the relevant
parameters (the gcd-of-exponents computation) — is the carried core.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4; Lidl–Niederreiter, *Finite Fields*,
Ch. 3 (linearized polynomials), Ch. 6 (quadratic forms).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
**The explicit Gold polar form.**  In characteristic `2`, the polar form of the
Gold monomial `Q(y) = λ·y^{2^j+1}` is the linearized bilinear form
`B(x,u) = λ·(x^{2^j}·u + x·u^{2^j})` (Freshman's dream makes `y ↦ y^{2^j}`
additive).
-/
omit [Fintype F] [DecidableEq F] in
theorem goldForm_polar (j : ℕ) (lam : F) (x u : F) :
    polar (fun y : F => lam * y ^ (2 ^ j + 1)) x u
      = lam * (x ^ (2 ^ j) * u + x * u ^ (2 ^ j)) := by
  have h : (x + u) ^ (2 ^ j) = x ^ (2 ^ j) + u ^ (2 ^ j) := add_pow_char_pow x u 2 j
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [polar, pow_succ, h]
  ring_nf
  linear_combination (lam * x ^ (2 ^ j) * x + lam * u ^ (2 ^ j) * u) * h2

/-
**The Gold radical as a trace-trivial kernel.**  `u` lies in the radical of the
Gold monomial `λ·y^{2^j+1}` iff the explicit linearized form
`λ(x^{2^j} u + x u^{2^j})` is trace-trivial for every `x`.
-/
omit [DecidableEq F] in
theorem goldForm_mem_radical (j : ℕ) (lam : F) (u : F) :
    u ∈ radical (fun y : F => lam * y ^ (2 ^ j + 1))
      ↔ ∀ x : F, Tr (lam * (x ^ (2 ^ j) * u + x * u ^ (2 ^ j))) = 0 := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · exact fun x => by simpa [ goldForm_polar ] using mem_radical.mp h x;
  · refine' Finset.mem_filter.mpr ⟨ Finset.mem_univ _, _ ⟩;
    convert h using 1;
    rw [ goldForm_polar ]

/-
**The auxiliary equation-(12) polar form.**  The polar form of the
sum-of-Gold auxiliary form `λ x^{2^{3k}+1} + a x^{2^k+1}` is the sum of the two
explicit Gold polar forms.
-/
omit [Fintype F] [DecidableEq F] in
theorem kasamiAux_polar (k : ℕ) (lam a : F) (x u : F) :
    polar (fun y : F => lam * y ^ (2 ^ (3 * k) + 1) + a * y ^ (2 ^ k + 1)) x u
      = lam * (x ^ (2 ^ (3 * k)) * u + x * u ^ (2 ^ (3 * k)))
        + a * (x ^ (2 ^ k) * u + x * u ^ (2 ^ k)) := by
  have h1 : (x + u) ^ (2 ^ (3 * k)) = x ^ (2 ^ (3 * k)) + u ^ (2 ^ (3 * k)) :=
    add_pow_char_pow x u 2 (3 * k)
  have h2 : (x + u) ^ (2 ^ k) = x ^ (2 ^ k) + u ^ (2 ^ k) := add_pow_char_pow x u 2 k
  have hc : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [polar, pow_succ, h1, h2]
  ring_nf
  linear_combination (lam * x ^ (2 ^ (3 * k)) * x + lam * u ^ (2 ^ (3 * k)) * u
    + a * x ^ (2 ^ k) * x + a * u ^ (2 ^ k) * u) * hc

end Vanish.Foundations