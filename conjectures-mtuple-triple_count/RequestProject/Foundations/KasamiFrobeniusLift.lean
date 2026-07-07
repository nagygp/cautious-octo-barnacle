import RequestProject.Foundations.KasamiTeichmullerChar
import RequestProject.Foundations.KasamiGrossKoblitz
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-5: the Frobenius lift

This module is the **fifth from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-4 (`KasamiTeichmullerChar.lean`) and the residue-level Frobenius
step `gaussSum_sq_char_step` (`KasamiGrossKoblitz.lean`).

The Gross–Koblitz argument propagates the valuation along the **Frobenius orbit**
`s ↦ 2s` of the prime `𝔭 ∣ (2)`: the arithmetic Frobenius `e` of the
decomposition group lifts the residue Frobenius `x ↦ x²`, and on Gauss sums it
realizes `g(ω^{-2s}) = e(g(ω^{-s}))`.  At the character / residue level this is the
Gauss-sum squaring law in characteristic two
(`gaussSum_sq_char_step`: `g(χ, ψ)² = g(χ², ψ²)`), since squaring the Teichmüller
character `ω^{-s}` is *literally* the doubling `s ↦ 2s`.

This module packages that on the Teichmüller character:

* `teichmullerChar_sq_pow` — `(ω^a)² = ω^{2a}`: squaring the character is the
  exponent doubling;
* `gaussSum_teichmuller_frobenius` — `g(ω^a, ψ)² = g(ω^{2a}, ψ²)`: the Gauss sum of
  `ω^a` squares to the Gauss sum of `ω^{2a}` (with `ψ ↦ ψ²`), the concrete Gauss-sum
  realization of the Frobenius doubling step.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the character-power packaging of the
already-proven `gaussSum_sq_char_step`; that the squaring map is the arithmetic
Frobenius `e` of the decomposition group (rather than just the residue `x ↦ x²`) is
the Galois-theoretic identification supplied by the cyclotomic prime A-fp-3.

## Sources

Gross–Koblitz (Ann. Math. 1979); Ireland–Rosen, Ch. 14; Washington, *Cyclotomic
Fields*, Ch. 6; Lidl–Niederreiter, *Finite Fields*, Ch. 5.
-/

namespace Vanish.Foundations

open BigOperators MulChar AddChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]

omit [Fintype F] [DecidableEq F] [IsDomain R] in
/-- **Squaring the Teichmüller character is exponent doubling.**
`(teichmullerChar ω ^ a)² = teichmullerChar ω ^ (2a)`. -/
theorem teichmullerChar_sq_pow (ω : Fˣ →* Rˣ) (a : ℕ) :
    (teichmullerChar ω ^ a) ^ 2 = teichmullerChar ω ^ (2 * a) := by
  rw [← pow_mul, mul_comm]

omit [DecidableEq F] [IsDomain R] in
/-- **The Frobenius doubling step on Gauss sums.**  In characteristic two, the
Gauss-sum squaring law `gaussSum_sq_char_step` applied to the Teichmüller
character power `ω^a` gives `g(ω^a, ψ)² = g(ω^{2a}, ψ²)`: squaring the Gauss sum is
the exponent doubling `a ↦ 2a` (the arithmetic-Frobenius action). -/
theorem gaussSum_teichmuller_frobenius [Fact (Nat.Prime 2)] [CharP R 2]
    (ω : Fˣ →* Rˣ) (a : ℕ) (ψ : AddChar F R) :
    gaussSum (teichmullerChar ω ^ a) ψ ^ 2
      = gaussSum (teichmullerChar ω ^ (2 * a)) (ψ ^ 2) := by
  rw [gaussSum_sq_char_step, teichmullerChar_sq_pow]

end Vanish.Foundations
