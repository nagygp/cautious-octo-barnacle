import RequestProject.Foundations.KasamiCyclotomicPrime
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-4: the Teichmüller character ω⁻ˢ

This module is the **fourth from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-2/3 (`KasamiTeichmullerLift.lean`, `KasamiCyclotomicPrime.lean`).

The Gauss sum whose `2`-adic valuation Gross–Koblitz computes is indexed by a
power `ω⁻ˢ` of the **Teichmüller character** `ω`.  Having built the Teichmüller
*lift* `ω : Fˣ →* Rˣ` (A-fp-2) as a group homomorphism, this module packages it as
a genuine **multiplicative character** `teichmullerChar ω : MulChar F R`
(via `MulChar.ofUnitHom`), so its powers `ω^a = (teichmullerChar ω)^a` are the
characters indexing the Gauss sums `g(ω^{-s}, ψ) = gaussSum (ω^{-s}) ψ`.

The results:

* `teichmullerChar` — the `MulChar F R` attached to the Teichmüller lift `ω`;
* `teichmullerChar_apply_unit` — its value on a unit is `ω x`
  (`teichmullerChar ω (x:F) = (ω x : R)` for `x : Fˣ`);
* `teichmullerChar_pow_card_eq_one` — `(teichmullerChar ω)^{q−1} = 1`: the
  character has order dividing `q − 1`, so the indexing `s ↦ ω⁻ˢ` factors through
  `ℤ/(q−1)` (the cyclic structure Gross–Koblitz/Stickelberger exploits).

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the character packaging of the
Teichmüller lift; the Gauss sum `gaussSum (teichmullerChar ω ^ s) ψ` is then a
Mathlib object (`gaussSum`) ready for the Frobenius step (A-fp-5) and the
valuation formula (A-fp-6).

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5 (multiplicative characters, Gauss
sums); Ireland–Rosen, Ch. 8; Washington, *Cyclotomic Fields*, Ch. 6.
-/

namespace Vanish.Foundations

open BigOperators MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The Teichmüller character.**  The multiplicative character `F → R` attached
to the Teichmüller lift `ω : Fˣ →* Rˣ` (A-fp-2), via `MulChar.ofUnitHom`. -/
noncomputable def teichmullerChar (ω : Fˣ →* Rˣ) : MulChar F R :=
  MulChar.ofUnitHom ω

omit [Fintype F] [DecidableEq F] [IsDomain R] in
/-- The Teichmüller character evaluated on a unit `x : Fˣ` is the Teichmüller
representative `ω x`. -/
@[simp] theorem teichmullerChar_apply_unit (ω : Fˣ →* Rˣ) (x : Fˣ) :
    teichmullerChar ω (x : F) = (ω x : R) := by
  rw [teichmullerChar, MulChar.ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe]

omit [IsDomain R] in
/--
**The Teichmüller character has order dividing `q − 1`.**  Every multiplicative
character of `F` has order dividing `#Fˣ = q − 1` (each unit `x` satisfies
`x^{q−1} = 1` by Lagrange), so in particular `(teichmullerChar ω)^{#Fˣ} = 1`: the
trivial character.  Hence the indexing `s ↦ (teichmullerChar ω)^{-s}` factors
through `ℤ/(q−1)`.
-/
theorem teichmullerChar_pow_card_eq_one (ω : Fˣ →* Rˣ) :
    (teichmullerChar ω) ^ Fintype.card Fˣ = 1 := by
  grind +suggestions

end Vanish.Foundations