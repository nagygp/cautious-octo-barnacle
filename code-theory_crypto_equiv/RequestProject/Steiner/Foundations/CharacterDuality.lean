import Mathlib

/-!
# Foundational layer F1 — Character duality over a finite field

This module is the first *bottom-up* foundational layer of the formalisation of

  M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
  Designs, Codes and Cryptography (2025) 93:2245–2262.

See `ROADMAP.md` for the global DAG of layers.  This file establishes, **fully
proved from Mathlib**, the structural fact that the additive characters of a
finite field `Fq` are *exactly* the `mulShift`s of one fixed primitive character
— the finite-field instance of Pontryagin duality `F ≅ F̂`.  It discharges the
skeleton lemma `Flystel.exists_eq_fundamental_smul`
([Lidl–Niederreiter, 5.7]).

## Caramello-bridge view

The statement we need ("every non-trivial `ψ` is `x ↦ ψ₁(b·x)`") lives in the
theory of *characters*.  Mathlib already proves the **dual** structural fact in
the theory of the *group `Fq` itself*:

* `AddChar.card_eq`                    : `#(AddChar Fq ℂ) = #Fq`            (counting)
* `AddChar.to_mulShift_inj_of_isPrimitive` : `mulShift ψ₁` is injective  (primitivity)
* `AddChar.IsPrimitive.of_ne_one`      : on a field, `≠ 1 ⇒ primitive`.

The bridge `Fintype.bijective_iff_injective_and_card` turns the *injective map of
equal-cardinality finite types* (the `F → F̂` direction) into a *bijection*,
whose surjectivity is precisely the existence statement we want.  No new
mathematics is created here — we only transport an already-available equivalence.

## DAG of this layer (each node = one logical step)

```
 [card_eq]   [to_mulShift_inj]   [of_ne_one]
      .            .                 .
        mulShift_bijective_of_primitive
                    .
           exists_mulShift_eq
                    .
         exists_eq_fundamental_smul   (= skeleton target)
```
-/

open scoped BigOperators

namespace Flystel.Foundations

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-! ## Layer F1.0 — the fundamental (primitive) character -/

/-- A fixed primitive additive character `ψ₁ : Fq → ℂ`.  It plays the role of the
"fundamental character" `ψ₁(x) = exp(2πi·Tr(x)/p)` of the paper. -/
noncomputable def fundamentalChar (Fq : Type*) [Field Fq] [Fintype Fq] :
    AddChar Fq ℂ :=
  AddChar.FiniteField.primitiveChar_to_Complex Fq

/-- The fundamental character is primitive. -/
theorem fundamentalChar_isPrimitive :
    (fundamentalChar Fq).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive Fq

/-! ## Layer F1.1 — the duality bijection `F → F̂` (one node each)

Each lemma performs exactly one logical step. -/

/-- **Atomic step (counting + injectivity ⇒ bijection).**
For a primitive character `ψ₁`, the map `b ↦ mulShift ψ₁ b : Fq → AddChar Fq ℂ`
is a bijection.  Combines `to_mulShift_inj_of_isPrimitive` (injectivity) with
`AddChar.card_eq` (equal finite cardinalities). -/
theorem mulShift_bijective_of_primitive
    {ψ₁ : AddChar Fq ℂ} (h : ψ₁.IsPrimitive) :
    Function.Bijective ψ₁.mulShift := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨AddChar.to_mulShift_inj_of_isPrimitive h, AddChar.card_eq.symm⟩

/-- **Atomic step (bijection ⇒ surjection).**
Every additive character of `Fq` is `mulShift ψ₁ b` for some `b`, where `ψ₁` is a
fixed primitive character. -/
theorem exists_mulShift_eq
    {ψ₁ : AddChar Fq ℂ} (h : ψ₁.IsPrimitive) (ψ : AddChar Fq ℂ) :
    ∃ b : Fq, ψ₁.mulShift b = ψ :=
  (mulShift_bijective_of_primitive h).surjective ψ

/-! ## Layer F1.2 — the skeleton target -/

/-- **[Lidl–Niederreiter, 5.7]** (discharges `Flystel.exists_eq_fundamental_smul`).
Every non-trivial additive character of `Fq` is `x ↦ ψ₁(b·x)` for some `b ≠ 0`
and `ψ₁` the fundamental character. -/
theorem exists_eq_fundamental_smul
    (ψ : AddChar Fq ℂ) (hψ : ψ ≠ 1) :
    ∃ (ψ₁ : AddChar Fq ℂ) (b : Fq), b ≠ 0 ∧ ∀ x : Fq, ψ x = ψ₁ (b * x) := by
  obtain ⟨b, hb⟩ := exists_mulShift_eq (fundamentalChar_isPrimitive (Fq := Fq)) ψ
  refine ⟨fundamentalChar Fq, b, ?_, ?_⟩
  · rintro rfl
    rw [AddChar.mulShift_zero] at hb
    exact hψ hb.symm
  · intro x
    rw [← hb, AddChar.mulShift_apply]

end Flystel.Foundations
