import Mathlib

/-!
# Foundational layer F2 — Power permutations of a finite field

This module is the second *bottom-up* foundational layer of the formalisation of

  M. J. Steiner, *A note on the Walsh spectrum of the Flystel*,
  Designs, Codes and Cryptography (2025) 93:2245–2262.

See `ROADMAP.md` for the global DAG.  It establishes, **fully proved from
Mathlib**, the characterisation of power permutations ([Lidl–Niederreiter, 7.8])
and discharges the skeleton lemma `Flystel.powMap_bijective_iff`.

## Caramello-bridge view

The target lives in the theory of the *field `Fq` as a set-with-a-power-map*.
The clean structural facts, however, live in the theory of the *cyclic group
`Fqˣ`*:

* `IsCyclic.card_powMonoidHom_ker` : `#ker(u ↦ uᵈ) = gcd(#Fqˣ, d)`   (cyclic engine)
* `Nat.Coprime.pow_left_bijective` : `gcd = 1 ⇒ uᵈ bijective`          (cyclic engine)
* `Fintype.card_units`             : `#Fqˣ = #Fq − 1`                  (bridge datum)

`field_pow_bijective_iff_units` is the *non-faithful functor*
`(Fq, ·ᵈ) ⇝ (Fqˣ, ·ᵈ)` that forgets the single fixed point `0`; it lets us
transport bijectivity back and forth between the two theories.  Once in the
cyclic theory, the gcd kernel-count gives the iff for free.

## Corrected statement

The paper assumes `d ≥ 1`.  We make this explicit as `0 < d`.  The hypothesis is
genuinely needed: for `d = 0` and `#Fq = 2` the map `x ↦ x⁰ = 1` is constant
(not bijective) while `gcd(0, 1) = 1` (coprime), so the bare `d : ℕ` statement is
false.  The skeleton declaration `Flystel.powMap_bijective_iff` is updated to
carry the `0 < d` hypothesis accordingly.

## DAG of this layer (each node = one logical step)

```
 [card_powMonoidHom_ker]   [pow_left_bijective]     [card_units]
            \                    /                      |
             units_pow_bijective_iff  ─────────────────/
                       |
        field_pow_bijective_iff_units   (forgetful bridge, uses 0<d)
                       |
              powMap_bijective_iff   (= skeleton target)
```
-/

open scoped BigOperators

namespace Flystel.Foundations

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-! ## Layer F2.1 — the cyclic-group engine

The multiplicative group `Fqˣ` is finite cyclic, so the power map there is
governed entirely by `gcd`. -/

/-- **Atomic step (cyclic kernel-count + Lagrange).**
On the units group, `u ↦ uᵈ` is a bijection iff `gcd(#Fq − 1, d) = 1`.
The forward direction reads off the kernel cardinality
`#ker = gcd(#Fqˣ, d)` (`IsCyclic.card_powMonoidHom_ker`); the backward direction
is `Nat.Coprime.pow_left_bijective`. -/
theorem units_pow_bijective_iff (d : ℕ) :
    Function.Bijective (fun u : Fqˣ => u ^ d) ↔ Nat.Coprime (Fintype.card Fq - 1) d := by
  classical
  have hcard : Nat.card Fqˣ = Fintype.card Fq - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hker : Nat.card (powMonoidHom d : Fqˣ →* Fqˣ).ker = (Nat.card Fqˣ).gcd d :=
    IsCyclic.card_powMonoidHom_ker Fqˣ d
  rw [hcard] at hker
  constructor
  · intro hbij
    have hinj : Function.Injective (powMonoidHom d : Fqˣ →* Fqˣ) := hbij.injective
    rw [← MonoidHom.ker_eq_bot_iff] at hinj
    rw [hinj] at hker
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton] at hker
    rw [Nat.Coprime]; exact hker.symm
  · intro hcop
    have : Nat.Coprime (Nat.card Fqˣ) d := by rw [hcard]; exact hcop
    exact Nat.Coprime.pow_left_bijective this

/-! ## Layer F2.2 — the forgetful bridge `(Fq, ·ᵈ) ⇝ (Fqˣ, ·ᵈ)` -/

/-- **Atomic step (forget the fixed point `0`).**
For `d > 0` the field power map `x ↦ xᵈ` is a bijection iff its restriction to
the units is.  Uses that `xᵈ = 0 ↔ x = 0` (a field has no nonzero nilpotents) to
match the single fixed point `0` on both sides. -/
theorem field_pow_bijective_iff_units (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun x : Fq => x ^ d) ↔ Function.Bijective (fun u : Fqˣ => u ^ d) := by
  classical
  rw [Finite.injective_iff_bijective (f := fun x : Fq => x ^ d) |>.symm,
      Finite.injective_iff_bijective (f := fun u : Fqˣ => u ^ d) |>.symm]
  have hd0 : d ≠ 0 := by omega
  constructor
  · intro hF u v huv
    apply Units.ext; apply hF
    have : ((u : Fq)) ^ d = ((v : Fq)) ^ d := by
      simpa [Units.val_pow_eq_pow_val] using congrArg (Units.val) huv
    simpa using this
  · intro hU x y hxy
    simp only at hxy
    by_cases hx : x = 0
    · subst hx
      have hyd : y ^ d = 0 := by rw [← hxy]; exact zero_pow hd0
      simp only [pow_eq_zero_iff hd0] at hyd; simp [hyd]
    · have hxd : x ^ d ≠ 0 := pow_ne_zero d hx
      have hy : y ≠ 0 := by
        rintro rfl; rw [zero_pow hd0] at hxy; exact hxd hxy
      have hu : Units.mk0 x hx ^ d = Units.mk0 y hy ^ d := by
        apply Units.ext; push_cast; exact hxy
      have h2 := hU hu
      have : (Units.mk0 x hx : Fq) = (Units.mk0 y hy : Fq) := by rw [h2]
      simpa using this

/-! ## Layer F2.3 — the skeleton target -/

/-- **[Lidl–Niederreiter, 7.8]** (discharges `Flystel.powMap_bijective_iff`).
For `d ≥ 1`, the power map `x ↦ xᵈ` is a permutation of `Fq` iff
`gcd(d, #Fq − 1) = 1`. -/
theorem powMap_bijective_iff (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun x : Fq => x ^ d) ↔ Nat.Coprime d (Fintype.card Fq - 1) := by
  rw [field_pow_bijective_iff_units d hd, units_pow_bijective_iff d, Nat.coprime_comm]

end Flystel.Foundations
