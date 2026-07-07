/-
Copyright (c) 2025 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Power permutations of a finite field

For a finite field `K` and an exponent `d ≥ 1`, the monomial map `x ↦ x ^ d` is a
permutation of `K` if and only if `d` is coprime to `#K - 1`
([Lidl–Niederreiter, *Finite Fields*, Theorem 7.8]).

Mathlib already knows the *group* version of this fact
(`Nat.Coprime.pow_left_bijective`, `powCoprime`), which governs the power map on
the unit group `Kˣ`. This file bridges that result across the single fixed point
`0` to obtain the statement for the whole field, and packages it as an `Equiv`.

This is a small, general, reusable pearl written to Mathlib conventions and is a
candidate for upstreaming to `Mathlib/FieldTheory/Finite/Basic.lean` (or a
dedicated `Mathlib/FieldTheory/Finite/PowerMap.lean`).

## Main results

* `FiniteField.units_pow_bijective_iff` — on `Kˣ`, `u ↦ u ^ d` is bijective iff
  `Nat.Coprime (#K - 1) d`.
* `FiniteField.pow_bijective_iff_units` — for `d > 0`, the field power map
  `x ↦ x ^ d` is bijective iff its restriction to the units is.
* `FiniteField.pow_bijective_iff` — the headline characterisation
  ([Lidl–Niederreiter, 7.8]): for `d > 0`, `x ↦ x ^ d` is a permutation of `K`
  iff `Nat.Coprime d (#K - 1)`.
* `FiniteField.powEquiv` — the corresponding `Equiv K K` when the coprimality
  holds.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Cambridge University Press,
  Theorem 7.8.

## Tags

finite field, power map, permutation polynomial, monomial
-/

open scoped BigOperators

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- On the unit group of a finite field, the power map `u ↦ u ^ d` is a bijection
iff `d` is coprime to `#K - 1 = #Kˣ`.

The forward direction reads off the kernel cardinality `#ker = gcd (#Kˣ) d`
(`IsCyclic.card_powMonoidHom_ker`); the backward direction is
`Nat.Coprime.pow_left_bijective`. -/
theorem units_pow_bijective_iff (d : ℕ) :
    Function.Bijective (fun u : Kˣ => u ^ d) ↔ Nat.Coprime (Fintype.card K - 1) d := by
  classical
  have hcard : Nat.card Kˣ = Fintype.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hker : Nat.card (powMonoidHom d : Kˣ →* Kˣ).ker = (Nat.card Kˣ).gcd d :=
    IsCyclic.card_powMonoidHom_ker Kˣ d
  rw [hcard] at hker
  constructor
  · intro hbij
    have hinj : Function.Injective (powMonoidHom d : Kˣ →* Kˣ) := hbij.injective
    rw [← MonoidHom.ker_eq_bot_iff] at hinj
    rw [hinj] at hker
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton] at hker
    rw [Nat.Coprime]; exact hker.symm
  · intro hcop
    have : Nat.Coprime (Nat.card Kˣ) d := by rw [hcard]; exact hcop
    exact Nat.Coprime.pow_left_bijective this

/-- For `d > 0`, the field power map `x ↦ x ^ d` is a bijection iff its
restriction to the unit group is. The two maps differ only on the fixed point
`0` (a field has no nonzero nilpotents), so bijectivity transports between them.
-/
theorem pow_bijective_iff_units (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun x : K => x ^ d) ↔ Function.Bijective (fun u : Kˣ => u ^ d) := by
  classical
  rw [Finite.injective_iff_bijective (f := fun x : K => x ^ d) |>.symm,
      Finite.injective_iff_bijective (f := fun u : Kˣ => u ^ d) |>.symm]
  have hd0 : d ≠ 0 := by omega
  constructor
  · intro hF u v huv
    apply Units.ext; apply hF
    have : ((u : K)) ^ d = ((v : K)) ^ d := by
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
      have : (Units.mk0 x hx : K) = (Units.mk0 y hy : K) := by rw [h2]
      simpa using this

/-- **[Lidl–Niederreiter, *Finite Fields*, Theorem 7.8].**
For `d ≥ 1`, the monomial map `x ↦ x ^ d` is a permutation of the finite field
`K` iff `d` is coprime to `#K - 1`.

The hypothesis `0 < d` is genuinely needed: for `d = 0` and `#K = 2`, the map
`x ↦ x ^ 0 = 1` is constant (not bijective) while `gcd 0 1 = 1`. -/
theorem pow_bijective_iff (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun x : K => x ^ d) ↔ Nat.Coprime d (Fintype.card K - 1) := by
  rw [pow_bijective_iff_units d hd, units_pow_bijective_iff d, Nat.coprime_comm]

/-- The permutation of a finite field `K` induced by `x ↦ x ^ d` when `d ≥ 1` is
coprime to `#K - 1`, packaged as an `Equiv`. -/
noncomputable def powEquiv (d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d (Fintype.card K - 1)) :
    K ≃ K :=
  Equiv.ofBijective (fun x : K => x ^ d) ((pow_bijective_iff d hd).mpr hcop)

@[simp]
theorem powEquiv_apply (d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d (Fintype.card K - 1))
    (x : K) : powEquiv d hd hcop x = x ^ d := rfl

end FiniteField
