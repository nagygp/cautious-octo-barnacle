import Mathlib
import CodeTheoryCryptoEquiv.DiffUniformity.Flystel
import CodeTheoryCryptoEquiv.DiffUniformity.CCZEquiv

/-!
# The field-level Flystel and the Anemoi round (CCZ instantiation)

This module completes the CCZ-equivalence track of `CODING_THEORY_DIRECTIONS.md`
on the *field side*: the **full field-level Flystel / Anemoi round instantiation**.
It builds on the generic open Flystel `APN.openFlystel` of
`CodeTheoryCryptoEquiv/DiffUniformity/Flystel.lean` and the CCZ-equivalence relation
`APN.CCZEquiv` of `CodeTheoryCryptoEquiv/DiffUniformity/CCZEquiv.lean`.

The Anemoi permutation (Bouvier–Briaud–Chaidos–Grassi–Manterola–Merino–
Roy–Schofnegger–Salen, 2023) is built over a finite field `K` from the **open
Flystel** of `K × K`, whose verification (arithmetisation) form is the **closed
Flystel** — its compositional inverse.  The structural fact that makes Anemoi
both secure and cheap to arithmetise is that the open and closed Flystels are
**CCZ-equivalent**, hence share their differential uniformity, even though the
closed form has low algebraic degree.

This file:

* gives the **explicit closed Flystel** (the inverse of the open Flystel) as a
  concrete formula `openFlystel_symm_apply` over any additive group;
* instantiates everything over a **finite field** `K`: `flystelField` and its
  CCZ-equivalence to the closed form (`cczEquiv_flystelField_symm`) and the
  shared differential uniformity (`differentialUniformity_flystelField_symm`);
* constructs the field **power-map permutation** `powerPerm` (the `x ↦ x^a`
  S-box of Anemoi, a permutation when `a` is coprime to `|K| - 1`) and packages
  the resulting concrete Anemoi-style Flystel `anemoiFlystel`, recording its
  open/closed CCZ-equivalence and δ-uniformity equality.

## Main results

* `openFlystel_symm_apply` — the explicit closed-Flystel formula.
* `cczEquiv_flystelField_symm`, `differentialUniformity_flystelField_symm` —
  the open and closed field Flystels are CCZ-equivalent with equal δ-uniformity.
* `powerPerm` — the field power-map permutation `x ↦ x^a` (`gcd(a, |K|-1) = 1`).
* `anemoiFlystel`, `cczEquiv_anemoiFlystel_symm`,
  `differentialUniformity_anemoiFlystel_symm` — the concrete Anemoi Flystel.
-/

open Finset

namespace APN

/-! ### The explicit closed Flystel (inverse of the open Flystel) -/

section Explicit
variable {V : Type*} [AddCommGroup V]

/-
**The closed Flystel, explicitly.**  Composing the inverse shears gives the
closed-form (verification) map: the inverse of the open Flystel sends `(x, y)`
to `(x - R y + Q (y + e⁻¹ (x - R y)), y + e⁻¹ (x - R y))`.
-/
theorem openFlystel_symm_apply (e : Equiv.Perm V) (Q R : V → V) (x y : V) :
    (openFlystel e Q R).symm (x, y)
      = (x - R y + Q (y + e.symm (x - R y)), y + e.symm (x - R y)) := by
  unfold openFlystel;
  simp +decide [ Equiv.symm_trans_apply, shearFst, shearSnd, Equiv.coe_fn_symm_mk ]

end Explicit

/-! ### The field-level Flystel -/

section Field
variable {K : Type*} [Field K] [Fintype K]

/-- The **field-level open Flystel**: the open Flystel of `K × K` built from a
permutation `e` of the field and two coordinate functions `Q R : K → K`. -/
def flystelField (e : Equiv.Perm K) (Q R : K → K) : Equiv.Perm (K × K) :=
  openFlystel e Q R

omit [Fintype K] in
/-- The open field Flystel is **CCZ-equivalent to the closed field Flystel**
(its compositional inverse). -/
theorem cczEquiv_flystelField_symm (e : Equiv.Perm K) (Q R : K → K) :
    CCZEquiv (⇑(flystelField e Q R)) (⇑(flystelField e Q R).symm) :=
  cczEquiv_inverse (flystelField e Q R)

/-- The open and closed field Flystels share their **differential uniformity**. -/
theorem differentialUniformity_flystelField_symm (e : Equiv.Perm K) (Q R : K → K) :
    differentialUniformity (⇑(flystelField e Q R).symm)
      = differentialUniformity (⇑(flystelField e Q R)) :=
  differentialUniformity_inverse (flystelField e Q R)

end Field

/-! ### The field power-map permutation and the concrete Anemoi Flystel -/

section PowerPerm
variable (K : Type*) [Field K] [Fintype K]

/-
The **power-map permutation** `x ↦ x^a` of a finite field `K`.  When `a` is
coprime to `|K| - 1` (the order of `Kˣ`) and `0 < a`, the map is a bijection: it
fixes `0` and restricts to a bijection on the cyclic group `Kˣ`.
-/
noncomputable def powerPerm (a : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime (Fintype.card K - 1) a) : Equiv.Perm K :=
  Equiv.ofBijective (fun x => x ^ a) (by
  -- Fix an arbitrary $x \in K$. Since the field $K$ is finite, every power map $x \mapsto x^a$ is bijective if $a$ is coprime to the order of the multiplicative group of $K$.
  have h_unit_group : Function.Bijective (fun u : (Kˣ) => u ^ a) := by
    have h_unit_group : ∀ u : Kˣ, u ^ a = 1 → u = 1 := by
      intro u hu
      have h_order : orderOf u ∣ a := by
        exact orderOf_dvd_of_pow_eq_one hu;
      have h_order_div : orderOf u ∣ Fintype.card K - 1 := by
        rw [ orderOf_dvd_iff_pow_eq_one ] at *;
        simp +decide [ ← Units.val_inj, FiniteField.pow_card_sub_one_eq_one ];
      have := Nat.dvd_gcd h_order_div h_order; aesop;
    have h_unit_group : Function.Injective (fun u : Kˣ => u ^ a) := by
      intro u v huv; specialize h_unit_group ( u * v⁻¹ ) ; simp_all +decide [ mul_pow ] ;
      simpa using eq_inv_of_mul_eq_one_left h_unit_group;
    exact ⟨ h_unit_group, Finite.injective_iff_surjective.mp h_unit_group ⟩;
  refine' ⟨ fun x y hxy => _, fun x => _ ⟩;
  · by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide;
    · rw [ zero_pow ha.ne', eq_comm ] at hxy ; aesop;
    · cases a <;> simp_all +decide;
    · obtain ⟨ u, hu ⟩ := h_unit_group.1 ( show ( Units.mk0 x hx ) ^ a = ( Units.mk0 y hy ) ^ a from by simpa [ Units.ext_iff ] using hxy ) ; aesop;
  · by_cases hx : x = 0;
    · exact ⟨ 0, by simp +decide [ hx, ha.ne' ] ⟩;
    · obtain ⟨ y, hy ⟩ := h_unit_group.2 ( Units.mk0 x hx ) ; use y; simp_all +decide [ Units.ext_iff ] ;)

@[simp] theorem powerPerm_apply (a : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime (Fintype.card K - 1) a) (x : K) :
    powerPerm K a ha hcop x = x ^ a := rfl

end PowerPerm

section Anemoi
variable {K : Type*} [Field K] [Fintype K]

/-- A concrete **Anemoi-style Flystel** over a finite field: the open Flystel
built from the power-map permutation `x ↦ x^a` and two quadratic coordinate
functions `Q R : K → K`. -/
noncomputable def anemoiFlystel (a : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime (Fintype.card K - 1) a) (Q R : K → K) : Equiv.Perm (K × K) :=
  flystelField (powerPerm K a ha hcop) Q R

/-- The open Anemoi Flystel is CCZ-equivalent to its closed (verification) form. -/
theorem cczEquiv_anemoiFlystel_symm (a : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime (Fintype.card K - 1) a) (Q R : K → K) :
    CCZEquiv (⇑(anemoiFlystel a ha hcop Q R)) (⇑(anemoiFlystel a ha hcop Q R).symm) :=
  cczEquiv_flystelField_symm _ _ _

/-- The open and closed Anemoi Flystels share their differential uniformity. -/
theorem differentialUniformity_anemoiFlystel_symm (a : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime (Fintype.card K - 1) a) (Q R : K → K) :
    differentialUniformity (⇑(anemoiFlystel a ha hcop Q R).symm)
      = differentialUniformity (⇑(anemoiFlystel a ha hcop Q R)) :=
  differentialUniformity_flystelField_symm _ _ _

end Anemoi

end APN