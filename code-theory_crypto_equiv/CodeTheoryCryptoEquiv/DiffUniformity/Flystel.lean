import Mathlib
import CodeTheoryCryptoEquiv.DiffUniformity.CCZEquivalence

/-!
# Inverse-permutation CCZ-equivalence and the open Flystel (Anemoi)

This module advances the CCZ-equivalence (Carlet–Charpin–Zinoviev) track of
`CODING_THEORY_DIRECTIONS.md`: the *remaining CCZ direction is the concrete
Flystel / Anemoi instantiations*.  It builds directly on the graph-level
CCZ-invariance theorem `APN.differentialUniformity_ccz` of
`CodeTheoryCryptoEquiv/DiffUniformity/CCZEquivalence.lean`.

The first headline is the **inverse-permutation** instance of CCZ-equivalence: a
permutation `e` and its compositional inverse `e⁻¹` are CCZ-equivalent, because
the graph of `e⁻¹` is the image of the graph of `e` under the coordinate-swap
automorphism `(x, y) ↦ (y, x)` of `V × V`.  Consequently `e` and `e⁻¹` have the
same differential uniformity, and APN- / PN-ness transfer between them
(`differentialUniformity_inverse`, `IsAPN.inverse`, `IsPN.inverse`).

This is the structural reason the Anemoi *open* and *closed* Flystels share their
differential properties: the closed Flystel is, up to coordinate ordering, the
inverse relation of the open Flystel.

The second part records the **open Flystel** itself (Bouvier–Briaud–Chaidos–
Grassi–Manterola–Merino–Roy–Schofnegger–Salen, *Anemoi*, 2023) as a concrete
permutation of `V × V`.  It is the alternating composition of three *shear*
maps built from a permutation `e : V ≃ V` (the power map `x ↦ x^α` in the field
instance) and two arbitrary coordinate functions `Q R : V → V` (the quadratics):

* `shearFst g : (x, y) ↦ (x + g y, y)`,
* `shearSnd g : (x, y) ↦ (x, y + g x)`,

`openFlystel e Q R := shearFst (-Q) ≫ shearSnd (-e⁻¹) ≫ shearFst R`.

Because each shear is a bijection, `openFlystel` is automatically a permutation,
and the inverse-CCZ headline applies to it: `differentialUniformity_openFlystel_symm`.

## Main results

* `graph_inverse_eq` — `graph e⁻¹ = prodComm '' graph e` (the swap relation).
* `differentialUniformity_inverse` — `δ(e⁻¹) = δ(e)` for a permutation `e`.
* `IsAPN.inverse`, `IsPN.inverse` — APN / PN transfer to the inverse permutation.
* `openFlystel` — the open Flystel permutation of `V × V`.
* `differentialUniformity_openFlystel_symm` — the open Flystel and its inverse
  (the closed Flystel, up to coordinate order) have equal differential uniformity.
-/

open Finset

namespace APN

/-! ### Coordinate shears of `V × V` -/

section Shear
variable {V : Type*} [AddCommGroup V]

/-- The first-coordinate **shear** `(x, y) ↦ (x + g y, y)`, a permutation of
`V × V` with inverse `(x, y) ↦ (x - g y, y)`. -/
def shearFst (g : V → V) : Equiv.Perm (V × V) where
  toFun p := (p.1 + g p.2, p.2)
  invFun p := (p.1 - g p.2, p.2)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

/-- The second-coordinate **shear** `(x, y) ↦ (x, y + g x)`, a permutation of
`V × V` with inverse `(x, y) ↦ (x, y - g x)`. -/
def shearSnd (g : V → V) : Equiv.Perm (V × V) where
  toFun p := (p.1, p.2 + g p.1)
  invFun p := (p.1, p.2 - g p.1)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

end Shear

/-! ### Inverse-permutation CCZ-equivalence -/

section Inverse
variable {V : Type*} [AddCommGroup V]

/-
The graph of the inverse permutation is the coordinate-swap image of the
graph of `e`: `graph e.symm = (fun z => AddEquiv.prodComm z) '' graph e`.
-/
theorem graph_inverse_eq (e : Equiv.Perm V) :
    graph (⇑e.symm) = (fun z : V × V => AddEquiv.prodComm z + 0) '' graph (⇑e) := by
  simp +decide [ graph, Set.ext_iff ];
  exact fun a b => ⟨ fun h => by rw [ h, Equiv.apply_symm_apply ], fun h => by rw [ ← h, Equiv.symm_apply_apply ] ⟩

variable [Fintype V]

/-
**Inverse-permutation CCZ-equivalence.** A permutation `e` and its
compositional inverse `e⁻¹` have the same differential uniformity, because their
graphs are related by the coordinate-swap automorphism of `V × V`.
-/
theorem differentialUniformity_inverse (e : Equiv.Perm V) :
    differentialUniformity (⇑e.symm) = differentialUniformity (⇑e) := by
  exact differentialUniformity_ccz _ _ _ _ ( graph_inverse_eq e )

/-- APN-ness transfers to the inverse permutation. -/
theorem IsAPN.inverse {e : Equiv.Perm V} (he : IsAPN (⇑e)) : IsAPN (⇑e.symm) := by
  unfold IsAPN at *; rw [differentialUniformity_inverse]; exact he

/-- PN-ness transfers to the inverse permutation. -/
theorem IsPN.inverse {e : Equiv.Perm V} (he : IsPN (⇑e)) : IsPN (⇑e.symm) := by
  unfold IsPN at *; rw [differentialUniformity_inverse]; exact he

end Inverse

/-! ### The open Flystel (Anemoi) -/

section Flystel
variable {V : Type*} [AddCommGroup V]

/-- The **open Flystel** permutation of `V × V` (Anemoi), the alternating
composition of three shears built from a permutation `e : V ≃ V` and two
coordinate functions `Q R : V → V`:
`shearFst (-Q) ≫ shearSnd (-e⁻¹) ≫ shearFst R`. -/
def openFlystel (e : Equiv.Perm V) (Q R : V → V) : Equiv.Perm (V × V) :=
  (shearFst (fun y => -Q y)).trans
    ((shearSnd (fun x => -e.symm x)).trans (shearFst R))

variable [Fintype V]

/-- **The open and closed Flystels share their differential uniformity.** The
open Flystel is a permutation, so by `differentialUniformity_inverse` it has the
same differential uniformity as its inverse — the closed Flystel up to
coordinate order. -/
theorem differentialUniformity_openFlystel_symm (e : Equiv.Perm V) (Q R : V → V) :
    differentialUniformity (⇑(openFlystel e Q R).symm)
      = differentialUniformity (⇑(openFlystel e Q R)) :=
  differentialUniformity_inverse (openFlystel e Q R)

end Flystel

end APN