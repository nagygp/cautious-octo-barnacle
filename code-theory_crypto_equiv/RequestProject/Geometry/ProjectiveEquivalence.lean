import Mathlib
import RequestProject.Geometry.Arcs

/-!
# Geometry track: projective invariance of arcs

An **arc** in `PG(k-1, q)` is a family of points in general position, encoded
(`RequestProject/Geometry/Arcs.lean`) as a generator matrix
`G : Matrix (Fin k) ι F` every `k` of whose columns are linearly independent
(`IsArc G`).  The columns are homogeneous coordinates of projective points, so
the natural symmetry group is `PGL(k, q)`, acting by an invertible linear change
of coordinates `v ↦ M v` (`M ∈ GL(k, q)`).

This module records that **arcs are a projective invariant**: applying an
invertible matrix `M` on the left of `G` (a projective coordinate change) sends
arcs to arcs, and conversely.  Column `i` of `M * G` is `M *ᵥ (column i of G)`,
and an invertible linear map preserves linear independence of every subfamily of
columns, so `IsArc (M * G) ↔ IsArc G`.  Together with `isMDS_genCode_iff_isArc`
this says the MDS property is invariant under monomial/projective equivalence of
generator matrices, the geometric counterpart of code equivalence.

## Main results

* `arcColumn_mulLeft` — `column i of (M * G) = M *ᵥ (column i of G)`.
* `IsArc.mulLeft` — an invertible left factor preserves arcs.
* `isArc_mulLeft_iff` — arcs are invariant under invertible projective coordinate
  changes.
-/

namespace CodingTheory

open scoped Classical
open Matrix

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] {k : ℕ}

/-
Column `i` of `M * G` is the image of column `i` of `G` under `v ↦ M *ᵥ v`.
-/
theorem arcColumn_mulLeft (M : Matrix (Fin k) (Fin k) F) (G : Matrix (Fin k) ι F)
    (i : ι) :
    arcColumn (M * G) i = M *ᵥ arcColumn G i := by
  funext r
  simp [arcColumn, Matrix.mulVec, Matrix.mul_apply, dotProduct]

/-
**An invertible left factor preserves arcs.** If `M` is invertible and `G` is
an arc, then `M * G` is an arc.
-/
theorem IsArc.mulLeft {G : Matrix (Fin k) ι F} (M : Matrix (Fin k) (Fin k) F)
    (hM : IsUnit M.det) (hG : IsArc G) : IsArc (M * G) := by
  intro S hS;
  have h_inj : Function.Injective (Matrix.mulVecLin M) := by
    intro x y hxy;
    apply_fun M⁻¹.mulVecLin at hxy ; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit ];
  convert ( hG S hS |> fun h => h.map' _ ( LinearMap.ker_eq_bot.mpr h_inj ) ) using 1

/-
**Projective invariance of arcs.** For an invertible `M`, `M * G` is an arc
iff `G` is an arc: arcs (hence MDS codes) are invariant under invertible
projective coordinate changes.
-/
theorem isArc_mulLeft_iff {G : Matrix (Fin k) ι F} (M : Matrix (Fin k) (Fin k) F)
    (hM : IsUnit M.det) : IsArc (M * G) ↔ IsArc G := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · convert IsArc.mulLeft ( M⁻¹ ) _ h using 1;
    · rw [ ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul ];
    · simp_all +decide [ Matrix.det_nonsing_inv ];
  · exact IsArc.mulLeft M hM h

end CodingTheory