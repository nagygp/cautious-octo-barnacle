import Mathlib
import RequestProject.DiffUniformity.DifferentialUniformity

/-!
# The inverse S-box is differentially 4-uniform (Nyberg)

The **inverse map** `x ↦ x⁻¹` of a finite field of characteristic two (with the
convention `0⁻¹ = 0`) is the S-box of the AES and many other ciphers.  Nyberg's
theorem states that it is **differentially `4`-uniform**: every nonzero
derivative fibre has at most `4` points (and exactly `4` when `[F : F₂]` is even,
e.g. AES with `n = 8`).  This module proves the sharp upper bound

  `differentialUniformity (x ↦ x⁻¹) ≤ 4`.

## Proof

Fix `a ≠ 0` and `b`.  A solution `x` of `(x+a)⁻¹ - x⁻¹ = b` either lies in
`{0, a}`, or, multiplying through by `x(x+a) ≠ 0` (in characteristic two), is a
root of the quadratic

  `p(X) = b·X² + (a·b)·X + a`.

Since `a ≠ 0`, `p` has nonzero constant term, hence `p ≠ 0`, so it has at most
`deg p ≤ 2` roots.  Therefore each fibre has at most `2 + 2 = 4` points.

## Main results

* `inverseSbox` — the field inverse S-box `x ↦ x⁻¹`.
* `inverseSbox_diffUnif_le_four` — `differentialUniformity inverseSbox ≤ 4`.
-/

namespace APNLib

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The **inverse S-box** `x ↦ x⁻¹` over a finite field (`0⁻¹ = 0`). -/
def inverseSbox (x : F) : F := x⁻¹

/-
**Nyberg's bound.**  The inverse S-box of a characteristic-two finite field is
differentially `4`-uniform: every nonzero derivative fibre has at most `4`
points.
-/
theorem inverseSbox_diffUnif_le_four :
    differentialUniformity (inverseSbox : F → F) ≤ 4 := by
  refine' diffUnif_le_iff _ _ |>.2 fun a ha b => _;
  -- Let `S := univ.filter (fun x => (x + a)⁻¹ - x⁻¹ = b)` and let
  -- `p : Polynomial F := C b * X ^ 2 + C (a * b) * X + C a`.
  set S := Finset.univ.filter (fun x => (x + a)⁻¹ - x⁻¹ = b)
  set p : Polynomial F := Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C (a * b) * Polynomial.X + Polynomial.C a;
  -- Since `p.coeff 0 = a ≠ 0`, `p ≠ 0`.
  have hp_ne_zero : p ≠ 0 := by
    simp +zetaDelta at *;
    exact ne_of_apply_ne ( fun p => p.coeff 0 ) ( by simp +decide [ ha ] );
  -- Since `p.natDegree ≤ 2`, we have `p.roots.toFinset.card ≤ 2`.
  have hp_roots_card : p.roots.toFinset.card ≤ 2 := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
    simp +zetaDelta at *;
    intro m hm; rcases m with ( _ | _ | _ | m ) <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
  -- Since `S ⊆ {0, a} ∪ p.roots.toFinset`, we have `S.card ≤ ({0, a} : Finset F).card + (p.roots.toFinset).card`.
  have hS_subset : S ⊆ {0, a} ∪ p.roots.toFinset := by
    intro x hx; by_cases hx0 : x = 0 <;> by_cases hxa : x = a <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
    simp +zetaDelta at *;
    grind;
  convert le_trans ( Finset.card_le_card hS_subset ) ( Finset.card_union_le _ _ ) |> le_trans <| add_le_add ( Finset.card_insert_le _ _ ) hp_roots_card using 1

end APNLib