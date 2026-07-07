import RequestProject.DiffUniformity.InverseSbox

/-!
# The inverse S-box is *exactly* differentially 4-uniform for even `n`

`RequestProject/DiffUniformity/InverseSbox.lean` proved Nyberg's upper bound
`differentialUniformity (x ↦ x⁻¹) ≤ 4` for the inverse S-box of a finite field of
characteristic two.  This module proves the matching **lower bound for even
extension degree**: when `#F = 2ⁿ` with `n` even, the inverse S-box attains
differential uniformity exactly `4`.

## The construction

When `n` is even, `3 ∣ 2ⁿ − 1 = |Fˣ|`, so `Fˣ` (cyclic) has an element `g` of
order `3`; equivalently `g ∉ {0, 1}` and `g² + g + 1 = 0` (a primitive cube root
of unity, `F₄ ⊆ F`).  Taking the direction `a = 1` and value `b = 1`, the
four **distinct** points `0, 1, g, g²` all solve

  `(x + 1)⁻¹ − x⁻¹ = 1`

(using `0⁻¹ = 0`, `g⁻¹ = g²`, `g + 1 = g²`, `g² + 1 = g` in characteristic two),
so the derivative fibre in direction `1` has at least `4` points.  Combined with
Nyberg's upper bound this gives differential uniformity exactly `4`.

## Main results

* `exists_primitive_cube_root` — for `#F = 2ⁿ` with `n` even, there is `g` with
  `g ≠ 0`, `g ≠ 1`, `g² + g + 1 = 0`.
* `four_le_fiberCard_inverseSbox` — the derivative fibre of `x ↦ x⁻¹` in direction
  `1` at value `1` has at least `4` points.
* `inverseSbox_diffUnif_ge_four` — `4 ≤ differentialUniformity (x ↦ x⁻¹)`.
* `inverseSbox_diffUnif_eq_four` — **`differentialUniformity (x ↦ x⁻¹) = 4`** for
  even `n` (Nyberg's exact value).
-/

namespace APNLib

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
For `#F = 2ⁿ` with `n` even, the field contains a primitive cube root of
unity: an element `g` with `g ≠ 0`, `g ≠ 1` and `g² + g + 1 = 0`.  (Then
`F₄ ⊆ F`.)
-/
omit [CharP F 2] in
theorem exists_primitive_cube_root {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Even n) :
    ∃ g : F, g ≠ 0 ∧ g ≠ 1 ∧ g ^ 2 + g + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, orderOf u = 3 := by
    apply exists_prime_orderOf_dvd_card 3
    rw [ Fintype.card_units, hcard ];
    obtain ⟨ k, rfl ⟩ := even_iff_two_dvd.mp hn; rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k ) ) 3 ] ; norm_num [ Nat.pow_mul, Nat.pow_mod ] ;
  refine' ⟨ u, _, _, _ ⟩ <;> simp_all +decide [ pow_succ, orderOf_eq_iff ];
  · exact fun h => hu.2 1 ( by decide ) ( by decide ) ( by simp +decide [ h ] );
  · have h_poly : (u : F) ^ 3 = 1 := by
      simpa [ pow_succ, mul_assoc ] using congr_arg ( fun x : Fˣ => ( x : F ) ) hu.1;
    exact mul_left_cancel₀ ( sub_ne_zero_of_ne ( show ( u : F ) ≠ 1 from by simpa using hu.2 1 ( by decide ) ( by decide ) ) ) ( by linear_combination' h_poly )

/-
The derivative fibre of the inverse S-box in direction `1` at value `1` has at
least `4` points: `0, 1, g, g²` for a primitive cube root `g`.
-/
theorem four_le_fiberCard_inverseSbox {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Even n) :
    4 ≤ fiberCard (inverseSbox : F → F) 1 1 := by
  obtain ⟨ g, hg₀, hg₁, hg₂ ⟩ := exists_primitive_cube_root hcard hn;
  refine' le_trans _ ( Finset.card_mono _ );
  rotate_left;
  exact { 0, 1, g, g ^ 2 };
  · simp +decide [ Finset.insert_subset_iff, derivMap, inverseSbox ];
    grind;
  · grind

/-- **Lower bound.** The inverse S-box of `F = GF(2ⁿ)` with `n` even has
differential uniformity at least `4`. -/
theorem inverseSbox_diffUnif_ge_four {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Even n) :
    4 ≤ differentialUniformity (inverseSbox : F → F) :=
  le_trans (four_le_fiberCard_inverseSbox hcard hn)
    (fiberCard_le_diffUnif _ (one_ne_zero) 1)

/-- **Nyberg's exact value.** For `F = GF(2ⁿ)` with `n` even the inverse S-box is
*exactly* differentially `4`-uniform. -/
theorem inverseSbox_diffUnif_eq_four {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Even n) :
    differentialUniformity (inverseSbox : F → F) = 4 :=
  le_antisymm inverseSbox_diffUnif_le_four (inverseSbox_diffUnif_ge_four hcard hn)

end APNLib