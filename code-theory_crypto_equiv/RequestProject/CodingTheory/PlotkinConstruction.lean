import Mathlib
import RequestProject.CodingTheory.LinearCode

/-!
# The `(u | u+v)` (Plotkin) construction and its minimum distance

This module is the coding-theory (Track 3) next step: the classical **`(u | u+v)`
construction** (MacWilliams–Sloane, Ch. 2, §9; the recursion behind the
Reed–Muller codes, roadmap items 12/14 of `CODING_THEORY_DIRECTIONS.md`).

Given two linear codes `C₁, C₂ ⊆ Fⁿ`, the `(u | u+v)` code in `F²ⁿ` is

```
{ (u, u + v) : u ∈ C₁, v ∈ C₂ } ⊆ (ι ⊕ ι → F).
```

Its minimum distance is `min (2·d(C₁), d(C₂))`. This is the construction used to
build the Reed–Muller family `RM(r, m)` from `RM(r, m−1)` and `RM(r−1, m−1)`,
linking the coding-theory layer to the Boolean-function / Walsh machinery already
in the project.

## Main results

* `uuvCode` — the `(u | u+v)` code as a `Submodule F (ι ⊕ ι → F)`.
* `mem_uuvCode` — its membership characterization.
* `hammingNorm_uuv` — the weight of `(u | u+v)` is `wt u + wt (u+v)`.
* `minWeight_uuvCode` — `minWeight (uuvCode C₁ C₂) = min (2·minWeight C₁) (minWeight C₂)`.
-/

open Finset BigOperators
open scoped Classical

namespace CodingTheory
namespace Plotkin

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- Hamming weight splits as a sum over the two halves of a sum-indexed word. -/
theorem hammingNorm_sum_index (w : ι ⊕ ι → F) :
    hammingNorm w = hammingNorm (w ∘ Sum.inl) + hammingNorm (w ∘ Sum.inr) := by
  classical
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_sum_type]
  rfl

/-- The `(u | u+v)` word in `ι ⊕ ι → F`. -/
def uuv (u v : ι → F) : ι ⊕ ι → F := Sum.elim u (u + v)

/-- The `(u | u+v)` construction as a linear map
`(ι → F) × (ι → F) →ₗ[F] (ι ⊕ ι → F)`. -/
def uuvMap : (ι → F) × (ι → F) →ₗ[F] (ι ⊕ ι → F) where
  toFun p := uuv p.1 p.2
  map_add' p q := by
    ext (i | i)
    · simp [uuv, Sum.elim]
    · simp [uuv, Sum.elim]; ring
  map_smul' c p := by
    ext (i | i) <;> simp [uuv, Sum.elim, mul_add]

/-- The **`(u | u+v)` code** of two linear codes `C₁, C₂ ⊆ Fⁿ`. -/
def uuvCode (C₁ C₂ : Submodule F (ι → F)) : Submodule F (ι ⊕ ι → F) :=
  (C₁.prod C₂).map uuvMap

omit [Fintype ι] in
/-- Membership in the `(u | u+v)` code. -/
theorem mem_uuvCode (C₁ C₂ : Submodule F (ι → F)) (w : ι ⊕ ι → F) :
    w ∈ uuvCode C₁ C₂ ↔ ∃ u ∈ C₁, ∃ v ∈ C₂, w = uuv u v := by
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩

/-- The Hamming weight of `(u | u+v)` is `wt u + wt (u+v)`. -/
theorem hammingNorm_uuv (u v : ι → F) :
    hammingNorm (uuv u v) = hammingNorm u + hammingNorm (u + v) := by
  rw [hammingNorm_sum_index]
  rfl

/-
**Minimum distance of the `(u | u+v)` construction.** For nonzero linear
codes `C₁, C₂ ⊆ Fⁿ`, the `(u | u+v)` code has minimum weight (= minimum distance)
`min (2·minWeight C₁) (minWeight C₂)`.
-/
theorem minWeight_uuvCode (C₁ C₂ : Submodule F (ι → F)) (h₁ : C₁ ≠ ⊥) (h₂ : C₂ ≠ ⊥) :
    minWeight (uuvCode C₁ C₂) = min (2 * minWeight C₁) (minWeight C₂) := by
  refine' le_antisymm _ _;
  · refine' le_min _ _;
    · obtain ⟨ u₀, hu₀, hu₀_ne, hu₀_min ⟩ := exists_eq_minWeight h₁;
      refine' le_trans ( minWeight_le _ _ ) _;
      exact uuv u₀ 0;
      · exact mem_uuvCode _ _ _ |>.2 ⟨ u₀, hu₀, 0, C₂.zero_mem, rfl ⟩;
      · exact fun h => hu₀_ne <| funext fun i => by simpa [ uuv ] using congr_fun h ( Sum.inl i ) ;
      · rw [ ← hu₀_min, hammingNorm_uuv ] ; simp +decide [ two_mul ];
    · obtain ⟨ v₀, hv₀ ⟩ := exists_eq_minWeight h₂;
      refine' le_trans ( minWeight_le _ _ ) _;
      exact uuv 0 v₀;
      · exact mem_uuvCode _ _ _ |>.2 ⟨ 0, C₁.zero_mem, v₀, hv₀.1, rfl ⟩;
      · exact fun h => hv₀.2.1 ( by ext i; simpa [ uuv, Sum.elim ] using congr_fun h ( Sum.inr i ) );
      · simp +decide [ ← hv₀.2.2, hammingNorm_uuv ];
  · -- By definition of minWeight, we need to show that for any nonzero codeword w in uuvCode C₁ C₂, its weight is at least min(2 * minWeight C₁, minWeight C₂).
    have h_min_weight : ∀ w ∈ uuvCode C₁ C₂, w ≠ 0 → min (2 * minWeight C₁) (minWeight C₂) ≤ hammingNorm w := by
      intro w hw hw0
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_uuvCode C₁ C₂ w |>.1 hw
      by_cases hv0 : v = 0;
      · simp_all +decide [ uuv ];
        exact Or.inl ( by rw [ hammingNorm_sum_index ] ; simpa [ two_mul ] using add_le_add ( minWeight_le hu ( show u ≠ 0 from fun h => hw0 <| by simp +decide [ h ] ) ) ( minWeight_le hu ( show u ≠ 0 from fun h => hw0 <| by simp +decide [ h ] ) ) );
      · have h_min_weight : hammingNorm v ≤ hammingNorm u + hammingNorm (u + v) := by
          unfold hammingNorm;
          rw [ ← Finset.card_union_add_card_inter ];
          exact le_add_right ( Finset.card_le_card fun i hi => by by_cases hi' : u i = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ] );
        exact le_trans ( min_le_right _ _ ) ( by rw [ hammingNorm_uuv ] ; exact le_trans ( minWeight_le hv hv0 ) h_min_weight );
    obtain ⟨ w, hw ⟩ := exists_eq_minWeight ( show uuvCode C₁ C₂ ≠ ⊥ from by
                                                simp_all +decide [ Submodule.eq_bot_iff ];
                                                obtain ⟨ x, hx₁, hx₂ ⟩ := h₁; use uuv x 0; simp_all +decide [ uuvCode ] ;
                                                exact ⟨ ⟨ x, 0, ⟨ hx₁, C₂.zero_mem ⟩, rfl ⟩, fun h => hx₂ <| funext fun i => by simpa [ uuv ] using congr_fun h ( Sum.inl i ) ⟩ );
    exact hw.2.2 ▸ h_min_weight w hw.1 hw.2.1

end Plotkin
end CodingTheory