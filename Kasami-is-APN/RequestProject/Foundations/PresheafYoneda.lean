/-
# Layer 3: Presheaf Category and Yoneda Embedding

The presheaf category Cᵒᵖ ⥤ Type is the "free cocompletion" of C.
The Yoneda embedding y : C → [Cᵒᵖ, Type] is fully faithful.

## DAG Structure (depends on Layer 0 = Mathlib)

```
    yoneda_preserves_limits
           |
    yoneda_full + yoneda_faithful
           |
    presheaf_has_limits + presheaf_has_colimits
```
-/
import Mathlib

namespace Caramello.PresheafYoneda

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [SmallCategory C]

/-! ## The Presheaf Category -/

/-- The presheaf category has all small limits. -/
lemma presheaf_has_limits : HasLimits (Cᵒᵖ ⥤ Type u) :=
  inferInstance

/-- The presheaf category has all small colimits. -/
lemma presheaf_has_colimits : HasColimits (Cᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ## Yoneda Embedding Atomic Facts -/

/-- The Yoneda embedding is full. -/
lemma yoneda_full : (yoneda (C := C)).Full :=
  inferInstance

/-- The Yoneda embedding is faithful. -/
lemma yoneda_faithful : (yoneda (C := C)).Faithful :=
  inferInstance

/-! ## Yoneda Lemma -/

/-- Yoneda lemma: natural transformations from y(X) to F are in bijection
    with elements of F(X). This is the cornerstone of presheaf theory. -/
noncomputable def yoneda_sections (X : C) (F : Cᵒᵖ ⥤ Type u) :
    (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X) :=
  yonedaEquiv

/-- The Yoneda embedding preserves all limits that exist. -/
noncomputable instance yoneda_preserves_limits :
    PreservesLimits (yoneda (C := C)) :=
  inferInstance

end Caramello.PresheafYoneda
