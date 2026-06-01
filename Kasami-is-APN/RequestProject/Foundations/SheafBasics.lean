/-
# Layer 4: Sheaves on Sites — Atomic Facts

Sheaves are presheaves satisfying a gluing condition with respect
to a Grothendieck topology. This file establishes atomic facts about
sheaves and sheafification.

## DAG Structure (depends on Layers 2, 3)

```
    sheafification_adj
           |
    sheaf_of_finer  ←── presheaf_isSheaf_bot
           |
    sheafToPresheaf_faithful
```
-/
import Mathlib

namespace Caramello.SheafBasics

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [SmallCategory C]

/-! ## Atomic Sheaf Facts -/

/-- Every presheaf is a sheaf for the trivial (bottom) topology. -/
lemma presheaf_isSheaf_bot (F : Cᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (⊥ : GrothendieckTopology C) F :=
  Presheaf.isSheaf_bot F

/-! ## Sheaf Category Structure -/

/-- The forgetful functor from sheaves to presheaves is faithful. -/
instance sheafToPresheaf_faithful (J : GrothendieckTopology C) :
    (sheafToPresheaf J (Type u)).Faithful :=
  inferInstance

/-- The forgetful functor from sheaves to presheaves is full. -/
instance sheafToPresheaf_full (J : GrothendieckTopology C) :
    (sheafToPresheaf J (Type u)).Full :=
  inferInstance

/-! ## Sheafification -/

/-- Sheafification exists and is left adjoint to the inclusion.
    This is the fundamental adjunction aSh ⊣ ι : Sh(C,J) → PSh(C). -/
noncomputable def sheafification_adj (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] :
    presheafToSheaf J (Type u) ⊣ sheafToPresheaf J (Type u) :=
  sheafificationAdjunction J (Type u)

/-! ## Comparison of Topologies -/

/-- A finer topology has fewer sheaves: if J ≤ K, then
    every K-sheaf is a J-sheaf. -/
lemma sheaf_of_finer {J K : GrothendieckTopology C} (hJK : J ≤ K)
    (F : Cᵒᵖ ⥤ Type u) (hF : Presheaf.IsSheaf K F) :
    Presheaf.IsSheaf J F := by
  intro E X S hS
  exact hF E S (hJK X hS)

end Caramello.SheafBasics
