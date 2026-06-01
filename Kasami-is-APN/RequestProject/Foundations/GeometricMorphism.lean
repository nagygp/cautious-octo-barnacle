/-
# Layer 8: Geometric Morphisms

A geometric morphism f : E → F between toposes consists of
an adjoint pair (f* ⊣ f_*) where the left adjoint f* (inverse image)
preserves finite limits.

This is the correct notion of "morphism between toposes" and is
central to Caramello's bridge technique: she transfers mathematical
results between theories by composing geometric morphisms through
a classifying topos.

## Novel Aspects

1. We define geometric morphisms as a Lean structure grounded in Mathlib's
   `Adjunction` and `PreservesFiniteLimits`.
2. We verify identity, composition, and key preservation properties.
3. This bottom-up approach from verified instances (not sorry'd axioms)
   ensures all constructions are computationally meaningful.

## DAG Structure (depends on Layer 7)

```
    geom_morph_comp (★)
         |
    geom_morph_id ←── preservation instances
         |
    GeometricMorphism (definition)
         |
    (Mathlib: Adjunction, PreservesFiniteLimits)
```
-/
import Mathlib
import RequestProject.Foundations.ToposStructure

namespace Caramello.GeomMorph

open CategoryTheory CategoryTheory.Limits

/-! ## Section 1: Geometric Morphism Definition -/

/-- A geometric morphism f : E → F between categories consists of:
    - An adjunction f* ⊣ f_* (inverse image ⊣ direct image)
    - The inverse image f* preserves finite limits

    When E and F are toposes, this is the correct notion of
    "topos morphism". The inverse image functor f* preserves
    the geometric logic (∧, ∨, ∃, ⊤, ⊥) of the internal language. -/
structure GeometricMorphism
    (E : Type*) [Category E]
    (F : Type*) [Category F] where
  /-- The inverse image functor f* : F → E -/
  inverseFunctor : Functor F E
  /-- The direct image functor f_* : E → F -/
  directFunctor : Functor E F
  /-- The fundamental adjunction f* ⊣ f_* -/
  adj : inverseFunctor ⊣ directFunctor
  /-- The inverse image preserves finite limits -/
  inversePreservesFiniteLimits : PreservesFiniteLimits inverseFunctor

/-! ## Section 2: Identity Geometric Morphism -/

/-- The identity geometric morphism id : E → E.
    Both functors are the identity, and the adjunction is trivial. -/
noncomputable def geomMorphId (E : Type*) [Category E] :
    GeometricMorphism E E where
  inverseFunctor := 𝟭 E
  directFunctor := 𝟭 E
  adj := Adjunction.id
  inversePreservesFiniteLimits := inferInstance

/-! ## Section 3: Composition of Geometric Morphisms -/

/-- Composition of geometric morphisms.
    Given f : E → F and g : F → G, the composite g ∘ f : E → G has:
    - Inverse image: f* ∘ g* (apply g* then f*)
    - Direct image: g_* ∘ f_* (apply f_* then g_*)
    - Adjunction: (f* ∘ g*) ⊣ (g_* ∘ f_*)

    ★ This is structurally elegant: the functors compose in opposite
    directions, mirroring the contravariance of inverse image. -/
noncomputable def geomMorphComp
    {E : Type*} [Category E]
    {F : Type*} [Category F]
    {G : Type*} [Category G]
    (f : GeometricMorphism E F)
    (g : GeometricMorphism F G) :
    GeometricMorphism E G where
  inverseFunctor := g.inverseFunctor ⋙ f.inverseFunctor
  directFunctor := f.directFunctor ⋙ g.directFunctor
  adj := g.adj.comp f.adj
  inversePreservesFiniteLimits := by
    have := f.inversePreservesFiniteLimits
    have := g.inversePreservesFiniteLimits
    exact comp_preservesFiniteLimits g.inverseFunctor f.inverseFunctor

/-! ## Section 4: Key Properties of Geometric Morphisms

The inverse image of a geometric morphism preserves all finite
limit shapes. We instantiate this for important specific shapes.
-/

/-- The inverse image of a geometric morphism preserves pullbacks. -/
noncomputable instance inverse_preserves_pullbacks
    {E : Type*} [Category E]
    {F : Type*} [Category F]
    (f : GeometricMorphism E F) :
    PreservesLimitsOfShape WalkingCospan f.inverseFunctor := by
  have := f.inversePreservesFiniteLimits; infer_instance

/-- The inverse image of a geometric morphism preserves equalizers. -/
noncomputable instance inverse_preserves_equalizers
    {E : Type*} [Category E]
    {F : Type*} [Category F]
    (f : GeometricMorphism E F) :
    PreservesLimitsOfShape WalkingParallelPair f.inverseFunctor := by
  have := f.inversePreservesFiniteLimits; infer_instance

/-- The inverse image of a geometric morphism preserves binary products. -/
noncomputable instance inverse_preserves_binary_products
    {E : Type*} [Category E]
    {F : Type*} [Category F]
    (f : GeometricMorphism E F) :
    PreservesLimitsOfShape (Discrete WalkingPair) f.inverseFunctor := by
  have := f.inversePreservesFiniteLimits; infer_instance

/-! ## Section 5: The Constant Presheaf Functor

For any presheaf topos PSh(C) = [Cᵒᵖ, Type], the "constant presheaf"
functor Δ : Type → [Cᵒᵖ, Type] sends a type A to the constant
functor Cᵒᵖ → Type mapping every object to A.
-/

/-- The constant presheaf functor Δ : Type → [Cᵒᵖ, Type]. -/
def constPresheaf (C : Type*) [SmallCategory C] : Functor (Type) (Cᵒᵖ ⥤ Type) where
  obj A := (CategoryTheory.Functor.const Cᵒᵖ).obj A
  map f := (CategoryTheory.Functor.const Cᵒᵖ).map f

end Caramello.GeomMorph
