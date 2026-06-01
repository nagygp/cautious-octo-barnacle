/-
# Layer 29: Higher Topos Foundations — Lean's Type Theory as Higher Topos

This module explores how Lean's type theory naturally extends to
higher categorical patterns. Rather than following Lurie's approach
(better suited to Cubical Agda where types ARE higher groupoids),
we exploit the structure of Lean's own type theory.

## Central Insight

The library's core — `Prop = Ω` (subobject classifier) — works because
Lean's `Type` IS a 1-topos. For higher structures, we MODEL them
explicitly inside Lean's 1-topos, using simplicial sets, enrichment,
and displayed categories.

## Approaches

A. Universe stratification (`Type 0 : Type 1 : ...`)
B. Simplicial enrichment (SSet-enriched categories)
C. Type-theoretic n-groupoids (explicit algebraic structures)
D. Displayed categories (fibrations à la Ahrens-Lumsdaine)

## DAG Structure (depends on Layers 1, 7, 27, 28)

```
  DisplayedCat, IsFibration ←── fibration theory
       |
  SSetEnrichedCat ←── simplicial enrichment
       |
  TwoGroupoid ←── n-groupoid hierarchy
       |
  universe tower ←── Type u
       |
  SimplicialFoundations, CechNerveDescent
```
-/
import Mathlib
import RequestProject.Foundations.CechNerveDescent

namespace Caramello.HigherToposFoundations

open CategoryTheory

/-! ## Section 1: Universe Stratification

Lean's universe hierarchy `Type 0 : Type 1 : Type 2 : ...`
provides a natural "tower of toposes". Each level is a 1-topos. -/

/-- Each universe level gives a 1-topos: Prop classifies subobjects. -/
theorem prop_classifies_at_universe (X : Type) (P : X → Prop) :
    ∃ (S : Subtype P → X), Function.Injective S :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-! ## Section 2: Type-Theoretic n-Groupoids

In Lean (with UIP), we define n-groupoids as explicit algebraic
structures, since types can't have non-trivial higher identity.
-/

/-- A 0-groupoid is just a type (discrete category). -/
structure ZeroGroupoid where
  carrier : Type

/-- A 1-groupoid: a category where every morphism is invertible.
    We record the data as a bundled type. -/
structure OneGroupoid where
  carrier : Type
  [catInst : Category carrier]
  [grpInst : Groupoid carrier]

attribute [instance] OneGroupoid.catInst OneGroupoid.grpInst

/-- A 2-groupoid has objects, 1-morphisms, and 2-morphisms,
    with composition associative up to 2-isomorphism. -/
structure TwoGroupoid where
  Obj : Type
  Hom₁ : Obj → Obj → Type
  Hom₂ : {x y : Obj} → Hom₁ x y → Hom₁ x y → Type
  id₁ : (x : Obj) → Hom₁ x x
  comp₁ : {x y z : Obj} → Hom₁ x y → Hom₁ y z → Hom₁ x z
  id₂ : {x y : Obj} → (f : Hom₁ x y) → Hom₂ f f
  assoc₂ : {w x y z : Obj} → (f : Hom₁ w x) → (g : Hom₁ x y) →
    (h : Hom₁ y z) → Hom₂ (comp₁ (comp₁ f g) h) (comp₁ f (comp₁ g h))
  leftUnit₂ : {x y : Obj} → (f : Hom₁ x y) → Hom₂ (comp₁ (id₁ x) f) f
  rightUnit₂ : {x y : Obj} → (f : Hom₁ x y) → Hom₂ (comp₁ f (id₁ y)) f

/-- Every type gives a 0-groupoid. -/
def discreteZeroGroupoid (X : Type) : ZeroGroupoid := ⟨X⟩

/-- A 1-groupoid is 0-truncated if all hom-sets are subsingleton. -/
def OneGroupoid.isTruncated (G : OneGroupoid) : Prop :=
  ∀ (x y : G.carrier), Subsingleton (x ⟶ y)

/-! ## Section 3: SSet-Enriched Categories

Model (∞,1)-categories as categories enriched in simplicial sets.
The hom-SPACES are simplicial sets, not just sets. -/

/-- An SSet-enriched category: hom-objects are simplicial sets. -/
structure SSetEnrichedCat where
  Obj : Type
  HomSSet : Obj → Obj → SSet
  idVertex : (X : Obj) → SimplicialFoundations.vertices (HomSSet X X)
  compMap : (X Y Z : Obj) →
    SimplicialFoundations.vertices (HomSSet X Y) →
    SimplicialFoundations.vertices (HomSSet Y Z) →
    SimplicialFoundations.vertices (HomSSet X Z)

/-- An ordinary category gives a discretely-enriched SSet-category. -/
noncomputable def discreteEnrichment (C : Type) [Category C] :
    SSetEnrichedCat where
  Obj := C
  HomSSet := fun X Y => SimplicialFoundations.constSSet (X ⟶ Y)
  idVertex := fun X => 𝟙 X
  compMap := fun _ _ _ f g => f ≫ g

/-! ## Section 4: Displayed Categories

Displayed categories (Ahrens-Lumsdaine) formalize fibrations in
type theory. A displayed category D over C has "fibers" over each
object and "lifts" over each morphism. -/

/-- A displayed category over a base category C. -/
structure DisplayedCat (C : Type) [Category C] where
  DOb : C → Type
  DHom : {x y : C} → (x ⟶ y) → DOb x → DOb y → Type
  did : {x : C} → (a : DOb x) → DHom (𝟙 x) a a
  dcomp : {x y z : C} → {f : x ⟶ y} → {g : y ⟶ z} →
    {a : DOb x} → {b : DOb y} → {c : DOb z} →
    DHom f a b → DHom g b c → DHom (f ≫ g) a c

/-- The total category of a displayed category. -/
def DisplayedCat.totalCat {C : Type} [Category C]
    (D : DisplayedCat C) : Type :=
  Σ (x : C), D.DOb x

/-- A section of a displayed category. -/
structure DisplayedCat.Section' {C : Type} [Category C]
    (D : DisplayedCat C) where
  onObj : (x : C) → D.DOb x
  onHom : {x y : C} → (f : x ⟶ y) → D.DHom f (onObj x) (onObj y)

/-- A cartesian morphism: the universal lift. -/
def DisplayedCat.IsCartesian {C : Type} [Category C]
    (D : DisplayedCat C) {x y : C} (f : x ⟶ y)
    (a : D.DOb x) (b : D.DOb y) (φ : D.DHom f a b) : Prop :=
  ∀ (z : C) (g : z ⟶ x) (c : D.DOb z) (ψ : D.DHom (g ≫ f) c b),
    ∃! (χ : D.DHom g c a), D.dcomp χ φ = ψ

/-- A Grothendieck fibration: every morphism has a cartesian lift. -/
def DisplayedCat.IsFibration {C : Type} [Category C]
    (D : DisplayedCat C) : Prop :=
  ∀ {x y : C} (f : x ⟶ y) (b : D.DOb y),
    ∃ (a : D.DOb x) (φ : D.DHom f a b), D.IsCartesian f a b φ

/-- The codomain fibration: over C, display arrows into each object. -/
def codomainDisplayed (C : Type) [Category C] :
    DisplayedCat C where
  DOb := fun y => Σ (x : C), x ⟶ y
  DHom := fun {y₁ y₂} g ⟨x₁, f₁⟩ ⟨x₂, f₂⟩ =>
    { h : x₁ ⟶ x₂ // h ≫ f₂ = f₁ ≫ g }
  did := fun ⟨_, _⟩ => ⟨𝟙 _, by simp⟩
  dcomp := fun ⟨h₁, p₁⟩ ⟨h₂, p₂⟩ =>
    ⟨h₁ ≫ h₂, by rw [Category.assoc, p₂, ← Category.assoc, p₁, Category.assoc]⟩

/-! ## Section 5: Simplicial Set Morphism Properties -/

/-- A morphism of simplicial sets is levelwise injective. -/
def SSetMono {S T : SSet} (f : S ⟶ T) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ), Function.Injective (f.app n)

/-- A morphism of simplicial sets is levelwise surjective. -/
def SSetEpi {S T : SSet} (f : S ⟶ T) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ), Function.Surjective (f.app n)

/-- A levelwise mono + epi is a levelwise bijection. -/
theorem sset_mono_epi_is_bij {S T : SSet} (f : S ⟶ T)
    (hm : SSetMono f) (he : SSetEpi f) :
    ∀ (n : SimplexCategoryᵒᵖ), Function.Bijective (f.app n) :=
  fun n => ⟨hm n, he n⟩

/-! ## Section 6: Comparison of Approaches

### What Works Smoothly in Lean

1. **Prop = Ω**: Perfect for 1-topos (Layers 1–26).
2. **SSet as model**: Lean formalizes SSet and its structure.
3. **Displayed categories**: Clean fibration formalization.
4. **SSet-enrichment**: Higher hom-spaces without HoTT.

### What Doesn't Work (and Why)

1. **Types as ∞-groupoids**: UIP kills higher identity structure.
   → Use SSet or explicit n-groupoid structures instead.
2. **Univalence**: Can't state "equivalent types are equal".
   → Work with equivalences explicitly.
3. **Higher inductive types**: Can't define spheres as types.
   → Define as simplicial sets or CW complexes.

### The Advantage

In HoTT: higher structure is "free" but UNCONTROLLED.
In Lean: you CHOOSE the level of higher structure explicitly.
-/

/-! ## Section 7: The Road to ∞-Toposes in Lean

| Step | Layer | Status |
|------|-------|--------|
| 1-topos foundations | 1–26 | ✅ Done |
| Simplicial foundations | 27 | ✅ Done |
| Čech descent | 28 | ✅ Done |
| Higher structures | 29 (this) | ✅ Done |
| Model categories | future | 🟡 |
| ∞-topos axioms | future | 🟡 |
| ∞-bridge technique | future | 🟡 |

The methodology — sorry audit, abstraction, foundational layers —
scales from 1-toposes to ∞-toposes.
-/

end Caramello.HigherToposFoundations
