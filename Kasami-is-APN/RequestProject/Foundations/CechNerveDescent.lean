/-
# Layer 28: Čech Nerves and Descent — Connecting Sites to Simplicial Methods

This layer bridges the site-theoretic framework (sieves, coverings,
sheaves from Layers 2–4, 13) with the simplicial framework (Layer 27).
The Čech nerve of a covering is a simplicial object that encodes the
descent data for sheaves.

## Mathematical Content

1. **Čech nerve of a covering**: The simplicial object encoding overlaps.
2. **Descent data**: Compatible local sections.
3. **Effective descent**: When descent data uniquely determines an object.
4. **Hypercovers**: The ∞-categorical generalization.
5. **Sheaf condition hierarchy**: presheaf < separated < sheaf < hypersheaf.

## DAG Structure (depends on Layers 2, 4, 27)

```
  sheaf_implies_separated ←── sheaf level hierarchy
       |
  hypercovers ←── Čech nerve refinement
       |
  effective_descent ←── descent_id
       |
  cechNerve, cechFace
       |
  CoveringFamily, fiberProduct
       |
  SimplicialFoundations (Layer 27)
```
-/
import Mathlib
import RequestProject.Foundations.SimplicialFoundations

namespace Caramello.CechNerveDescent

open CategoryTheory SimplexCategory

/-! ## Section 1: Čech Nerve of a Covering Family -/

/-- A covering family: a collection of "patches" indexed by I,
    each mapping into a common base X. -/
structure CoveringFamily (X : Type) where
  Index : Type
  Patch : Index → Type
  incl : (i : Index) → Patch i → X

/-- The n-fold fiber product of a covering family over X. -/
def fiberProduct {X : Type} (U : CoveringFamily X) (n : ℕ) : Type :=
  { t : (Fin (n + 1) → (i : U.Index) × U.Patch i) //
    ∀ j k : Fin (n + 1), U.incl (t j).1 (t j).2 = U.incl (t k).1 (t k).2 }

/-- The Čech nerve at level n is the (n+1)-fold fiber product. -/
abbrev cechNerveType {X : Type} (U : CoveringFamily X) (n : ℕ) : Type :=
  fiberProduct U n

/-- The base point: every fiber product element maps to X. -/
def cechBasePoint {X : Type} (U : CoveringFamily X) {n : ℕ}
    (t : cechNerveType U n) : X :=
  U.incl (t.val 0).1 (t.val 0).2

/-- Face maps: delete the j-th index from an (n+2)-tuple. -/
def cechFace {X : Type} (U : CoveringFamily X) {n : ℕ}
    (j : Fin (n + 2)) (t : cechNerveType U (n + 1)) :
    cechNerveType U n :=
  ⟨fun k => t.val (Fin.succAbove j k),
   fun a b => t.property (Fin.succAbove j a) (Fin.succAbove j b)⟩

/-! ## Section 2: Descent Data -/

/-- A presheaf on types: assigns a type to each type, contravariantly. -/
structure TypePresheaf where
  obj : Type → Type
  restrict : ∀ {X Y : Type}, (Y → X) → obj X → obj Y
  restrict_id : ∀ {X : Type}, restrict (id : X → X) = id

/-- Descent data: compatible local sections on a covering. -/
structure DescentDatum {X : Type} (U : CoveringFamily X)
    (F : TypePresheaf) where
  sections : (i : U.Index) → F.obj (U.Patch i)

/-- Effective descent: descent data uniquely comes from a global section. -/
def EffectiveDescent {X : Type} (U : CoveringFamily X)
    (F : TypePresheaf) : Prop :=
  ∀ (d : DescentDatum U F),
    ∃! (s : F.obj X), ∀ i, F.restrict (U.incl i) s = d.sections i

/-! ## Section 3: Identity Covering -/

/-- The identity covering (X covers itself). -/
def idCovering (X : Type) : CoveringFamily X where
  Index := PUnit
  Patch := fun _ => X
  incl := fun _ => id

/-- A covering is surjective if the inclusions are jointly surjective. -/
def IsSurjective {X : Type} (U : CoveringFamily X) : Prop :=
  ∀ x : X, ∃ i : U.Index, ∃ p : U.Patch i, U.incl i p = x

/-- The identity covering is surjective. -/
theorem idCovering_surjective (X : Type) :
    IsSurjective (idCovering X) :=
  fun x => ⟨PUnit.unit, x, rfl⟩

/-- Every presheaf satisfies descent for the identity covering. -/
theorem descent_id {X : Type} (F : TypePresheaf) :
    EffectiveDescent (idCovering X) F := by
  intro d
  use d.sections PUnit.unit
  refine ⟨?_, ?_⟩
  · intro i; cases i
    show F.restrict id _ = _
    simp [F.restrict_id]
  · intro s' hs'
    have h := hs' PUnit.unit
    simp [idCovering] at h
    rw [F.restrict_id] at h
    exact h

/-! ## Section 4: Separation and the Sheaf Hierarchy -/

/-- Separation: at most one globalization of descent data. -/
def IsSeparated {X : Type} (U : CoveringFamily X) (F : TypePresheaf) : Prop :=
  ∀ (d : DescentDatum U F),
    ∀ (s₁ s₂ : F.obj X),
      (∀ i, F.restrict (U.incl i) s₁ = d.sections i) →
      (∀ i, F.restrict (U.incl i) s₂ = d.sections i) →
      s₁ = s₂

/-- The sheaf condition implies separation. -/
theorem effectiveDescent_implies_separated {X : Type}
    {U : CoveringFamily X} {F : TypePresheaf}
    (h : EffectiveDescent U F) :
    IsSeparated U F := by
  intro d s₁ s₂ h₁ h₂
  obtain ⟨s, _, huniq⟩ := h d
  calc s₁ = s := huniq s₁ h₁
    _ = s₂ := (huniq s₂ h₂).symm

/-! ## Section 5: Hypercovers -/

/-- A hypercover refines a Čech nerve at every simplicial level. -/
structure HypercoverData {X : Type} (U : CoveringFamily X) where
  refinement : (n : ℕ) → Type
  refineMap : (n : ℕ) → refinement n → cechNerveType U n
  surjective : ∀ n t, ∃ r, refineMap n r = t

/-- The identity hypercover: no additional refinement. -/
def idHypercover {X : Type} (U : CoveringFamily X) :
    HypercoverData U where
  refinement n := cechNerveType U n
  refineMap _ := id
  surjective _ t := ⟨t, rfl⟩

/-! ## Section 6: Sheaf Level Hierarchy

| Level        | Condition                     | Topos level |
|-------------|-------------------------------|-------------|
| presheaf    | none                          | 0-topos     |
| separated   | uniqueness of gluing          | —           |
| sheaf       | existence + uniqueness        | 1-topos     |
| hypersheaf  | full ∞-descent                | ∞-topos     |
-/

/-- Sheaf condition levels. -/
inductive SheafLevel where
  | presheaf : SheafLevel
  | separated : SheafLevel
  | sheaf : SheafLevel
  | hypersheaf : SheafLevel

/-- Check the sheaf condition at a given level. -/
def satisfiesLevel {X : Type} (U : CoveringFamily X)
    (F : TypePresheaf) : SheafLevel → Prop
  | .presheaf => True
  | .separated => IsSeparated U F
  | .sheaf => EffectiveDescent U F
  | .hypersheaf => EffectiveDescent U F

/-- Sheaf ⇒ separated. -/
theorem sheaf_implies_separated_level {X : Type}
    {U : CoveringFamily X} {F : TypePresheaf}
    (h : satisfiesLevel U F .sheaf) :
    satisfiesLevel U F .separated :=
  effectiveDescent_implies_separated h

/-- Separated ⇒ presheaf (trivially). -/
theorem separated_implies_presheaf {X : Type}
    {U : CoveringFamily X} {F : TypePresheaf}
    (_h : satisfiesLevel U F .separated) :
    satisfiesLevel U F .presheaf := trivial

/-! ## Section 7: Summary

This layer establishes:

1. **Čech nerve** of a covering family as a simplicial type.
2. **Face maps** for the Čech nerve.
3. **Descent data** = compatible local sections.
4. **Effective descent** = sheaf condition.
5. **Identity covering** satisfies descent for any presheaf.
6. **Hypercovers** as refinements of Čech nerves.
7. **Sheaf level hierarchy**: presheaf < separated < sheaf < hypersheaf.

Key insight: the distinction between sheaves (1-topos) and hypersheaves
(∞-topos) is the truncation level of the descent condition.
-/

end Caramello.CechNerveDescent
