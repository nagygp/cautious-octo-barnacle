/-
# Layer 16: Grothendieck Topos Structure & Points

This layer defines Grothendieck toposes abstractly (as structures),
establishes points of a topos, and connects everything to the
classifying topos from Layer 14.

## Mathematical Content

1. **Grothendieck topos axioms** (as a structure): a category E is a
   Grothendieck topos if it satisfies certain completeness/cocompleteness
   conditions.

2. **Points of a topos**: geometric morphisms Set → E. For Set,
   there is exactly one point (the identity).

3. **Enough points**: a topos has enough points when stalk functors
   jointly reflect isomorphisms.

4. **Topos-theoretic invariants**: properties preserved by Morita
   equivalence. Concrete examples: consistency, inconsistency,
   unique model, decidability of model existence.

5. **Locale morphisms**: frame homomorphisms between Lindenbaum–Tarski
   algebras, induced by theory morphisms.

## DAG Structure (depends on Layers 8, 14, 15)

```
  MoritaInvariant examples
       |
  MoritaInvariant (structure)
       |
  set_has_enough_points ←── ToposHasEnoughPoints
       |
  setCanonicalPoint ←── ToposPoint
       |
  GrothendieckToposData ←── GeometricMorphism (Layer 8)
```
-/
import Mathlib
import RequestProject.Foundations.MoritaEquivalence

namespace Caramello.GrothendieckTopos

open CategoryTheory GeometricLogic SyntacticCategory ClassifyingTopos MoritaEquivalence

/-! ## Section 1: Grothendieck Topos Data -/

/-- Data witnessing that a category E is a Grothendieck topos. -/
structure GrothendieckToposData (E : Type*) [Category E] where
  /-- E has all finite limits -/
  hasFiniteLimits : Limits.HasFiniteLimits E
  /-- E has all finite colimits -/
  hasFiniteColimits : Limits.HasFiniteColimits E
  /-- E has a terminal object -/
  hasTerminal : Limits.HasTerminal E
  /-- E has binary products -/
  hasBinaryProducts : Limits.HasBinaryProducts E
  /-- E has equalizers -/
  hasEqualizers : Limits.HasEqualizers E
  /-- Exactness property -/
  isExact : Prop

/-- Type (= Set) is a Grothendieck topos. -/
noncomputable def setIsGrothendieckTopos : GrothendieckToposData (Type) where
  hasFiniteLimits := inferInstance
  hasFiniteColimits := inferInstance
  hasTerminal := inferInstance
  hasBinaryProducts := inferInstance
  hasEqualizers := inferInstance
  isExact := True

/-! ## Section 2: Points of a Topos -/

/-- A point of a topos E is a geometric morphism from Set (Type) to E. -/
structure ToposPoint (E : Type*) [Category E] where
  /-- The inverse image (stalk) functor: E → Set -/
  stalk : Functor E (Type)
  /-- The direct image (germ) functor: Set → E -/
  germ : Functor (Type) E
  /-- The adjunction: stalk ⊣ germ -/
  adj : stalk ⊣ germ
  /-- stalk preserves finite limits -/
  stalkLeftExact : Limits.PreservesFiniteLimits stalk

/-- For Set = Type, the identity functors give a canonical point. -/
noncomputable def setCanonicalPoint : ToposPoint (Type) where
  stalk := Functor.id (Type)
  germ := Functor.id (Type)
  adj := Adjunction.id
  stalkLeftExact := inferInstance

/-- The collection of all points of a topos. -/
def PointSet (E : Type*) [Category E] := ToposPoint E

/-- A topos has **enough points** if the stalk functors jointly
    detect isomorphisms. -/
def ToposHasEnoughPoints (E : Type*) [Category E] : Prop :=
  ∀ {X Y : E} (f : X ⟶ Y),
    (∀ p : ToposPoint E, Function.Bijective (p.stalk.map f)) →
    IsIso f

/-- Set (Type) has enough points. -/
theorem set_has_enough_points : ToposHasEnoughPoints (Type) := by
  intro X Y f hbij
  have hf := hbij setCanonicalPoint
  simp [setCanonicalPoint] at hf
  exact (isIso_iff_bijective f).mpr hf

/-! ## Section 3: Topos-Theoretic Invariants -/

/-- A Morita invariant: a property of geometric theories preserved
    by Morita equivalence. -/
structure MoritaInvariant where
  /-- The property -/
  prop : ∀ {α : Type}, GeomTheory α → Prop
  /-- The invariance proof -/
  invariant : ∀ {α β : Type} {T₁ : GeomTheory α} {T₂ : GeomTheory β},
    MoritaEquiv T₁ T₂ → prop T₁ → prop T₂

/-- Consistency (having a model) is a Morita invariant. -/
def consistencyInvariant : MoritaInvariant where
  prop := fun {α} T => ∃ v : α → Prop, T.Model v
  invariant := fun hme hcons => consistency_morita_invariant hme hcons

/-- Inconsistency (having no model) is a Morita invariant. -/
def inconsistencyInvariant : MoritaInvariant where
  prop := fun {α} T => ¬ ∃ v : α → Prop, T.Model v
  invariant := fun hme hincons hcons =>
    hincons (consistency_morita_invariant (morita_equiv_symm hme) hcons)

/-- Having exactly one model is a Morita invariant. -/
def uniqueModelInvariant : MoritaInvariant where
  prop := fun {α} T => (∃ v : α → Prop, T.Model v) ∧
    (∀ v₁ v₂ : α → Prop, T.Model v₁ → T.Model v₂ → v₁ = v₂)
  invariant := by
    intro α β T₁ T₂ hme ⟨hcons, huniq⟩
    exact ⟨consistency_morita_invariant hme hcons,
           unique_model_morita_invariant hme huniq⟩

/-- Having no more than one model is a Morita invariant. -/
def atMostOneModelInvariant : MoritaInvariant where
  prop := fun {α} T =>
    ∀ v₁ v₂ : α → Prop, T.Model v₁ → T.Model v₂ → v₁ = v₂
  invariant := fun hme huniq =>
    unique_model_morita_invariant hme huniq

/-- Decidability of model existence is a Morita invariant. -/
def modelExistenceDecidableInvariant : MoritaInvariant where
  prop := fun {α} T =>
    (∃ v : α → Prop, T.Model v) ∨ (¬ ∃ v : α → Prop, T.Model v)
  invariant := by
    intro α β T₁ T₂ hme h
    rcases h with ⟨v, hv⟩ | hno
    · exact Or.inl (consistency_morita_invariant hme ⟨v, hv⟩)
    · exact Or.inr (fun ⟨w, hw⟩ =>
        hno (consistency_morita_invariant (morita_equiv_symm hme) ⟨w, hw⟩))

/-- The conjunction of two Morita invariants is a Morita invariant. -/
def conjInvariant (I₁ I₂ : MoritaInvariant) : MoritaInvariant where
  prop := fun T => I₁.prop T ∧ I₂.prop T
  invariant := fun hme ⟨h₁, h₂⟩ =>
    ⟨I₁.invariant hme h₁, I₂.invariant hme h₂⟩

/-- The disjunction of two Morita invariants is a Morita invariant. -/
def disjInvariant (I₁ I₂ : MoritaInvariant) : MoritaInvariant where
  prop := fun T => I₁.prop T ∨ I₂.prop T
  invariant := fun hme h => h.elim
    (fun h₁ => Or.inl (I₁.invariant hme h₁))
    (fun h₂ => Or.inr (I₂.invariant hme h₂))

/-! ## Section 4: Connecting Points to Models -/

/-- A point of the classifying topos of T. -/
def ClassifyingToposPoint' {α : Type} (T : GeomTheory α) :=
  ClassifyingPoint T

/-- Models correspond to points of the classifying topos. -/
theorem models_are_points {α : Type} (T : GeomTheory α) (v : α → Prop) :
    T.Model v ↔ ∃ p : ClassifyingToposPoint' T,
      frameHom_to_valuation p = v :=
  classifying_universal_property T v

/-! ## Section 5: Frame Homomorphisms Between Lindenbaum–Tarski Algebras

A theory morphism σ : T₁ → T₂ (mapping atoms α → β) induces a
frame homomorphism L_T₁ → L_T₂ via mapAtoms. This goes covariantly
on the frame side (contravariantly on models/locales).
-/

/-- A frame homomorphism between Lindenbaum–Tarski algebras,
    going covariantly (from source frame to target frame). -/
structure FrameHom {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β) where
  /-- The underlying map on formulas -/
  onFormulas : GeomFormula α → GeomFormula β
  /-- Respects T-equivalence -/
  resp_equiv : ∀ φ ψ : GeomFormula α,
    (T₁ ⊢g φ ⟺ ψ) → (T₂ ⊢g onFormulas φ ⟺ onFormulas ψ)
  /-- Preserves derivability order -/
  monotone : ∀ φ ψ : GeomFormula α,
    (T₁ ⊢g φ ⟹ ψ) → (T₂ ⊢g onFormulas φ ⟹ onFormulas ψ)

/-- A theory morphism induces a frame homomorphism via mapAtoms. -/
def theoryMorphismToFrameHom {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂) : FrameHom T₁ T₂ where
  onFormulas := GeomFormula.mapAtoms σ.onAtoms
  resp_equiv := fun _ _ ⟨hfwd, hbwd⟩ =>
    ⟨σ.preserves_derivability hfwd, σ.preserves_derivability hbwd⟩
  monotone := fun _ _ h => σ.preserves_derivability h

/-- Identity frame homomorphism. -/
def frameHomId {α : Type} (T : GeomTheory α) : FrameHom T T where
  onFormulas := id
  resp_equiv := fun _ _ h => h
  monotone := fun _ _ h => h

/-- Composition of frame homomorphisms. -/
def frameHomComp {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (f : FrameHom T₁ T₂) (g : FrameHom T₂ T₃) :
    FrameHom T₁ T₃ where
  onFormulas := g.onFormulas ∘ f.onFormulas
  resp_equiv := fun _ _ h => g.resp_equiv _ _ (f.resp_equiv _ _ h)
  monotone := fun _ _ h => g.monotone _ _ (f.monotone _ _ h)

/-- A frame homomorphism composed with a FrameHomLT gives
    a model of the source theory. This is expressed via
    theory morphisms, which is the proper route. -/
theorem frameHom_comp_gives_model {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    (w : β → Prop) (hw : T₂.Model w) :
    T₁.Model (reindexValuation σ.onAtoms w) :=
  theoryMorphism_pullback_model σ w hw

/-! ## Section 6: Subterminal Objects -/

/-- A type is subterminal if it has at most one element. -/
def IsSubterminal (X : Type*) : Prop :=
  ∀ x y : X, x = y

/-- The subterminal order on Prop. -/
def SubterminalOrder : Prop → Prop → Prop :=
  fun P Q => P → Q

theorem subterminal_order_refl (P : Prop) : SubterminalOrder P P := id

theorem subterminal_order_trans (P Q R : Prop)
    (h₁ : SubterminalOrder P Q) (h₂ : SubterminalOrder Q R) :
    SubterminalOrder P R := h₂ ∘ h₁

/-! ## Section 7: Internal Language -/

/-- A sentence in the internal language of Set is a proposition. -/
def InternalSentence := Prop

/-- Interpretation of a geometric formula as an internal sentence of Set. -/
def interpretInSet {α : Type} (v : α → Prop) (φ : GeomFormula α) :
    InternalSentence :=
  φ.eval v

theorem interpretInSet_preserves_conj {α : Type} (v : α → Prop)
    (φ ψ : GeomFormula α) :
    interpretInSet v (.conj φ ψ) ↔ (interpretInSet v φ ∧ interpretInSet v ψ) :=
  Iff.rfl

theorem interpretInSet_preserves_disj {α : Type} (v : α → Prop)
    (φ ψ : GeomFormula α) :
    interpretInSet v (.disj φ ψ) ↔ (interpretInSet v φ ∨ interpretInSet v ψ) :=
  Iff.rfl

theorem interpretInSet_preserves_top {α : Type} (v : α → Prop) :
    interpretInSet v .top ↔ True :=
  Iff.rfl

theorem interpretInSet_preserves_bot {α : Type} (v : α → Prop) :
    interpretInSet v .bot ↔ False :=
  Iff.rfl

theorem interpretInSet_preserves_iDisj {α : Type} (v : α → Prop)
    (ι : Type) (f : ι → GeomFormula α) :
    interpretInSet v (.iDisj ι f) ↔ ∃ i, interpretInSet v (f i) :=
  Iff.rfl

end Caramello.GrothendieckTopos
