/-
# Caramello MVP: Foundations for "Theories, Sites, Toposes"

This file is the root of the MVP formalization of foundational concepts
from Caramello's "Theories, Sites, Toposes" (2018).

## Central Insight: Lean's Type Theory IS a Topos

The key architectural decision: rather than building topos theory
abstractly and then instantiating, we ground everything in the fact
that **Lean's own `Prop` is the subobject classifier `Ω`** of the
topos `Type`. This makes Lean's internal logic the *model* topos,
and all abstract constructions are verified against this model.

## DAG Architecture (26 Layers)

```
Layer 10: GeometricLogic — geometric formulas, sequents, theories
  │  Geometric formulas as inductive type, frame preservation
  │
Layer 9: ProofMetadata — DAG classification engine (novel)
  │  LemmaClass, ProofNode, ProofDAG, computational analysis
  │
Layer 8: GeometricMorphism — geometric morphisms between toposes
  │  GeometricMorphism structure, identity, composition
  │
Layer 7: ToposStructure — Type is an elementary topos
  │  Finite limits + exponentials + subobject classifier
  │
Layer 6: HeytingOmega — Ω as Heyting algebra / Frame
  │  Prop is a Frame, Set X is a Frame, charMap preserves structure
  │
Layer 5: InternalLogic — Prop↔Subobject bridge
  │  pred_mono_roundtrip, logical ops = categorical ops
  │
Layer 1: PropAsOmega ★ — typesClassifier : Classifier Type
  │
Layer 2: SieveBasics — Sieve pullback algebra
  │
Layer 3: PresheafYoneda — Yoneda embedding
  │
Layer 4: SheafBasics — Sheaves on sites
```

## What This MVP Establishes

1. **Prop = Ω**: The fundamental theorem `typesClassifier` shows that
   `Type` has a subobject classifier, and it is `Prop`.

2. **Predicate ↔ Subobject correspondence**: The round-trip
   `pred_mono_roundtrip` shows that predicates classify subtypes.

3. **Site infrastructure**: Sieves, Grothendieck topologies, and
   sheaves are set up with their key properties.

4. **Logical operations = Categorical operations**: Conjunction is
   intersection, disjunction is union, negation is complement.

5. **Heyting algebra / Frame structure**: Prop and Set X carry
   the frame structure that geometric logic operates on.

6. **Elementary topos verification**: Type satisfies all three
   elementary topos axioms (finite limits, exponentials, classifier).

7. **Geometric morphisms**: Definition, identity, composition,
   and preservation of finite limits.

8. **Geometric logic**: Geometric formulas, sequents, theories,
   and their frame-theoretic preservation.

9. **Proof metadata**: DAG classification system for structural
   analysis of proof complexity.

## Roadmap for Full Formalization

Completed layers:
- **Layers 16–18**: Grothendieck topos, equivalences, applications
- **Layers 19–23**: Filters, completeness, spectral topology
- **Layers 24–26**: Stone duality, subobject lattices, coherent completeness
-/
import RequestProject.Foundations.PropAsOmega
import RequestProject.Foundations.SieveBasics
import RequestProject.Foundations.PresheafYoneda
import RequestProject.Foundations.SheafBasics
import RequestProject.Foundations.InternalLogic
import RequestProject.Foundations.HeytingOmega
import RequestProject.Foundations.ToposStructure
import RequestProject.Foundations.GeometricMorphism
import RequestProject.Foundations.GeometricLogic
import RequestProject.Foundations.ProofMetadata
import RequestProject.Foundations.TopologicalSite
import RequestProject.Foundations.SyntacticCategory
import RequestProject.Foundations.SyntacticSite
import RequestProject.Foundations.ClassifyingTopos
import RequestProject.Foundations.MoritaEquivalence
import RequestProject.Foundations.GrothendieckTopos
import RequestProject.Foundations.ToposEquivalence
import RequestProject.Foundations.Applications
import RequestProject.Foundations.Filters
import RequestProject.Foundations.FinitaryCompleteness
import RequestProject.Foundations.LatticeTheories
import RequestProject.Foundations.PrimeFilterExtension
import RequestProject.Foundations.TopologicalSpectrum
import RequestProject.Foundations.StoneDuality
import RequestProject.Foundations.SubobjectLattice
import RequestProject.Foundations.CoherentCompleteness
import RequestProject.Foundations.SimplicialFoundations
import RequestProject.Foundations.CechNerveDescent
import RequestProject.Foundations.HigherToposFoundations
import RequestProject.Foundations.WeakFactorizationSystems
import RequestProject.Foundations.LocalizationPresentability
import RequestProject.Foundations.InfinityBridgeTechnique
import RequestProject.Foundations.EnrichedMoritaTheory
import RequestProject.Foundations.KripkeJoyalSemantics
import RequestProject.Foundations.CohomologicalInvariants
import RequestProject.Foundations.OpenQuestions
import RequestProject.Foundations.DiaconescuTheorem
import RequestProject.Foundations.SymbolicDynamics
import RequestProject.Foundations.APNTheory
import RequestProject.Foundations.DynamicsAlgebraBridge
import RequestProject.Foundations.MCMInjectivity
import RequestProject.Foundations.BooleanFunctions
import RequestProject.Foundations.KasamiAPN
import RequestProject.Foundations.MathLibGrounding
import RequestProject.Foundations.KasamiDirectProof

namespace Caramello

/-! ## Re-exports for convenient access -/

/-- The fundamental theorem: `Type` is a topos with `Prop` as `Ω`. -/
noncomputable example : CategoryTheory.Classifier (Type) :=
  PropAsOmega.typesClassifier

/-- Lean's `Prop` is the subobject classifier. -/
example : PropAsOmega.typesClassifier.Ω = Prop := rfl

/-- The truth morphism is `fun _ => True`. -/
example : PropAsOmega.typesClassifier.truth = PropAsOmega.truth := rfl

/-- The terminal object (domain of truth) is `PUnit`. -/
example : PropAsOmega.typesClassifier.Ω₀ = PUnit := rfl

/-- Predicates classify subtypes: the round-trip recovers the predicate. -/
example {X : Type} (P : X → Prop) :
    InternalLogic.pred_of_mono (InternalLogic.subobject_of_pred P) = P :=
  InternalLogic.pred_mono_roundtrip P

/-- Prop is a frame (geometric logic foundation). -/
example : Order.Frame Prop := HeytingOmega.prop_frame

/-- Type is an elementary topos. -/
noncomputable example : ToposStructure.ElementaryToposWitness Type :=
  ToposStructure.typeIsTopos

/-- Geometric morphisms compose. -/
noncomputable example {E F G : Type*}
    [CategoryTheory.Category E] [CategoryTheory.Category F] [CategoryTheory.Category G]
    (f : GeomMorph.GeometricMorphism E F)
    (g : GeomMorph.GeometricMorphism F G) :
    GeomMorph.GeometricMorphism E G :=
  GeomMorph.geomMorphComp f g

/-- Soundness of geometric logic: derivable sequents are valid in all models. -/
example {α : Type} {T : GeometricLogic.GeomTheory α}
    {φ ψ : GeometricLogic.GeomFormula α}
    (hd : SyntacticCategory.Derivable T φ ψ)
    (v : α → Prop) (hmodel : T.Model v) :
    φ.eval v → ψ.eval v :=
  SyntacticCategory.soundness hd v hmodel

/-- Subcanonical property: representable presheaves are sheaves for the syntactic topology. -/
example {α : Type} (T : GeometricLogic.GeomTheory α)
    (χ : GeometricLogic.GeomFormula α) :
    SyntacticSite.SheafCondition T (fun φ => SyntacticCategory.Derivable T φ χ) :=
  SyntacticSite.subcanonical_syntactic T χ

/-- Caramello correspondence: models of T ↔ frame homomorphisms L_T → Ω. -/
example {α : Type} (T : GeometricLogic.GeomTheory α) (v : α → Prop) :
    T.Model v ↔ ∃ h : ClassifyingTopos.FrameHomLT T,
      ClassifyingTopos.frameHom_to_valuation h = v :=
  ClassifyingTopos.classifying_universal_property T v

/-- Morita equivalence is transitive. -/
example {α β γ : Type}
    {T₁ : GeometricLogic.GeomTheory α}
    {T₂ : GeometricLogic.GeomTheory β}
    {T₃ : GeometricLogic.GeomTheory γ}
    (h₁₂ : MoritaEquivalence.MoritaEquiv T₁ T₂)
    (h₂₃ : MoritaEquivalence.MoritaEquiv T₂ T₃) :
    MoritaEquivalence.MoritaEquiv T₁ T₃ :=
  MoritaEquivalence.morita_equiv_trans h₁₂ h₂₃

/-- Bridge technique: consistency transfers across Morita equivalence. -/
example {α β : Type}
    {T₁ : GeometricLogic.GeomTheory α}
    {T₂ : GeometricLogic.GeomTheory β}
    (hme : MoritaEquivalence.MoritaEquiv T₁ T₂)
    (hcons : ∃ v, T₁.Model v) :
    ∃ w, T₂.Model w :=
  MoritaEquivalence.bridge_consistency hme hcons

/-- Set (Type) has enough points. -/
example : GrothendieckTopos.ToposHasEnoughPoints (Type) :=
  GrothendieckTopos.set_has_enough_points

/-- The bridge technique gives iff for Morita invariants. -/
example {α β : Type}
    {T₁ : GeometricLogic.GeomTheory α}
    {T₂ : GeometricLogic.GeomTheory β}
    (I : GrothendieckTopos.MoritaInvariant)
    (hme : MoritaEquivalence.MoritaEquiv T₁ T₂) :
    I.prop T₁ ↔ I.prop T₂ :=
  ToposEquivalence.bridge_technique I hme

/-- Atom renaming gives Morita equivalence. -/
example {α β : Type} (e : α ≃ β) {T : GeometricLogic.GeomTheory α} :
    MoritaEquivalence.MoritaEquiv T (Applications.theoryRename e T) :=
  Applications.theoryRename_morita e

/-- Models ↔ completely prime filters (Layer 19). -/
example {α : Type} (T : GeometricLogic.GeomTheory α) (v : α → Prop) :
    T.Model v ↔ ∃ F : Filters.CompletelyPrimeFilter T,
      Filters.cpfilter_to_valuation F = v :=
  Filters.model_filter_correspondence T v

/-- Separation ↔ completeness (Layer 20). -/
example {α : Type} {T : GeometricLogic.GeomTheory α} :
    FinitaryCompleteness.HasSeparation T ↔ ToposEquivalence.IsComplete T :=
  FinitaryCompleteness.separation_iff_complete

/-- Spectral maps compose contravariantly (Layer 21). -/
example {α β γ : Type}
    {T₁ : GeometricLogic.GeomTheory α}
    {T₂ : GeometricLogic.GeomTheory β}
    {T₃ : GeometricLogic.GeomTheory γ}
    (σ : SyntacticCategory.TheoryMorphism T₁ T₂)
    (τ : SyntacticCategory.TheoryMorphism T₂ T₃)
    (p : Filters.Spectrum T₃) :
    (LatticeTheories.spectralMap (SyntacticCategory.theoryMorphismComp σ τ) p).carrier =
    (LatticeTheories.spectralMap σ (LatticeTheories.spectralMap τ p)).carrier :=
  LatticeTheories.spectralMap_comp σ τ p

/-- Stone duality: under completeness, D(φ) ⊆ D(ψ) ↔ T ⊢ φ ⟹ ψ (Layer 24). -/
example {α : Type} {T : GeometricLogic.GeomTheory α}
    (hc : ToposEquivalence.IsComplete T)
    (φ ψ : GeometricLogic.GeomFormula α) :
    Filters.basicOpen (T := T) φ ⊆ Filters.basicOpen ψ ↔
    SyntacticCategory.Derivable T φ ψ :=
  StoneDuality.basicOpen_sub_iff_derivable hc φ ψ

/-- Geometric connectives match subobject lattice operations (Layer 25). -/
example {α : Type} (φ ψ : GeometricLogic.GeomFormula α) :
    SubobjectLattice.formulaToSubobject (.conj φ ψ) =
    SubobjectLattice.subMeet
      (SubobjectLattice.formulaToSubobject φ)
      (SubobjectLattice.formulaToSubobject ψ) :=
  SubobjectLattice.formulaToSubobject_conj φ ψ

/-- Completeness ↔ enough points for classifying toposes (Layer 26). -/
example {α : Type} {T : GeometricLogic.GeomTheory α} :
    ToposEquivalence.IsComplete T ↔
    ClassifyingTopos.HasEnoughPoints T :=
  CoherentCompleteness.completeness_iff_enough_points

/-- SSet has all limits (Layer 27 — simplicial foundations). -/
noncomputable example : CategoryTheory.Limits.HasLimits SSet := inferInstance

/-- SSet has all colimits (Layer 27). -/
noncomputable example : CategoryTheory.Limits.HasColimits SSet := inferInstance

/-- Nerve functor from categories to simplicial sets (Layer 27). -/
example : CategoryTheory.Functor CategoryTheory.Cat SSet :=
  CategoryTheory.nerveFunctor

/-- Prop is (-1)-truncated: proof irrelevance (Layer 27). -/
example : ∀ (P : Prop) (p q : P), p = q :=
  SimplicialFoundations.TruncLevel.prop_is_negOne_truncated

/-- Effective descent implies separation (Layer 28). -/
example {X : Type} {U : CechNerveDescent.CoveringFamily X}
    {F : CechNerveDescent.TypePresheaf}
    (h : CechNerveDescent.EffectiveDescent U F) :
    CechNerveDescent.IsSeparated U F :=
  CechNerveDescent.effectiveDescent_implies_separated h

/-- The codomain fibration is a displayed category (Layer 29). -/
example (C : Type) [CategoryTheory.Category C] :
    HigherToposFoundations.DisplayedCat C :=
  HigherToposFoundations.codomainDisplayed C
/-- Left homotopy is reflexive (Layer 30). -/
example {C : Type*} [CategoryTheory.Category C] {A X : C}
    (f : A ⟶ X) : WeakFactorizationSystems.LeftHomotopic f f :=
  WeakFactorizationSystems.leftHomotopic_refl f

/-- Type is a presentable category (Layer 31). -/
example : LocalizationPresentability.IsPresentable (Type) :=
  LocalizationPresentability.type_isPresentable

/-- Isomorphisms satisfy the right Ore condition (Layer 31). -/
example (C : Type*) [CategoryTheory.Category C] :
    LocalizationPresentability.RightOreCondition
      (LocalizationPresentability.isoMorphismSystem C) :=
  LocalizationPresentability.iso_rightOre C

/-- ∞-bridge technique: transfer ∞-invariants (Layer 32). -/
example {E F : Type} [CategoryTheory.Category E] [CategoryTheory.Category F]
    (I : InfinityBridgeTechnique.InfMoritaInvariant)
    (hme : InfinityBridgeTechnique.InfMoritaEquiv E F) :
    I.prop E ↔ I.prop F :=
  InfinityBridgeTechnique.inf_bridge_technique I hme

/-- Iterated truncation reaches locale level (Layer 32). -/
example (n : ℕ) :
    (InfinityBridgeTechnique.toposLevelTrunc^[n + 1])
      (.nTopos n) = .locale :=
  InfinityBridgeTechnique.truncation_to_locale n

/-- Stable bridge technique for spectra (Layer 33). -/
example (I : EnrichedMoritaTheory.StableMoritaInvariant)
    {E F : EnrichedMoritaTheory.PreSpectrum}
    (h : EnrichedMoritaTheory.StableEquiv E F) :
    I.prop E ↔ I.prop F :=
  EnrichedMoritaTheory.stable_bridge_technique I h

/-- Morita-equivalent theories have stably equivalent spectra (Layer 33). -/
noncomputable example {α β : Type}
    {T₁ : GeometricLogic.GeomTheory α} {T₂ : GeometricLogic.GeomTheory β}
    (hme : MoritaEquivalence.MoritaEquiv T₁ T₂) :
    EnrichedMoritaTheory.StableEquiv
      (EnrichedMoritaTheory.theorySpectrum T₁)
      (EnrichedMoritaTheory.theorySpectrum T₂) :=
  EnrichedMoritaTheory.morita_gives_stable_equiv hme

/-- Kripke-Joyal forcing = eval in Type (Layer 34). -/
example {α : Type} (v : α → Prop) (φ : GeometricLogic.GeomFormula α)
    (U : KripkeJoyalSemantics.Stage) :
    KripkeJoyalSemantics.forces U v φ = φ.eval v :=
  KripkeJoyalSemantics.forces_eq_eval v φ U

/-- Beth semantics = classical semantics in Type (Layer 34). -/
example {α : Type} (v : α → Prop) (φ : GeometricLogic.GeomFormula α)
    (U : KripkeJoyalSemantics.Stage) :
    KripkeJoyalSemantics.BethForces v U φ ↔ KripkeJoyalSemantics.forces U v φ :=
  KripkeJoyalSemantics.beth_eq_classical v φ U

/-- Cohomological properties transfer across Morita equivalence (Layer 35). -/
example {α β : Type}
    {T₁ : GeometricLogic.GeomTheory α} {T₂ : GeometricLogic.GeomTheory β}
    (I : CohomologicalInvariants.CohomologicalInvariant)
    (hme : MoritaEquivalence.MoritaEquiv T₁ T₂) :
    CohomologicalInvariants.TheoryCohProperty T₁ I ↔
    CohomologicalInvariants.TheoryCohProperty T₂ I :=
  CohomologicalInvariants.cohProperty_morita_transfer I hme

/-- Model cardinality is a Morita invariant (Conjectural, proved). -/
example {α β : Type}
    {T₁ : GeometricLogic.GeomTheory α} {T₂ : GeometricLogic.GeomTheory β}
    (hme : MoritaEquivalence.MoritaEquiv T₁ T₂) :
    Nonempty (MoritaEquivalence.ModelOf T₁ ≃ MoritaEquivalence.ModelOf T₂) :=
  OpenQuestions.model_cardinality_invariant hme

/-- Completeness ↔ Spatiality (Conjectural, proved). -/
example {α : Type} {T : GeometricLogic.GeomTheory α} :
    ToposEquivalence.IsComplete T ↔
    (∀ φ ψ : GeometricLogic.GeomFormula α,
      (∀ p : Filters.Spectrum T,
        φ.eval (Filters.cpfilter_to_valuation p) →
        ψ.eval (Filters.cpfilter_to_valuation p)) →
      SyntacticCategory.Derivable T φ ψ) :=
  OpenQuestions.completeness_iff_spatial

end Caramello
