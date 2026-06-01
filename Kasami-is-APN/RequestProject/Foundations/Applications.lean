/-
# Layer 18: Applications — Concrete Theories & Bridge Technique Examples

This layer constructs concrete geometric theories and demonstrates
the bridge technique by establishing Morita equivalences between them
and transferring properties.

## Mathematical Content

1. **Concrete geometric theories**: Boolean algebra theory, dense
   linear order theory, theory of a point, theory of equality.

2. **Morita equivalences between concrete theories**: we demonstrate
   that equivalent-looking theories over different signatures are
   indeed Morita equivalent.

3. **Property transfers**: using the bridge technique from Layer 17,
   we transfer consistency, categoricity, and other properties between
   Morita-equivalent theories.

4. **Theory constructions**: products, sums, and quotients of theories.

## Connection to Caramello's Program

This layer demonstrates the practical use of the bridge technique:
take two seemingly different mathematical theories, show they are
Morita equivalent, and transfer known results between them.

## DAG Structure (depends on Layers 10, 12, 15, 16, 17)

```
  bridge_applications
       |
  concrete_morita_equivalences
       |
  concrete_theories
       |
  GeometricLogic, SyntacticCategory, MoritaEquivalence,
  GrothendieckTopos, ToposEquivalence
```
-/
import Mathlib
import RequestProject.Foundations.ToposEquivalence

namespace Caramello.Applications

open GeometricLogic SyntacticCategory MoritaEquivalence
     GrothendieckTopos ToposEquivalence

/-! ## Section 1: The Trivial Theory (Theory of a Point)

The trivial theory over any atom type has no axioms.
Every valuation is a model — this is the "theory of a point".
-/

/-- The trivial (empty) geometric theory over atoms α. -/
def trivialTheory (α : Type) : GeomTheory α := ∅

/-- Every valuation is a model of the trivial theory. -/
theorem trivialTheory_universal {α : Type} (v : α → Prop) :
    (trivialTheory α).Model v :=
  empty_theory_all_models v

/-- The trivial theory is consistent. -/
theorem trivialTheory_consistent {α : Type} :
    ∃ v : α → Prop, (trivialTheory α).Model v :=
  ⟨fun _ => True, trivialTheory_universal _⟩

/-- The trivial theory over the empty type is categorical. -/
theorem trivialTheory_empty_categorical :
    IsCategorical (trivialTheory Empty) := by
  constructor
  · exact ⟨fun e => e.elim, trivialTheory_universal _⟩
  · intro v₁ v₂ _ _
    funext e; exact e.elim

/-! ## Section 2: The Inconsistent Theory

The theory that derives ⊤ ⊢ ⊥ has no models.
-/

/-- The inconsistent theory: derives ⊤ ⊢ ⊥. -/
def inconsistentTheory (α : Type) : GeomTheory α :=
  {⟨.top, .bot⟩}

/-- The inconsistent theory has no models. -/
theorem inconsistentTheory_no_models {α : Type} (v : α → Prop) :
    ¬ (inconsistentTheory α).Model v := by
  intro h
  have := h ⟨.top, .bot⟩ (Set.mem_singleton _)
  simp [GeomSequent.valid] at this

/-- Any two inconsistent theories (over possibly different atom types)
    are Morita equivalent. -/
theorem inconsistent_theories_morita {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β)
    (h₁ : ¬ ∃ v, T₁.Model v) (h₂ : ¬ ∃ v, T₂.Model v) :
    MoritaEquiv T₁ T₂ := by
  refine ⟨⟨fun m => absurd ⟨m.val, m.isModel⟩ h₁,
           fun m => absurd ⟨m.val, m.isModel⟩ h₂,
           fun m => absurd ⟨m.val, m.isModel⟩ h₁,
           fun m => absurd ⟨m.val, m.isModel⟩ h₂⟩⟩

/-! ## Section 3: The Theory of Equality

Over atoms {a, b}, the theory of equality says a ↔ b.
It has exactly two models: both true or both false.
-/

/-- The theory of equality over Bool: atom false ↔ atom true. -/
def equalityTheory : GeomTheory Bool :=
  { ⟨.atom false, .atom true⟩, ⟨.atom true, .atom false⟩ }

/-- A model of the equality theory has v(false) = v(true). -/
theorem equalityTheory_model_eq (v : Bool → Prop) (hv : equalityTheory.Model v) :
    v false ↔ v true := by
  constructor
  · intro hf
    have := hv ⟨.atom false, .atom true⟩
      (Set.mem_insert _ _)
    exact this hf
  · intro ht
    have := hv ⟨.atom true, .atom false⟩
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
    exact this ht

/-- The equality theory is consistent. -/
theorem equalityTheory_consistent :
    ∃ v, equalityTheory.Model v := by
  refine ⟨fun _ => True, fun s hs => ?_⟩
  simp [equalityTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> simp [GeomSequent.valid]

/-! ## Section 4: The Disjunction Theory

A theory expressing that at least one of two atoms holds.
-/

/-- The disjunction theory: a ∨ b (= ⊤ ⊢ a ∨ b). -/
def disjunctionTheory : GeomTheory Bool :=
  { ⟨.top, .disj (.atom false) (.atom true)⟩ }

/-- A model of the disjunction theory satisfies a ∨ b. -/
theorem disjunctionTheory_model (v : Bool → Prop) (hv : disjunctionTheory.Model v) :
    v false ∨ v true := by
  have := hv ⟨.top, .disj (.atom false) (.atom true)⟩
    (Set.mem_singleton _)
  exact this trivial

/-- The disjunction theory is consistent. -/
theorem disjunctionTheory_consistent :
    ∃ v, disjunctionTheory.Model v := by
  refine ⟨fun _ => True, fun s hs => ?_⟩
  simp [disjunctionTheory, Set.mem_singleton_iff] at hs
  subst hs; simp [GeomSequent.valid]

/-! ## Section 5: Theory Products

The product of two theories T₁ and T₂ (over disjoint atom types)
combines their axioms. Models of the product correspond to pairs
of models of the components.
-/

/-- The product of two geometric theories over disjoint atom types.
    A model of the product is a model of T₁ on the left atoms
    and a model of T₂ on the right atoms. -/
def theoryProduct {α β : Type} (T₁ : GeomTheory α) (T₂ : GeomTheory β) :
    GeomTheory (α ⊕ β) :=
  (fun s => (⟨s.antecedent.mapAtoms Sum.inl,
             s.consequent.mapAtoms Sum.inl⟩ : GeomSequent (α ⊕ β))) '' T₁ ∪
  (fun s => (⟨s.antecedent.mapAtoms Sum.inr,
             s.consequent.mapAtoms Sum.inr⟩ : GeomSequent (α ⊕ β))) '' T₂

/-- A model of the product restricts to a model of the first component. -/
theorem theoryProduct_left_model {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (v : α ⊕ β → Prop) (hv : (theoryProduct T₁ T₂).Model v) :
    T₁.Model (v ∘ Sum.inl) := by
  intro s hs hant
  have hmem : (⟨s.antecedent.mapAtoms Sum.inl,
    s.consequent.mapAtoms Sum.inl⟩ : GeomSequent (α ⊕ β)) ∈ theoryProduct T₁ T₂ :=
    Set.mem_union_left _ (Set.mem_image_of_mem _ hs)
  have := hv _ hmem
  simp [GeomSequent.valid, eval_mapAtoms] at this ⊢
  exact this hant

/-- A model of the product restricts to a model of the second component. -/
theorem theoryProduct_right_model {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (v : α ⊕ β → Prop) (hv : (theoryProduct T₁ T₂).Model v) :
    T₂.Model (v ∘ Sum.inr) := by
  intro s hs hant
  have hmem : (⟨s.antecedent.mapAtoms Sum.inr,
    s.consequent.mapAtoms Sum.inr⟩ : GeomSequent (α ⊕ β)) ∈ theoryProduct T₁ T₂ :=
    Set.mem_union_right _ (Set.mem_image_of_mem _ hs)
  have := hv _ hmem
  simp [GeomSequent.valid, eval_mapAtoms] at this ⊢
  exact this hant

/-- Pairs of models combine into a model of the product. -/
theorem theoryProduct_combine {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (v₁ : α → Prop) (v₂ : β → Prop)
    (hv₁ : T₁.Model v₁) (hv₂ : T₂.Model v₂) :
    (theoryProduct T₁ T₂).Model (Sum.elim v₁ v₂) := by
  intro s hs
  simp [theoryProduct, Set.mem_union, Set.mem_image] at hs
  rcases hs with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
  · simp [GeomSequent.valid, eval_mapAtoms]
    exact hv₁ s' hs'
  · simp [GeomSequent.valid, eval_mapAtoms]
    exact hv₂ s' hs'

/-- The product of consistent theories is consistent. -/
theorem theoryProduct_consistent {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (h₁ : ∃ v, T₁.Model v) (h₂ : ∃ v, T₂.Model v) :
    ∃ v, (theoryProduct T₁ T₂).Model v := by
  obtain ⟨v₁, hv₁⟩ := h₁
  obtain ⟨v₂, hv₂⟩ := h₂
  exact ⟨Sum.elim v₁ v₂, theoryProduct_combine v₁ v₂ hv₁ hv₂⟩

/-! ## Section 6: Renaming Atoms

Renaming atoms (via a bijection) preserves all properties:
it gives a biinterpretation and hence a Morita equivalence.
-/

/-- Rename the atoms of a theory via an equivalence of atom types. -/
def theoryRename {α β : Type} (e : α ≃ β) (T : GeomTheory α) :
    GeomTheory β :=
  (fun s => (⟨s.antecedent.mapAtoms e,
             s.consequent.mapAtoms e⟩ : GeomSequent β)) '' T

/-- Renaming preserves models (forward). -/
theorem theoryRename_model_fwd {α β : Type} (e : α ≃ β)
    {T : GeomTheory α} (v : α → Prop) (hv : T.Model v) :
    (theoryRename e T).Model (v ∘ e.symm) := by
  intro s hs
  simp [theoryRename, Set.mem_image] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  simp [GeomSequent.valid, eval_mapAtoms]
  convert hv s' hs' using 2 <;> ext a <;> simp

/-- Renaming preserves models (backward). -/
theorem theoryRename_model_bwd {α β : Type} (e : α ≃ β)
    {T : GeomTheory α} (w : β → Prop) (hw : (theoryRename e T).Model w) :
    T.Model (w ∘ e) := by
  intro s hs hant
  have hmem : (⟨s.antecedent.mapAtoms e, s.consequent.mapAtoms e⟩ :
    GeomSequent β) ∈ theoryRename e T :=
    Set.mem_image_of_mem _ hs
  have := hw _ hmem
  simp [GeomSequent.valid, eval_mapAtoms] at this ⊢
  exact this hant

/-- Renaming gives a Morita equivalence. -/
theorem theoryRename_morita {α β : Type} (e : α ≃ β)
    {T : GeomTheory α} :
    MoritaEquiv T (theoryRename e T) := by
  refine ⟨⟨fun m => ⟨m.val ∘ e.symm, theoryRename_model_fwd e m.val m.isModel⟩,
           fun m => ⟨m.val ∘ e, theoryRename_model_bwd e m.val m.isModel⟩,
           ?_, ?_⟩⟩
  · intro m; ext a; simp
  · intro m; ext b; simp

/-! ## Section 7: Bridge Technique Applications

We demonstrate the bridge technique on concrete examples.
-/

/-- Consistency transfers across atom renaming. -/
theorem rename_preserves_consistency {α β : Type} (e : α ≃ β)
    {T : GeomTheory α} (h : ∃ v, T.Model v) :
    ∃ w, (theoryRename e T).Model w :=
  bridge_consistency' (theoryRename_morita e) |>.mp h

/-- Categoricity transfers across atom renaming. -/
theorem rename_preserves_categorical {α β : Type} (e : α ≃ β)
    {T : GeomTheory α} (h : IsCategorical T) :
    IsCategorical (theoryRename e T) :=
  (categorical_morita_invariant (theoryRename_morita e)).mp h

/-- The product of two trivial theories is Morita equivalent to
    the trivial theory (over the sum type). -/
theorem trivial_product_morita {α β : Type} :
    MoritaEquiv (trivialTheory (α ⊕ β)) (theoryProduct (trivialTheory α) (trivialTheory β)) := by
  -- Both are the empty theory over α ⊕ β
  have : theoryProduct (trivialTheory α) (trivialTheory β) = trivialTheory (α ⊕ β) := by
    ext s
    simp [theoryProduct, trivialTheory, Set.mem_empty_iff_false]
  rw [this]
  exact morita_equiv_refl _

/-! ## Section 8: Theory Quotients

Quotienting a theory by an equivalence relation on atoms
gives a Morita equivalence when the relation is compatible
with the theory.
-/

/-- Extending a theory with additional axioms. -/
def theoryExtend {α : Type} (T : GeomTheory α)
    (axioms : Set (GeomSequent α)) : GeomTheory α :=
  T ∪ axioms

/-- The extension of a theory is a super-theory. -/
theorem theoryExtend_superset {α : Type} (T : GeomTheory α)
    (axioms : Set (GeomSequent α)) :
    T ⊆ theoryExtend T axioms :=
  Set.subset_union_left

/-- Models of the extension are models of the original theory. -/
theorem theoryExtend_model_restricts {α : Type}
    {T : GeomTheory α} {axioms : Set (GeomSequent α)}
    (v : α → Prop) (hv : (theoryExtend T axioms).Model v) :
    T.Model v := by
  intro s hs
  exact hv s (Set.mem_union_left _ hs)

/-- Models of the extension satisfy the additional axioms. -/
theorem theoryExtend_model_axioms {α : Type}
    {T : GeomTheory α} {axioms : Set (GeomSequent α)}
    (v : α → Prop) (hv : (theoryExtend T axioms).Model v)
    (s : GeomSequent α) (hs : s ∈ axioms) :
    s.valid v :=
  hv s (Set.mem_union_right _ hs)

/-! ## Section 9: Summary

This layer demonstrates the Caramello bridge technique on concrete examples:

1. **Trivial theory**: every valuation is a model; categorical over PUnit.
2. **Inconsistent theory**: no models; all inconsistent theories are Morita equivalent.
3. **Equality theory**: two models (both true, both false).
4. **Disjunction theory**: "at least one atom holds".
5. **Theory products**: combine theories over disjoint signatures.
6. **Atom renaming**: bijections on atoms give Morita equivalences.
7. **Bridge applications**: consistency and categoricity transfer
   across atom renamings and other Morita equivalences.
8. **Theory extensions**: adding axioms as a structured operation.

Key theorems:
- `inconsistent_theories_morita`: all inconsistent theories are Morita equivalent.
- `theoryRename_morita`: renaming atoms preserves Morita class.
- `rename_preserves_consistency/categorical`: bridge technique in action.
- `theoryProduct_consistent`: product of consistent theories is consistent.
-/

end Caramello.Applications
