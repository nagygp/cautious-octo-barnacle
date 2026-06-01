/-
# Layer 25: Subobject Lattices & Logical Functors

This layer develops the lattice structure on subobjects in Set (Type),
connecting it to the Heyting algebra structure on Prop (Layer 6) and
the geometric logic framework (Layer 10).

## Mathematical Content

1. **Subobject lattice of Set**: The subobjects of a type X in Set
   are the predicates X → Prop, which form a complete Heyting algebra.

2. **Logical functors**: Functors that preserve the subobject classifier.

3. **Image factorization**: Every morphism factors as epi ∘ mono.

4. **Power object**: The power object P(X) = X → Prop in Set.

5. **Formula-to-subobject**: Geometric formulas define subobjects.

## DAG Structure (depends on Layers 1, 5, 6, 7, 10, 12)

```
  formula_subobject_correspondence
       |
  logical_maps ←── preimageLogicalMap
       |
  image_factorization
       |
  subobject_lattice ←── HeytingOmega (Layer 6)
       |
  PropAsOmega, InternalLogic, GeometricLogic, SyntacticCategory
```
-/
import Mathlib
import RequestProject.Foundations.SyntacticCategory

namespace Caramello.SubobjectLattice

open CategoryTheory GeometricLogic SyntacticCategory

/-! ## Section 1: Subobject Lattice in Set -/

/-- The subobject lattice of X in Set is (X → Prop). -/
abbrev SubObj (X : Type) := X → Prop

/-- The bottom subobject (empty predicate). -/
def subBottom (X : Type) : SubObj X := fun _ => False

/-- The top subobject (full predicate). -/
def subTop (X : Type) : SubObj X := fun _ => True

/-- Meet of two subobjects. -/
def subMeet {X : Type} (P Q : SubObj X) : SubObj X :=
  fun x => P x ∧ Q x

/-- Join of two subobjects. -/
def subJoin {X : Type} (P Q : SubObj X) : SubObj X :=
  fun x => P x ∨ Q x

/-- Arbitrary meet of subobjects. -/
def subInf {X : Type} {ι : Type} (f : ι → SubObj X) : SubObj X :=
  fun x => ∀ i, f i x

/-- Arbitrary join of subobjects. -/
def subSup {X : Type} {ι : Type} (f : ι → SubObj X) : SubObj X :=
  fun x => ∃ i, f i x

/-- The implication (Heyting arrow) of subobjects. -/
def subImpl {X : Type} (P Q : SubObj X) : SubObj X :=
  fun x => P x → Q x

/-- The negation of a subobject. -/
def subNeg {X : Type} (P : SubObj X) : SubObj X :=
  fun x => ¬ P x

/-- Subobject inclusion as a partial order. -/
def subLe {X : Type} (P Q : SubObj X) : Prop :=
  ∀ x, P x → Q x

/-- Subobject inclusion is reflexive. -/
theorem subLe_refl {X : Type} (P : SubObj X) : subLe P P :=
  fun _ h => h

/-- Subobject inclusion is transitive. -/
theorem subLe_trans {X : Type} (P Q R : SubObj X)
    (h₁ : subLe P Q) (h₂ : subLe Q R) : subLe P R :=
  fun x hx => h₂ x (h₁ x hx)

/-- Subobject inclusion is antisymmetric. -/
theorem subLe_antisymm {X : Type} (P Q : SubObj X)
    (h₁ : subLe P Q) (h₂ : subLe Q P) : P = Q :=
  funext fun x => propext ⟨h₁ x, h₂ x⟩

/-- Meet is commutative. -/
theorem subMeet_comm {X : Type} (P Q : SubObj X) :
    subMeet P Q = subMeet Q P :=
  funext fun _ => propext And.comm

/-- Join is commutative. -/
theorem subJoin_comm {X : Type} (P Q : SubObj X) :
    subJoin P Q = subJoin Q P :=
  funext fun _ => propext Or.comm

/-- Meet distributes over join. -/
theorem subMeet_distrib_subJoin {X : Type}
    (P Q R : SubObj X) :
    subMeet P (subJoin Q R) = subJoin (subMeet P Q) (subMeet P R) :=
  funext fun _ => propext and_or_left

/-- Join distributes over meet. -/
theorem subJoin_distrib_subMeet {X : Type}
    (P Q R : SubObj X) :
    subJoin P (subMeet Q R) = subMeet (subJoin P Q) (subJoin P R) :=
  funext fun _ => propext or_and_left

/-- Meet distributes over arbitrary join (frame law). -/
theorem subMeet_distrib_subSup {X : Type} {ι : Type}
    (P : SubObj X) (f : ι → SubObj X) :
    subMeet P (subSup f) = subSup (fun i => subMeet P (f i)) :=
  funext fun _ => propext
    ⟨fun ⟨hp, i, hfi⟩ => ⟨i, hp, hfi⟩,
     fun ⟨i, hp, hfi⟩ => ⟨hp, i, hfi⟩⟩

/-- The subobject lattice is complete: every set has a greatest lower bound. -/
theorem subobject_lattice_complete {X : Type} :
    ∀ (S : Set (SubObj X)),
      ∃ (lb : SubObj X),
        (∀ P ∈ S, subLe lb P) ∧
        (∀ Q : SubObj X, (∀ P ∈ S, subLe Q P) → subLe Q lb) :=
  fun S => ⟨fun y => ∀ P ∈ S, P y,
            fun P hP _ hx => hx P hP,
            fun _ hQ _ hx P hP => hQ P hP _ hx⟩

/-! ## Section 2: Image Factorization in Set -/

/-- The image of a function. -/
def FunImage {X Y : Type} (f : X → Y) : Type :=
  { y : Y // ∃ x, f x = y }

/-- The surjection onto the image. -/
def toImage {X Y : Type} (f : X → Y) : X → FunImage f :=
  fun x => ⟨f x, ⟨x, rfl⟩⟩

/-- The injection from the image. -/
def fromImage {X Y : Type} (f : X → Y) : FunImage f → Y :=
  fun ⟨y, _⟩ => y

/-- The factorization recovers f. -/
theorem image_factorization {X Y : Type} (f : X → Y) :
    fromImage f ∘ toImage f = f := rfl

/-- The injection from the image is injective. -/
theorem fromImage_injective {X Y : Type} (f : X → Y) :
    Function.Injective (fromImage f) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext h

/-- The surjection onto the image is surjective. -/
theorem toImage_surjective {X Y : Type} (f : X → Y) :
    Function.Surjective (toImage f) :=
  fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩

/-- The image of f as a subobject of Y. -/
def imageSubobject {X Y : Type} (f : X → Y) : SubObj Y :=
  fun y => ∃ x, f x = y

/-- The image subobject is the smallest through which f factors. -/
theorem imageSubobject_smallest {X Y : Type} (f : X → Y)
    (Q : SubObj Y) (h : ∀ x, Q (f x)) :
    subLe (imageSubobject f) Q :=
  fun _ ⟨_, hx⟩ => hx ▸ h _

/-! ## Section 3: Power Object -/

/-- The power object of X in Set. -/
abbrev PowerObject (X : Type) := X → Prop

/-- The membership relation: x ∈ P for P : PowerObject X. -/
def membershipRel {X : Type} : X × PowerObject X → Prop :=
  fun ⟨x, P⟩ => P x

/-- The characteristic map: given R ⊆ X × Y, get χ : Y → PowerObject X. -/
def charMapPower {X Y : Type} (R : X × Y → Prop) : Y → PowerObject X :=
  fun y x => R (x, y)

/-- The membership relation recovers R via the characteristic map. -/
theorem charMapPower_membership {X Y : Type} (R : X × Y → Prop) (x : X) (y : Y) :
    membershipRel (x, charMapPower R y) ↔ R (x, y) :=
  Iff.rfl

/-- The singleton map: X → P(X). -/
def singletonMap {X : Type} : X → PowerObject X :=
  fun x y => y = x

/-- Singleton membership. -/
theorem singleton_mem {X : Type} (x y : X) :
    membershipRel (y, singletonMap x) ↔ y = x :=
  Iff.rfl

/-! ## Section 4: Logical Functors -/

/-- A "logical" map between subobject lattices: preserves lattice ops. -/
structure LogicalMap (X Y : Type) where
  /-- The underlying function on subobjects -/
  onSub : SubObj X → SubObj Y
  /-- Preserves top -/
  pres_top : onSub (subTop X) = subTop Y
  /-- Preserves bottom -/
  pres_bot : onSub (subBottom X) = subBottom Y
  /-- Preserves meets -/
  pres_meet : ∀ P Q, onSub (subMeet P Q) = subMeet (onSub P) (onSub Q)
  /-- Preserves joins -/
  pres_join : ∀ P Q, onSub (subJoin P Q) = subJoin (onSub P) (onSub Q)

/-- The identity logical map. -/
def logicalMapId (X : Type) : LogicalMap X X where
  onSub := id
  pres_top := rfl
  pres_bot := rfl
  pres_meet := fun _ _ => rfl
  pres_join := fun _ _ => rfl

/-- Composition of logical maps. -/
def logicalMapComp {X Y Z : Type}
    (f : LogicalMap X Y) (g : LogicalMap Y Z) : LogicalMap X Z where
  onSub := g.onSub ∘ f.onSub
  pres_top := by simp [Function.comp, f.pres_top, g.pres_top]
  pres_bot := by simp [Function.comp, f.pres_bot, g.pres_bot]
  pres_meet := fun P Q => by simp [Function.comp, f.pres_meet, g.pres_meet]
  pres_join := fun P Q => by simp [Function.comp, f.pres_join, g.pres_join]

/-- Preimage of a function induces a logical map. -/
def preimageLogicalMap {X Y : Type} (f : X → Y) : LogicalMap Y X where
  onSub := fun P x => P (f x)
  pres_top := rfl
  pres_bot := rfl
  pres_meet := fun _ _ => rfl
  pres_join := fun _ _ => rfl

/-- Preimage preserves the lattice order. -/
theorem preimage_monotone {X Y : Type} (f : X → Y)
    (P Q : SubObj Y) (h : subLe P Q) :
    subLe ((preimageLogicalMap f).onSub P) ((preimageLogicalMap f).onSub Q) :=
  fun _ hx => h _ hx

/-! ## Section 5: Connecting to Geometric Logic -/

/-- A geometric formula defines a subobject of the model space. -/
def formulaToSubobject {α : Type} (φ : GeomFormula α) : SubObj (α → Prop) :=
  fun v => φ.eval v

/-- Top formula gives top subobject. -/
theorem formulaToSubobject_top {α : Type} :
    formulaToSubobject (.top : GeomFormula α) = subTop _ := rfl

/-- Bottom formula gives bottom subobject. -/
theorem formulaToSubobject_bot {α : Type} :
    formulaToSubobject (.bot : GeomFormula α) = subBottom _ := rfl

/-- Conjunction corresponds to meet. -/
theorem formulaToSubobject_conj {α : Type}
    (φ ψ : GeomFormula α) :
    formulaToSubobject (.conj φ ψ) =
    subMeet (formulaToSubobject φ) (formulaToSubobject ψ) := rfl

/-- Disjunction corresponds to join. -/
theorem formulaToSubobject_disj {α : Type}
    (φ ψ : GeomFormula α) :
    formulaToSubobject (.disj φ ψ) =
    subJoin (formulaToSubobject φ) (formulaToSubobject ψ) := rfl

/-- Infinitary disjunction corresponds to supremum. -/
theorem formulaToSubobject_iDisj {α : Type}
    (ι : Type) (f : ι → GeomFormula α) :
    formulaToSubobject (.iDisj ι f) =
    subSup (fun i => formulaToSubobject (f i)) := rfl

/-- Derivability corresponds to subobject inclusion. -/
theorem derivable_iff_subobject_le {α : Type}
    {T : GeomTheory α}
    {φ ψ : GeomFormula α}
    (h : Derivable T φ ψ) :
    ∀ v : α → Prop, T.Model v →
    formulaToSubobject φ v → formulaToSubobject ψ v :=
  fun v hm hφ => soundness h v hm hφ

/-- Models correspond to valuations above all axiom subobjects. -/
theorem model_iff_above_axioms {α : Type}
    (T : GeomTheory α) (v : α → Prop) :
    T.Model v ↔ ∀ s ∈ T,
      formulaToSubobject s.antecedent v → formulaToSubobject s.consequent v :=
  Iff.rfl

/-! ## Section 6: Pullback Stability -/

/-- Preimage preserves geometric formula evaluation. -/
theorem preimage_formulaToSubobject {α : Type}
    {X Y : Type} (g : X → Y)
    (φ : GeomFormula α)
    (embed_X : α → (X → Prop)) (embed_Y : α → (Y → Prop))
    (h_compat : ∀ a x, embed_X a x ↔ embed_Y a (g x)) :
    ∀ x, φ.eval (fun a => embed_X a x) ↔ φ.eval (fun a => embed_Y a (g x)) := by
  intro x
  induction φ with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | atom a => exact h_compat a x
  | conj _ _ ih₁ ih₂ =>
    simp only [GeomFormula.eval]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨ih₁.mp h₁, ih₂.mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨ih₁.mpr h₁, ih₂.mpr h₂⟩⟩
  | disj _ _ ih₁ ih₂ =>
    simp only [GeomFormula.eval]
    exact ⟨fun h => h.elim (Or.inl ∘ ih₁.mp) (Or.inr ∘ ih₂.mp),
           fun h => h.elim (Or.inl ∘ ih₁.mpr) (Or.inr ∘ ih₂.mpr)⟩
  | iDisj _ _ ih =>
    simp only [GeomFormula.eval]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, (ih i).mp hi⟩,
           fun ⟨i, hi⟩ => ⟨i, (ih i).mpr hi⟩⟩
  | ex _ _ ih =>
    simp only [GeomFormula.eval]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, (ih b).mp hb⟩,
           fun ⟨b, hb⟩ => ⟨b, (ih b).mpr hb⟩⟩

/-! ## Section 7: Summary

This layer connects:

1. **Subobject lattice** of Set = predicates = complete Heyting algebra.
2. **Image factorization** = epi-mono in Set.
3. **Power object** P(X) = X → Prop with characteristic maps.
4. **Logical maps** preserve lattice structure, preimage is logical.
5. **Formula-to-subobject** correspondence: geometric connectives
   match lattice operations (meet, join, supremum).
6. **Pullback stability**: geometric formulas are preserved by preimage.
-/

end Caramello.SubobjectLattice
