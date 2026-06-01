/-
# Layer 5: Internal Logic — Prop as Ω Connects to Subobjects

This layer bridges the internal type-theoretic view (Prop is Ω)
with the external categorical view (subobject classifier).

In Lean's type theory:
- `P : X → Prop` is a predicate (= characteristic map χ : X → Ω)
- `{x : X // P x}` is the subtype (= the subobject classified by χ)
- `Set.range (Subtype.val : {x // P x} → X)` recovers P

## DAG Structure (depends on Layer 1: PropAsOmega)

```
    pred_mono_roundtrip
           |
    charMap_subtype_eq ←── subtype_range
           |                    |
    subtype_mono         subtype_val_injective
```
-/
import Mathlib
import RequestProject.Foundations.PropAsOmega

namespace Caramello.InternalLogic

open CategoryTheory CategoryTheory.Limits

/-! ## Subtype as Subobject -/

/-- The inclusion of a subtype is injective (hence mono in Type). -/
lemma subtype_val_injective {X : Type} (P : X → Prop) :
    Function.Injective (Subtype.val : {x : X // P x} → X) :=
  Subtype.val_injective

/-- The inclusion of a subtype is mono in the categorical sense. -/
instance subtype_mono {X : Type} (P : X → Prop) :
    Mono (show ({x : X // P x} : Type) ⟶ (X : Type) from Subtype.val) := by
  rw [mono_iff_injective]
  exact subtype_val_injective P

/-- The range of the subtype inclusion is exactly the predicate. -/
lemma subtype_range {X : Type} (P : X → Prop) :
    Set.range (Subtype.val : {x : X // P x} → X) = {x | P x} := by
  ext x; simp

/-- The characteristic map of the subtype inclusion recovers the predicate. -/
lemma charMap_subtype_eq {X : Type} (P : X → Prop) :
    PropAsOmega.charMap (show ({x : X // P x} : Type) ⟶ (X : Type) from Subtype.val) = P := by
  ext x
  simp [PropAsOmega.charMap]

/-! ## Predicate ↔ Subobject Correspondence -/

/-- Every predicate P : X → Prop gives a subobject via subtype inclusion.
    This is the "decoding" direction: Ω → Sub(X). -/
def subobject_of_pred {X : Type} (P : X → Prop) :
    ({x : X // P x} : Type) ⟶ (X : Type) :=
  Subtype.val

/-- Every monomorphism m : U → X gives a predicate via the characteristic map.
    This is the "encoding" direction: Sub(X) → Ω. -/
def pred_of_mono {U X : Type} (m : U ⟶ X) : X → Prop :=
  PropAsOmega.charMap m

/-- Round-trip: starting from a predicate, forming the subobject, and
    taking the characteristic map recovers the original predicate. -/
lemma pred_mono_roundtrip {X : Type} (P : X → Prop) :
    pred_of_mono (subobject_of_pred P) = P :=
  charMap_subtype_eq P

/-! ## Logical Operations as Categorical Operations -/

/-- Conjunction of predicates corresponds to intersection of subobjects. -/
lemma conj_pred_eq_inter {X : Type} (P Q : X → Prop) :
    (fun x => P x ∧ Q x) = (fun x => x ∈ {x | P x} ∩ {x | Q x}) := by
  ext x; simp

/-- Disjunction of predicates corresponds to union of subobjects. -/
lemma disj_pred_eq_union {X : Type} (P Q : X → Prop) :
    (fun x => P x ∨ Q x) = (fun x => x ∈ {x | P x} ∪ {x | Q x}) := by
  ext x; simp

/-- Negation of predicates corresponds to complement. -/
lemma neg_pred_eq_compl {X : Type} (P : X → Prop) :
    (fun x => ¬ P x) = (fun x => x ∈ {x | P x}ᶜ) := by
  ext x; simp

/-- Universal quantification over fibers corresponds to
    the internal ∀ in the topos. -/
lemma forall_fiber {X Y : Type} (f : X → Y) (P : X → Prop) :
    (fun y => ∀ x, f x = y → P x) =
    (fun y => ∀ x ∈ f ⁻¹' {y}, P x) := by
  ext y; simp [Set.mem_preimage]

/-- Existential quantification over fibers corresponds to
    the internal ∃ in the topos (image factorization). -/
lemma exists_fiber {X Y : Type} (f : X → Y) (P : X → Prop) :
    (fun y => ∃ x, f x = y ∧ P x) =
    (fun y => ∃ x ∈ f ⁻¹' {y}, P x) := by
  ext y; simp [Set.mem_preimage]

end Caramello.InternalLogic
