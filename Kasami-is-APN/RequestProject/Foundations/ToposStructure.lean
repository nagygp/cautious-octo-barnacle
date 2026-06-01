/-
# Layer 7: Elementary Topos Structure of Type

An elementary topos is a category with:
1. Finite limits
2. Exponentials (cartesian closed)
3. A subobject classifier

We verify all three for `Type`, assembling the results from
earlier layers into a single coherent structure.

## Novel Contribution

This file provides a **verified elementary topos checklist** for Type,
connecting Lean's built-in type theory to the abstract topos axioms.
Each axiom is witnessed by a Mathlib instance or our Layer 1 theorem.

## DAG Structure (depends on Layers 1, 3, 6)

```
    typeIsTopos (★ main result)
         / | \
        /  |  \
  has_finite_limits  has_exponentials  has_subobj_classifier
       |                  |                    |
  (Mathlib)        (MonoidalClosed)     (PropAsOmega.lean)
```

## Proof Shape Classification

| Lemma | Tag | κ |
|-------|-----|---|
| `type_has_finite_limits` | 🧩 atomic | 0 |
| `type_has_finite_colimits` | 🧩 atomic | 0 |
| `type_has_all_limits` | 🧩 atomic | 0 |
| `type_has_all_colimits` | 🧩 atomic | 0 |
| `type_monoidal_closed` | 🧩 atomic | 0 |
| `type_has_classifier` | 🔁 reducible | 1 |
| `typeIsTopos` | 🌌 structural | 2 |
-/
import Mathlib
import RequestProject.Foundations.PropAsOmega

namespace Caramello.ToposStructure

open CategoryTheory CategoryTheory.Limits

/-! ## Section 1: Finite Limit Structure (Topos Axiom 1)

An elementary topos must have all finite limits.
Type has all limits (not just finite ones).
-/

/-- Type has all (small) limits. -/
instance type_has_all_limits : HasLimits (Type) := inferInstance

/-- Type has all (small) colimits. -/
instance type_has_all_colimits : HasColimits (Type) := inferInstance

/-- Type has finite limits (follows from having all limits). -/
instance type_has_finite_limits : HasFiniteLimits (Type) := inferInstance

/-- Type has finite colimits. -/
instance type_has_finite_colimits : HasFiniteColimits (Type) := inferInstance

/-- Type has pullbacks (key building block for finite limits). -/
instance type_has_pullbacks : HasPullbacks (Type) := inferInstance

/-- Type has equalizers. -/
instance type_has_equalizers : HasEqualizers (Type) := inferInstance

/-- Type has a terminal object (PUnit). -/
instance type_has_terminal : HasTerminal (Type) := inferInstance

/-- Type has an initial object (Empty). -/
instance type_has_initial : HasInitial (Type) := inferInstance

/-- Type has binary products. -/
instance type_has_binary_products : HasBinaryProducts (Type) := inferInstance

/-- Type has binary coproducts. -/
instance type_has_binary_coproducts : HasBinaryCoproducts (Type) := inferInstance

/-- Type has images (needed for subobject lattice). -/
instance type_has_images : HasImages (Type) := inferInstance

/-! ## Section 2: Exponential Objects (Topos Axiom 2)

An elementary topos must be cartesian closed: for every object A,
the functor (– × A) has a right adjoint (–)^A (the exponential).
In Type, this is just the function type A → B.
-/

/-- Type is monoidal closed (every object is exponentiable). -/
instance type_monoidal_closed : MonoidalClosed (Type) := inferInstance

/-! ## Section 3: Subobject Classifier (Topos Axiom 3)

Already proved in Layer 1. We re-export and connect.
-/

/-- Type has a subobject classifier, and it is Prop.
    (Re-exported from Layer 1 for the topos structure.) -/
noncomputable def type_has_classifier : Classifier (Type) :=
  PropAsOmega.typesClassifier

/-! ## Section 4: Elementary Topos Verification

All three axioms are now verified. We package them together.
-/

/-- **The Elementary Topos Structure of Type.**

    An elementary topos requires:
    1. Finite limits ✓ (`type_has_finite_limits`)
    2. Cartesian closed ✓ (`type_monoidal_closed`)
    3. Subobject classifier ✓ (`type_has_classifier`)

    This structure witnesses that `Type` satisfies all elementary topos axioms,
    with Lean's `Prop` as the subobject classifier Ω. -/
structure ElementaryToposWitness (C : Type*) [Category C] [MonoidalCategory C] where
  /-- Axiom 1: Finite limits -/
  finLimits : HasFiniteLimits C
  /-- Axiom 2: Cartesian closed (every object exponentiable) -/
  closed : MonoidalClosed C
  /-- Axiom 3: Subobject classifier -/
  classifier : Classifier C

/-- Type is an elementary topos. -/
noncomputable def typeIsTopos : ElementaryToposWitness (Type) where
  finLimits := type_has_finite_limits
  closed := type_monoidal_closed
  classifier := type_has_classifier

/-! ## Section 5: Subobject Lattice in the Topos

Using the full topos structure, we can show that subobjects
form a lattice. For Type, this lattice is isomorphic to Set X.
-/

/-- Subobjects of X in Type form a lattice. -/
noncomputable instance subobject_lattice (X : Type) : Lattice (Subobject X) :=
  inferInstance

/-- Subobjects form a partial order. -/
instance subobject_partial_order (X : Type) : PartialOrder (Subobject X) :=
  inferInstance

end Caramello.ToposStructure
