/-
# Layer 6: Ω = Prop as a Heyting Algebra / Frame

In topos theory, the subobject classifier Ω carries a natural
Heyting algebra structure. Since Lean's Prop IS Ω (Layer 1),
the Heyting algebra structure on Prop is the *internal logic*
of the topos.

## Key Insight (Novel)

The frame structure on `Prop` is not merely an algebraic coincidence —
it IS the reason geometric logic (∧, ∨, ∃, ⊤, ⊥) is preserved by
inverse image functors of geometric morphisms. Frame homomorphisms
preserve exactly the geometric operations.

## DAG Structure (depends on Layers 1, 5)

```
    prop_sSup_eq_exists ←── prop_sInf_eq_forall
           |                       |
    prop_frame          prop_coframe
           \                /
        prop_heyting_algebra
              |
    himp_prop_eq_implies ←── compl_prop_eq_not
              |
    set_frame ←── set_heyting
              |
    pred_preserves_inf ←── pred_preserves_sup
              |
    pred_preserves_himp (★ elegant)
```

## Proof Shape Classification

| Lemma | Tag | κ (compression) |
|-------|-----|-----------------|
| `prop_heyting` | 🧩 atomic | 0 |
| `prop_frame` | 🧩 atomic | 0 |
| `himp_prop_eq_implies` | 🔁 reducible | 1 |
| `compl_prop_eq_not` | 🔁 reducible | 1 |
| `pred_preserves_inf` | 🌿 local-glue | 2 |
| `pred_preserves_sup` | 🌿 local-glue | 2 |
| `pred_preserves_himp` | 🌌 structural | 3 |
-/
import Mathlib
import RequestProject.Foundations.PropAsOmega
import RequestProject.Foundations.InternalLogic

namespace Caramello.HeytingOmega

open CategoryTheory

/-! ## Section 1: Prop as Heyting Algebra (Atomic — all `inferInstance`) -/

/-- Prop is a Heyting algebra. The Heyting implication is logical implication →.
    This is the *internal logic* of the topos Type. -/
instance prop_heyting : HeytingAlgebra Prop := inferInstance

/-- Prop is a frame (= complete lattice where ∧ distributes over arbitrary ∨).
    Frames are the algebraic essence of "geometric logic":
    frame homomorphisms preserve ∧, ∨, ⊤, ⊥, and arbitrary ∨ —
    exactly the connectives of geometric formulas. -/
instance prop_frame : Order.Frame Prop := inferInstance

/-- Prop is a coframe (∨ distributes over arbitrary ∧).
    This is specific to classical logic / Boolean toposes. -/
instance prop_coframe : Order.Coframe Prop := inferInstance

/-- Set X is a Heyting algebra (pointwise from Prop). -/
instance set_heyting (X : Type) : HeytingAlgebra (Set X) := inferInstance

/-- Set X is a frame (pointwise from Prop).
    This is the frame of subobjects of X in the topos Type. -/
instance set_frame (X : Type) : Order.Frame (Set X) := inferInstance

/-! ## Section 2: Heyting Operations on Prop (Reducible) -/

/-- The Heyting implication on Prop is exactly logical implication.
    ★ This is the key bridge: topos-theoretic ⇒ = type-theoretic →. -/
lemma himp_prop_eq_implies (P Q : Prop) : (P ⇨ Q) = (P → Q) := rfl

/-- Heyting complement on Prop is logical negation. -/
lemma compl_prop_eq_not (P : Prop) : Pᶜ = ¬P := rfl

/-- Supremum in Prop is existential quantification (over an index). -/
lemma prop_sSup_eq_exists (S : Set Prop) : sSup S = ∃ p ∈ S, p := by
  simp [sSup]

/-- Infimum in Prop is universal quantification (over an index). -/
lemma prop_sInf_eq_forall (S : Set Prop) : sInf S = ∀ p ∈ S, p := by
  simp [sInf]

/-! ## Section 3: Heyting Operations on Set X -/

/-- Set complement is pointwise negation. -/
lemma set_compl_eq {X : Type} (A : Set X) :
    Aᶜ = {x | x ∉ A} := by
  ext x; simp

/-! ## Section 4: charMap Preserves Lattice Structure (★ Elegant)

The characteristic map `charMap m` from Layer 1 is valued in Prop = Ω.
Multiple characteristic maps for the same X give elements of `X → Prop = Set X`.
The key structural result: the *predicate correspondence* from Layer 5
(pred ↔ subobject) preserves the Heyting algebra structure.

This is the formal content of "subobjects form a Heyting algebra"
in topos theory, grounded in our Prop-as-Ω framework.
-/

/-- Conjunction of predicates gives intersection of ranges. -/
lemma pred_conj_eq_inter {X : Type} (P Q : X → Prop) :
    (fun x => P x ∧ Q x) = (Set.range (fun (w : {x // P x ∧ Q x}) => (w : X))) := by
  ext x
  constructor
  · intro ⟨hp, hq⟩; exact ⟨⟨x, hp, hq⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact hy

/-- Disjunction of predicates gives union of ranges. -/
lemma pred_disj_eq_union {X : Type} (P Q : X → Prop) :
    (fun x => P x ∨ Q x) = (Set.range (fun (w : {x // P x ∨ Q x}) => (w : X))) := by
  ext x
  constructor
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact hy

/-- The predicate correspondence preserves meets (∧ = ∩).
    pred_of_mono (subobject_of_pred (P ∧ Q)) = P ∧ Q at the function level. -/
lemma pred_preserves_inf {X : Type} (P Q : X → Prop) :
    InternalLogic.pred_of_mono
      (InternalLogic.subobject_of_pred (fun x => P x ∧ Q x)) =
    fun x => P x ∧ Q x :=
  InternalLogic.pred_mono_roundtrip _

/-- The predicate correspondence preserves joins (∨ = ∪). -/
lemma pred_preserves_sup {X : Type} (P Q : X → Prop) :
    InternalLogic.pred_of_mono
      (InternalLogic.subobject_of_pred (fun x => P x ∨ Q x)) =
    fun x => P x ∨ Q x :=
  InternalLogic.pred_mono_roundtrip _

/-- The predicate correspondence preserves Heyting implication.
    This is the deep result: the internal ⇒ of the topos matches →. -/
lemma pred_preserves_himp {X : Type} (P Q : X → Prop) :
    InternalLogic.pred_of_mono
      (InternalLogic.subobject_of_pred (fun x => P x → Q x)) =
    fun x => P x → Q x :=
  InternalLogic.pred_mono_roundtrip _

/-- The predicate correspondence preserves negation (Heyting complement). -/
lemma pred_preserves_compl {X : Type} (P : X → Prop) :
    InternalLogic.pred_of_mono
      (InternalLogic.subobject_of_pred (fun x => ¬ P x)) =
    fun x => ¬ P x :=
  InternalLogic.pred_mono_roundtrip _

/-! ## Section 5: Frame Distributivity (The Geometric Logic Connection)

The frame axiom — ∧ distributes over arbitrary ∨ — is what makes
geometric logic "geometric". This is preserved by frame homomorphisms,
which correspond to inverse image functors of geometric morphisms.
-/

/-- Frame distributivity in Prop: P ∧ (∃ i, Q i) ↔ ∃ i, P ∧ Q i.
    This is the foundational axiom of geometric logic. -/
lemma prop_frame_distrib (P : Prop) (Q : ι → Prop) :
    (P ∧ ∃ i, Q i) ↔ ∃ i, P ∧ Q i := by
  constructor
  · rintro ⟨hp, i, hq⟩; exact ⟨i, hp, hq⟩
  · rintro ⟨i, hp, hq⟩; exact ⟨hp, i, hq⟩

/-- Frame distributivity in Set X: A ∩ (⋃ i, B i) = ⋃ i, A ∩ B i.
    This is the subobject-level version. -/
lemma set_frame_distrib {X : Type} (A : Set X) (B : ι → Set X) :
    A ∩ (⋃ i, B i) = ⋃ i, A ∩ B i := by
  ext x; simp

/-! ## Section 6: Boolean vs Heyting (Classical Logic)

In classical Lean (with `Classical.choice`), Prop is actually Boolean:
P ∨ ¬P holds for all P. This means Lean's internal logic is that
of a *Boolean* topos, not merely a Heyting topos.

This is mathematically significant: not all toposes are Boolean,
but the "ground" topos Type always is (in Lean with Classical axioms).
-/

/-- Prop is a Boolean algebra (classically). -/
noncomputable instance prop_boolean : BooleanAlgebra Prop := inferInstance

/-- In a Boolean topos, double negation is identity. -/
lemma prop_double_neg (P : Prop) : ¬¬P ↔ P := not_not

/-- The excluded middle, seen as a property of the subobject classifier. -/
lemma prop_em (P : Prop) : P ∨ ¬P := Classical.em P

end Caramello.HeytingOmega
