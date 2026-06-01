/-
# Layer 10: Geometric Logic — The Language of Toposes

Geometric logic is the fragment of first-order logic preserved by
inverse image functors of geometric morphisms. It uses only:
  ⊤, ⊥, ∧, ∨ (including infinitary), ∃

NO negation, NO universal quantification, NO implication.

This is the "lingua franca" of toposes: a geometric sentence true in
one topos can be transferred to any other topos connected by a
geometric morphism. This is the formal basis of Caramello's bridge technique.

## Novel Contribution

We formalize geometric formulas as an inductive type and prove that
their semantics in the topos `Type` (via Prop) uses only frame operations.
We also prove functoriality of atom-mapping and monotonicity of evaluation.

This connects:
- Layer 1 (Prop = Ω) — semantics target
- Layer 6 (Frame structure) — algebraic content
- Layer 8 (Geometric morphisms) — preservation theorems

## DAG Structure

```
    geom_eval_congr (★)
         |
    geom_eval_monotone
         |
    eval_mapAtoms ←── mapAtoms_comp ←── mapAtoms_id
         |
    eval lemmas (atomic, simp)
         |
    GeomFormula.eval ←── GeomFormula (inductive)
```

## Proof Shape Classification

| Lemma | Tag | κ |
|-------|-----|---|
| `eval_*` (7 simp lemmas) | 🧩 atomic | 0 |
| `eval_mapAtoms` | 🔁 reducible | 1 |
| `mapAtoms_id` | 🔁 reducible | 1 |
| `mapAtoms_comp` | 🔁 reducible | 1 |
| `geom_eval_monotone` | 🌌 structural | 2 |
| `geom_eval_congr` | 🌿 local-glue | 2 |
| `model_atomHolds_iff` | 🌿 local-glue | 2 |
-/
import Mathlib
import RequestProject.Foundations.HeytingOmega

namespace Caramello.GeometricLogic

/-! ## Section 1: Geometric Formulas (Inductive Definition)

A geometric formula over a set of "atomic propositions" (indexed by α)
is built from ⊤, ⊥, finite ∧, arbitrary ∨, and ∃.

We model this as propositions built from atoms using geometric connectives.
For simplicity, we work over Prop directly (since Prop = Ω in our topos).
-/

/-- A geometric formula over atomic propositions indexed by α.
    These are the formulas preserved by geometric morphisms. -/
inductive GeomFormula (α : Type) where
  /-- Truth: always holds -/
  | top : GeomFormula α
  /-- Falsity: never holds -/
  | bot : GeomFormula α
  /-- Atomic proposition -/
  | atom : α → GeomFormula α
  /-- Finite conjunction -/
  | conj : GeomFormula α → GeomFormula α → GeomFormula α
  /-- Finite disjunction -/
  | disj : GeomFormula α → GeomFormula α → GeomFormula α
  /-- Infinitary disjunction (indexed by a type) -/
  | iDisj : (ι : Type) → (ι → GeomFormula α) → GeomFormula α
  /-- Existential quantification (geometric ∃) -/
  | ex : (β : Type) → (β → GeomFormula α) → GeomFormula α

/-- Evaluate a geometric formula given a valuation of atoms.
    The semantics maps into Prop (= Ω, the subobject classifier). -/
def GeomFormula.eval {α : Type} (v : α → Prop) : GeomFormula α → Prop
  | .top => True
  | .bot => False
  | .atom a => v a
  | .conj φ ψ => φ.eval v ∧ ψ.eval v
  | .disj φ ψ => φ.eval v ∨ ψ.eval v
  | .iDisj ι f => ∃ i : ι, (f i).eval v
  | .ex β f => ∃ b : β, (f b).eval v

/-! ## Section 2: Semantics Verification (Atomic — all `rfl`) -/

@[simp] lemma eval_top {α : Type} (v : α → Prop) :
    GeomFormula.eval v .top = True := rfl

@[simp] lemma eval_bot {α : Type} (v : α → Prop) :
    GeomFormula.eval v .bot = False := rfl

@[simp] lemma eval_atom {α : Type} (v : α → Prop) (a : α) :
    GeomFormula.eval v (.atom a) = v a := rfl

@[simp] lemma eval_conj {α : Type} (v : α → Prop) (φ ψ : GeomFormula α) :
    GeomFormula.eval v (.conj φ ψ) = (φ.eval v ∧ ψ.eval v) := rfl

@[simp] lemma eval_disj {α : Type} (v : α → Prop) (φ ψ : GeomFormula α) :
    GeomFormula.eval v (.disj φ ψ) = (φ.eval v ∨ ψ.eval v) := rfl

@[simp] lemma eval_iDisj {α : Type} (v : α → Prop) (ι : Type)
    (f : ι → GeomFormula α) :
    GeomFormula.eval v (.iDisj ι f) = (∃ i, (f i).eval v) := rfl

@[simp] lemma eval_ex {α : Type} (v : α → Prop) (β : Type)
    (f : β → GeomFormula α) :
    GeomFormula.eval v (.ex β f) = (∃ b, (f b).eval v) := rfl

/-! ## Section 3: Map Atoms — Functorial Action on Formulas

Geometric formulas are functorial in their atoms: a function f : α → β
induces a map GeomFormula α → GeomFormula β. This functoriality is
key to understanding how geometric theories transform under reinterpretation.
-/

/-- Map the atoms of a geometric formula via a function f : α → β.
    This is the functorial action on formulas. -/
def GeomFormula.mapAtoms {α β : Type} (f : α → β) : GeomFormula α → GeomFormula β
  | .top => .top
  | .bot => .bot
  | .atom a => .atom (f a)
  | .conj φ ψ => .conj (φ.mapAtoms f) (ψ.mapAtoms f)
  | .disj φ ψ => .disj (φ.mapAtoms f) (ψ.mapAtoms f)
  | .iDisj ι g => .iDisj ι (fun i => (g i).mapAtoms f)
  | .ex β' g => .ex β' (fun b => (g b).mapAtoms f)

/-- Evaluation commutes with atom mapping:
    evaluating a mapped formula = evaluating the original with composed valuation.
    ★ This is the formal expression of "reinterpretation preserves geometric truth". -/
lemma eval_mapAtoms {α β : Type} (φ : GeomFormula α)
    (f : α → β) (v : β → Prop) :
    (φ.mapAtoms f).eval v = φ.eval (v ∘ f) := by
  induction φ with
  | top => simp [GeomFormula.mapAtoms]
  | bot => simp [GeomFormula.mapAtoms]
  | atom a => simp [GeomFormula.mapAtoms]
  | conj φ ψ ihφ ihψ => simp [GeomFormula.mapAtoms, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [GeomFormula.mapAtoms, ihφ, ihψ]
  | iDisj ι g ih => simp [GeomFormula.mapAtoms, ih]
  | ex β' g ih => simp [GeomFormula.mapAtoms, ih]

/-- Mapping atoms by id is identity (functor identity law). -/
lemma mapAtoms_id {α : Type} (φ : GeomFormula α) :
    φ.mapAtoms id = φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | atom _ => rfl
  | conj _ _ ih1 ih2 => simp [GeomFormula.mapAtoms, ih1, ih2]
  | disj _ _ ih1 ih2 => simp [GeomFormula.mapAtoms, ih1, ih2]
  | iDisj _ _ ih => simp [GeomFormula.mapAtoms]; ext i; exact ih i
  | ex _ _ ih => simp [GeomFormula.mapAtoms]; ext b; exact ih b

/-- Mapping atoms by g ∘ f = mapping by f then by g (functor composition law). -/
lemma mapAtoms_comp {α β γ : Type} (φ : GeomFormula α) (f : α → β) (g : β → γ) :
    φ.mapAtoms (g ∘ f) = (φ.mapAtoms f).mapAtoms g := by
  induction φ with
  | top => rfl
  | bot => rfl
  | atom _ => rfl
  | conj _ _ ih1 ih2 => simp [GeomFormula.mapAtoms, ih1, ih2]
  | disj _ _ ih1 ih2 => simp [GeomFormula.mapAtoms, ih1, ih2]
  | iDisj _ _ ih => simp [GeomFormula.mapAtoms]; ext i; exact ih i
  | ex _ _ ih => simp [GeomFormula.mapAtoms]; ext b; exact ih b

/-! ## Section 4: Geometric Sequents and Theories

A geometric sequent is a pair (φ, ψ) of geometric formulas,
written φ ⊢ ψ, meaning "φ entails ψ in geometric logic".
A geometric theory is a collection of geometric sequents.
-/

/-- A geometric sequent: an entailment between geometric formulas. -/
structure GeomSequent (α : Type) where
  /-- The antecedent -/
  antecedent : GeomFormula α
  /-- The consequent -/
  consequent : GeomFormula α

/-- A geometric sequent is valid under valuation v if
    the antecedent implies the consequent. -/
def GeomSequent.valid {α : Type} (s : GeomSequent α) (v : α → Prop) : Prop :=
  s.antecedent.eval v → s.consequent.eval v

/-- A geometric theory is a set of geometric sequents.
    Using `abbrev` so that `Set` instances (membership, singleton, etc.) are inherited. -/
abbrev GeomTheory (α : Type) := Set (GeomSequent α)

/-- A model of a geometric theory: a valuation satisfying all sequents. -/
def GeomTheory.Model {α : Type} (T : GeomTheory α) (v : α → Prop) : Prop :=
  ∀ s ∈ T, s.valid v

/-! ## Section 5: The Key Insight — Geometric = Frame-Theoretic

★ **Novel observation formalized**: The evaluation of geometric formulas
uses ONLY the frame operations on Prop:
- `True` = ⊤ (top of frame)
- `False` = ⊥ (bot of frame)
- `∧` = ⊓ (binary meet)
- `∨` = ⊔ (binary join)
- `∃` = ⊔ᵢ (arbitrary join)

This is precisely why geometric formulas are preserved by
frame homomorphisms, which are the Ω-components of geometric morphisms.
-/

/-- Geometric conjunction = frame meet on Prop. -/
lemma eval_conj_eq_inf {α : Type} (v : α → Prop) (φ ψ : GeomFormula α) :
    (φ.eval v ∧ ψ.eval v) ↔ (φ.eval v ⊓ ψ.eval v) := Iff.rfl

/-- Geometric disjunction = frame join on Prop. -/
lemma eval_disj_eq_sup {α : Type} (v : α → Prop) (φ ψ : GeomFormula α) :
    (φ.eval v ∨ ψ.eval v) ↔ (φ.eval v ⊔ ψ.eval v) := Iff.rfl

/-- Geometric truth = frame top. -/
lemma eval_top_eq_top {α : Type} (v : α → Prop) :
    GeomFormula.eval v .top = (⊤ : Prop) := rfl

/-- Geometric falsity = frame bottom. -/
lemma eval_bot_eq_bot {α : Type} (v : α → Prop) :
    GeomFormula.eval v .bot = (⊥ : Prop) := rfl

/-! ## Section 6: Examples of Geometric Theories -/

/-- The empty theory (no axioms). Every valuation is a model. -/
def theoryEmpty (α : Type) : GeomTheory α := ∅

/-- Every valuation models the empty theory. -/
lemma model_empty {α : Type} (v : α → Prop) :
    (theoryEmpty α).Model v := by
  intro s hs; exact absurd hs id

/-- Theory asserting that some atom holds: ⊤ ⊢ a. -/
def theoryAtomHolds {α : Type} (a : α) : GeomTheory α :=
  {⟨.top, .atom a⟩}

/-- A model of `theoryAtomHolds a` is exactly a valuation where `v a` holds. -/
lemma model_atomHolds_iff {α : Type} (a : α) (v : α → Prop) :
    (theoryAtomHolds a).Model v ↔ v a := by
  unfold GeomTheory.Model theoryAtomHolds
  constructor
  · intro h
    have := h ⟨.top, .atom a⟩ rfl
    simpa [GeomSequent.valid, GeomFormula.eval] using this
  · intro ha s hs
    simp at hs; subst hs
    intro _; exact ha

/-! ## Section 7: Monotonicity and Invariance (★ Key Theorems)

These results formalize the core property of geometric logic:
it is monotone with respect to atom valuations, and invariant
under logical equivalence of atoms.
-/

/-- A monotone map between Prop-valued predicates that preserves
    the atom valuations preserves the truth of geometric formulas.
    ★ This is the "preservation theorem" for geometric logic. -/
lemma geom_eval_monotone {α : Type} (v w : α → Prop)
    (h : ∀ a, v a → w a)
    (φ : GeomFormula α) (hφ : φ.eval v) : φ.eval w := by
  induction φ with
  | top => trivial
  | bot => exact absurd hφ id
  | atom a => exact h a hφ
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ hφ.1, ihψ hφ.2⟩
  | disj φ ψ ihφ ihψ =>
    exact hφ.elim (Or.inl ∘ ihφ) (Or.inr ∘ ihψ)
  | iDisj ι f ih =>
    obtain ⟨i, hi⟩ := hφ; exact ⟨i, ih i hi⟩
  | ex β f ih =>
    obtain ⟨b, hb⟩ := hφ; exact ⟨b, ih b hb⟩

/-- Geometric formulas respect logical equivalence of atoms.
    This is the invariance property: if two valuations agree on atoms,
    they agree on all geometric formulas. -/
lemma geom_eval_congr {α : Type} (v w : α → Prop)
    (h : ∀ a, v a ↔ w a)
    (φ : GeomFormula α) : φ.eval v ↔ φ.eval w :=
  ⟨geom_eval_monotone v w (fun a => (h a).mp) φ,
   geom_eval_monotone w v (fun a => (h a).mpr) φ⟩

/-- If a geometric theory T has a model, then any theory T' ⊆ T also has a model
    (with the same valuation). -/
lemma model_of_subset {α : Type} (T T' : GeomTheory α) (h : T' ⊆ T)
    (v : α → Prop) (hv : T.Model v) : T'.Model v :=
  fun s hs => hv s (h hs)

end Caramello.GeometricLogic
