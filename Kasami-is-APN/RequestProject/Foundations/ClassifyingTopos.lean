/-
# Layer 14: Classifying Toposes — The Universal Property

Given a geometric theory T, the **classifying topos** is the sheaf topos
Sh(C_T, J_T). Its universal property says that models of T in Set are
in natural bijection with "points" of the classifying topos.

## Mathematical Content

For a propositional geometric theory T over atoms α:

1. **Frame homomorphisms**: A frame homomorphism from the Lindenbaum–Tarski
   algebra L_T to Prop (= Ω) is a map preserving ⊤, ⊥, ∧, ∨, and ⋁ᵢ.

2. **Models = Frame homomorphisms**: A model v of T (a valuation α → Prop
   satisfying all axioms) extends uniquely to a frame homomorphism L_T → Ω.
   This is the **Caramello correspondence** for the topos of sets.

3. **The generic model**: In the classifying topos, there is a "generic" or
   "universal" model — the tautological evaluation that sends each formula
   to its equivalence class. Every concrete model factors through it.

4. **Points**: A point of the classifying topos is a geometric morphism
   Set → Sh(C_T, J_T). For propositional theories, these correspond
   exactly to models of T.

5. **Flat functors**: A functor from C_T to Set is "flat" if it preserves
   finite limits. Flat functors on the syntactic category correspond to
   models of T (Diaconescu's theorem).

## Connection to Caramello's Program

This is the keystone: the classifying topos mediates between
- the syntactic side (formulas, proofs, derivability) and
- the semantic side (models, truth, satisfaction).

Caramello's bridge technique (Layer 16) exploits the fact that
Morita-equivalent theories (Layer 15) have equivalent classifying
toposes, so topos-theoretic invariants transfer between theories.

## DAG Structure (depends on Layers 10, 12, 13)

```
  classifying_universal_property (★)
       |
  model_to_frameHom ←→ frameHom_to_model
       |
  evalQuotient_preserves_iSup ←── evalQuotient_preserves_inf
       |
  FrameHomLT (definition) ←── LindenbaumTarski (Layer 12)
       |
  genericModel ←── SheafCondition (Layer 13)
       |
  Derivable, GeomFormula (Layers 10, 12)
```
-/
import Mathlib
import RequestProject.Foundations.SyntacticSite

namespace Caramello.ClassifyingTopos

open GeometricLogic SyntacticCategory SyntacticSite

/-! ## Section 1: Frame Homomorphisms on the Lindenbaum–Tarski Algebra

A frame homomorphism from L_T to Prop preserves ⊤, ∧, and arbitrary ∨.
Since L_T is a bounded distributive lattice (Layer 12), this captures
the geometric content of T.
-/

/-- A frame homomorphism from the Lindenbaum–Tarski algebra of T to Prop.
    This is a function on formulas that:
    1. Respects T-equivalence (descends to the quotient)
    2. Preserves ⊤ (top)
    3. Preserves ∧ (binary meets = conjunction)
    4. Preserves ∨ (binary joins = disjunction)
    5. Preserves ⋁ᵢ (infinitary joins = infinitary disjunction)
    6. Preserves ⊥ (bottom) -/
structure FrameHomLT {α : Type} (T : GeomTheory α) where
  /-- The underlying function on formulas -/
  toFun : GeomFormula α → Prop
  /-- Respects T-equivalence: T-equivalent formulas get the same value -/
  resp_equiv : ∀ φ ψ, (T ⊢g φ ⟺ ψ) → (toFun φ ↔ toFun ψ)
  /-- Preserves top -/
  pres_top : toFun .top
  /-- Preserves bottom -/
  pres_bot : ¬ toFun .bot
  /-- Preserves conjunction (binary meet) -/
  pres_conj : ∀ φ ψ, toFun (.conj φ ψ) ↔ (toFun φ ∧ toFun ψ)
  /-- Preserves disjunction (binary join) -/
  pres_disj : ∀ φ ψ, toFun (.disj φ ψ) ↔ (toFun φ ∨ toFun ψ)
  /-- Preserves infinitary disjunction -/
  pres_iDisj : ∀ (ι : Type) (f : ι → GeomFormula α),
    toFun (.iDisj ι f) ↔ ∃ i, toFun (f i)
  /-- Preserves existential quantification -/
  pres_ex : ∀ (β : Type) (f : β → GeomFormula α),
    toFun (.ex β f) ↔ ∃ b, toFun (f b)
  /-- Monotone: respects derivability -/
  monotone : ∀ φ ψ, (T ⊢g φ ⟹ ψ) → toFun φ → toFun ψ

/-! ## Section 2: Models Give Frame Homomorphisms

Every model v of T gives a frame homomorphism eval v : L_T → Prop.
This is the "forward direction" of the Caramello correspondence.
-/

/-- Evaluation at a model is a frame homomorphism.
    This is immediate from the recursive definition of eval. -/
def model_to_frameHom {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) : FrameHomLT T where
  toFun := GeomFormula.eval v
  resp_equiv := fun φ ψ ⟨hfwd, hbwd⟩ =>
    ⟨soundness hfwd v hmodel, soundness hbwd v hmodel⟩
  pres_top := trivial
  pres_bot := id
  pres_conj := fun _ _ => Iff.rfl
  pres_disj := fun _ _ => Iff.rfl
  pres_iDisj := fun _ _ => Iff.rfl
  pres_ex := fun _ _ => Iff.rfl
  monotone := fun _ _ hle hφ => soundness hle v hmodel hφ

/-- Frame homomorphisms give models: a frame homomorphism determines
    a valuation by evaluating atoms, and this valuation satisfies T. -/
def frameHom_to_valuation {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) : α → Prop :=
  fun a => h.toFun (.atom a)

/-
The valuation extracted from a frame homomorphism agrees with
    the frame homomorphism on all formulas. This is proved by
    structural induction on formulas.
-/
theorem frameHom_eval_agree {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) (φ : GeomFormula α) :
    GeomFormula.eval (frameHom_to_valuation h) φ ↔ h.toFun φ := by
      induction' φ with a φ ψ ih₁ ih₂ φ ψ ih₁ ih₂ ι f ih₁ β f ih₁;
      all_goals simp_all +decide [ GeomFormula.eval, FrameHomLT.pres_conj, FrameHomLT.pres_disj, FrameHomLT.pres_iDisj, FrameHomLT.pres_ex ];
      · exact h.pres_top;
      · exact h.pres_bot;
      · rfl

/-
A frame homomorphism determines a model of T.
-/
theorem frameHom_to_model {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) : T.Model (frameHom_to_valuation h) := by
      intro s hs;
      intro hv_antecedent
      have h_valid : h.toFun s.antecedent → h.toFun s.consequent := by
        exact h.monotone _ _ ( Derivable.axiom_rule _ hs );
      exact frameHom_eval_agree h s.consequent |>.2 ( h_valid ( frameHom_eval_agree h s.antecedent |>.1 hv_antecedent ) )

/-! ## Section 3: The Caramello Correspondence (★)

Models of T in Set are in natural bijection with frame homomorphisms
from L_T to Ω (= Prop). This is the universal property of the
classifying topos, restricted to the topos of sets.
-/

/-- The round-trip: starting from a model, extracting its frame homomorphism,
    and recovering the valuation, gives back the original valuation. -/
theorem model_frameHom_roundtrip {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    frameHom_to_valuation (model_to_frameHom T v hmodel) = v := by
  ext a; rfl

/-
The round-trip: starting from a frame homomorphism, extracting its
    model, and building a new frame homomorphism, agrees on all formulas.
-/
theorem frameHom_model_roundtrip {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) (φ : GeomFormula α) :
    (model_to_frameHom T (frameHom_to_valuation h)
      (frameHom_to_model h)).toFun φ ↔ h.toFun φ := by
        convert frameHom_eval_agree h φ using 1

/-
**The Caramello Correspondence (★)**: There is a natural bijection
    between models of T and frame homomorphisms L_T → Ω.

    Forward: v ↦ eval v
    Backward: h ↦ (a ↦ h(atom a))

    This is the universal property of the classifying topos for Set.
-/
theorem classifying_universal_property {α : Type} (T : GeomTheory α) :
    -- A valuation is a model iff its evaluation is a frame homomorphism,
    -- and every frame homomorphism arises this way.
    ∀ v : α → Prop, T.Model v ↔
      ∃ h : FrameHomLT T, frameHom_to_valuation h = v := by
        intro v;
        constructor;
        · exact fun h => ⟨ model_to_frameHom T v h, model_frameHom_roundtrip v h ⟩;
        · rintro ⟨ h, rfl ⟩ ; exact frameHom_to_model h;

/-! ## Section 4: The Generic Model

The "generic model" or "universal model" of T lives not in Set but
in the classifying topos itself. In our propositional setting, it
is the tautological interpretation that sends each atom to the
derivability predicate "T ⊢ — ⟹ atom a".
-/

/-- The generic model of T: sends each atom a to the predicate
    φ ↦ (T ⊢ φ ⟹ atom a) on the syntactic category.
    This is a "model in the classifying topos". -/
def genericModel {α : Type} (T : GeomTheory α) :
    α → (GeomFormula α → Prop) :=
  fun a φ => T ⊢g φ ⟹ .atom a

/-- Each component of the generic model is a sheaf
    (by the subcanonical property, Layer 13). -/
theorem genericModel_sheaf {α : Type} (T : GeomTheory α) (a : α) :
    SheafCondition T (genericModel T a) :=
  subcanonical_syntactic T (.atom a)

/-- The generic model "classifies" concrete models: evaluating
    the generic model at a point (= concrete model v) recovers
    the truth value of atoms in v. -/
theorem genericModel_classifies {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) (a : α) :
    (∀ φ, genericModel T a φ → φ.eval v → v a) :=
  fun _φ hder hφ => soundness hder v hmodel hφ

/-! ## Section 5: Points of the Classifying Topos

A "point" of the classifying topos is a frame homomorphism L_T → Prop.
The space of points is thus exactly the space of models of T.

For a propositional theory, the "enough points" property says:
if T ⊢ φ ⟹ ψ fails, there exists a model separating them.
This is completeness of geometric logic (dual to soundness).
-/

/-- A point of the classifying topos of T. -/
abbrev ClassifyingPoint {α : Type} (T : GeomTheory α) := FrameHomLT T

/-- Every model gives a point. -/
def modelToPoint {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) : ClassifyingPoint T :=
  model_to_frameHom T v hmodel

/-- Every point gives a model. -/
def pointToModel {α : Type} {T : GeomTheory α}
    (p : ClassifyingPoint T) : α → Prop :=
  frameHom_to_valuation p

/-- The model extracted from a point is indeed a model of T. -/
theorem pointToModel_isModel {α : Type} {T : GeomTheory α}
    (p : ClassifyingPoint T) : T.Model (pointToModel p) :=
  frameHom_to_model p

/-! ## Section 6: Evaluation Preserves Frame Operations

These lemmas verify that eval v : L_T → Prop preserves all the
relevant frame operations, establishing that it is truly a frame
homomorphism. They are the building blocks for the Caramello correspondence.
-/

/-- Evaluation preserves ⊤. -/
lemma eval_preserves_top {α : Type} (v : α → Prop) :
    GeomFormula.eval v .top = True := rfl

/-- Evaluation preserves ⊥. -/
lemma eval_preserves_bot {α : Type} (v : α → Prop) :
    GeomFormula.eval v .bot = False := rfl

/-- Evaluation preserves conjunction. -/
lemma eval_preserves_conj {α : Type} (v : α → Prop)
    (φ ψ : GeomFormula α) :
    GeomFormula.eval v (.conj φ ψ) = (φ.eval v ∧ ψ.eval v) := rfl

/-- Evaluation preserves disjunction. -/
lemma eval_preserves_disj {α : Type} (v : α → Prop)
    (φ ψ : GeomFormula α) :
    GeomFormula.eval v (.disj φ ψ) = (φ.eval v ∨ ψ.eval v) := rfl

/-- Evaluation preserves infinitary disjunction. -/
lemma eval_preserves_iDisj {α : Type} (v : α → Prop)
    (ι : Type) (f : ι → GeomFormula α) :
    GeomFormula.eval v (.iDisj ι f) = (∃ i, (f i).eval v) := rfl

/-- Evaluation preserves existentials. -/
lemma eval_preserves_ex {α : Type} (v : α → Prop)
    (β : Type) (f : β → GeomFormula α) :
    GeomFormula.eval v (.ex β f) = (∃ b, (f b).eval v) := rfl

/-! ## Section 7: Flat Functors and Diaconescu's Theorem (Statement)

Diaconescu's theorem: for a small category C with a Grothendieck
topology J, geometric morphisms Set → Sh(C, J) correspond to
J-continuous flat functors C → Set.

For the syntactic category C_T with syntactic topology J_T,
this specializes to: models of T ↔ flat functors C_T → Set.

We define flat functors on the syntactic preorder and state
this correspondence.
-/

/-- A flat functor on the syntactic preorder of T is a Prop-valued
    assignment that preserves finite limits (= ⊤ and ∧ in the preorder).
    In the thin/preorder case, this is a filter-like condition. -/
structure FlatFunctor {α : Type} (T : GeomTheory α) where
  /-- The underlying assignment -/
  toFun : GeomFormula α → Prop
  /-- Respects T-equivalence -/
  resp_equiv : ∀ φ ψ, (T ⊢g φ ⟺ ψ) → (toFun φ ↔ toFun ψ)
  /-- Preserves terminal (⊤ maps to True) -/
  pres_top : toFun .top
  /-- Preserves binary products (∧ maps to ∧) -/
  pres_conj : ∀ φ ψ, toFun (.conj φ ψ) ↔ (toFun φ ∧ toFun ψ)
  /-- Monotone: preserves the order -/
  mono : ∀ φ ψ, (T ⊢g φ ⟹ ψ) → toFun φ → toFun ψ

/-- A J_T-continuous flat functor additionally respects covers. -/
structure ContinuousFlatFunctor {α : Type} (T : GeomTheory α)
    extends FlatFunctor T where
  /-- Continuity: respects covering families (local character) -/
  pres_covers : ∀ (φ : GeomFormula α) (ι : Type) (ψ : ι → GeomFormula α),
    Covers T φ ι ψ → toFun φ → ∃ i, toFun (ψ i)

/-- Every model gives a continuous flat functor via evaluation. -/
def model_to_continuousFlatFunctor {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) : ContinuousFlatFunctor T where
  toFun := GeomFormula.eval v
  resp_equiv := fun φ ψ ⟨hfwd, hbwd⟩ =>
    ⟨soundness hfwd v hmodel, soundness hbwd v hmodel⟩
  pres_top := trivial
  pres_conj := fun _ _ => Iff.rfl
  mono := fun _ _ hle hφ => soundness hle v hmodel hφ
  pres_covers := fun _ _ _ hcov hφ => covers_sound hcov v hmodel hφ

/-- A continuous flat functor gives a model: extract the valuation
    from atoms and verify the axioms are satisfied. -/
def continuousFlatFunctor_to_valuation {α : Type} {T : GeomTheory α}
    (F : ContinuousFlatFunctor T) : α → Prop :=
  fun a => F.toFun (.atom a)

/-
The valuation from a continuous flat functor agrees with F on all formulas.
    This is the key lemma for the Diaconescu correspondence.
-/
theorem continuousFlat_eval_agree {α : Type} {T : GeomTheory α}
    (F : ContinuousFlatFunctor T) (φ : GeomFormula α) :
    GeomFormula.eval (continuousFlatFunctor_to_valuation F) φ ↔ F.toFun φ := by
      induction' φ with φ ψ ihφ ihψ;
      all_goals simp_all +decide [ GeomFormula.eval ];
      exact F.pres_top;
      have := F.pres_covers .bot ( Empty ) ( fun e => e.elim ) ?_ <;> simp_all +decide [ covers_bot ];
      · rfl;
      · rw [ F.pres_conj ];
      · rename_i φ ψ hφ hψ;
        constructor;
        · rintro ( h | h );
          · exact F.mono _ _ ( Derivable.disj_intro_left φ ψ ) h;
          · exact F.mono _ _ ( Derivable.disj_intro_right _ _ ) h;
        · have := F.pres_covers ( φ.disj ψ ) Bool ( fun b => Bool.rec ψ φ b ) ?_ <;> simp_all +decide [ covers_of_binaryCover, binaryCover_of_disj ];
          grind +revert;
      · constructor <;> intro h;
        · convert F.mono _ _ _ h.choose_spec;
          exact Derivable.iDisj_intro _ _ _;
        · exact F.pres_covers _ _ _ ( covers_iDisj T _ _ ) h;
      · constructor <;> intro h;
        · obtain ⟨ b, hb ⟩ := h;
          exact F.mono _ _ ( Derivable.ex_intro _ _ _ ) hb;
        · have := F.pres_covers _ _ _ ( covers_ex T _ _ ) h; aesop;

/-
A continuous flat functor determines a model of T.
    This is the backward direction of Diaconescu's theorem for Set.
-/
theorem continuousFlatFunctor_to_model {α : Type} {T : GeomTheory α}
    (F : ContinuousFlatFunctor T) :
    T.Model (continuousFlatFunctor_to_valuation F) := by
      intro s hs hv;
      convert F.mono s.antecedent s.consequent _ _;
      · exact funext fun x => by simpa using continuousFlat_eval_agree F x;
      · exact?;
      · grind +suggestions

/-! ## Section 8: Soundness and Completeness at the Level of Points

Soundness (Layer 12) says: if T ⊢ φ ⟹ ψ, then φ(v) → ψ(v) for all models v.
Completeness (for propositional theories) is the converse: if φ(v) → ψ(v) for
all models, then T ⊢ φ ⟹ ψ.

We state completeness as a property and prove partial results.
-/

/-- Soundness restated in terms of points: derivability is preserved by
    every point of the classifying topos. -/
theorem derivable_preserved_by_points {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) (hder : T ⊢g φ ⟹ ψ) :
    ∀ p : ClassifyingPoint T, p.toFun φ → p.toFun ψ :=
  fun p => p.monotone φ ψ hder

/-- Validity at all points: φ entails ψ at every point. -/
def ValidAtAllPoints {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) : Prop :=
  ∀ p : ClassifyingPoint T, p.toFun φ → p.toFun ψ

/-- Soundness implies validity at all points. -/
theorem soundness_points {α : Type} (T : GeomTheory α)
    (φ ψ : GeomFormula α) (hder : T ⊢g φ ⟹ ψ) :
    ValidAtAllPoints T φ ψ :=
  derivable_preserved_by_points T φ ψ hder

/-- The "enough points" property: T has enough points if derivability
    is equivalent to validity at all points.
    This is the completeness theorem for propositional geometric logic. -/
def HasEnoughPoints {α : Type} (T : GeomTheory α) : Prop :=
  ∀ φ ψ : GeomFormula α, ValidAtAllPoints T φ ψ → (T ⊢g φ ⟹ ψ)

/-! ## Section 9: Theory Extensions and Conservative Extensions

A theory extension T ⊆ T' is conservative if it doesn't prove new
sequents between formulas of the original language.
-/

/-- T' is an extension of T. -/
def IsExtension {α : Type} (T T' : GeomTheory α) : Prop := T ⊆ T'

/-- T' is a conservative extension of T: every sequent derivable in T'
    between formulas of the original theory is already derivable in T. -/
def IsConservativeExtension {α : Type} (T T' : GeomTheory α) : Prop :=
  IsExtension T T' ∧
  ∀ φ ψ : GeomFormula α, (Derivable T' φ ψ) → (Derivable T φ ψ)

/-- The identity extension is conservative. -/
lemma conservative_refl {α : Type} (T : GeomTheory α) :
    IsConservativeExtension T T :=
  ⟨Set.Subset.rfl, fun _ _ h => h⟩

/-- If T' is a conservative extension of T, then T and T' have the same
    derivable sequents (between formulas in the common language). -/
lemma conservative_iff_derivable {α : Type} {T T' : GeomTheory α}
    (hcons : IsConservativeExtension T T') (φ ψ : GeomFormula α) :
    (Derivable T φ ψ) ↔ (Derivable T' φ ψ) := by
  constructor
  · exact derivable_mono hcons.1
  · exact hcons.2 φ ψ

end Caramello.ClassifyingTopos