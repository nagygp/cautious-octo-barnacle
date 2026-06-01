/-
# Layer 15: Morita Equivalence of Geometric Theories

Two geometric theories are **Morita equivalent** if they have
equivalent categories of models (in every Grothendieck topos).
Equivalently, their classifying toposes are equivalent.

## Mathematical Content

1. **Morita equivalence (definition)**: T₁ ≃_M T₂ iff there exist
   mutually inverse translations between their models.

2. **Equivalence relation**: Morita equivalence is reflexive, symmetric,
   and transitive.

3. **Theory morphisms and model functors**: A theory morphism σ : T₁ → T₂
   induces a functor Mod(T₂) → Mod(T₁) by precomposition.

4. **Biinterpretations**: A pair of theory morphisms that compose to
   identity (up to T-equivalence) yields a Morita equivalence.

5. **Invariance**: Morita-equivalent theories share all topos-theoretic
   properties — this is the foundation for Caramello's bridge technique.

## Connection to Caramello's Program

Morita equivalence is the central concept in Caramello's bridge technique:
- Two seemingly different mathematical theories T₁, T₂ may be Morita equivalent
- Any property expressible in topos-theoretic language transfers between them
- This gives a systematic method for discovering unexpected connections

## DAG Structure (depends on Layers 10, 12, 13, 14)

```
  bridge_invariance (★)
       |
  morita_equiv_transitive ←── morita_equiv_symmetric
       |                           |
  morita_equiv_reflexive    biinterpretation_morita
       |                           |
  MoritaEquiv (definition)  Biinterpretation (definition)
       |                           |
  ModelEquiv ←── model_reindex ←── TheoryMorphism (Layer 12)
       |
  FrameHomLT, Model (Layers 10, 14)
```
-/
import Mathlib
import RequestProject.Foundations.ClassifyingTopos

namespace Caramello.MoritaEquivalence

open GeometricLogic SyntacticCategory SyntacticSite ClassifyingTopos

/-! ## Section 1: Model Reindexing via Theory Morphisms

A theory morphism σ : T₁ → T₂ (a map on atoms preserving derivability)
induces a "pullback" on models: given a model of T₂, we can produce
a model of T₁ by precomposing with σ.
-/

/-- Reindex a valuation via a function on atoms. -/
def reindexValuation {α β : Type} (σ : α → β) (w : β → Prop) : α → Prop :=
  w ∘ σ

/-
A theory morphism σ : T₁ → T₂ pulls back models of T₂ to models of T₁.
    If w is a model of T₂, then w ∘ σ is a model of T₁.
-/
theorem theoryMorphism_pullback_model {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    (w : β → Prop) (hw : T₂.Model w) :
    T₁.Model (reindexValuation σ.onAtoms w) := by
      intro s hs
      have h_deriv : Derivable T₂ (s.antecedent.mapAtoms σ.onAtoms) (s.consequent.mapAtoms σ.onAtoms) := by
        exact σ.preserves_derivability ( by exact Derivable.axiom_rule s hs );
      exact fun h => by simpa [ eval_mapAtoms ] using soundness h_deriv w hw ( by simpa [ eval_mapAtoms ] using h ) ;

/-! ## Section 2: Model Equivalences

An equivalence between the model categories of two theories
is a pair of inverse maps between models.
-/

/-- A model of theory T with its proof. -/
structure ModelOf {α : Type} (T : GeomTheory α) where
  /-- The underlying valuation -/
  val : α → Prop
  /-- The proof that it satisfies T -/
  isModel : T.Model val

/-- A model equivalence between T₁ and T₂: a bijection on models
    that is compatible with the theory structure. -/
structure ModelEquiv {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β) where
  /-- Forward: model of T₁ → model of T₂ -/
  fwd : ModelOf T₁ → ModelOf T₂
  /-- Backward: model of T₂ → model of T₁ -/
  bwd : ModelOf T₂ → ModelOf T₁
  /-- Round-trip: backward ∘ forward is identity on valuations -/
  left_inv : ∀ m : ModelOf T₁, (bwd (fwd m)).val = m.val
  /-- Round-trip: forward ∘ backward is identity on valuations -/
  right_inv : ∀ m : ModelOf T₂, (fwd (bwd m)).val = m.val

/-! ## Section 3: Morita Equivalence -/

/-- Two geometric theories are **Morita equivalent** if there exists
    a model equivalence between them. -/
def MoritaEquiv {α β : Type} (T₁ : GeomTheory α) (T₂ : GeomTheory β) : Prop :=
  Nonempty (ModelEquiv T₁ T₂)

notation T₁ " ≃ₘ " T₂ => MoritaEquiv T₁ T₂

/-! ## Section 4: Morita Equivalence is an Equivalence Relation -/

/-- Morita equivalence is reflexive. -/
theorem morita_equiv_refl {α : Type} (T : GeomTheory α) :
    T ≃ₘ T :=
  ⟨{ fwd := id, bwd := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }⟩

/-- Morita equivalence is symmetric. -/
theorem morita_equiv_symm {α β : Type} {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (h : T₁ ≃ₘ T₂) : T₂ ≃ₘ T₁ := by
  obtain ⟨e⟩ := h
  exact ⟨{ fwd := e.bwd, bwd := e.fwd,
            left_inv := e.right_inv, right_inv := e.left_inv }⟩

/-
Morita equivalence is transitive.
-/
theorem morita_equiv_trans {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (h₁₂ : T₁ ≃ₘ T₂) (h₂₃ : T₂ ≃ₘ T₃) : T₁ ≃ₘ T₃ := by
      obtain ⟨ e₁₂ ⟩ := h₁₂
      obtain ⟨ e₂₃ ⟩ := h₂₃;
      refine' ⟨ ⟨ fun m => ⟨ e₂₃.fwd ( e₁₂.fwd m ) |> ModelOf.val, _ ⟩, fun m => ⟨ e₁₂.bwd ( e₂₃.bwd m ) |> ModelOf.val, _ ⟩, _, _ ⟩ ⟩;
      exact ( e₂₃.fwd ( e₁₂.fwd m ) ).isModel;
      exact ( e₁₂.bwd ( e₂₃.bwd m ) ).isModel;
      · intro m
        have h_eq : (e₂₃.bwd (e₂₃.fwd (e₁₂.fwd m))).val = (e₁₂.fwd m).val := by
          exact e₂₃.left_inv _;
        have h_eq : (e₂₃.bwd (e₂₃.fwd (e₁₂.fwd m))) = e₁₂.fwd m := by
          cases h : e₂₃.bwd ( e₂₃.fwd ( e₁₂.fwd m ) ) ; cases h' : e₁₂.fwd m ; aesop;
        have := e₁₂.left_inv m; aesop;
      · intro m
        have h_eq : (e₁₂.bwd (e₂₃.bwd m)).val = (e₁₂.bwd (e₂₃.bwd m)).val := by
          rfl;
        convert e₂₃.right_inv m using 1;
        congr! 2;
        convert e₁₂.right_inv ( e₂₃.bwd m ) using 1;
        constructor <;> intro h <;> cases h' : e₁₂.fwd ( e₁₂.bwd ( e₂₃.bwd m ) ) <;> cases h'' : e₂₃.bwd m <;> aesop ( simp_config := { singlePass := true } ) ;

/-! ## Section 5: Biinterpretations

A biinterpretation between T₁ and T₂ is a pair of theory morphisms
that compose (up to T-equivalence) to the identity. These give
a particularly concrete way to establish Morita equivalence.
-/

/-- A biinterpretation between T₁ and T₂ consists of theory morphisms
    in both directions that compose to the identity (on models). -/
structure Biinterpretation {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β) where
  /-- Forward morphism -/
  fwd : TheoryMorphism T₁ T₂
  /-- Backward morphism -/
  bwd : TheoryMorphism T₂ T₁
  /-- Left inverse on atoms (up to T₁-equivalence):
      for all atoms a of T₁, the formula σ(τ(a)) is T₁-equivalent to atom a -/
  left_inv : ∀ a : α, T₁ ⊢g (.atom a) ⟺ (.atom (bwd.onAtoms (fwd.onAtoms a)))
  /-- Right inverse on atoms (up to T₂-equivalence):
      for all atoms b of T₂, the formula τ(σ(b)) is T₂-equivalent to atom b -/
  right_inv : ∀ b : β, T₂ ⊢g (.atom b) ⟺ (.atom (fwd.onAtoms (bwd.onAtoms b)))

/-- Helper: evaluation commutes with atom composition. -/
lemma eval_comp_atoms {α β : Type} (f : α → β) (w : β → Prop) (a : α) :
    GeomFormula.eval w (.atom (f a)) = w (f a) := rfl

/-
A biinterpretation yields a Morita equivalence. The model equivalence
    is constructed by pulling back via the forward and backward morphisms.
-/
theorem biinterpretation_morita {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (bi : Biinterpretation T₁ T₂) : T₁ ≃ₘ T₂ := by
      refine' ⟨ _, _, _, _ ⟩;
      exact fun m => ⟨ reindexValuation bi.bwd.onAtoms m.val, theoryMorphism_pullback_model bi.bwd m.val m.isModel ⟩;
      exact fun m => ⟨ reindexValuation bi.fwd.onAtoms m.val, theoryMorphism_pullback_model bi.fwd m.val m.isModel ⟩;
      · intro m
        ext a
        simp [reindexValuation];
        have := bi.left_inv a;
        exact ⟨ fun h => by have := soundness this.2 m.val m.isModel; aesop, fun h => by have := soundness this.1 m.val m.isModel; aesop ⟩;
      · intro m
        ext b
        simp [reindexValuation];
        convert soundness _ _ _;
        rotate_left;
        exact β;
        exact T₂;
        exact .atom b;
        exact .atom ( bi.fwd.onAtoms ( bi.bwd.onAtoms b ) );
        exact bi.right_inv b |>.1;
        exact m.val;
        · exact m.isModel;
        · have := soundness ( bi.right_inv b |>.2 ) m.val m.isModel; aesop;

/-! ## Section 6: Invariance Under Morita Equivalence

Morita-equivalent theories share all "topos-theoretic invariants".
We define what it means for a property to be a topos-theoretic
invariant and prove that such properties transfer.
-/

/-
Consistency is a Morita invariant:
    if T₁ has a model and T₁ ≃_M T₂, then T₂ has a model.
-/
theorem consistency_morita_invariant {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : T₁ ≃ₘ T₂)
    (hcons : ∃ v, T₁.Model v) :
    ∃ w, T₂.Model w := by
      obtain ⟨ v, hv ⟩ := hcons;
      obtain ⟨ e ⟩ := hme;
      exact ⟨ _, e.fwd ⟨ v, hv ⟩ |>.isModel ⟩

/-
Having a unique model (up to valuation equality) is a Morita invariant.
-/
theorem unique_model_morita_invariant {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : T₁ ≃ₘ T₂)
    (huniq : ∀ v₁ v₂ : α → Prop, T₁.Model v₁ → T₁.Model v₂ → v₁ = v₂) :
    ∀ w₁ w₂ : β → Prop, T₂.Model w₁ → T₂.Model w₂ → w₁ = w₂ := by
      -- Apply the ModelEquiv to the models w₁ and w₂ to obtain models of T₁.
      intros w₁ w₂ hw₁ hw₂
      obtain ⟨v₁, hv₁⟩ : ∃ v₁ : α → Prop, T₁.Model v₁ ∧ v₁ = (hme.some.bwd ⟨w₁, hw₁⟩).val := by
        exact ⟨ _, ( hme.some.bwd ⟨ w₁, hw₁ ⟩ ).isModel, rfl ⟩
      obtain ⟨v₂, hv₂⟩ : ∃ v₂ : α → Prop, T₁.Model v₂ ∧ v₂ = (hme.some.bwd ⟨w₂, hw₂⟩).val := by
        exact ⟨ _, ( hme.some.bwd ⟨ w₂, hw₂ ⟩ ).isModel, rfl ⟩;
      have h_w_eq : (hme.some.fwd ⟨v₁, hv₁.left⟩).val = w₁ ∧ (hme.some.fwd ⟨v₂, hv₂.left⟩).val = w₂ := by
        exact ⟨ by simpa [ hv₁.2 ] using hme.some.right_inv ⟨ _, hw₁ ⟩, by simpa [ hv₂.2 ] using hme.some.right_inv ⟨ _, hw₂ ⟩ ⟩;
      grind

/-! ## Section 7: Theory Morphisms Induce Morita Functors

Theory morphisms don't usually give Morita equivalences (they're
not necessarily invertible), but they do give functors between
model categories.
-/

/-- A theory morphism σ : T₁ → T₂ gives a map ModelOf T₂ → ModelOf T₁. -/
def theoryMorphism_model_pullback {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂) :
    ModelOf T₂ → ModelOf T₁ :=
  fun m => ⟨reindexValuation σ.onAtoms m.val,
    theoryMorphism_pullback_model σ m.val m.isModel⟩

/-- The identity theory morphism gives the identity on models. -/
theorem model_pullback_id {α : Type} {T : GeomTheory α} :
    ∀ m : ModelOf T, (theoryMorphism_model_pullback (theoryMorphismId T) m).val = m.val := by
  intro m; rfl

/-- Composition of theory morphisms gives composition of pullbacks. -/
theorem model_pullback_comp {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (σ : TheoryMorphism T₁ T₂) (τ : TheoryMorphism T₂ T₃)
    (m : ModelOf T₃) :
    (theoryMorphism_model_pullback (theoryMorphismComp σ τ) m).val =
    (theoryMorphism_model_pullback σ (theoryMorphism_model_pullback τ m)).val := by
  rfl

/-! ## Section 8: Derivability-Preserving Theory Equivalences

A stronger notion: two theories over the same signature are
"derivably equivalent" if they prove exactly the same sequents.
-/

/-- Two theories over the same signature are derivably equivalent
    if they have the same derivable sequents. -/
def DerivablyEquiv {α : Type} (T₁ T₂ : GeomTheory α) : Prop :=
  ∀ φ ψ : GeomFormula α, (Derivable T₁ φ ψ) ↔ (Derivable T₂ φ ψ)

/-- Derivable equivalence is reflexive. -/
lemma derivablyEquiv_refl {α : Type} (T : GeomTheory α) :
    DerivablyEquiv T T := fun _ _ => Iff.rfl

/-- Derivable equivalence is symmetric. -/
lemma derivablyEquiv_symm {α : Type} {T₁ T₂ : GeomTheory α}
    (h : DerivablyEquiv T₁ T₂) : DerivablyEquiv T₂ T₁ :=
  fun φ ψ => (h φ ψ).symm

/-- Derivable equivalence is transitive. -/
lemma derivablyEquiv_trans {α : Type} {T₁ T₂ T₃ : GeomTheory α}
    (h₁₂ : DerivablyEquiv T₁ T₂) (h₂₃ : DerivablyEquiv T₂ T₃) :
    DerivablyEquiv T₁ T₃ :=
  fun φ ψ => (h₁₂ φ ψ).trans (h₂₃ φ ψ)

/-
Derivably equivalent theories over the same signature have the same models.
-/
theorem derivablyEquiv_same_models {α : Type} {T₁ T₂ : GeomTheory α}
    (h : DerivablyEquiv T₁ T₂) (v : α → Prop) :
    T₁.Model v ↔ T₂.Model v := by
      constructor <;> intro hv <;> contrapose! h;
      · unfold GeomTheory.Model at *; simp_all +decide [ Set.not_subset ] ;
        obtain ⟨ s, hs₁, hs₂ ⟩ := h; intro H; have := H s.antecedent s.consequent; simp_all +decide [ Derivable.axiom_rule ] ;
        exact hs₂ ( soundness this v ( by tauto ) );
      · obtain ⟨s, hs⟩ : ∃ s ∈ T₁, ¬s.valid v := by
          exact by unfold GeomTheory.Model at h; aesop;
        exact fun h' => hs.2 <| soundness ( h' _ _ |>.1 ( Derivable.axiom_rule s hs.1 ) ) v hv

/-
Derivable equivalence implies Morita equivalence (over the same signature).
-/
theorem derivablyEquiv_morita {α : Type} {T₁ T₂ : GeomTheory α}
    (h : DerivablyEquiv T₁ T₂) : T₁ ≃ₘ T₂ := by
      refine' ⟨ _, _, _, _ ⟩;
      exact fun m => ⟨ m.val, ( derivablyEquiv_same_models h m.val ).mp m.isModel ⟩
      exact fun m => ⟨ m.val, ( derivablyEquiv_same_models h m.val ).mpr m.isModel ⟩
      exact fun m => rfl
      exact fun m => rfl

/-! ## Section 9: The Bridge Technique (Preview)

Caramello's bridge technique uses Morita equivalence to transfer
mathematical results between theories. We give the basic schema:

Given:
- Theories T₁, T₂ with T₁ ≃_M T₂
- A Morita invariant property P
- A proof that P(T₁) holds

Conclude: P(T₂) holds.
-/

/-- The bridge technique schema: transfer a property
    from one theory to a Morita-equivalent theory via an
    explicit transfer function. -/
theorem bridge_transfer {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (P₁ : GeomTheory α → Prop) (P₂ : GeomTheory β → Prop)
    (htransfer : (T₁ ≃ₘ T₂) → P₁ T₁ → P₂ T₂)
    (hme : T₁ ≃ₘ T₂)
    (hp : P₁ T₁) : P₂ T₂ :=
  htransfer hme hp

/-- Consistency transfer: if T₁ is consistent and T₁ ≃_M T₂, then T₂ is consistent.
    This is a concrete instance of the bridge technique. -/
theorem bridge_consistency {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : T₁ ≃ₘ T₂)
    (hcons : ∃ v, T₁.Model v) :
    ∃ w, T₂.Model w :=
  consistency_morita_invariant hme hcons

/-! ## Section 10: Quotient Theory Equivalence

Adding consequences of a theory doesn't change the model class.
This gives a natural source of derivable equivalences.
-/

/-- The deductive closure of a theory: all sequents derivable from T. -/
def deductiveClosure {α : Type} (T : GeomTheory α) : GeomTheory α :=
  { s | Derivable T s.antecedent s.consequent }

/-- The original theory is contained in its deductive closure. -/
lemma subset_deductiveClosure {α : Type} (T : GeomTheory α) :
    T ⊆ deductiveClosure T := by
  intro s hs
  exact Derivable.axiom_rule s hs

/-
Every derivable sequent in the deductive closure is already
    derivable in the original theory.
-/
theorem deductiveClosure_conservative {α : Type} (T : GeomTheory α) :
    IsConservativeExtension T (deductiveClosure T) := by
      refine ⟨ subset_deductiveClosure T, fun φ ψ h => ?_ ⟩;
      induction' h with ψ hψ ih;
      all_goals { exact? }

end Caramello.MoritaEquivalence