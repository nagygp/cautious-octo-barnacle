/-
# Layer 17: Topos Equivalences & General Morita Theory

This layer formalizes the relationship between Morita equivalence of
geometric theories and equivalences of their classifying toposes.

## Mathematical Content

1. **Classifying topos equivalence**: bijections on frame homomorphisms.
2. **Morita equivalence → model bijection**: cleaner restatement.
3. **Invariant transfer chains**: systematic transfer along chains.
4. **Theory extensions**: adding derivable sequents preserves Morita class.
5. **Completeness and compactness**: stated as formal properties.
6. **Definitional extensions**: adding defined atoms.
7. **Theory interpretations**: full interpretations give Morita equivalences.

## DAG Structure (depends on Layers 14, 15, 16)

```
  fullInterp_morita
       |
  definitionalExtension_extends ←── definitionalExtension_restricts
       |
  derivable_extension_morita ←── derivable_extension_backward
       |
  bridge_technique ←── invariant_roundtrip
       |
  ClassifyingToposEquiv
       |
  GrothendieckTopos, MoritaEquiv (Layers 15, 16)
```
-/
import Mathlib
import RequestProject.Foundations.GrothendieckTopos

namespace Caramello.ToposEquivalence

open GeometricLogic SyntacticCategory ClassifyingTopos MoritaEquivalence
     GrothendieckTopos

/-! ## Section 1: Classifying Topos Equivalence -/

/-- A classifying topos equivalence between T₁ and T₂ (for Set):
    a bijection between their frame homomorphisms to Prop. -/
structure ClassifyingToposEquiv {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β) where
  /-- Forward: frame hom of T₁ → frame hom of T₂ -/
  fwd : FrameHomLT T₁ → FrameHomLT T₂
  /-- Backward: frame hom of T₂ → frame hom of T₁ -/
  bwd : FrameHomLT T₂ → FrameHomLT T₁
  /-- Left inverse -/
  left_inv : ∀ h, (bwd (fwd h)).toFun = h.toFun
  /-- Right inverse -/
  right_inv : ∀ h, (fwd (bwd h)).toFun = h.toFun

/-- Reflexivity. -/
def classifyingToposEquiv_refl {α : Type} (T : GeomTheory α) :
    ClassifyingToposEquiv T T where
  fwd := id; bwd := id
  left_inv := fun _ => rfl; right_inv := fun _ => rfl

/-- Symmetry. -/
def classifyingToposEquiv_symm {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (e : ClassifyingToposEquiv T₁ T₂) :
    ClassifyingToposEquiv T₂ T₁ where
  fwd := e.bwd; bwd := e.fwd
  left_inv := e.right_inv; right_inv := e.left_inv

/-! ## Section 2: Morita Equivalence → Model Bijection -/

/-- A Morita equivalence gives a bijection on models. -/
theorem morita_model_bijection {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂) :
    ∃ (F : ModelOf T₁ → ModelOf T₂) (G : ModelOf T₂ → ModelOf T₁),
      (∀ m, (G (F m)).val = m.val) ∧ (∀ m, (F (G m)).val = m.val) := by
  obtain ⟨e⟩ := hme
  exact ⟨e.fwd, e.bwd, e.left_inv, e.right_inv⟩

/-! ## Section 3: Invariant Transfer -/

/-- Transfer an invariant along two Morita equivalences. -/
theorem invariant_transfer_chain₂ {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (I : MoritaInvariant)
    (h₁₂ : MoritaEquiv T₁ T₂) (h₂₃ : MoritaEquiv T₂ T₃)
    (hp : I.prop T₁) : I.prop T₃ :=
  I.invariant h₂₃ (I.invariant h₁₂ hp)

/-- Transfer an invariant along three Morita equivalences. -/
theorem invariant_transfer_chain₃ {α β γ δ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    {T₃ : GeomTheory γ} {T₄ : GeomTheory δ}
    (I : MoritaInvariant)
    (h₁₂ : MoritaEquiv T₁ T₂) (h₂₃ : MoritaEquiv T₂ T₃)
    (h₃₄ : MoritaEquiv T₃ T₄)
    (hp : I.prop T₁) : I.prop T₄ :=
  I.invariant h₃₄ (I.invariant h₂₃ (I.invariant h₁₂ hp))

/-- The bridge technique: Morita invariants transfer iff. -/
theorem invariant_roundtrip {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (I : MoritaInvariant) (h : MoritaEquiv T₁ T₂) :
    I.prop T₁ ↔ I.prop T₂ :=
  ⟨I.invariant h, I.invariant (morita_equiv_symm h)⟩

/-! ## Section 4: Theory Extensions -/

/-- Adding a derivable sequent doesn't change models. -/
theorem derivable_extension_same_models {α : Type}
    {T : GeomTheory α} {s : GeomSequent α}
    (hder : Derivable T s.antecedent s.consequent) (v : α → Prop) :
    T.Model v ↔ (T ∪ {s}).Model v := by
  constructor
  · intro hv seq hmem
    rcases hmem with h | h
    · exact hv seq h
    · rw [Set.mem_singleton_iff] at h; subst h
      exact fun hant => soundness hder v hv hant
  · intro hv seq hmem
    exact hv seq (Set.mem_union_left _ hmem)

/-
Derivations in T ∪ {s} reduce to T when s is derivable in T.
-/
theorem derivable_extension_backward {α : Type}
    {T : GeomTheory α} {s : GeomSequent α}
    (hder : Derivable T s.antecedent s.consequent)
    {φ ψ : GeomFormula α}
    (h : Derivable (T ∪ {s}) φ ψ) : Derivable T φ ψ := by
  induction h;
  all_goals try tauto;
  all_goals try exact?;
  cases ‹_› <;> simp_all +decide [ Derivable.axiom_rule ]

/-- Adding a derivable sequent gives a derivably equivalent theory. -/
theorem derivable_extension_equiv {α : Type}
    {T : GeomTheory α} {s : GeomSequent α}
    (hder : Derivable T s.antecedent s.consequent) :
    DerivablyEquiv T (T ∪ {s}) := by
  intro φ ψ
  constructor
  · exact fun h => derivable_mono Set.subset_union_left h
  · exact fun h => derivable_extension_backward hder h

/-- Adding a derivable sequent gives a Morita-equivalent theory. -/
theorem derivable_extension_morita {α : Type}
    {T : GeomTheory α} {s : GeomSequent α}
    (hder : Derivable T s.antecedent s.consequent) :
    MoritaEquiv T (T ∪ {s}) :=
  derivablyEquiv_morita (derivable_extension_equiv hder)

/-! ## Section 5: Completeness and Compactness -/

/-- Completeness of propositional geometric logic (statement). -/
def IsComplete {α : Type} (T : GeomTheory α) : Prop :=
  ∀ φ ψ : GeomFormula α,
    (∀ v : α → Prop, T.Model v → φ.eval v → ψ.eval v) →
    Derivable T φ ψ

/-- Soundness is always true. -/
theorem soundness_always {α : Type} (T : GeomTheory α) :
    ∀ φ ψ : GeomFormula α, Derivable T φ ψ →
    (∀ v : α → Prop, T.Model v → φ.eval v → ψ.eval v) :=
  fun _ _ h v hm => soundness h v hm

/-- Completeness implies enough points. -/
theorem complete_implies_enough_points {α : Type} {T : GeomTheory α}
    (hc : IsComplete T) : HasEnoughPoints T := by
  intro φ ψ hvalid
  apply hc φ ψ
  intro v hm hφ
  exact hvalid (model_to_frameHom T v hm) hφ

/-- Compactness (statement). -/
def Compactness {α : Type} (T : GeomTheory α) : Prop :=
  (∀ T₀ : Finset (GeomSequent α), (↑T₀ : Set _) ⊆ T →
    ∃ v : α → Prop, GeomTheory.Model (↑T₀ : Set _) v) →
  ∃ v : α → Prop, T.Model v

/-! ## Section 6: The Full Bridge Technique -/

/-- The full bridge technique: I(T₁) ↔ I(T₂). -/
theorem bridge_technique {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (I : MoritaInvariant) (hme : MoritaEquiv T₁ T₂) :
    I.prop T₁ ↔ I.prop T₂ :=
  invariant_roundtrip I hme

/-- Bridge technique for consistency. -/
theorem bridge_consistency' {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂) :
    (∃ v, T₁.Model v) ↔ (∃ w, T₂.Model w) :=
  bridge_technique consistencyInvariant hme

/-- Bridge technique for unique models. -/
theorem bridge_unique_model {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂) :
    ((∃ v, T₁.Model v) ∧ (∀ v₁ v₂, T₁.Model v₁ → T₁.Model v₂ → v₁ = v₂)) ↔
    ((∃ w, T₂.Model w) ∧ (∀ w₁ w₂, T₂.Model w₁ → T₂.Model w₂ → w₁ = w₂)) :=
  bridge_technique uniqueModelInvariant hme

/-! ## Section 7: Definitional Extensions -/

/-- A definitional extension adds a new atom defined as φ. -/
def definitionalExtension {α : Type} (T : GeomTheory α)
    (φ : GeomFormula α) : GeomTheory (Option α) :=
  (fun s => (⟨s.antecedent.mapAtoms some, s.consequent.mapAtoms some⟩ :
    GeomSequent (Option α))) '' T
  ∪ { ⟨.atom none, φ.mapAtoms some⟩, ⟨φ.mapAtoms some, .atom none⟩ }

/-- A model of the definitional extension restricts to a model of T. -/
theorem definitionalExtension_restricts {α : Type}
    {T : GeomTheory α} {φ : GeomFormula α}
    (w : Option α → Prop) (hw : (definitionalExtension T φ).Model w) :
    T.Model (w ∘ some) := by
  intro s hs hant
  have hmem : (⟨s.antecedent.mapAtoms some, s.consequent.mapAtoms some⟩ :
    GeomSequent (Option α)) ∈ definitionalExtension T φ :=
    Set.mem_union_left _ (Set.mem_image_of_mem _ hs)
  have := hw _ hmem
  simp only [GeomSequent.valid, eval_mapAtoms] at this ⊢
  exact this hant

/-- A model of T extends to a model of the definitional extension. -/
theorem definitionalExtension_extends {α : Type}
    {T : GeomTheory α} {φ : GeomFormula α}
    (v : α → Prop) (hv : T.Model v) :
    (definitionalExtension T φ).Model
      (fun a => match a with | some a => v a | none => φ.eval v) := by
  intro s hs
  simp only [definitionalExtension, Set.mem_union, Set.mem_image,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with ⟨s', hs', hs_eq⟩ | hs_eq | hs_eq
  · subst hs_eq
    simp only [GeomSequent.valid, eval_mapAtoms]
    exact hv s' hs'
  · subst hs_eq
    unfold GeomSequent.valid
    simp only [eval_mapAtoms]
    intro h; convert h using 1
  · subst hs_eq
    unfold GeomSequent.valid
    simp only [GeomFormula.eval, eval_mapAtoms]
    intro h; convert h using 1

/-! ## Section 8: Model Theory Connections -/

/-- A theory is categorical if it has exactly one model. -/
def IsCategorical {α : Type} (T : GeomTheory α) : Prop :=
  (∃ v, T.Model v) ∧ ∀ v₁ v₂ : α → Prop, T.Model v₁ → T.Model v₂ → v₁ = v₂

/-- Categoricity is a Morita invariant. -/
theorem categorical_morita_invariant {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂) :
    IsCategorical T₁ ↔ IsCategorical T₂ :=
  bridge_technique uniqueModelInvariant hme

/-- A theory T is decidable if every sequent is either derivable
    or has a separating model. -/
def IsDecidable {α : Type} (T : GeomTheory α) : Prop :=
  ∀ φ ψ : GeomFormula α,
    Derivable T φ ψ ∨
    (∃ v : α → Prop, T.Model v ∧ φ.eval v ∧ ¬ ψ.eval v)

/-- A complete theory decides all sequents. -/
theorem complete_is_decidable {α : Type} {T : GeomTheory α}
    (hc : IsComplete T) : IsDecidable T := by
  intro φ ψ
  by_cases h : ∀ v : α → Prop, T.Model v → φ.eval v → ψ.eval v
  · exact Or.inl (hc φ ψ h)
  · push_neg at h
    obtain ⟨v, hv, hφ, hψ⟩ := h
    exact Or.inr ⟨v, hv, hφ, hψ⟩

/-- The empty theory has every valuation as a model. -/
theorem empty_theory_all_models {α : Type} (v : α → Prop) :
    (∅ : GeomTheory α).Model v :=
  fun _ hs => absurd hs (Set.notMem_empty _)

/-- The empty theory is consistent. -/
theorem empty_theory_consistent {α : Type} :
    ∃ v : α → Prop, (∅ : GeomTheory α).Model v :=
  ⟨fun _ => True, empty_theory_all_models _⟩

/-- The inconsistent theory (⊤ ⊢ ⊥) has no models. -/
theorem inconsistent_theory_no_models {α : Type} :
    ¬ (({⟨.top, .bot⟩} : GeomTheory α).Model (fun _ => True)) := by
  intro h
  have := h ⟨.top, .bot⟩ (Set.mem_singleton _)
  simp [GeomSequent.valid] at this

/-! ## Section 9: Theory Interpretations -/

/-- A full interpretation is a theory morphism that also reflects
    derivability. -/
structure FullInterpretation {α β : Type}
    (T₁ : GeomTheory α) (T₂ : GeomTheory β)
    extends TheoryMorphism T₁ T₂ where
  /-- Reflects derivability -/
  reflects_derivability : ∀ {φ ψ : GeomFormula α},
    Derivable T₂ (φ.mapAtoms onAtoms) (ψ.mapAtoms onAtoms) →
    Derivable T₁ φ ψ

/-- Full interpretations with mutual inverses give a biinterpretation. -/
def fullInterpretation_to_biinterp {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (f : FullInterpretation T₁ T₂) (g : FullInterpretation T₂ T₁)
    (left_inv : ∀ a : α, T₁ ⊢g (.atom a) ⟺ (.atom (g.onAtoms (f.onAtoms a))))
    (right_inv : ∀ b : β, T₂ ⊢g (.atom b) ⟺ (.atom (f.onAtoms (g.onAtoms b)))) :
    Biinterpretation T₁ T₂ :=
  { fwd := f.toTheoryMorphism
    bwd := g.toTheoryMorphism
    left_inv := left_inv
    right_inv := right_inv }

/-- Full interpretations with mutual inverses give Morita equivalence. -/
theorem fullInterp_morita {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (f : FullInterpretation T₁ T₂) (g : FullInterpretation T₂ T₁)
    (left_inv : ∀ a : α, T₁ ⊢g (.atom a) ⟺ (.atom (g.onAtoms (f.onAtoms a))))
    (right_inv : ∀ b : β, T₂ ⊢g (.atom b) ⟺ (.atom (f.onAtoms (g.onAtoms b)))) :
    MoritaEquiv T₁ T₂ :=
  biinterpretation_morita (fullInterpretation_to_biinterp f g left_inv right_inv)

end Caramello.ToposEquivalence