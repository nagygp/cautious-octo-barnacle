/-
# Layer 21: Lattice-Theoretic Theories & Spectral Duality

This layer develops concrete geometric theories whose models are
lattice-theoretic structures, and establishes duality results
connecting theories to their spectra.

## Mathematical Content

1. **Concrete geometric theories**: Implication, negation, exclusion,
   chain theories demonstrating how algebraic properties are expressed
   as geometric sequents.

2. **Theory operations**: Union of theories, theory from lists.

3. **Spectral maps**: Theory morphisms induce contravariantly functorial
   maps on spectra, preserving the basic open topology.

4. **Spectral duality**: Model equivalences give bijections on spectra.

## DAG Structure (depends on Layers 10, 12, 15, 18, 19)

```
  spectralMap_comp ←── spectralMap_id
       |
  spectralMap (definition) ←── Spectrum (Layer 19)
       |
  concrete theories
       |
  GeomFormula, TheoryMorphism (Layers 10, 12)
```
-/
import Mathlib
import RequestProject.Foundations.Filters
import RequestProject.Foundations.Applications

namespace Caramello.LatticeTheories

open GeometricLogic SyntacticCategory MoritaEquivalence
     Filters Applications

/-! ## Section 1: The Implication Theory -/

/-- A theory asserting that atom a implies atom b: the sequent a ⊢ b. -/
def implicationTheory {α : Type} (a b : α) : GeomTheory α :=
  { ⟨.atom a, .atom b⟩ }

/-- A model of the implication theory satisfies v(a) → v(b). -/
theorem implicationTheory_model {α : Type} {a b : α}
    (v : α → Prop) (hv : (implicationTheory a b).Model v) :
    v a → v b :=
  hv ⟨.atom a, .atom b⟩ (Set.mem_singleton _)

/-- Characterization of models of the implication theory. -/
theorem implicationTheory_model_iff {α : Type} {a b : α}
    (v : α → Prop) :
    (implicationTheory a b).Model v ↔ (v a → v b) := by
  constructor
  · exact implicationTheory_model v
  · intro h s hs
    simp [implicationTheory] at hs
    subst hs; exact h

/-- The implication theory is consistent. -/
theorem implicationTheory_consistent {α : Type} {a b : α} :
    ∃ v, (implicationTheory a b).Model v :=
  ⟨fun _ => True, (implicationTheory_model_iff _).mpr (fun _ => trivial)⟩

/-! ## Section 2: The Negation Theory -/

/-- A theory asserting that atom a is false: a ⊢ ⊥. -/
def negationTheory {α : Type} (a : α) : GeomTheory α :=
  { ⟨.atom a, .bot⟩ }

/-- A model of the negation theory has ¬v(a). -/
theorem negationTheory_model {α : Type} {a : α}
    (v : α → Prop) (hv : (negationTheory a).Model v) :
    ¬ v a :=
  fun ha => hv ⟨.atom a, .bot⟩ (Set.mem_singleton _) ha

/-- The negation theory is consistent. -/
theorem negationTheory_consistent {α : Type} {a : α} :
    ∃ v, (negationTheory a).Model v :=
  ⟨fun _ => False, fun s hs => by
    simp [negationTheory] at hs; subst hs; exact id⟩

/-! ## Section 3: The Exclusion Theory -/

/-- A theory asserting a ⊢ b ∨ c. -/
def exclusionTheory {α : Type} (a b c : α) : GeomTheory α :=
  { ⟨.atom a, .disj (.atom b) (.atom c)⟩ }

/-- A model of the exclusion theory has v(a) → v(b) ∨ v(c). -/
theorem exclusionTheory_model {α : Type} {a b c : α}
    (v : α → Prop) (hv : (exclusionTheory a b c).Model v) :
    v a → v b ∨ v c :=
  hv ⟨.atom a, .disj (.atom b) (.atom c)⟩ (Set.mem_singleton _)

/-! ## Section 4: The Chain Theory -/

/-- Theory of a chain: a ⊢ b and b ⊢ c. -/
def chainTheory {α : Type} (a b c : α) : GeomTheory α :=
  { ⟨.atom a, .atom b⟩, ⟨.atom b, .atom c⟩ }

/-- In a model of the chain theory, a → b and b → c. -/
theorem chainTheory_model {α : Type} {a b c : α}
    (v : α → Prop) (hv : (chainTheory a b c).Model v) :
    (v a → v b) ∧ (v b → v c) :=
  ⟨hv ⟨.atom a, .atom b⟩ (Set.mem_insert _ _),
   hv ⟨.atom b, .atom c⟩ (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))⟩

/-- Transitivity from the chain theory. -/
theorem chainTheory_transitive {α : Type} {a b c : α}
    (v : α → Prop) (hv : (chainTheory a b c).Model v) :
    v a → v c :=
  fun ha => (chainTheory_model v hv).2 ((chainTheory_model v hv).1 ha)

/-! ## Section 5: Theory Operations -/

/-- The union of two theories: a model satisfies all axioms from both. -/
def theoryUnion {α : Type}
    (T₁ T₂ : GeomTheory α) : GeomTheory α :=
  T₁ ∪ T₂

/-- A model of the union models the first component. -/
theorem theoryUnion_model_left {α : Type}
    {T₁ T₂ : GeomTheory α}
    (v : α → Prop) (hv : (theoryUnion T₁ T₂).Model v) :
    T₁.Model v :=
  fun s hs => hv s (Set.mem_union_left _ hs)

/-- A model of the union models the second component. -/
theorem theoryUnion_model_right {α : Type}
    {T₁ T₂ : GeomTheory α}
    (v : α → Prop) (hv : (theoryUnion T₁ T₂).Model v) :
    T₂.Model v :=
  fun s hs => hv s (Set.mem_union_right _ hs)

/-- Models of both theories are models of the union. -/
theorem theoryUnion_model_combine {α : Type}
    {T₁ T₂ : GeomTheory α}
    (v : α → Prop) (hv₁ : T₁.Model v) (hv₂ : T₂.Model v) :
    (theoryUnion T₁ T₂).Model v := by
  intro s hs
  rcases hs with h | h
  · exact hv₁ s h
  · exact hv₂ s h

/-- A theory from a list of sequents. -/
def theoryOfList {α : Type} (l : List (GeomSequent α)) : GeomTheory α :=
  { s | s ∈ l }

/-- A model of a list-theory satisfies all sequents in the list. -/
theorem theoryOfList_model {α : Type}
    {l : List (GeomSequent α)} {v : α → Prop}
    (hv : (theoryOfList l).Model v) (s : GeomSequent α) (hs : s ∈ l) :
    s.valid v :=
  hv s hs

/-! ## Section 6: Spectral Maps

A theory morphism σ : T₁ → T₂ induces a map on spectra
Spec(T₂) → Spec(T₁) (contravariantly).
-/

/-- A theory morphism induces a map on spectra (contravariantly). -/
def spectralMap {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂) :
    Spectrum T₂ → Spectrum T₁ :=
  fun p =>
  { carrier := { φ | φ.mapAtoms σ.onAtoms ∈ p.carrier }
    top_mem := by
      show GeomFormula.top.mapAtoms σ.onAtoms ∈ p.carrier
      simp [GeomFormula.mapAtoms]; exact p.top_mem
    upward := fun {φ ψ} hφ hle =>
      p.upward hφ (σ.preserves_derivability hle)
    conj_mem := fun {φ ψ} hφ hψ => by
      show (GeomFormula.conj φ ψ).mapAtoms σ.onAtoms ∈ p.carrier
      simp [GeomFormula.mapAtoms]
      exact p.conj_mem hφ hψ
    proper := by
      show GeomFormula.bot.mapAtoms σ.onAtoms ∉ p.carrier
      simp [GeomFormula.mapAtoms]; exact p.proper
    prime := fun {φ ψ} h => by
      have : (GeomFormula.disj φ ψ).mapAtoms σ.onAtoms ∈ p.carrier := h
      simp [GeomFormula.mapAtoms] at this
      exact p.prime this
    iDisj_mem := fun {ι f} h => by
      have : (GeomFormula.iDisj ι f).mapAtoms σ.onAtoms ∈ p.carrier := h
      simp [GeomFormula.mapAtoms] at this
      obtain ⟨i, hi⟩ := p.iDisj_mem this
      exact ⟨i, hi⟩
    ex_mem := fun {_β' _f} h => by
      have : (GeomFormula.ex _β' _f).mapAtoms σ.onAtoms ∈ p.carrier := h
      simp [GeomFormula.mapAtoms] at this
      obtain ⟨b, hb⟩ := p.ex_mem this
      exact ⟨b, hb⟩ }

/-- The identity theory morphism gives the identity on spectra. -/
theorem spectralMap_id {α : Type} {T : GeomTheory α}
    (p : Spectrum T) :
    (spectralMap (theoryMorphismId T) p).carrier = p.carrier := by
  ext φ
  simp [spectralMap, theoryMorphismId, mapAtoms_id]

/-- Spectral maps compose contravariantly. -/
theorem spectralMap_comp {α β γ : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β} {T₃ : GeomTheory γ}
    (σ : TheoryMorphism T₁ T₂) (τ : TheoryMorphism T₂ T₃)
    (p : Spectrum T₃) :
    (spectralMap (theoryMorphismComp σ τ) p).carrier =
    (spectralMap σ (spectralMap τ p)).carrier := by
  ext φ
  simp [spectralMap, theoryMorphismComp, mapAtoms_comp]

/-! ## Section 7: Spectral Continuity -/

/-- The preimage of a basic open under a spectral map is a basic open. -/
theorem spectralMap_preimage_basicOpen {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    (φ : GeomFormula α) :
    spectralMap σ ⁻¹' (basicOpen φ) = basicOpen (φ.mapAtoms σ.onAtoms) := by
  ext p
  simp [spectralMap, basicOpen]

/-! ## Section 8: Morita Equivalence and Spectra -/

/-- A model equivalence induces a map on spectra (forward). -/
def modelEquiv_to_spectrumFwd {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (e : ModelEquiv T₁ T₂) :
    Spectrum T₁ → Spectrum T₂ :=
  fun F =>
    let m₁ : ModelOf T₁ := ⟨cpfilter_to_valuation F, cpfilter_to_model F⟩
    let m₂ : ModelOf T₂ := e.fwd m₁
    model_to_cpfilter T₂ m₂.val m₂.isModel

/-- A model equivalence induces a map on spectra (backward). -/
def modelEquiv_to_spectrumBwd {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (e : ModelEquiv T₁ T₂) :
    Spectrum T₂ → Spectrum T₁ :=
  fun F =>
    let m₂ : ModelOf T₂ := ⟨cpfilter_to_valuation F, cpfilter_to_model F⟩
    let m₁ : ModelOf T₁ := e.bwd m₂
    model_to_cpfilter T₁ m₁.val m₁.isModel

/-
The spectrum bijection round-trips (left inverse).
-/
theorem spectrumBij_left_inv {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (e : ModelEquiv T₁ T₂) (F : Spectrum T₁) :
    (modelEquiv_to_spectrumBwd e (modelEquiv_to_spectrumFwd e F)).carrier =
    F.carrier := by
  unfold modelEquiv_to_spectrumFwd modelEquiv_to_spectrumBwd;
  ext φ; simp +decide [ model_to_cpfilter ] ;
  convert cpfilter_eval_agree F φ using 1;
  convert Iff.rfl using 2;
  convert e.left_inv ⟨ cpfilter_to_valuation F, cpfilter_to_model F ⟩ |> Eq.symm

/-
The spectrum bijection round-trips (right inverse).
-/
theorem spectrumBij_right_inv {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (e : ModelEquiv T₁ T₂) (F : Spectrum T₂) :
    (modelEquiv_to_spectrumFwd e (modelEquiv_to_spectrumBwd e F)).carrier =
    F.carrier := by
  unfold modelEquiv_to_spectrumFwd modelEquiv_to_spectrumBwd;
  unfold model_to_cpfilter cpfilter_to_valuation; simp +decide [ e.right_inv ] ;
  convert cpfilter_eval_agree F using 1;
  grind

/-! ## Section 9: The Spectrum of Concrete Theories -/

/-- The spectrum of the trivial theory is nonempty (for inhabited types). -/
theorem spectrum_trivial_nonempty {α : Type} [Inhabited α] :
    Nonempty (Spectrum (trivialTheory α)) :=
  spectrum_nonempty_iff_consistent.mpr ⟨fun _ => True, trivialTheory_universal _⟩

/-- The spectrum of an inconsistent theory is empty. -/
theorem spectrum_inconsistent_empty {α : Type} :
    IsEmpty (Spectrum (inconsistentTheory α)) :=
  spectrum_empty_iff_inconsistent.mpr (fun ⟨v, hv⟩ =>
    inconsistentTheory_no_models v hv)

/-- The implication theory a ⊢ b has a nonempty spectrum. -/
theorem spectrum_implication_nonempty {α : Type} {a b : α} :
    Nonempty (Spectrum (implicationTheory a b)) :=
  spectrum_nonempty_iff_consistent.mpr implicationTheory_consistent

/-- The negation theory a ⊢ ⊥ has a nonempty spectrum. -/
theorem spectrum_negation_nonempty {α : Type} {a : α} :
    Nonempty (Spectrum (negationTheory a)) :=
  spectrum_nonempty_iff_consistent.mpr negationTheory_consistent

/-! ## Section 10: Morita Invariance of Spectrum Properties -/

/-- Having a nonempty spectrum is a Morita invariant
    (this is just consistency). -/
theorem spectrum_nonempty_morita_invariant {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂)
    (h : Nonempty (Spectrum T₁)) :
    Nonempty (Spectrum T₂) := by
  rw [spectrum_nonempty_iff_consistent] at h ⊢
  exact consistency_morita_invariant hme h

/-- Having an empty spectrum is a Morita invariant
    (this is just inconsistency). -/
theorem spectrum_empty_morita_invariant {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂)
    (h : IsEmpty (Spectrum T₁)) :
    IsEmpty (Spectrum T₂) := by
  rw [spectrum_empty_iff_inconsistent] at h ⊢
  intro ⟨w, hw⟩
  exact h (consistency_morita_invariant (morita_equiv_symm hme) ⟨w, hw⟩)

/-! ## Section 11: Theory Homomorphisms between Concrete Theories -/

/-- The implication theory a ⊢ b is a subtheory of the chain theory a ⊢ b ⊢ c. -/
theorem implication_sub_chain {α : Type} {a b c : α} :
    implicationTheory a b ⊆ chainTheory a b c :=
  fun s hs => by
    simp [implicationTheory] at hs
    subst hs
    exact Set.mem_insert _ _

/-- The chain theory gives a model of the implication theory. -/
theorem chain_models_implication {α : Type} {a b c : α}
    (v : α → Prop) (hv : (chainTheory a b c).Model v) :
    (implicationTheory a b).Model v :=
  fun s hs => hv s (implication_sub_chain hs)

/-! ## Section 12: Summary

This layer provides:

1. **Concrete geometric theories**: Implication, negation, exclusion,
   chain theories showing how algebraic properties are expressed
   as geometric sequents.

2. **Theory operations**: Union of theories, theory from lists.

3. **Spectral maps**: Theory morphisms induce contravariantly functorial
   maps on spectra with composition law and continuity.

4. **Spectral duality**: Model equivalences give bijections on spectra
   with round-trip properties.

5. **Concrete spectra**: Nonemptiness/emptiness for specific theories.

6. **Morita invariance**: Spectrum properties transfer across Morita equiv.

Key theorems:
- `spectralMap_comp`: spectral maps compose contravariantly
- `spectralMap_preimage_basicOpen`: spectral maps are continuous
- `spectrumBij_left_inv/right_inv`: Morita equivalence ↔ spectrum bijection
- `spectrum_nonempty_morita_invariant`: nonempty spectrum is Morita invariant
-/

end Caramello.LatticeTheories