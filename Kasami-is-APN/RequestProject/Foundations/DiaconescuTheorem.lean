/-
# Layer 36: Diaconescu's Theorem & Flat Functors

Diaconescu's theorem: geometric morphisms E → Sh(C, J) correspond to
J-continuous flat functors C → E. For Set, this gives:
**models of T ↔ flat functors C_T → Set**.

For propositional geometric theories, a "flat functor" C_T → Set is
determined by which formulas get sent to nonempty sets — captured by
a completely prime filter on L_T, which corresponds to models (Layer 19).

## DAG Structure (depends on Layers 10, 12, 14, 19, 26)

```
  diaconescu_theorem (★)
       |
  flat_iff_cpfilter ←── flatToCPFilter
       |
  FlatCondition ←── modelIsFlat
       |
  Filters.CompletelyPrimeFilter (Layer 19)
```
-/
import Mathlib
import RequestProject.Foundations.CoherentCompleteness
import RequestProject.Foundations.OpenQuestions

namespace Caramello.DiaconescuTheorem

open GeometricLogic SyntacticCategory ClassifyingTopos MoritaEquivalence Filters

/-! ## Section 1: Flat Conditions

A "flat condition" on a set of formulas captures when the set behaves
like the support of a flat functor: it contains ⊤, is closed under
derivability, respects ∧ as products, and covers disjunctions.
-/

/-- A flat condition on a set of formulas:
    represents which formulas φ have F(φ) nonempty. -/
structure FlatCondition {α : Type} (T : GeomTheory α) where
  /-- The support: formulas φ with F(φ) nonempty -/
  support : Set (GeomFormula α)
  /-- F(⊤) is nonempty -/
  top_mem : GeomFormula.top ∈ support
  /-- F(⊥) is empty -/
  bot_nmem : GeomFormula.bot ∉ support
  /-- Upward closed under derivability -/
  upward : ∀ {φ ψ}, φ ∈ support → Derivable T φ ψ → ψ ∈ support
  /-- F preserves products: φ ∧ ψ ∈ S ↔ φ ∈ S ∧ ψ ∈ S -/
  conj_iff : ∀ {φ ψ}, GeomFormula.conj φ ψ ∈ support ↔
    (φ ∈ support ∧ ψ ∈ support)
  /-- F covers disjunctions -/
  disj_cover : ∀ {φ ψ}, GeomFormula.disj φ ψ ∈ support →
    (φ ∈ support ∨ ψ ∈ support)
  /-- F covers infinitary disjunctions -/
  iDisj_cover : ∀ {ι : Type} {φ : ι → GeomFormula α},
    GeomFormula.iDisj ι φ ∈ support → ∃ i, φ i ∈ support
  /-- F covers existentials -/
  ex_cover : ∀ {β : Type} {φ : β → GeomFormula α},
    GeomFormula.ex β φ ∈ support → ∃ b, φ b ∈ support

/-! ## Section 2: Models Give Flat Conditions -/

/-- The support of a model: formulas true in the model. -/
def modelSupport {α : Type} (v : α → Prop) : Set (GeomFormula α) :=
  { φ | φ.eval v }

/-- Every model of T gives a flat condition. -/
def modelIsFlat {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hv : T.Model v) : FlatCondition T where
  support := modelSupport v
  top_mem := by simp [modelSupport, GeomFormula.eval]
  bot_nmem := by simp [modelSupport, GeomFormula.eval]
  upward := fun hφ hder => soundness hder v hv hφ
  conj_iff := by simp [modelSupport, GeomFormula.eval]
  disj_cover := by simp [modelSupport, GeomFormula.eval]
  iDisj_cover := by simp [modelSupport, GeomFormula.eval]
  ex_cover := by simp [modelSupport, GeomFormula.eval]

/-! ## Section 3: Flat Conditions ↔ Completely Prime Filters -/

/-- A flat condition gives a completely prime filter. -/
def flatToCPFilter {α : Type} {T : GeomTheory α}
    (F : FlatCondition T) : CompletelyPrimeFilter T where
  carrier := F.support
  top_mem := F.top_mem
  upward := fun hφ hder => F.upward hφ hder
  conj_mem := fun hφ hψ => F.conj_iff.mpr ⟨hφ, hψ⟩
  proper := F.bot_nmem
  prime := fun hφψ => F.disj_cover hφψ
  iDisj_mem := fun h => F.iDisj_cover h
  ex_mem := fun h => F.ex_cover h

/-- A completely prime filter gives a flat condition. -/
def cpfilterToFlat {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) : FlatCondition T where
  support := F.carrier
  top_mem := F.top_mem
  bot_nmem := F.proper
  upward := fun hφ hder => F.upward hφ hder
  conj_iff := ⟨fun h => ⟨F.upward h (Derivable.conj_elim_left _ _),
                          F.upward h (Derivable.conj_elim_right _ _)⟩,
               fun ⟨hφ, hψ⟩ => F.conj_mem hφ hψ⟩
  disj_cover := fun h => F.prime h
  iDisj_cover := fun h => F.iDisj_mem h
  ex_cover := fun h => F.ex_mem h

/-- Flat conditions biject with completely prime filters. -/
theorem flat_iff_cpfilter {α : Type} {T : GeomTheory α}
    (S : Set (GeomFormula α)) :
    (∃ F : FlatCondition T, F.support = S) ↔
    (∃ F : CompletelyPrimeFilter T, F.carrier = S) :=
  ⟨fun ⟨F, hF⟩ => ⟨flatToCPFilter F, hF⟩,
   fun ⟨F, hF⟩ => ⟨cpfilterToFlat F, hF⟩⟩

/-! ## Section 4: Diaconescu Correspondence -/

/-- From a flat condition, extract a valuation. -/
def flatToValuation {α : Type} {T : GeomTheory α}
    (F : FlatCondition T) : α → Prop :=
  cpfilter_to_valuation (flatToCPFilter F)

/-- The flat → model → flat round-trip recovers the valuation. -/
theorem flat_model_roundtrip {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hv : T.Model v) :
    flatToValuation (modelIsFlat v hv) = v := by
  ext a
  simp [flatToValuation, cpfilter_to_valuation, flatToCPFilter,
        modelIsFlat, modelSupport, GeomFormula.eval]

/-- A flat condition determines a model of T. -/
theorem flatGivesModel {α : Type} {T : GeomTheory α}
    (F : FlatCondition T) : T.Model (flatToValuation F) :=
  cpfilter_to_model (flatToCPFilter F)

/-- **Diaconescu's Theorem** (propositional version):
    Models of T ↔ flat conditions on C_T. -/
theorem diaconescu_theorem {α : Type} {T : GeomTheory α}
    (v : α → Prop) :
    T.Model v ↔ ∃ F : FlatCondition T, flatToValuation F = v :=
  ⟨fun hv => ⟨modelIsFlat v hv, flat_model_roundtrip v hv⟩,
   fun ⟨F, hF⟩ => hF ▸ flatGivesModel F⟩

/-! ## Section 5: Continuity -/

/-- Every flat condition is automatically continuous. -/
theorem flat_is_continuous {α : Type} {T : GeomTheory α}
    (F : FlatCondition T) {φ : GeomFormula α} {ι : Type}
    {ψ : ι → GeomFormula α}
    (hder : Derivable T φ (.iDisj ι ψ)) (hφ : φ ∈ F.support) :
    ∃ i, ψ i ∈ F.support :=
  F.iDisj_cover (F.upward hφ hder)

/-! ## Section 6: Morita via Flat Functors -/

/-
Morita equivalence gives a bijection on flat conditions.
-/
/-- Helper: if two models have the same valuation, their flat conditions are equal. -/
theorem modelIsFlat_eq_of_val_eq {α : Type} {T : GeomTheory α}
    (v w : α → Prop) (hv : T.Model v) (hw : T.Model w) (heq : v = w) :
    modelIsFlat v hv = modelIsFlat w hw := by
  subst heq; rfl

/-- Helper: the support of modelIsFlat is determined by the valuation. -/
theorem modelIsFlat_support {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hv : T.Model v) :
    (modelIsFlat v hv).support = modelSupport v := rfl

/-- Helper: for a flat condition F, modelIsFlat(flatToValuation F) has the same support. -/
theorem modelIsFlat_flatToValuation_support {α : Type} {T : GeomTheory α}
    (F : FlatCondition T) :
    (modelIsFlat _ (flatGivesModel F)).support = F.support := by
  ext φ
  simp only [modelIsFlat_support, modelSupport, Set.mem_setOf_eq]
  constructor
  · intro h; exact (cpfilter_eval_agree (flatToCPFilter F) φ).mp h
  · intro h; exact (cpfilter_eval_agree (flatToCPFilter F) φ).mpr h

/-- FlatCondition is determined by its support. -/
theorem flatCondition_ext {α : Type} {T : GeomTheory α}
    (F G : FlatCondition T) (h : F.support = G.support) : F = G := by
  cases F; cases G; simp at h; subst h; rfl

/-- FlatCondition T ≃ Spectrum T via flatToCPFilter / cpfilterToFlat. -/
noncomputable def flatEquivSpectrum {α : Type} {T : GeomTheory α} :
    FlatCondition T ≃ Spectrum T where
  toFun := flatToCPFilter
  invFun := cpfilterToFlat
  left_inv F := flatCondition_ext _ _ rfl
  right_inv F := by
    simp only [flatToCPFilter, cpfilterToFlat]
    rfl

/-
Spectrum T ≃ ModelOf T via cpfilter_to_valuation / model_to_cpfilter.
-/
noncomputable def spectrumEquivModel {α : Type} {T : GeomTheory α} :
    Spectrum T ≃ ModelOf T where
  toFun F := ⟨cpfilter_to_valuation F, cpfilter_to_model F⟩
  invFun m := model_to_cpfilter T m.val m.isModel
  left_inv F := by
    convert cpfilter_model_roundtrip F using 1;
    simp +decide [ model_to_cpfilter ];
    exact ⟨ fun h => congr_arg ( fun f => f.carrier ) h, fun h => by cases F; aesop ⟩
  right_inv m := by
    cases m with | mk v hv =>
    simp only
    exact ModelOf.mk.injEq _ _ _ _ |>.mpr (model_cpfilter_roundtrip v hv)

theorem morita_flat_bijection {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (hme : MoritaEquiv T₁ T₂) :
    Nonempty (FlatCondition T₁ ≃ FlatCondition T₂) := by
  obtain ⟨e⟩ := hme
  have modelEquiv : ModelOf T₁ ≃ ModelOf T₂ :=
    (OpenQuestions.model_cardinality_invariant ⟨e⟩).some
  exact ⟨flatEquivSpectrum.trans
    (spectrumEquivModel.trans (modelEquiv.trans
    (spectrumEquivModel.symm.trans flatEquivSpectrum.symm)))⟩

end Caramello.DiaconescuTheorem