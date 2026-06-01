/-
# Layer 19: Filters on the Lindenbaum–Tarski Algebra

This layer develops the theory of filters and prime filters on the
syntactic preorder / Lindenbaum–Tarski algebra of a geometric theory.

## Mathematical Content

1. **Filters**: Upward-closed sets closed under finite meets (∧),
   containing ⊤. These are the "consistent observations" of a theory.

2. **Prime filters**: Filters that respect disjunction (if φ ∨ ψ ∈ F
   then φ ∈ F or ψ ∈ F). These correspond to "two-valued" observations.

3. **Completely prime filters**: Prime filters that also respect
   infinitary disjunction and existentials. These correspond exactly
   to models of the theory.

4. **Model ↔ Completely prime filter correspondence**: Every model
   determines a completely prime filter, and vice versa.

5. **Spectrum**: The set of completely prime filters = the model space.

## Connection to Caramello's Program

The spectrum of the Lindenbaum–Tarski algebra is the space of models
(= points of the classifying topos). This connects the algebraic
(lattice-theoretic) side to the model-theoretic side, and is the
foundation for Stone-type duality results.

## DAG Structure (depends on Layers 10, 12, 14)

```
  spectrum_is_model_space (★)
       |
  cpfilter_to_model ←→ model_to_cpfilter
       |
  CompletelyPrimeFilter ←── PrimeFilter ←── Filter
       |
  Derivable, GeomFormula, FrameHomLT (Layers 10, 12, 14)
```
-/
import Mathlib
import RequestProject.Foundations.ClassifyingTopos

namespace Caramello.Filters

open GeometricLogic SyntacticCategory ClassifyingTopos

/-! ## Section 1: Filters on the Syntactic Preorder

A filter on the syntactic preorder of T is a collection of formulas
that is upward-closed (under derivability), closed under conjunction,
and contains ⊤. Intuitively, it is a "consistent set of truths".
-/

/-- A filter on the syntactic preorder of a geometric theory T.
    A set F of formulas such that:
    - ⊤ ∈ F
    - If φ ∈ F and T ⊢ φ ⟹ ψ then ψ ∈ F (upward closed)
    - If φ ∈ F and ψ ∈ F then φ ∧ ψ ∈ F (closed under meets) -/
structure SyntacticFilter {α : Type} (T : GeomTheory α) where
  /-- The underlying set of formulas -/
  carrier : Set (GeomFormula α)
  /-- Contains ⊤ -/
  top_mem : GeomFormula.top ∈ carrier
  /-- Upward closed: if φ ∈ F and T ⊢ φ ⟹ ψ then ψ ∈ F -/
  upward : ∀ {φ ψ}, φ ∈ carrier → (T ⊢g φ ⟹ ψ) → ψ ∈ carrier
  /-- Closed under meets: if φ ∈ F and ψ ∈ F then φ ∧ ψ ∈ F -/
  conj_mem : ∀ {φ ψ}, φ ∈ carrier → ψ ∈ carrier → GeomFormula.conj φ ψ ∈ carrier

/-- A filter is proper if it does not contain ⊥. -/
def SyntacticFilter.isProper {α : Type} {T : GeomTheory α}
    (F : SyntacticFilter T) : Prop :=
  GeomFormula.bot ∉ F.carrier

/-- Every formula T-equivalent to a filter member is also in the filter. -/
theorem filter_tequiv_mem {α : Type} {T : GeomTheory α}
    (F : SyntacticFilter T) {φ ψ : GeomFormula α}
    (hφ : φ ∈ F.carrier) (h : T ⊢g φ ⟺ ψ) : ψ ∈ F.carrier :=
  F.upward hφ h.1

/-! ## Section 2: Prime Filters

A prime filter additionally satisfies the disjunction property:
if φ ∨ ψ ∈ F then φ ∈ F or ψ ∈ F. This makes the filter
"two-valued" with respect to disjunctions.
-/

/-- A prime filter on the syntactic preorder: a proper filter
    that respects disjunction. -/
structure PrimeFilter {α : Type} (T : GeomTheory α)
    extends SyntacticFilter T where
  /-- Proper: ⊥ ∉ F -/
  proper : toSyntacticFilter.isProper
  /-- Prime: if φ ∨ ψ ∈ F then φ ∈ F or ψ ∈ F -/
  prime : ∀ {φ ψ}, GeomFormula.disj φ ψ ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier

/-- A prime filter does not contain ⊥. -/
theorem primeFilter_no_bot {α : Type} {T : GeomTheory α}
    (F : PrimeFilter T) : GeomFormula.bot ∉ F.carrier :=
  F.proper

/-! ## Section 3: Completely Prime Filters

A completely prime filter also respects infinitary disjunctions
and existential quantification. These correspond exactly to models.
-/

/-- A completely prime filter: a prime filter that also respects
    infinitary disjunctions and existentials. -/
structure CompletelyPrimeFilter {α : Type} (T : GeomTheory α)
    extends PrimeFilter T where
  /-- Respects infinitary disjunction: if ⋁ᵢ φᵢ ∈ F then ∃ i, φᵢ ∈ F -/
  iDisj_mem : ∀ {ι : Type} {f : ι → GeomFormula α},
    GeomFormula.iDisj ι f ∈ carrier → ∃ i, f i ∈ carrier
  /-- Respects existential: if ∃x.φ(x) ∈ F then ∃ b, φ(b) ∈ F -/
  ex_mem : ∀ {β : Type} {f : β → GeomFormula α},
    GeomFormula.ex β f ∈ carrier → ∃ b, f b ∈ carrier

/-! ## Section 4: Models Give Completely Prime Filters

Every model v of T determines a completely prime filter:
the set of formulas true under v.
-/

/-- The truth filter of a model: {φ | φ.eval v}. -/
def truthFilter {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) : SyntacticFilter T where
  carrier := { φ | φ.eval v }
  top_mem := trivial
  upward := fun hφ hle => soundness hle v hmodel hφ
  conj_mem := fun hφ hψ => ⟨hφ, hψ⟩

/-- The truth filter is proper (since ⊥ evaluates to False). -/
theorem truthFilter_proper {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    (truthFilter T v hmodel).isProper :=
  id

/-- The truth filter is prime. -/
theorem truthFilter_prime {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v)
    {φ ψ : GeomFormula α} (h : GeomFormula.disj φ ψ ∈ (truthFilter T v hmodel).carrier) :
    φ ∈ (truthFilter T v hmodel).carrier ∨ ψ ∈ (truthFilter T v hmodel).carrier :=
  h

/-- Every model gives a completely prime filter. -/
def model_to_cpfilter {α : Type} (T : GeomTheory α)
    (v : α → Prop) (hmodel : T.Model v) : CompletelyPrimeFilter T where
  carrier := { φ | φ.eval v }
  top_mem := trivial
  upward := fun hφ hle => soundness hle v hmodel hφ
  conj_mem := fun hφ hψ => ⟨hφ, hψ⟩
  proper := id
  prime := fun h => h
  iDisj_mem := fun h => h
  ex_mem := fun h => h

/-! ## Section 5: Completely Prime Filters Give Models

Conversely, a completely prime filter determines a model of T.
The valuation is: v(a) := (atom a ∈ F).
-/

/-- Extract a valuation from a completely prime filter. -/
def cpfilter_to_valuation {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) : α → Prop :=
  fun a => GeomFormula.atom a ∈ F.carrier

/-- The valuation from a completely prime filter agrees with
    filter membership on all formulas. -/
theorem cpfilter_eval_agree {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) (φ : GeomFormula α) :
    φ.eval (cpfilter_to_valuation F) ↔ φ ∈ F.carrier := by
  induction φ with
  | top => exact ⟨fun _ => F.top_mem, fun _ => trivial⟩
  | bot => exact ⟨False.elim, fun h => absurd h F.proper⟩
  | atom a => exact Iff.rfl
  | conj φ ψ ihφ ihψ =>
    constructor
    · intro ⟨hφ, hψ⟩; exact F.conj_mem (ihφ.mp hφ) (ihψ.mp hψ)
    · intro h
      exact ⟨ihφ.mpr (F.upward h (Derivable.conj_elim_left _ _)),
             ihψ.mpr (F.upward h (Derivable.conj_elim_right _ _))⟩
  | disj φ ψ ihφ ihψ =>
    constructor
    · intro h
      rcases h with hφ | hψ
      · exact F.upward (ihφ.mp hφ) (Derivable.disj_intro_left _ _)
      · exact F.upward (ihψ.mp hψ) (Derivable.disj_intro_right _ _)
    · intro h
      rcases F.prime h with hφ | hψ
      · exact Or.inl (ihφ.mpr hφ)
      · exact Or.inr (ihψ.mpr hψ)
  | iDisj ι f ih =>
    constructor
    · intro ⟨i, hi⟩
      exact F.upward ((ih i).mp hi) (Derivable.iDisj_intro _ _ _)
    · intro h
      obtain ⟨i, hi⟩ := F.iDisj_mem h
      exact ⟨i, (ih i).mpr hi⟩
  | ex β f ih =>
    constructor
    · intro ⟨b, hb⟩
      exact F.upward ((ih b).mp hb) (Derivable.ex_intro _ _ _)
    · intro h
      obtain ⟨b, hb⟩ := F.ex_mem h
      exact ⟨b, (ih b).mpr hb⟩

/-- A completely prime filter determines a model of T. -/
theorem cpfilter_to_model {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) : T.Model (cpfilter_to_valuation F) := by
  intro s hs hant
  have hmem : s.antecedent ∈ F.carrier := (cpfilter_eval_agree F s.antecedent).mp hant
  have hcons : s.consequent ∈ F.carrier :=
    F.upward hmem (Derivable.axiom_rule s hs)
  exact (cpfilter_eval_agree F s.consequent).mpr hcons

/-! ## Section 6: The Correspondence (★)

Models of T are in natural bijection with completely prime filters
on the Lindenbaum–Tarski algebra.
-/

/-- Round-trip: model → cpfilter → valuation recovers the original. -/
theorem model_cpfilter_roundtrip {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    cpfilter_to_valuation (model_to_cpfilter T v hmodel) = v := by
  ext a; rfl

/-- Round-trip: cpfilter → valuation → cpfilter has the same carrier. -/
theorem cpfilter_model_roundtrip {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) :
    (model_to_cpfilter T (cpfilter_to_valuation F) (cpfilter_to_model F)).carrier =
    F.carrier := by
  ext φ
  exact cpfilter_eval_agree F φ

/-- ★ The model-filter correspondence: valuations that are models of T
    are in natural bijection with completely prime filters. -/
theorem model_filter_correspondence {α : Type} (T : GeomTheory α)
    (v : α → Prop) :
    T.Model v ↔ ∃ F : CompletelyPrimeFilter T, cpfilter_to_valuation F = v := by
  constructor
  · intro hm
    exact ⟨model_to_cpfilter T v hm, model_cpfilter_roundtrip v hm⟩
  · intro ⟨F, hF⟩
    rw [← hF]
    exact cpfilter_to_model F

/-! ## Section 7: The Spectrum

The spectrum of a theory is the set of all completely prime filters.
This is the "model space" of the theory, viewed lattice-theoretically.
-/

/-- The spectrum of a geometric theory: the type of completely prime filters. -/
def Spectrum {α : Type} (T : GeomTheory α) := CompletelyPrimeFilter T

/-- The evaluation map: given a point of the spectrum, evaluate a formula. -/
def spectrumEval {α : Type} {T : GeomTheory α}
    (p : Spectrum T) (φ : GeomFormula α) : Prop :=
  φ ∈ p.carrier

/-- The basic open set D(φ) = {p ∈ Spec(T) | φ ∈ p}. -/
def basicOpen {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) : Set (Spectrum T) :=
  { p | φ ∈ p.carrier }

/-- D(⊤) is the whole spectrum. -/
theorem basicOpen_top {α : Type} {T : GeomTheory α} :
    basicOpen (T := T) .top = Set.univ :=
  Set.eq_univ_of_forall fun p => p.top_mem

/-- D(⊥) is empty. -/
theorem basicOpen_bot {α : Type} {T : GeomTheory α} :
    basicOpen (T := T) .bot = ∅ :=
  Set.eq_empty_of_subset_empty fun p hp => p.proper hp

/-- D(φ ∧ ψ) = D(φ) ∩ D(ψ). -/
theorem basicOpen_conj {α : Type} {T : GeomTheory α}
    (φ ψ : GeomFormula α) :
    basicOpen (T := T) (.conj φ ψ) = basicOpen φ ∩ basicOpen ψ := by
  ext p
  simp only [basicOpen, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨p.upward h (Derivable.conj_elim_left _ _),
           p.upward h (Derivable.conj_elim_right _ _)⟩
  · intro ⟨hφ, hψ⟩
    exact p.conj_mem hφ hψ

/-- D(φ ∨ ψ) = D(φ) ∪ D(ψ). -/
theorem basicOpen_disj {α : Type} {T : GeomTheory α}
    (φ ψ : GeomFormula α) :
    basicOpen (T := T) (.disj φ ψ) = basicOpen φ ∪ basicOpen ψ := by
  ext p
  simp only [basicOpen, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · exact p.prime
  · intro h
    rcases h with hφ | hψ
    · exact p.upward hφ (Derivable.disj_intro_left _ _)
    · exact p.upward hψ (Derivable.disj_intro_right _ _)

/-- D(⋁ᵢ φᵢ) = ⋃ᵢ D(φᵢ). -/
theorem basicOpen_iDisj {α : Type} {T : GeomTheory α}
    (ι : Type) (f : ι → GeomFormula α) :
    basicOpen (T := T) (.iDisj ι f) = ⋃ i, basicOpen (f i) := by
  ext p
  simp only [basicOpen, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · exact p.iDisj_mem
  · intro ⟨i, hi⟩
    exact p.upward hi (Derivable.iDisj_intro _ _ _)

/-- If T ⊢ φ ⟹ ψ then D(φ) ⊆ D(ψ). -/
theorem basicOpen_mono {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (h : T ⊢g φ ⟹ ψ) :
    basicOpen (T := T) φ ⊆ basicOpen ψ :=
  fun p hp => p.upward hp h

/-- T-equivalent formulas have the same basic open. -/
theorem basicOpen_tequiv {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (h : T ⊢g φ ⟺ ψ) :
    basicOpen (T := T) φ = basicOpen ψ :=
  Set.Subset.antisymm (basicOpen_mono h.1) (basicOpen_mono h.2)

/-! ## Section 8: Filter Properties of Models

Additional properties connecting models and filters.
-/

/-- A model is consistent iff its truth filter is proper. -/
theorem model_proper {α : Type} {T : GeomTheory α}
    (v : α → Prop) (hmodel : T.Model v) :
    (truthFilter T v hmodel).isProper :=
  truthFilter_proper v hmodel

/-- Two models agree iff their truth filters agree. -/
theorem models_agree_iff_filters_agree {α : Type} {T : GeomTheory α}
    (v₁ v₂ : α → Prop) (h₁ : T.Model v₁) (h₂ : T.Model v₂) :
    v₁ = v₂ ↔
    (model_to_cpfilter T v₁ h₁).carrier = (model_to_cpfilter T v₂ h₂).carrier := by
  constructor
  · intro h; subst h; rfl
  · intro h
    ext a
    have : GeomFormula.atom a ∈ (model_to_cpfilter T v₁ h₁).carrier ↔
           GeomFormula.atom a ∈ (model_to_cpfilter T v₂ h₂).carrier := by
      rw [h]
    exact this

/-- The spectrum is empty iff the theory is inconsistent. -/
theorem spectrum_empty_iff_inconsistent {α : Type} {T : GeomTheory α} :
    IsEmpty (Spectrum T) ↔ ¬ ∃ v : α → Prop, T.Model v := by
  constructor
  · intro ⟨h⟩ ⟨v, hv⟩
    exact h (model_to_cpfilter T v hv)
  · intro h
    exact ⟨fun F => h ⟨cpfilter_to_valuation F, cpfilter_to_model F⟩⟩

/-- The spectrum is nonempty iff the theory is consistent. -/
theorem spectrum_nonempty_iff_consistent {α : Type} {T : GeomTheory α} :
    Nonempty (Spectrum T) ↔ ∃ v : α → Prop, T.Model v := by
  constructor
  · intro ⟨F⟩; exact ⟨cpfilter_to_valuation F, cpfilter_to_model F⟩
  · intro ⟨v, hv⟩; exact ⟨model_to_cpfilter T v hv⟩

/-! ## Section 9: Frame Homomorphisms and Completely Prime Filters

The connection between FrameHomLT (Layer 14) and completely prime filters:
every frame homomorphism h : L_T → Prop determines a completely prime filter
{φ | h(φ)}, and vice versa.
-/

/-- A frame homomorphism determines a completely prime filter. -/
def frameHom_to_cpfilter {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) : CompletelyPrimeFilter T where
  carrier := { φ | h.toFun φ }
  top_mem := h.pres_top
  upward := fun hφ hle => h.monotone _ _ hle hφ
  conj_mem := fun hφ hψ => (h.pres_conj _ _).mpr ⟨hφ, hψ⟩
  proper := h.pres_bot
  prime := fun h_disj => (h.pres_disj _ _).mp h_disj
  iDisj_mem := fun h_iDisj => (h.pres_iDisj _ _).mp h_iDisj
  ex_mem := fun h_ex => (h.pres_ex _ _).mp h_ex

/-- A completely prime filter determines a frame homomorphism. -/
def cpfilter_to_frameHom {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) : FrameHomLT T where
  toFun := fun φ => φ ∈ F.carrier
  resp_equiv := fun _ _ h =>
    ⟨fun hφ => F.upward hφ h.1, fun hψ => F.upward hψ h.2⟩
  pres_top := F.top_mem
  pres_bot := F.proper
  pres_conj := fun _φ _ψ =>
    ⟨fun h => ⟨F.upward h (Derivable.conj_elim_left _ _),
              F.upward h (Derivable.conj_elim_right _ _)⟩,
     fun ⟨hφ, hψ⟩ => F.conj_mem hφ hψ⟩
  pres_disj := fun _φ _ψ =>
    ⟨fun h => F.prime h,
     fun h => h.elim
       (fun hφ => F.upward hφ (Derivable.disj_intro_left _ _))
       (fun hψ => F.upward hψ (Derivable.disj_intro_right _ _))⟩
  pres_iDisj := fun _ι _f =>
    ⟨fun h => F.iDisj_mem h,
     fun ⟨_i, hi⟩ => F.upward hi (Derivable.iDisj_intro _ _ _)⟩
  pres_ex := fun _β _f =>
    ⟨fun h => F.ex_mem h,
     fun ⟨_b, hb⟩ => F.upward hb (Derivable.ex_intro _ _ _)⟩
  monotone := fun _ _ h hφ => F.upward hφ h

/-- Round-trip: frameHom → cpfilter → frameHom agrees. -/
theorem frameHom_cpfilter_roundtrip {α : Type} {T : GeomTheory α}
    (h : FrameHomLT T) (φ : GeomFormula α) :
    (cpfilter_to_frameHom (frameHom_to_cpfilter h)).toFun φ ↔ h.toFun φ :=
  Iff.rfl

/-- Round-trip: cpfilter → frameHom → cpfilter has the same carrier. -/
theorem cpfilter_frameHom_roundtrip {α : Type} {T : GeomTheory α}
    (F : CompletelyPrimeFilter T) :
    (frameHom_to_cpfilter (cpfilter_to_frameHom F)).carrier = F.carrier :=
  rfl

/-! ## Section 10: Summary

This layer establishes the fundamental correspondence:

    Models of T ↔ Completely prime filters on L_T ↔ Frame homomorphisms L_T → Prop

All three viewpoints on the "model space" are formally shown to be equivalent.
The spectrum (set of completely prime filters) provides a lattice-theoretic
perspective on the model space, with basic opens D(φ) giving a natural topology.

Key theorems:
- `cpfilter_eval_agree`: cpfilter membership ↔ evaluation
- `model_filter_correspondence`: models ↔ completely prime filters
- `spectrum_nonempty_iff_consistent`: Spec(T) ≠ ∅ ↔ T consistent
- `basicOpen_conj/disj/iDisj`: basic opens form a frame
- `frameHom_cpfilter_roundtrip`: frame homs ↔ cpfilters
-/

end Caramello.Filters
