/-
# Layer 24: Stone Duality for Geometric Theories

This layer develops Stone-type duality connecting the algebraic
(Lindenbaum–Tarski algebra) and spatial (spectrum) sides of
geometric theories.

## Mathematical Content

1. **Specialization order**: partial order structure on the spectrum.
2. **Patch topology**: the constructible (patch) topology.
3. **Constructible sets**: finite Boolean combinations of basic opens.
4. **Stone duality**: under completeness, D(φ) ⊆ D(ψ) iff T ⊢ φ ⟹ ψ.
5. **Quasi-compact opens**: definition and basic structure.
6. **Sobriety**: definition and spectral space structure.

## DAG Structure (depends on Layers 19, 20, 21, 23)

```
  basicOpen_sub_iff_derivable ←── completeness
       |
  constructible sets ←── basicOpen, vanishingSet
       |
  patch topology ←── spectral topology
       |
  specialization order
       |
  Filters, TopologicalSpectrum
```
-/
import Mathlib
import RequestProject.Foundations.TopologicalSpectrum

namespace Caramello.StoneDuality

open GeometricLogic SyntacticCategory Filters TopologicalSpectrum

/-! ## Section 1: Quasi-Compact Opens -/

/-- A set of spectrum points is quasi-compact:
    every cover by basic opens has a finite subcover. -/
def IsQuasiCompact {α : Type} {T : GeomTheory α}
    (U : Set (Spectrum T)) : Prop :=
  ∀ (ι : Type) (f : ι → GeomFormula α),
    U ⊆ ⋃ i, basicOpen (f i) →
    ∃ S : Finset ι, U ⊆ ⋃ i ∈ S, basicOpen (f i)

/-- A cover of a basic open by basic opens. -/
structure BasicCover {α : Type} (T : GeomTheory α)
    (φ : GeomFormula α) where
  /-- Index type -/
  ι : Type
  /-- Covering formulas -/
  covers : ι → GeomFormula α
  /-- The cover property: φ ⊢ ⋁ᵢ covers(i) -/
  isCover : Derivable T φ (.iDisj ι covers)

/-- A finite subcover. -/
structure FiniteSubcover {α : Type} {T : GeomTheory α}
    {φ : GeomFormula α} (c : BasicCover T φ) where
  /-- The finite index set -/
  indices : Finset c.ι
  /-- The subcover property -/
  isSubcover : ∀ F : Spectrum T, F.carrier φ →
    ∃ i ∈ indices, F.carrier (c.covers i)

/-! ## Section 2: Irreducible Closed Sets and Sobriety -/

/-- A closed set in the spectral topology. -/
def IsSpectralClosed {α : Type} {T : GeomTheory α}
    (C : Set (Spectrum T)) : Prop :=
  ∃ S : Set (GeomFormula α), C = ⋂ φ ∈ S, vanishingSet (T := T) φ

/-- A closed set is irreducible. -/
def IsIrreducible {α : Type} {T : GeomTheory α}
    (C : Set (Spectrum T)) : Prop :=
  C.Nonempty ∧
  ∀ C₁ C₂ : Set (Spectrum T),
    IsSpectralClosed C₁ → IsSpectralClosed C₂ →
    C ⊆ C₁ ∪ C₂ → C ⊆ C₁ ∨ C ⊆ C₂

/-- A point p is a generic point of C. -/
def IsGenericPointOf {α : Type} {T : GeomTheory α}
    (p : Spectrum T) (C : Set (Spectrum T)) : Prop :=
  C = { q | ∀ φ : GeomFormula α, p.carrier φ → q.carrier φ }

/-- The spectral topology is sober. -/
def IsSober {α : Type} (T : GeomTheory α) : Prop :=
  ∀ C : Set (Spectrum T),
    IsSpectralClosed C → IsIrreducible C →
    ∃! p : Spectrum T, IsGenericPointOf p C

/-! ## Section 3: Open and Closed Basis Properties -/

/-- The intersection of two basic opens is a basic open. -/
theorem basicOpen_inter_eq {α : Type} {T : GeomTheory α}
    (φ ψ : GeomFormula α) :
    basicOpen (T := T) φ ∩ basicOpen ψ = basicOpen (.conj φ ψ) := by
  ext p
  simp only [Set.mem_inter_iff, basicOpen, Set.mem_setOf_eq]
  exact ⟨fun ⟨h₁, h₂⟩ => p.conj_mem h₁ h₂,
         fun h => ⟨p.upward h (Derivable.conj_elim_left φ ψ),
                   p.upward h (Derivable.conj_elim_right φ ψ)⟩⟩

/-- Complement of a basic open is a vanishing set. -/
theorem compl_basicOpen_eq_vanishing {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) :
    (basicOpen (T := T) φ)ᶜ = vanishingSet (T := T) φ := rfl

/-- Complement of a vanishing set is a basic open. -/
theorem compl_vanishing_eq_basicOpen {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) :
    (vanishingSet (T := T) φ)ᶜ = basicOpen (T := T) φ := by
  ext p; simp [basicOpen, vanishingSet]

/-! ## Section 4: Specialization Order -/

/-
The specialization order is antisymmetric (T₀ property).
-/
theorem specialization_antisymm {α : Type} {T : GeomTheory α}
    (p q : Spectrum T)
    (hpq : p.carrier ⊆ q.carrier)
    (hqp : q.carrier ⊆ p.carrier) :
    p = q := by
  have heq : p.carrier = q.carrier := Set.Subset.antisymm hpq hqp
  cases p ; cases q ; simp_all +decide [ funext_iff ];
  rename_i h₁ h₂ h₃ h₄ h₅ h₆;
  cases h₁ ; cases h₄ ; simp_all +decide [ funext_iff, PrimeFilter ];
  cases ‹SyntacticFilter T› ; cases ‹SyntacticFilter T› ; simp_all +decide [ funext_iff, PrimeFilter ]

/-- The closure of a point in the spectral topology (set of specializations). -/
def pointClosure {α : Type} {T : GeomTheory α}
    (p : Spectrum T) : Set (Spectrum T) :=
  { q | p.carrier ⊆ q.carrier }

/-- The closure of a point contains the point itself. -/
theorem pointClosure_self {α : Type} {T : GeomTheory α}
    (p : Spectrum T) : p ∈ pointClosure p :=
  Set.Subset.rfl

/-- A point is closed iff its closure is a singleton. -/
def IsClosedPoint {α : Type} {T : GeomTheory α}
    (p : Spectrum T) : Prop :=
  pointClosure p = {p}

/-- A point is generic iff it is minimal in the specialization order. -/
def IsGenericPoint' {α : Type} {T : GeomTheory α}
    (p : Spectrum T) : Prop :=
  ∀ q : Spectrum T, q.carrier ⊆ p.carrier → q = p

/-- A closed point has maximal carrier set. -/
theorem closedPoint_maximal {α : Type} {T : GeomTheory α}
    (p : Spectrum T) (hp : IsClosedPoint p)
    (q : Spectrum T) (hpq : p.carrier ⊆ q.carrier) :
    p = q := by
  have : q ∈ pointClosure p := hpq
  rw [hp] at this
  exact (Set.mem_singleton_iff.mp this).symm

/-! ## Section 5: Patch (Constructible) Topology -/

/-- The patch topology subbasis: both basic opens and vanishing sets. -/
def patchSubbasis {α : Type} (T : GeomTheory α) :
    Set (Set (Spectrum T)) :=
  { U | ∃ φ : GeomFormula α, U = basicOpen (T := T) φ ∨ U = vanishingSet (T := T) φ }

/-- A set is patch-open if it's in the topology generated by the patch subbasis. -/
inductive IsPatchOpen {α : Type} {T : GeomTheory α} :
    Set (Spectrum T) → Prop where
  | subbasis : ∀ U, U ∈ patchSubbasis T → IsPatchOpen U
  | univ : IsPatchOpen Set.univ
  | inter : ∀ U V, IsPatchOpen U → IsPatchOpen V → IsPatchOpen (U ∩ V)
  | sUnion : ∀ S : Set (Set (Spectrum T)),
      (∀ U ∈ S, IsPatchOpen U) → IsPatchOpen (⋃₀ S)

/-- Every basic open is patch-open. -/
theorem basicOpen_isPatchOpen {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) : IsPatchOpen (basicOpen (T := T) φ) :=
  IsPatchOpen.subbasis _ ⟨φ, Or.inl rfl⟩

/-- Every vanishing set is patch-open. -/
theorem vanishingSet_isPatchOpen {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) : IsPatchOpen (vanishingSet (T := T) φ) :=
  IsPatchOpen.subbasis _ ⟨φ, Or.inr rfl⟩

/-! ## Section 6: Constructible Sets -/

/-- A constructible set is a finite Boolean combination of basic opens. -/
inductive IsConstructible {α : Type} {T : GeomTheory α} :
    Set (Spectrum T) → Prop where
  | basicOpen (φ : GeomFormula α) : IsConstructible (basicOpen (T := T) φ)
  | compl (U : Set (Spectrum T)) : IsConstructible U → IsConstructible Uᶜ
  | inter (U V : Set (Spectrum T)) :
      IsConstructible U → IsConstructible V → IsConstructible (U ∩ V)
  | union (U V : Set (Spectrum T)) :
      IsConstructible U → IsConstructible V → IsConstructible (U ∪ V)

/-- Vanishing sets are constructible. -/
theorem vanishingSet_constructible {α : Type} {T : GeomTheory α}
    (φ : GeomFormula α) :
    IsConstructible (vanishingSet (T := T) φ) := by
  rw [← compl_basicOpen_eq_vanishing]
  exact IsConstructible.compl _ (IsConstructible.basicOpen φ)

/-- The empty set is constructible. -/
theorem empty_constructible {α : Type} {T : GeomTheory α} :
    IsConstructible (∅ : Set (Spectrum T)) := by
  have h : (∅ : Set (Spectrum T)) = basicOpen (T := T) .bot :=
    basicOpen_bot_eq_empty.symm
  rw [h]; exact IsConstructible.basicOpen _

/-- The full spectrum is constructible. -/
theorem univ_constructible {α : Type} {T : GeomTheory α} :
    IsConstructible (Set.univ : Set (Spectrum T)) := by
  have h : (Set.univ : Set (Spectrum T)) = basicOpen (T := T) .top :=
    basicOpen_top_eq_univ.symm
  rw [h]; exact IsConstructible.basicOpen _

/-- Constructible sets are closed under difference. -/
theorem constructible_diff {α : Type} {T : GeomTheory α}
    {U V : Set (Spectrum T)}
    (hU : IsConstructible U) (hV : IsConstructible V) :
    IsConstructible (U \ V) := by
  have : U \ V = U ∩ Vᶜ := Set.diff_eq U V
  rw [this]
  exact IsConstructible.inter _ _ hU (IsConstructible.compl _ hV)

/-! ## Section 7: Frame Recovery — Stone Duality -/

/-- Forward direction: derivability implies inclusion of basic opens. -/
theorem derivable_implies_subset {α : Type} {T : GeomTheory α}
    {φ ψ : GeomFormula α} (h : Derivable T φ ψ) :
    basicOpen (T := T) φ ⊆ basicOpen ψ :=
  derivable_implies_basicOpen_sub h

/-- Under completeness, inclusion of basic opens implies derivability. -/
theorem subset_implies_derivable_of_complete {α : Type} {T : GeomTheory α}
    (hc : ToposEquivalence.IsComplete T)
    {φ ψ : GeomFormula α} (h : basicOpen (T := T) φ ⊆ basicOpen ψ) :
    Derivable T φ ψ := by
  apply hc
  intro v hmodel heval
  let F := model_to_cpfilter T v hmodel
  have hF_mem : (F : Spectrum T) ∈ basicOpen (T := T) φ := by
    show φ ∈ F.carrier
    exact heval
  have hψ := h hF_mem
  exact hψ

/-- Stone duality: under completeness, D(φ) ⊆ D(ψ) ↔ T ⊢ φ ⟹ ψ. -/
theorem basicOpen_sub_iff_derivable {α : Type} {T : GeomTheory α}
    (hc : ToposEquivalence.IsComplete T)
    (φ ψ : GeomFormula α) :
    basicOpen (T := T) φ ⊆ basicOpen ψ ↔ Derivable T φ ψ :=
  ⟨subset_implies_derivable_of_complete hc, derivable_implies_subset⟩

/-- Under completeness, basic open equality = T-equivalence. -/
theorem basicOpen_eq_iff_tequiv {α : Type} {T : GeomTheory α}
    (hc : ToposEquivalence.IsComplete T)
    (φ ψ : GeomFormula α) :
    basicOpen (T := T) φ = basicOpen ψ ↔ (T ⊢g φ ⟺ ψ) := by
  constructor
  · intro h
    exact ⟨subset_implies_derivable_of_complete hc (h ▸ Set.Subset.rfl),
           subset_implies_derivable_of_complete hc (h ▸ Set.Subset.rfl)⟩
  · intro ⟨h₁, h₂⟩
    exact Set.Subset.antisymm (derivable_implies_subset h₁) (derivable_implies_subset h₂)

/-! ## Section 8: Spectral Maps and Order -/

/-- Spectral maps preserve the specialization order. -/
theorem spectralMap_preserves_order {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    (p q : Spectrum T₂)
    (hpq : p.carrier ⊆ q.carrier) :
    (LatticeTheories.spectralMap σ p).carrier ⊆
    (LatticeTheories.spectralMap σ q).carrier := by
  intro φ hφ
  simp only [LatticeTheories.spectralMap] at hφ ⊢
  exact hpq hφ

/-
The preimage of a constructible set under a spectral map is constructible.
-/
theorem spectralMap_preimage_constructible {α β : Type}
    {T₁ : GeomTheory α} {T₂ : GeomTheory β}
    (σ : TheoryMorphism T₁ T₂)
    {U : Set (Spectrum T₁)} (hU : IsConstructible U) :
    IsConstructible (LatticeTheories.spectralMap σ ⁻¹' U) := by
  induction' hU with U hU ih;
  · convert IsConstructible.basicOpen ( U.mapAtoms σ.onAtoms ) using 1;
  · convert IsConstructible.compl _ ‹_› using 1;
  · rw [ Set.preimage_inter ] ; exact IsConstructible.inter _ _ ‹_› ‹_›;
  · rename_i U V hU hV hU' hV';
    simpa only [ Set.preimage_union ] using IsConstructible.union _ _ hU' hV'

/-! ## Section 9: Summary

This layer establishes:

1. **Quasi-compactness** as a property of basic opens.
2. **Sobriety** as a formal property of the spectral topology.
3. **Specialization order** antisymmetry (from T₀).
4. **Patch topology** refines the spectral topology.
5. **Constructible sets** form a Boolean algebra.
6. **Stone duality** (`basicOpen_sub_iff_derivable`):
   under completeness, D(φ) ⊆ D(ψ) ↔ T ⊢ φ ⟹ ψ.
-/

end Caramello.StoneDuality