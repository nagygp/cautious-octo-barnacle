/-
# Layer 41: Boolean Functions, Walsh Transform & APN/AB Categories

This module formalizes:
1. **Boolean functions** as maps on GF(2^n) with their differential properties
2. **Walsh–Hadamard transform** and the Almost Bent (AB) property
3. **Categories of APN and AB arrows** — morphisms are CCZ-equivalences
4. **Ω-morphism perspective** — APN/AB as conditions on subobject classifiers

## Key Mathematical Insight: APN/AB as Ω-Morphisms

In the topos `Type`, the subobject classifier Ω = Prop. A function
f : F → F induces a "differential characteristic map":

  χ_f : F \ {0} → (F → Ω)
  χ_f(a) = fun x ↦ (f(x + a) + f(x) ∈ S)

The APN condition says each fiber of χ_f has cardinality ≤ 2.
The AB condition constrains the "Fourier dual" of this Ω-morphism.

This connects the finite field theory to the topos-theoretic framework:
Boolean functions ARE Ω-morphisms, and APN/AB are regularity conditions
on these morphisms.

## DAG Structure (depends on Layers 1, 7, 38, 40)
import Mathlib
import RequestProject.Foundations.MCMInjectivity

-/
namespace Caramello.BooleanFunctions

-/
open Caramello.APNTheory Caramello.MCMInjectivity
-/
open Finset

-/
/-! ## Section 1: Boolean Function Basics -/

/-- A Boolean function structure: a function on a finite field of characteristic 2. -/
-/
structure BoolFun (F : Type*) [Field F] [Fintype F] where
  /-- The underlying function -/
  toFun : F → F

-/
instance {F : Type*} [Field F] [Fintype F] : CoeFun (BoolFun F) (fun _ => F → F) where
  coe := BoolFun.toFun

/-- The zero function. -/
-/
def BoolFun.zero (F : Type*) [Field F] [Fintype F] : BoolFun F :=
  ⟨fun _ => 0⟩

/-- A power function as a BoolFun. -/
-/
def BoolFun.power {F : Type*} [Field F] [Fintype F] (d : ℕ) : BoolFun F :=
  ⟨fun x => x ^ d⟩

/-- The Gold power function. -/
-/
def BoolFun.gold {F : Type*} [Field F] [Fintype F] (k : ℕ) : BoolFun F :=
  BoolFun.power (goldExponent k)

/-- The Kasami power function. -/
-/
def BoolFun.kasami {F : Type*} [Field F] [Fintype F] (k : ℕ) : BoolFun F :=
  BoolFun.power (kasamiExponent k)

-/
/-! ## Section 2: Differential Characteristic Map (Ω-Morphism)

In the topos Type, Ω = Prop. The differential of f induces a map
to Ω via the characteristic function of each fiber.

This is the precise connection between finite field cryptography
and topos theory: **the APN condition is a condition on an Ω-morphism**.

/-- The differential Ω-morphism: for each nonzero a, gives a predicate on F.
    χ_f(a)(b) = "the equation f(x+a) + f(x) = b has a solution". -/
-/
-/
def differentialOmegaMorphism {F : Type*} [Add F] [Zero F]
    (f : F → F) (a : F) : F → Prop :=
  fun b => ∃ x : F, f (x + a) + f x = b

/-- The differential fiber: the set of solutions to f(x+a)+f(x) = b. -/
-/
-/
def differentialFiber {F : Type*} [Add F]
    (f : F → F) (a b : F) : Set F :=
  { x | f (x + a) + f x = b }

/-- The Ω-morphism view: APN means each differential fiber has ≤ 2 elements. -/
-/
-/
def IsAPN_Omega {F : Type*} [Add F] [Zero F] [Fintype F] [DecidableEq F]
    (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    Fintype.card { x : F // f (x + a) + f x = b } ≤ 2

/-- The Ω-morphism characterization is equivalent to the standard APN definition. -/
-/
-/
theorem isAPN_omega_iff_isAPN {F : Type*} [AddCommGroup F]
    [Fintype F] [DecidableEq F] (f : F → F) :
    IsAPN_Omega f ↔ IsAPN f := by
  constructor
  · intro h
    unfold IsAPN differentialUniformity
    apply Finset.sup_le; intro a ha
    apply Finset.sup_le; intro b _
    exact h a (Finset.mem_filter.mp ha).2 b
  · intro h a ha b
    exact le_trans (Finset.le_sup (f := fun b => differentialCount _ a b)
      (Finset.mem_univ b))
      (le_trans (Finset.le_sup
        (f := fun a => Finset.sup Finset.univ (fun b => differentialCount _ a b))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)) h)

-/
-/
/-! ## Section 3: Walsh–Hadamard Transform

The Walsh transform is the "Fourier transform" over GF(2).
For a function f : GF(2^n) → GF(2^n), the Walsh coefficient at (a,b) is:

  W_f(a,b) = Σ_{x ∈ F} (-1)^{Tr(ax + bf(x))}

where Tr : GF(2^n) → GF(2) is the absolute trace.

Note: We define the trace abstractly as a parameter since the full
trace theory for GaloisField requires substantial infrastructure.

/-- The Walsh–Hadamard coefficient of f at (a, b), given a trace function. -/
-/
-/
-/
noncomputable def walshCoeff {F : Type*} [Field F] [Fintype F]
    (trace : F → ZMod 2) (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, if trace (a * x + b * f x) = 0 then 1 else -1

/-- The Walsh spectrum: the set of Walsh coefficient values. -/
-/
-/
-/
noncomputable def walshSpectrum {F : Type*} [Field F] [Fintype F]
    (trace : F → ZMod 2) (f : F → F) : Finset ℤ :=
  (Finset.univ.product Finset.univ).image (fun p => walshCoeff trace f p.1 p.2)

-/
-/
-/
/-! ## Section 4: Almost Bent (AB) Property -/

/-- A function is Almost Bent (AB) if its Walsh coefficients
    take only the values 0, +2^{(n+1)/2}, -2^{(n+1)/2}.
    This requires n to be odd. -/
-/
-/
-/
def IsAB {F : Type*} [Field F] [Fintype F]
    (trace : F → ZMod 2) (n : ℕ) (f : F → F) : Prop :=
  ∀ a b : F, walshCoeff trace f a b ∈
    ({0, 2 ^ ((n + 1) / 2), -(2 ^ ((n + 1) / 2))} : Set ℤ)

-/
-/
-/
theorem ab_implies_apn {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (trace : F → ZMod 2) (hn : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hAB : IsAB trace n f) : IsAPN_Omega f := by
  sorry

-/
-/
-/
/-! ## Section 5: The Category of APN Functions

Objects: pairs (F, f) where F is a finite field and f : F → F is APN.
Morphisms: CCZ-equivalences preserving the graph structure.

/-- An APN object: a finite field with an APN function. -/
-/
-/
-/
-/
structure APNObject where
  /-- The carrier type -/
  F : Type*
  /-- Field instance -/
  instField : Field F
  /-- Fintype instance -/
  instFintype : Fintype F
  /-- DecidableEq instance -/
  instDecEq : DecidableEq F
  /-- The function -/
  func : F → F
  /-- APN property -/
  isAPN : @IsAPN_Omega F
    instField.toAdd
    instField.toMonoidWithZero.toZero
    instFintype instDecEq func

/-- A morphism between APN objects: a CCZ-equivalence. -/
-/
-/
-/
-/
structure APNMorphism (X Y : APNObject) where
  /-- The graph bijection witnessing CCZ-equivalence -/
  graphEquiv : X.F × X.F ≃ Y.F × Y.F
  /-- The bijection maps the graph of X.func into the graph of Y.func -/
  mapsGraph : ∀ p, p ∈ functionGraph X.func ↔ graphEquiv p ∈ functionGraph Y.func

/-- Identity morphism for APN objects. -/
-/
-/
-/
-/
def APNMorphism.id (X : APNObject) : APNMorphism X X :=
  ⟨Equiv.refl _, fun _ => Iff.rfl⟩

/-- Composition of APN morphisms. -/
-/
-/
-/
-/
def APNMorphism.comp {X Y Z : APNObject}
    (g : APNMorphism Y Z) (f : APNMorphism X Y) : APNMorphism X Z :=
  ⟨f.graphEquiv.trans g.graphEquiv,
   fun p => (f.mapsGraph p).trans (g.mapsGraph _)⟩

/-- An AB object: a finite field with an AB function. -/
-/
-/
-/
-/
structure ABObject where
  /-- The carrier type -/
  F : Type*
  /-- Field instance -/
  instField : Field F
  /-- Fintype instance -/
  instFintype : Fintype F
  /-- DecidableEq instance -/
  instDecEq : DecidableEq F
  /-- The dimension -/
  dim : ℕ
  /-- Dimension is odd -/
  dimOdd : Odd dim
  /-- Cardinality matches -/
  card : @Fintype.card F instFintype = 2 ^ dim
  /-- Trace function -/
  trace : F → ZMod 2
  /-- The function -/
  func : F → F
  /-- AB property -/
  isAB : @IsAB F instField instFintype trace dim func

/-- A morphism between AB objects. -/
-/
-/
-/
-/
structure ABMorphism (X Y : ABObject) where
  /-- The graph bijection -/
  graphEquiv : X.F × X.F ≃ Y.F × Y.F
  /-- Preserves graphs -/
  mapsGraph : ∀ p, p ∈ functionGraph X.func ↔ graphEquiv p ∈ functionGraph Y.func

/-- Identity AB morphism. -/
-/
-/
-/
-/
def ABMorphism.id (X : ABObject) : ABMorphism X X :=
  ⟨Equiv.refl _, fun _ => Iff.rfl⟩

/-- Composition of AB morphisms. -/
-/
-/
-/
-/
def ABMorphism.comp {X Y Z : ABObject}
    (g : ABMorphism Y Z) (f : ABMorphism X Y) : ABMorphism X Z :=
  ⟨f.graphEquiv.trans g.graphEquiv,
   fun p => (f.mapsGraph p).trans (g.mapsGraph _)⟩

-/
-/
-/
-/
/-! ## Section 6: Ω-Morphism Framing

In the topos Type, Ω = Prop. We can view differential properties
as structure on Ω-valued morphisms.

A "differential Ω-morphism" from F is a family of predicates:
  D_f : F \ {0} → (F → Ω)

The APN condition says each fiber {x : D_f(a)(b)} has ≤ 2 elements.
This is an intrinsic condition on the Ω-morphism, independent of
the particular representation of f.

/-- An Ω-morphism: a family of predicates parametrized by a type.
    In the topos Type, Ω = Prop, so this is just a two-parameter predicate. -/
-/
-/
-/
-/
-/
@[ext]
-/
-/
-/
-/
-/
structure OmegaMorphism (A B : Type*) where
  /-- The classifier map: for each parameter a, gives a predicate on B -/
  classify : A → B → Prop

/-- The full differential Ω-morphism (parametrized by output). -/
-/
-/
-/
-/
-/
def fullDifferentialOmega {F : Type*} [Add F] (f : F → F) :
    OmegaMorphism (F × F) F where
  classify p x := f (x + p.1) + f x = p.2

/-- The fiber of an Ω-morphism at a point. -/
-/
-/
-/
-/
-/
def OmegaMorphism.fiber {A B : Type*} (χ : OmegaMorphism A B) (a : A) : Set B :=
  { b | χ.classify a b }

/-- An Ω-morphism has bounded fibers if each fiber has at most k elements. -/
-/
-/
-/
-/
-/
def OmegaMorphism.hasBoundedFibers {A B : Type*} [Fintype B] [DecidableEq B]
    (χ : OmegaMorphism A B) (k : ℕ)
    [∀ a : A, ∀ b : B, Decidable (χ.classify a b)] : Prop :=
  ∀ a : A, Fintype.card { b : B // χ.classify a b } ≤ k

/-- APN is equivalent to the full differential Ω-morphism having bounded fibers
    (restricted to nonzero differences). -/
-/
-/
-/
-/
-/
theorem apn_iff_bounded_omega {F : Type*} [AddCommGroup F]
    [Fintype F] [DecidableEq F] (f : F → F) :
    IsAPN_Omega f ↔
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card { x : F // f (x + a) + f x = b } ≤ 2 :=
  Iff.rfl

-/
-/
-/
-/
-/
/-! ## Section 7: Ω-Morphism Category

The category where objects are types and morphisms are Ω-morphisms
(predicates/relations). This is essentially the category of relations,
which is a well-known categorical structure.

/-- Composition of Ω-morphisms (relational composition). -/
-/
-/
-/
-/
-/
-/
def OmegaMorphism.comp {A B C : Type*}
    (g : OmegaMorphism B C) (f : OmegaMorphism A B) : OmegaMorphism A C where
  classify a c := ∃ b : B, f.classify a b ∧ g.classify b c

/-- Identity Ω-morphism. -/
-/
-/
-/
-/
-/
-/
def OmegaMorphism.idMorphism (A : Type*) : OmegaMorphism A A where
  classify a b := a = b

/-- Left identity law. -/
-/
-/
-/
-/
-/
-/
theorem OmegaMorphism.id_comp {A B : Type*} (f : OmegaMorphism A B) :
    (OmegaMorphism.idMorphism B).comp f = f := by
  ext a b; simp [comp, idMorphism]

/-- Right identity law. -/
-/
-/
-/
-/
-/
-/
theorem OmegaMorphism.comp_id {A B : Type*} (f : OmegaMorphism A B) :
    f.comp (OmegaMorphism.idMorphism A) = f := by
  ext a b; simp [comp, idMorphism]

/-- Associativity of composition. -/
-/
-/
-/
-/
-/
-/
theorem OmegaMorphism.comp_assoc {A B C D : Type*}
    (h : OmegaMorphism C D) (g : OmegaMorphism B C) (f : OmegaMorphism A B) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  ext a d
  simp [comp]
  constructor
  · rintro ⟨c, ⟨b, hf, hg⟩, hh⟩; exact ⟨b, hf, c, hg, hh⟩
  · rintro ⟨b, hf, c, hg, hh⟩; exact ⟨c, ⟨b, hf, hg⟩, hh⟩

-/
-/
-/
-/
-/
-/
/-! ## Section 8: The Ω-Morphism Pushforward and Pullback -/

/-- The Ω-morphism functor: composition with g : F → F' gives a new Ω-morphism. -/
-/
-/
-/
-/
-/
-/
def OmegaMorphism.pushforward {A B B' : Type*}
    (χ : OmegaMorphism A B) (g : B → B') : OmegaMorphism A B' where
  classify a b' := ∃ b : B, χ.classify a b ∧ g b = b'

/-- The Ω-morphism pullback. -/
-/
-/
-/
-/
-/
-/
def OmegaMorphism.pullback {A A' B : Type*}
    (χ : OmegaMorphism A B) (g : A' → A) : OmegaMorphism A' B where
  classify a' b := χ.classify (g a') b

-/
-/
-/
-/
-/
-/
/-! ## Section 9: APN/AB as Invariants of Ω-Morphisms -/

/-- Every APN function has a well-defined differential Ω-morphism
    with bounded fibers. -/
-/
-/
-/
-/
-/
-/
theorem apn_has_omega_morphism {F : Type*} [AddCommGroup F]
    [Fintype F] [DecidableEq F]
    (f : F → F) (hAPN : IsAPN_Omega f) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card { x : F // f (x + a) + f x = b } ≤ 2 := hAPN

-/
-/
-/
-/
-/
-/
/-! ## Section 10: Connection to Topos-Theoretic Bridge

The differential Ω-morphism connects to the bridge technique:

1. Given f : F → F, the differential Ω-morphism χ_f classifies
   the "difference set" of f.
2. The APN property is a condition on χ_f (bounded fibers).
3. CCZ-equivalence preserves graph structure ≃ Ω-morphism equivalence.
4. This is analogous to Morita invariance: a topos-theoretic property
   (bounded fibers) that transfers across equivalences (CCZ).

The abstraction hierarchy:
  Concrete: f : GF(2^n) → GF(2^n)
    → Ω-morphism: χ_f : F × F → Prop
    → Geometric theory: axioms encoding the differential structure
    → Classifying topos: Sh(C_T, J_T)
    → Morita invariant: bounded fiber property

-/
-/
-/
-/
-/
-/
-/
/-! ## Section 11: Summary

1. **BoolFun**: Boolean function structure with Gold/Kasami instances
2. **differentialOmegaMorphism**: The Ω-morphism view of differentials
3. **IsAPN_Omega ↔ IsAPN**: Equivalence of Ω-morphism and standard APN
4. **Walsh transform / IsAB**: Almost Bent functions and spectrum
5. **APNObject/APNMorphism**: Category of APN functions with CCZ morphisms
6. **ABObject/ABMorphism**: Category of AB functions
7. **OmegaMorphism**: General Ω-morphism category (Rel)
8. **apn_iff_bounded_omega**: APN = bounded fibers of Ω-morphism
9. **Bridge connection**: Differential → Ω-morphism → theory → topos

-/
-/
-/
-/
-/
-/
-/
-/
end Caramello.BooleanFunctions

-/
-/
-/
-/
-/
-/
-/
-/