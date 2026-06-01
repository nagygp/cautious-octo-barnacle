/-
# Layer 30: Weak Factorization Systems & Model Category Foundations

This layer introduces the basic building blocks of abstract homotopy
theory: lifting properties, weak factorization systems (WFS), and
the axioms for model categories. These structures organize the
"fibration / cofibration / weak equivalence" trichotomy that underpins
all model category theory.

## Mathematical Content

1. **Lifting properties**: left lifting property (LLP), right lifting property (RLP).
2. **Weak factorization systems**: (L, R) where every morphism factors as L ∘ R
   and L = LLP(R), R = RLP(L).
3. **Retract closure**: retracts of morphisms in a class remain in the class.
4. **Model category axioms**: MC1–MC5 (Quillen's axioms).
5. **Cylinder and path objects**: for homotopy theory.
6. **Type-theoretic examples**: trivial fibrations = surjections in Type.

## DAG Structure (depends on Layers 1, 7, 29)

```
  ModelCatAxioms ←── MC1–MC5
       |
  FunctorialFactorization ←── factorization axioms
       |
  WeakFactorizationSystem ←── (L, R) pair
       |
  LLP, RLP ←── lifting properties
       |
  HasLift ←── lifting squares
       |
  HigherToposFoundations (Layer 29)
```
-/
import Mathlib
import RequestProject.Foundations.HigherToposFoundations

namespace Caramello.WeakFactorizationSystems

open CategoryTheory

/-! ## Section 1: Lifting Properties

A commutative square in a category C:

```
  A ---f--→ X
  |         |
  i         p
  ↓         ↓
  B ---g--→ Y
```

has a lift h : B → X if h ∘ i = f and p ∘ h = g.
-/

/-- A commutative square in a category. -/
structure CommSquare {C : Type*} [Category C] {A B X Y : C}
    (f : A ⟶ X) (i : A ⟶ B) (p : X ⟶ Y) (g : B ⟶ Y) : Prop where
  comm : i ≫ g = f ≫ p

/-- A lift in a commutative square. -/
structure HasLift {C : Type*} [Category C] {A B X Y : C}
    (f : A ⟶ X) (i : A ⟶ B) (p : X ⟶ Y) (g : B ⟶ Y) where
  lift : B ⟶ X
  fac_left : i ≫ lift = f
  fac_right : lift ≫ p = g

/-- i has the left lifting property with respect to p if every
    commutative square with i on the left and p on the right has a lift. -/
def HasLLP {C : Type*} [Category C] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) : Prop :=
  ∀ (f : A ⟶ X) (g : B ⟶ Y), CommSquare f i p g → Nonempty (HasLift f i p g)

/-- p has the right lifting property with respect to i
    (equivalent to i having the LLP w.r.t. p). -/
def HasRLP {C : Type*} [Category C] {A B X Y : C}
    (p : X ⟶ Y) (i : A ⟶ B) : Prop := HasLLP i p

/-- LLP and RLP are equivalent (by definition). -/
theorem llp_iff_rlp {C : Type*} [Category C] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) : HasLLP i p ↔ HasRLP p i := Iff.rfl

/-- Identity morphisms have the LLP with respect to everything. -/
theorem id_hasLLP {C : Type*} [Category C] {X Y : C}
    (p : X ⟶ Y) : HasLLP (𝟙 X) p := by
  intro f g ⟨hcomm⟩
  exact ⟨⟨f, Category.id_comp f, by rw [← Category.id_comp g, ← hcomm, Category.id_comp]⟩⟩

/-- Everything has the RLP with respect to identity morphisms. -/
theorem hasRLP_id {C : Type*} [Category C] {A B : C}
    (i : A ⟶ B) : HasRLP (𝟙 B) i := by
  intro f g ⟨hcomm⟩
  exact ⟨⟨g, by rwa [Category.comp_id] at hcomm, Category.comp_id g⟩⟩

/-! ## Section 2: Morphism Classes and Retract Closure -/

/-- A class of morphisms in C. -/
def MorphismClass (C : Type*) [Category C] :=
  ∀ {X Y : C}, (X ⟶ Y) → Prop

/-- The right lifting class: all morphisms having the RLP
    with respect to every morphism in S. -/
def rightLiftingClass {C : Type*} [Category C]
    (S : MorphismClass C) : MorphismClass C :=
  fun p => ∀ {A B : C} (i : A ⟶ B), S i → HasRLP p i

/-- The left lifting class: all morphisms having the LLP
    with respect to every morphism in S. -/
def leftLiftingClass {C : Type*} [Category C]
    (S : MorphismClass C) : MorphismClass C :=
  fun i => ∀ {X Y : C} (p : X ⟶ Y), S p → HasLLP i p

/-- A retract diagram: f is a retract of g. -/
structure IsRetract {C : Type*} [Category C] {A B X Y : C}
    (f : A ⟶ B) (g : X ⟶ Y) where
  secA : A ⟶ X
  retA : X ⟶ A
  secB : B ⟶ Y
  retB : Y ⟶ B
  retract_left : secA ≫ retA = 𝟙 A
  retract_right : secB ≫ retB = 𝟙 B
  comm_top : secA ≫ g = f ≫ secB
  comm_bot : retA ≫ f = g ≫ retB

/-- Any morphism is a retract of itself. -/
def isRetract_refl {C : Type*} [Category C] {A B : C}
    (f : A ⟶ B) : IsRetract f f where
  secA := 𝟙 A
  retA := 𝟙 A
  secB := 𝟙 B
  retB := 𝟙 B
  retract_left := Category.comp_id _
  retract_right := Category.comp_id _
  comm_top := by simp
  comm_bot := by simp

/-- A morphism class is closed under retracts. -/
def IsRetractClosed {C : Type*} [Category C]
    (S : MorphismClass C) : Prop :=
  ∀ {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y),
    IsRetract f g → S g → S f

/-! ## Section 3: Weak Factorization Systems -/

/-- A factorization of f into i followed by p. -/
structure Factorization {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) where
  mid : C
  left : X ⟶ mid
  right : mid ⟶ Y
  fac : left ≫ right = f

/-- A weak factorization system (WFS) on C: a pair (L, R) where
    - every morphism factors as l ∘ r with l ∈ L and r ∈ R
    - L = LLP(R) and R = RLP(L). -/
structure WeakFactorizationSystem (C : Type*) [Category C] where
  leftClass : MorphismClass C
  rightClass : MorphismClass C
  factorize : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (Z : C) (l : X ⟶ Z) (r : Z ⟶ Y),
      leftClass l ∧ rightClass r ∧ l ≫ r = f
  left_eq_llp : ∀ {A B : C} (i : A ⟶ B),
    leftClass i ↔ ∀ {X Y : C} (p : X ⟶ Y), rightClass p → HasLLP i p
  right_eq_rlp : ∀ {X Y : C} (p : X ⟶ Y),
    rightClass p ↔ ∀ {A B : C} (i : A ⟶ B), leftClass i → HasRLP p i

/-- In a WFS, the left class has the LLP with respect to the right class. -/
theorem wfs_llp {C : Type*} [Category C]
    (W : WeakFactorizationSystem C)
    {A B X Y : C} {i : A ⟶ B} {p : X ⟶ Y}
    (hi : W.leftClass i) (hp : W.rightClass p) :
    HasLLP i p :=
  (W.left_eq_llp i).mp hi p hp

/-! ## Section 4: Model Category Axioms -/

/-- The data of three morphism classes forming a model structure. -/
structure ModelCategoryData (C : Type*) [Category C] where
  weq : MorphismClass C
  cof : MorphismClass C
  fib : MorphismClass C

/-- MC2: Two-out-of-three property for a morphism class. -/
def TwoOutOfThree {C : Type*} [Category C]
    (W : MorphismClass C) : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    (W f → W g → W (f ≫ g)) ∧
    (W f → W (f ≫ g) → W g) ∧
    (W g → W (f ≫ g) → W f)

/-- The full model category axioms. -/
structure IsModelCategory {C : Type*} [Category C]
    (M : ModelCategoryData C) : Prop where
  hasFiniteLimits : Limits.HasFiniteLimits C
  hasFiniteColimits : Limits.HasFiniteColimits C
  twoOfThree : TwoOutOfThree M.weq
  weq_retract : IsRetractClosed M.weq
  cof_retract : IsRetractClosed M.cof
  fib_retract : IsRetractClosed M.fib
  trivCof_lift_fib : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
    M.cof i → M.weq i → M.fib p → HasLLP i p
  cof_lift_trivFib : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
    M.cof i → M.fib p → M.weq p → HasLLP i p
  factor_trivCof_fib : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
      M.cof i ∧ M.weq i ∧ M.fib p ∧ i ≫ p = f
  factor_cof_trivFib : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
      M.cof i ∧ M.fib p ∧ M.weq p ∧ i ≫ p = f

/-! ## Section 5: Cylinder and Path Objects -/

/-- A cylinder object for A: A ⊔ A → Cyl(A) → A. -/
structure CylinderObject {C : Type*} [Category C] (A : C) where
  cyl : C
  incl₀ : A ⟶ cyl
  incl₁ : A ⟶ cyl
  proj : cyl ⟶ A

/-- A path object for X: X → Path(X) → X × X. -/
structure PathObject {C : Type*} [Category C] (X : C)
    [Limits.HasBinaryProduct X X] where
  path : C
  diag : X ⟶ path
  endpoints : path ⟶ X ⨯ X

/-- Left homotopy via a cylinder object. -/
def LeftHomotopic {C : Type*} [Category C] {A X : C}
    (f g : A ⟶ X) : Prop :=
  ∃ (cyl : CylinderObject A) (H : cyl.cyl ⟶ X),
    cyl.incl₀ ≫ H = f ∧ cyl.incl₁ ≫ H = g

/-- Left homotopy is reflexive (via the trivial cylinder). -/
theorem leftHomotopic_refl {C : Type*} [Category C] {A X : C}
    (f : A ⟶ X) : LeftHomotopic f f := by
  refine ⟨⟨A, 𝟙 A, 𝟙 A, 𝟙 A⟩, f, ?_, ?_⟩ <;> simp

/-! ## Section 6: Type-Theoretic Examples -/

/-- Trivial fibrations in Type are surjections. -/
def IsTrivialFibration (f : α → β) : Prop :=
  Function.Surjective f

/-- Cofibrations in Type are injections. -/
def IsCofibration (f : α → β) : Prop :=
  Function.Injective f

/-- The identity is both a trivial fibration and a cofibration. -/
theorem id_trivFib (α : Type) : IsTrivialFibration (id : α → α) :=
  Function.surjective_id

theorem id_cof (α : Type) : IsCofibration (id : α → α) :=
  Function.injective_id

/-- Composition of surjections is surjective. -/
theorem trivFib_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : IsTrivialFibration f) (hg : IsTrivialFibration g) :
    IsTrivialFibration (g ∘ f) :=
  Function.Surjective.comp hg hf

/-- Composition of injections is injective. -/
theorem cof_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : IsCofibration f) (hg : IsCofibration g) :
    IsCofibration (g ∘ f) :=
  Function.Injective.comp hg hf

/-
The lifting property: injections lift against surjections in Type.
-/
theorem type_lifting {A B X Y : Type}
    (i : A → B) (p : X → Y) (f : A → X) (g : B → Y)
    (hi : IsCofibration i) (hp : IsTrivialFibration p)
    (hcomm : p ∘ f = g ∘ i) :
    ∃ h : B → X, h ∘ i = f ∧ p ∘ h = g := by
      -- Since $p$ is surjective, we can define $h(b) = f(a)$ for any $a$ such that $i(a) = b$.
      have h_exists : ∀ b : B, ∃ x : X, p x = g b := by
        exact fun b => hp _;
      -- Define $h(b) = f(a)$ for any $a$ such that $i(a) = b$.
      have h_def : ∀ b : B, ∃ x : X, p x = g b ∧ (∀ a : A, i a = b → x = f a) := by
        intro b
        by_cases hb : ∃ a : A, i a = b;
        · obtain ⟨ a, rfl ⟩ := hb;
          exact ⟨ f a, congr_fun hcomm a, fun b hb => by have := hi hb; aesop ⟩;
        · exact Exists.elim ( h_exists b ) fun x hx => ⟨ x, hx, fun a ha => False.elim <| hb ⟨ a, ha ⟩ ⟩;
      choose h hh hh' using h_def; aesop;

/-- Every function in Type factors as injection followed by a map. -/
theorem type_factorization {A B : Type} (f : A → B) :
    ∃ (Z : Type) (i : A → Z) (p : Z → B),
      IsCofibration i ∧ (p ∘ i = f) :=
  ⟨A, id, f, Function.injective_id, by ext; simp⟩

/-! ## Section 7: Homotopy Equivalences -/

/-- A weak equivalence in Type: a bijection. -/
def IsWeakEquivalence (f : α → β) : Prop :=
  Function.Bijective f

/-
The two-out-of-three property holds for bijections.
-/
theorem weq_twoOfThree {α β γ : Type} (f : α → β) (g : β → γ) :
    (IsWeakEquivalence f → IsWeakEquivalence g → IsWeakEquivalence (g ∘ f)) ∧
    (IsWeakEquivalence f → IsWeakEquivalence (g ∘ f) → IsWeakEquivalence g) ∧
    (IsWeakEquivalence g → IsWeakEquivalence (g ∘ f) → IsWeakEquivalence f) := by
      refine' ⟨ _, _, _ ⟩ <;> intro hf hg <;> simp_all +decide [ IsWeakEquivalence, Function.Bijective ]

/-- Identity is a weak equivalence. -/
theorem id_weq (α : Type) : IsWeakEquivalence (id : α → α) :=
  Function.bijective_id

/-! ## Section 8: Summary

This layer establishes:

1. **Lifting properties** (LLP, RLP) for morphisms in any category.
2. **Weak factorization systems** as the algebraic structure underlying
   model categories.
3. **Retract closure** and its role in the model category axioms.
4. **Model category axioms** MC1–MC5 (Quillen's original formulation).
5. **Cylinder and path objects** for abstract homotopy theory.
6. **Type-theoretic examples**: surjections = trivial fibrations,
   injections = cofibrations, bijections = weak equivalences.
7. **Two-out-of-three** for weak equivalences in Type.

Key insight: In the topos Type, the "folk model structure" makes
surjections = trivial fibrations and injections = cofibrations,
while weak equivalences are bijections. This is the (−1)-truncated
shadow of the full model structure on SSet.
-/

end Caramello.WeakFactorizationSystems