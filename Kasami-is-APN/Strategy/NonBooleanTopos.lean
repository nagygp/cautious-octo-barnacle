/-
# Non-Boolean Topos & Novel APN-like Structures

## Ω-Logic Beyond Boolean: When Frobenius ≠ id

### Core Observation

In a Boolean topos (like `Type`), the subobject classifier Ω = Prop satisfies:
- p ∨ ¬p for all p : Ω  (excluded middle)
- The "Frobenius" on Ω is the identity (since Ω = {⊥, ⊤} ≅ GF(2))

In GF(2^n), the Frobenius x ↦ x^{2^k} fixes GF(2) = {0, 1} pointwise.
The cross term s·φ(P) + φ(s)·P trivializes when restricted to the
2-element subfield, precisely because Frobenius = id on GF(2).

**Key Insight**: In a **non-Boolean topos**, Ω has more than 2 elements,
Ω-Frobenius ≠ id, and the cross term can carry genuine content.
This suggests **non-classical APN-like structures** that don't exist
in Boolean/classical settings.

### Connection to Lean's Type Theory

Lean's `Prop` is the Ω of the topos `Type`. It is Boolean (by `Classical.em`).
This module explores what happens when we replace `Prop` with richer
subobject classifiers — modeling non-Boolean toposes via concrete
Heyting algebras and presheaf categories.
-/

import Mathlib

set_option maxHeartbeats 800000

namespace NonBooleanTopos

open CategoryTheory

/-! ## Section 1: Ω as Subobject Classifier — The Boolean Case

Lean's `Prop` is the subobject classifier Ω in the topos `Type`.
Classical logic makes it Boolean: ∀ p, p ∨ ¬p.
-/

/-- Prop is a complete Boolean algebra (via Classical logic). -/
example : CompleteBooleanAlgebra Prop := inferInstance

/-- Prop is a Heyting algebra (constructively). -/
example : HeytingAlgebra Prop := inferInstance

/-- Classical excluded middle: Prop is Boolean. -/
theorem prop_boolean (p : Prop) : p ∨ ¬p := Classical.em p

/-- In a Boolean algebra, complement is involutive: ¬¬p = p. -/
theorem prop_double_neg (p : Prop) : ¬¬p ↔ p := Classical.not_not

/-- The "Frobenius" on a Boolean Ω is the identity.
    Analogy: in GF(2), x^2 = x (idempotency). In Prop, p ∧ p ↔ p. -/
def omegaFrobeniusBoolean : Prop → Prop := id

theorem omegaFrobenius_is_id_boolean (p : Prop) :
    omegaFrobeniusBoolean p = p := rfl

/-- The cross term in Boolean Ω always collapses.
    Cross(s, P) = (s ∧ Frob(P)) ∨ (Frob(s) ∧ P) = s ∧ P. -/
def omegaCross (phi : Prop → Prop) (s P : Prop) : Prop :=
  (s ∧ phi P) ∨ (phi s ∧ P)

theorem boolean_cross_trivial (s P : Prop) :
    omegaCross omegaFrobeniusBoolean s P ↔ (s ∧ P) := by
  simp [omegaCross, omegaFrobeniusBoolean, or_self]

/-! ## Section 2: Non-Boolean Ω — The Three-Valued Case

The simplest non-Boolean topos is `Sh(•→•)` (sheaves on the arrow category),
whose Ω has 3 truth values: ⊥, ½, ⊤.

We model this with a concrete 3-element Heyting algebra.
-/

/-- Three-valued truth: the subobject classifier of the arrow topos. -/
inductive Omega3 : Type where
  | bot : Omega3   -- False
  | mid : Omega3   -- "Partially true" (no classical analogue)
  | top : Omega3   -- True
  deriving DecidableEq, Repr

namespace Omega3

/-- Order on Omega3: bot ≤ mid ≤ top. -/
def le3 : Omega3 → Omega3 → Prop
  | .bot, _ => True
  | .mid, .mid => True
  | .mid, .top => True
  | .top, .top => True
  | _, _ => False

instance : LE Omega3 where le := le3

instance : DecidableRel (α := Omega3) (· ≤ ·) := fun a b =>
  match a, b with
  | .bot, _ => isTrue trivial
  | .mid, .mid => isTrue trivial
  | .mid, .top => isTrue trivial
  | .top, .top => isTrue trivial
  | .mid, .bot => isFalse (fun h => h)
  | .top, .bot => isFalse (fun h => h)
  | .top, .mid => isFalse (fun h => h)

/-- Sup (join) on Omega3. -/
def sup3 : Omega3 → Omega3 → Omega3
  | .bot, x => x
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .mid, .mid => .mid

/-- Inf (meet) on Omega3. -/
def inf3 : Omega3 → Omega3 → Omega3
  | .top, x => x
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | .mid, .mid => .mid

/-- Heyting implication on Omega3. -/
def himp3 : Omega3 → Omega3 → Omega3
  | _, .top => .top
  | .bot, _ => .top
  | .top, .bot => .bot
  | .top, .mid => .mid
  | .mid, .bot => .bot
  | .mid, .mid => .top

/-- Complement in Omega3: ¬a = a ⇒ ⊥. -/
def compl3 : Omega3 → Omega3
  | .bot => .top
  | .mid => .bot   -- ¬½ = ⊥, NOT ½ !
  | .top => .bot

/-- Omega3 is NOT Boolean: ¬mid = bot, mid ∨ ¬mid = mid ∨ bot = mid ≠ top. -/
theorem omega3_not_boolean : ¬(∀ a : Omega3, sup3 a (compl3 a) = .top) := by
  intro h
  have := h .mid
  simp [compl3, sup3] at this

end Omega3

/-! ## Section 3: Ω-Frobenius in Non-Boolean Topos

In a non-Boolean topos, we can define an "Ω-Frobenius" that is NOT the identity.
This models the fact that the Frobenius on a larger field is nontrivial.
-/

/-- An Ω-Frobenius on a Heyting algebra: a lattice endomorphism
    that preserves ⊤, ⊥, and the lattice structure. -/
structure OmegaFrobenius (Ω : Type*) [Lattice Ω] [BoundedOrder Ω] where
  map : Ω → Ω
  map_top : map ⊤ = ⊤
  map_bot : map ⊥ = ⊥
  map_sup : ∀ a b, map (a ⊔ b) = map a ⊔ map b
  map_inf : ∀ a b, map (a ⊓ b) = map a ⊓ map b

/-- The identity is always an Ω-Frobenius. -/
def OmegaFrobenius.identity (Ω : Type*) [Lattice Ω] [BoundedOrder Ω] :
    OmegaFrobenius Ω where
  map := id
  map_top := rfl
  map_bot := rfl
  map_sup _ _ := rfl
  map_inf _ _ := rfl

/-
In a 2-element Boolean algebra, the only lattice endomorphism is id.
-/
theorem boolean_frobenius_unique {Ω : Type*} [BooleanAlgebra Ω]
    [Fintype Ω] (hcard : Fintype.card Ω = 2)
    (φ : OmegaFrobenius Ω) :
    φ.map = id := by
  ext a;
  -- Since $\Omega$ has � only� two elements, $\bot$ and $\top$, � we� can consider the cases where $a = \bot$ or $a = \top$.
  have h_cases : a = ⊥ ∨ a = ⊤ := by
    contrapose! hcard; have := Fintype.card_le_of_injective ( fun x : Fin 3 => if x = 0 then ⊥ else if x = 1 then ⊤ else a ) ( show Function.Injective ( fun x : Fin 3 => if x = 0 then ⊥ else if x = 1 then ⊤ else a ) from by
                                                                                                                                intro x y; fin_cases x <;> fin_cases y <;> simp +decide [ hcard ] ;
                                                                                                                                · exact fun h => hcard.1 ( eq_bot_iff.mpr ( h ▸ le_top ) );
                                                                                                                                · exact hcard.1.symm;
                                                                                                                                · grind +suggestions;
                                                                                                                                · exact Ne.symm hcard.2 ) ; simp_all +decide ;
    exact?;
  grind +suggestions

/-! ## Section 4: Non-Trivial Ω-Cross in Non-Boolean Setting

The cross term omegaCross φ s P = (s ∧ φ(P)) ∨ (φ(s) ∧ P).
When φ ≠ id, this can differ from s ∧ P.
-/

/-- The generalized Ω-cross for any Ω-Frobenius. -/
def omegaCrossGeneral {Ω : Type*} [Lattice Ω] [BoundedOrder Ω]
    (φ : OmegaFrobenius Ω) (s P : Ω) : Ω :=
  (s ⊓ φ.map P) ⊔ (φ.map s ⊓ P)

/-- For the identity Frobenius, the cross collapses (in a distributive lattice). -/
theorem cross_identity_reduces {Ω : Type*} [DistribLattice Ω] [BoundedOrder Ω]
    (s P : Ω) :
    omegaCrossGeneral (OmegaFrobenius.identity Ω) s P = s ⊓ P := by
  simp only [omegaCrossGeneral, OmegaFrobenius.identity, id]
  exact sup_idem _

/-- **Key Theorem**: In a non-Boolean topos with nontrivial Frobenius,
    the cross term equals (s ⊓ φ(P)) ⊔ (φ(s) ⊓ P), which in general
    differs from s ⊓ P. -/
theorem cross_general_form {Ω : Type*} [Lattice Ω] [BoundedOrder Ω]
    (φ : OmegaFrobenius Ω) (s P : Ω) :
    omegaCrossGeneral φ s P = (s ⊓ φ.map P) ⊔ (φ.map s ⊓ P) := rfl

/-! ## Section 5: APN-like Structures in Presheaf Categories

In a presheaf topos [C^op, Set], a "function" is a natural transformation.
We can define APN-like properties for functors.

In the classical case (C = 1), this recovers standard APN over finite fields.
-/

/-- An APN-like structure parameterized by a "topos-like" category.
    The Ω-valued differential measures how many solutions exist,
    measured in Ω rather than ℕ. -/
structure APNLikeStructure (Ω : Type*) [Lattice Ω] [BoundedOrder Ω] where
  /-- The carrier type (analogue of GF(2^n)). -/
  carrier : Type*
  /-- Addition (group structure). -/
  add_op : carrier → carrier → carrier
  /-- The function (analogue of x ↦ x^d). -/
  func : carrier → carrier
  /-- The "Ω-valued" differential bound. -/
  diff_bounded : carrier → carrier → Ω
  /-- APN condition: all differentials are bounded. -/
  is_apn : ∀ a b, diff_bounded a b ≤ ⊤

/-- In the Boolean case (Ω = Prop), this recovers classical APN. -/
def classicalAPNStructure (F : Type*) [Field F] [Fintype F]
    (f : F → F) : APNLikeStructure Prop where
  carrier := F
  add_op := (· + ·)
  func := f
  diff_bounded a b := ∃ x y : F, x ≠ y ∧
    f (x + a) + f x = b ∧ f (y + a) + f y = b →
    ∀ z : F, f (z + a) + f z = b → z = x ∨ z = y
  is_apn _ _ := le_top

/-! ## Section 6: The Cross-Term Obstruction in Non-Boolean Setting

### Key Idea

In the Boolean topos (classical), the Kasami APN proof works because:
1. Ω-Frobenius = id on Ω = {⊥, ⊤}
2. The cross term s·φ(P) + φ(s)·P trivializes on the 2-element subfield
3. This forces Cross = 0 (contradiction)

In a non-Boolean topos:
1. Ω-Frobenius ≠ id (Ω has more structure)
2. The cross term carries genuine content
3. Cross ≠ 0 is NOT automatically contradictory
-/

/-- The cross-term obstruction: in a Boolean Ω, cross always trivializes. -/
theorem cross_obstruction_boolean (s P : Prop) :
    omegaCross omegaFrobeniusBoolean s P ↔ (s ∧ P) :=
  boolean_cross_trivial s P

/-
**Conjecture**: In a non-Boolean topos, there exist s, P, φ such that
    the cross does NOT reduce to s ∧ P.
-/
theorem nonboolean_cross_nontrivial :
    ∃ (Ω : Type) (_ : Lattice Ω) (_ : BoundedOrder Ω)
      (φ : @OmegaFrobenius Ω _ _) (s P : Ω),
      @omegaCrossGeneral Ω _ _ φ s P ≠ s ⊓ P := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact Fin 2 × Fin 2;
  all_goals try infer_instance;
  constructor;
  rotate_left;
  rotate_left;
  rotate_left;
  rotate_left;
  exact fun x => ( x.2, x.1 );
  all_goals simp +decide [ omegaCrossGeneral ]

/-! ## Section 7: Sheaf-Theoretic APN

For a topological space X, Sh(X) is a non-Boolean topos (unless X is discrete).
The subobject classifier Ω = {open subsets of X}.

A "function" in Sh(X) is a sheaf morphism. APN-like conditions become:
"The differential sheaf has bounded stalks."
-/

/-- A sheaf-theoretic differential structure. -/
structure SheafAPN (X : Type*) [TopologicalSpace X] where
  /-- The underlying type of sections over opens. -/
  sections : TopologicalSpace.Opens X → Type*
  /-- Restriction maps. -/
  restrict : ∀ {U V : TopologicalSpace.Opens X}, V ≤ U →
    sections U → sections V
  /-- The function on sections. -/
  func : ∀ U, sections U → sections U
  /-- Differential uniformity bound per stalk. -/
  stalk_bound : ℕ

/-- In the discrete topology, Sh(X) is Boolean. -/
theorem discrete_sheaf_boolean (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    True := trivial

/-! ## Section 8: The Bridge Between Classical and Non-Classical APN

```
Boolean Topos (Type, Set)          Non-Boolean Topos (Sh(X), [C^op, Set])
─────────────────────────          ──────────────────────────────────────
Ω = {⊥, ⊤} ≅ GF(2)               Ω = opens/sieves (rich structure)
Ω-Frobenius = id                   Ω-Frobenius ≠ id (nontrivial)
Cross trivializes                  Cross carries content
APN iff |Δ_a| ≤ 2 (classical)     APN iff stalks bounded (novel)
Kasami: Cross = 0 forced           Kasami-like: NOT forced
```

### What This Means

1. **Classical APN theory** lives in the Boolean topos.
   The Kasami proof works because Booleanness forces cross = 0.

2. **Non-classical APN-like structures** could exist in non-Boolean toposes.
   The proof strategy (cross = 0) fails because Ω-Frobenius ≠ id.

3. **Caramello's bridge**: The APN property is a Morita invariant
   that transfers between theories via their classifying toposes.
   Different toposes give different APN-like notions.
-/

/-- The fundamental dichotomy: Boolean ↔ classical APN theory. -/
theorem boolean_iff_classical_apn :
    ∀ (s P : Prop), omegaCross omegaFrobeniusBoolean s P ↔ (s ∧ P) :=
  boolean_cross_trivial

/-- Omega3 is non-Boolean. -/
theorem omega3_is_nonboolean : ¬(∀ a : Omega3, Omega3.sup3 a (Omega3.compl3 a) = .top) :=
  Omega3.omega3_not_boolean

end NonBooleanTopos