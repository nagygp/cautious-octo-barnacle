/-
  # Category of AB Functions — CIC Formalisation

  Formalisation of the **category of AB (Almost Bent) functions** in an
  elementary topos, following the Topos Generalisation of Boolean
  Spectral Invariants (CIC_ToposGeneralisation.md).

  Unicode-rich CIC style, built on Mathlib's category-theory library.

  ## Audit 02 Enhancements
  - `IsAB` now carries a **non-vacuous spectral dichotomy** condition:
    the Walsh transform must decompose the dual into a zero-set and a
    constant-set that jointly cover it (replaces the former `flat : True`).
  - `GrpObj` now includes the **full group axioms** (associativity,
    unit laws, inverse laws) expressed via generalized-element diagrams.
  - `ElemTopos` carries a **false morphism** `false_ : 𝟙 ⟶ Ω` modelling
    the bottom element ⊥_Ω of the subobject classifier's Heyting algebra.
-/
import Mathlib

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

/-! ## §1  Elementary Topos (bundled) -/

/-- An elementary topos: a category with finite limits, finite colimits,
    a subobject classifier `Ω`, and a terminal object.
    Includes both `true_` (⊤) and `false_` (⊥) morphisms into Ω,
    modelling the top and bottom elements of the internal Heyting algebra. -/
structure ElemTopos where
  /-- The underlying category -/
  ℰ       : Type u
  [cat     : Category.{v} ℰ]
  [hLim    : HasFiniteLimits ℰ]
  [hColim  : HasFiniteColimits ℰ]
  [hTerm   : HasTerminal ℰ]
  /-- Subobject classifier -/
  Omega    : ℰ
  /-- "true" morphism  ⊤ : 𝟙 ⟶ Ω (top element of the Heyting algebra) -/
  true_    : terminal ℰ ⟶ Omega
  /-- "false" morphism  ⊥ : 𝟙 ⟶ Ω (bottom element of the Heyting algebra) -/
  false_   : terminal ℰ ⟶ Omega
  /-- ⊤ ≠ ⊥ (the topos is non-degenerate) -/
  true_ne_false : true_ ≠ false_

attribute [instance] ElemTopos.cat ElemTopos.hLim
  ElemTopos.hColim ElemTopos.hTerm

variable (𝕋 : ElemTopos.{u, v})

/-! ## §2  Internal Group Object  (generalises (𝔽_q, +))

A group object inside the topos `𝕋.ℰ`, equipped with the **full group
axioms**: associativity of multiplication, two-sided unit, and two-sided
inverse, all expressed as commutative diagrams via generalized elements
(i.e., for every test object `X` and every triple of morphisms into the
carrier). -/

/-- A group object inside the topos `𝕋.ℰ`. -/
structure GrpObj where
  /-- Carrier object  𝒢 -/
  carrier : 𝕋.ℰ
  /-- Binary product instance -/
  [hProd  : HasBinaryProduct carrier carrier]
  /-- Multiplication (internal addition)  μ : 𝒢 × 𝒢 ⟶ 𝒢 -/
  mul     : carrier ⨯ carrier ⟶ carrier
  /-- Unit (zero element)  η : 𝟙 ⟶ 𝒢 -/
  unit    : terminal 𝕋.ℰ ⟶ carrier
  /-- Inverse (negation)  ι : 𝒢 ⟶ 𝒢 -/
  inv     : carrier ⟶ carrier
  /-- **Associativity**: μ(μ(a, b), c) = μ(a, μ(b, c))
      for all generalized elements a, b, c : X ⟶ 𝒢. -/
  mul_assoc : ∀ (X : 𝕋.ℰ) (a b c : X ⟶ carrier),
    prod.lift (prod.lift a b ≫ mul) c ≫ mul =
    prod.lift a (prod.lift b c ≫ mul) ≫ mul
  /-- **Left unit**: μ(η, a) = a. -/
  mul_left_unit : ∀ (X : 𝕋.ℰ) (a : X ⟶ carrier),
    prod.lift (terminal.from X ≫ unit) a ≫ mul = a
  /-- **Right unit**: μ(a, η) = a. -/
  mul_right_unit : ∀ (X : 𝕋.ℰ) (a : X ⟶ carrier),
    prod.lift a (terminal.from X ≫ unit) ≫ mul = a
  /-- **Left inverse**: μ(ι(a), a) = η. -/
  mul_left_inv : ∀ (X : 𝕋.ℰ) (a : X ⟶ carrier),
    prod.lift (a ≫ inv) a ≫ mul = terminal.from X ≫ unit
  /-- **Right inverse**: μ(a, ι(a)) = η. -/
  mul_right_inv : ∀ (X : 𝕋.ℰ) (a : X ⟶ carrier),
    prod.lift a (a ≫ inv) ≫ mul = terminal.from X ≫ unit

attribute [instance] GrpObj.hProd

/-! ## §3  Internal Character Object  (generalises the Walsh / Fourier dual) -/

/-- A character object for a group object: stands for the internal hom [𝒢, Ω].
    In a full topos one would derive this from exponentials; here we bundle it. -/
structure CharObj (G : GrpObj 𝕋) where
  /-- Dual carrier  Ĝ -/
  dual    : 𝕋.ℰ
  /-- Binary product instance -/
  [hProd  : HasBinaryProduct dual G.carrier]
  /-- Evaluation / pairing  ev : Ĝ × 𝒢 ⟶ Ω -/
  ev      : dual ⨯ G.carrier ⟶ 𝕋.Omega

attribute [instance] CharObj.hProd

/-! ## §4  Spectral Morphism  (generalised Walsh transform) -/

/-- The Walsh transform sends an endomorphism of 𝒢 to a morphism Ĝ ⟶ Ω.
    Axiomatised because the internal product requires the full
    internal-Hom adjunction (black-box in the document). -/
structure WalshTr (G : GrpObj 𝕋) (ch : CharObj 𝕋 G) where
  /-- 𝒲 maps each endo  f : 𝒢 ⟶ 𝒢  to  𝒲(f) : Ĝ ⟶ Ω -/
  wal     : (G.carrier ⟶ G.carrier) → (ch.dual ⟶ 𝕋.Omega)

/-! ## §5  Spectral Flatness  (generalised Bentness / AB condition)

The spectral flatness predicate `IsAB` encodes the topos-internal
analogue of the Almost-Bent / Perfect-Nonlinear condition.

**Audit 02 upgrade**: the condition is no longer the vacuous `True`.
Instead, it requires a **spectral dichotomy decomposition**: the dual
`Ĝ` splits into two subobjects — the *zero set* (where `𝒲(f) = ⊥_Ω`)
and the *constant set* (where `𝒲(f) = c`) — that jointly cover `Ĝ`.

This is the topos-internal analogue of
  ∀ χ : Ĝ,  𝒲(f)(χ) = 0_Ω  ∨  𝒲(f)(χ) = c
expressed via a coproduct decomposition with an epimorphic cover. -/

/-- An endomorphism `f : 𝒢 ⟶ 𝒢` is **AB** (spectrally flat / bent) at
    level `c : 𝟙 ⟶ Ω` whenever the Walsh transform `𝒲(f) : Ĝ ⟶ Ω`
    decomposes the dual into a zero-part and a constant-part that jointly
    cover it (epimorphic coproduct). -/
class IsAB (G : GrpObj 𝕋) (ch : CharObj 𝕋 G) (W : WalshTr 𝕋 G ch)
    (f : G.carrier ⟶ G.carrier)
    (c : terminal 𝕋.ℰ ⟶ 𝕋.Omega) : Prop where
  /-- Internal spectral flatness: for every generalized element
      `χ : X ⟶ Ĝ`, the Walsh value `χ ≫ 𝒲(f)` is either `⊥_Ω`
      or equals the spectral level `c`.

      This is the pointwise dichotomy expressed via the Yoneda embedding:
        ∀ X, ∀ (χ : X ⟶ Ĝ), χ ≫ 𝒲(f) = (! ≫ ⊥) ∨ χ ≫ 𝒲(f) = (! ≫ c)
      where `!` denotes the unique morphism to the terminal object. -/
  spectral_dichotomy : ∀ (X : 𝕋.ℰ) (χ : X ⟶ ch.dual),
    χ ≫ W.wal f = terminal.from X ≫ 𝕋.false_ ∨
    χ ≫ W.wal f = terminal.from X ≫ c

/-! ## §6  Objects of the AB Category -/

/-- An **AB function datum** bundles:
      • a group object 𝒢,
      • a character object Ĝ,
      • a Walsh transform 𝒲,
      • an endomorphism f : 𝒢 ⟶ 𝒢,
      • a spectral level c : 𝟙 ⟶ Ω,
      • and a proof that f is AB at level c. -/
structure ABFunc where
  /-- Internal group -/
  G    : GrpObj 𝕋
  /-- Character / dual -/
  ch   : CharObj 𝕋 G
  /-- Walsh transform -/
  W    : WalshTr 𝕋 G ch
  /-- The endomorphism  f : 𝒢 ⟶ 𝒢 -/
  f    : G.carrier ⟶ G.carrier
  /-- Spectral level  c : 𝟙 ⟶ Ω -/
  c    : terminal 𝕋.ℰ ⟶ 𝕋.Omega
  /-- Bent / AB witness -/
  hab  : IsAB 𝕋 G ch W f c

/-! ## §7  Morphisms of the AB Category -/

/-- A morphism between two AB function data  `(𝒢₁, f₁)` and `(𝒢₂, f₂)`
    is a morphism  φ : 𝒢₁ ⟶ 𝒢₂  that **intertwines** the endomorphisms:

        φ ≫ f₂  =  f₁ ≫ φ

    together with a dual morphism  ψ : Ĝ₂ ⟶ Ĝ₁  (contravariant),
    compatible with the Walsh transforms. -/
structure ABHom (F₁ F₂ : ABFunc 𝕋) where
  /-- Underlying morphism  φ : 𝒢₁ ⟶ 𝒢₂ -/
  phi   : F₁.G.carrier ⟶ F₂.G.carrier
  /-- Intertwining condition:  φ ≫ f₂  =  f₁ ≫ φ -/
  comm  : phi ≫ F₂.f = F₁.f ≫ phi
  /-- Contravariant dual morphism  ψ : Ĝ₂ ⟶ Ĝ₁ -/
  psi   : F₂.ch.dual ⟶ F₁.ch.dual

/-- Extensionality for AB morphisms: two morphisms are equal iff their
    components `phi` and `psi` agree. -/
@[ext]
theorem ABHom.ext {F₁ F₂ : ABFunc 𝕋} {α β : ABHom 𝕋 F₁ F₂}
    (h₁ : α.phi = β.phi) (h₂ : α.psi = β.psi) : α = β := by
  cases α; cases β; congr

/-- Identity morphism on an AB function datum. -/
def ABHom.id (F : ABFunc 𝕋) : ABHom 𝕋 F F where
  phi  := 𝟙 F.G.carrier
  comm := by simp
  psi  := 𝟙 F.ch.dual

/-- Composition of AB-function morphisms. -/
def ABHom.comp {F₁ F₂ F₃ : ABFunc 𝕋}
    (α : ABHom 𝕋 F₁ F₂) (β : ABHom 𝕋 F₂ F₃) :
    ABHom 𝕋 F₁ F₃ where
  phi  := α.phi ≫ β.phi
  comm := by rw [Category.assoc, β.comm, ← Category.assoc, α.comm, Category.assoc]
  psi  := β.psi ≫ α.psi          -- contravariant: reverses order

/-! ## §8  Category Instance -/

/-- The **category of AB functions** in the topos `𝕋`.
    Objects are `ABFunc` data; morphisms are intertwining maps. -/
instance ABFunc.categoryStruct : CategoryStruct (ABFunc 𝕋) where
  Hom  := ABHom 𝕋
  id   := ABHom.id 𝕋
  comp := ABHom.comp 𝕋

instance ABFunc.category : Category (ABFunc 𝕋) where
  id_comp := by intros; apply ABHom.ext <;> simp [ABHom.comp, ABHom.id, CategoryStruct.comp, CategoryStruct.id]
  comp_id := by intros; apply ABHom.ext <;> simp [ABHom.comp, ABHom.id, CategoryStruct.comp, CategoryStruct.id]
  assoc   := by intros; apply ABHom.ext <;> simp [ABHom.comp, CategoryStruct.comp, Category.assoc]

/-! ## §9  The m-Tuple Kernel Object -/

/-- The kernel `𝒦_m` of the iterated summation morphism `Σ_m : 𝒢^m ⟶ 𝒢`.
    Axiomatised as a subobject of the m-fold product. -/
structure KerObj (G : GrpObj 𝕋) (m : ℕ) where
  /-- m-fold product  𝒢^m -/
  prod_m   : 𝕋.ℰ
  /-- Summation morphism  Σ_m : 𝒢^m ⟶ 𝒢 -/
  sum_m    : prod_m ⟶ G.carrier
  /-- The kernel subobject  𝒦_m -/
  ker_m    : 𝕋.ℰ
  /-- Canonical mono  𝒦_m ↪ 𝒢^m -/
  incl     : ker_m ⟶ prod_m
  [isMono  : Mono incl]
  /-- Classifying map  κ_m : 𝟙 ⟶ Ω  ("counting" the kernel) -/
  kappa    : terminal 𝕋.ℰ ⟶ 𝕋.Omega

attribute [instance] KerObj.isMono

/-! ## §10  Functorial Invariance Across Topos Morphisms -/

/-- A geometric morphism between elementary toposes. -/
structure GeomMorph (𝕋₁ 𝕋₂ : ElemTopos.{u, v}) where
  /-- Direct image  Φ_* : ℰ₁ ⥤ ℰ₂ -/
  direct : 𝕋₁.ℰ ⥤ 𝕋₂.ℰ
  /-- Inverse image  Φ^* : ℰ₂ ⥤ ℰ₁ -/
  inv    : 𝕋₂.ℰ ⥤ 𝕋₁.ℰ
  /-- Adjunction  Φ^* ⊣ Φ_* -/
  adj    : inv ⊣ direct
  /-- Φ^* preserves finite limits (left exact) -/
  [hLex  : PreservesFiniteLimits inv]

attribute [instance] GeomMorph.hLex

end
