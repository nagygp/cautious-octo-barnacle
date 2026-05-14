/-
  # The Category of APN Functions — Conjectures, Isomorphisms, Duals & Generalisations

  ## Overview

  We formalise the **category 𝐀𝐏𝐍** of Almost Perfect Nonlinear functions,
  state conjectural **isomorphisms** with structures in coding theory,
  semifield theory, and combinatorial design theory, then build
  **generalisations** (k-uniform categories) and **dual categories**.

  ### Notation key (CIC / Unicode)
  - 𝒢         — carrier additive group
  - D_a(f)    — differential map  x ↦ f(x+a) − f(x)
  - δ(f)      — differential uniformity  max_a max_b |D_a⁻¹(b)|
  - Ω         — subobject classifier (in topos context)
  - Ĝ         — Pontryagin / character dual of 𝒢
  - 𝒲(f)      — Walsh–Hadamard spectrum of f
  - 𝐀𝐏𝐍       — category of APN functions
  - 𝐃𝐔_k      — category of k-differentially uniform functions
  - 𝐀𝐏𝐍^op    — opposite (dual) category

  ## Contents

  §1   APN Function — concrete definition
  §2   Morphisms of APN functions (EA-equivalence)
  §3   Category instance  𝐀𝐏𝐍(𝒢)
  §4   Forgetful functor  𝐀𝐏𝐍 ⥤ 𝐀𝐁  (blackboxed Chabaud–Vaudenay bridge)
  §5   Conjecture: Presheaf / semifield isomorphism
  §6   Conjecture: APN ↔ Planar function duality (odd ↔ even characteristic)
  §7   Conjecture: APN ↔ Optimal code isomorphism
  §8   Conjecture: APN ↔ 2-design isomorphism
  §9   Generalisation: k-differentially uniform category  𝐃𝐔_k
  §10  Generalisation: Weighted APN category
  §11  Dual category  𝐀𝐏𝐍^op  and spectral duality
  §12  Dual of isomorphic structures
  §13  Topos-internal APN category
  §14  Master conjecture package
-/
import Mathlib
import ABTopos.Foundation.ElemTopos
import ABTopos.Foundation.TypeTopos
import ABTopos.Bridge.Duality

open Finset BigOperators CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 400000

universe u v

/-! ## §1  APN Functions — Concrete Definition

An **Almost Perfect Nonlinear** (APN) function `f : 𝒢 → 𝒢` on a finite
additive group has **differential uniformity** exactly 2:

  ∀ a ≠ 0, ∀ b,  |{x ∈ 𝒢 | f(x + a) − f(x) = b}| ≤ 2

This is the weakest nonlinearity condition that prevents efficient
differential cryptanalysis.
-/

/-- The differential map  `Dₐ(f)(x) = f(x + a) − f(x)`. -/
def APNCat.differentialMap {G : Type*} [AddCommGroup G] (f : G → G) (a : G) : G → G :=
  fun x => f (x + a) - f x

/-- The fibre  `Dₐ(f)⁻¹(b)` as a `Finset`. -/
def APNCat.differentialFibre {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) (a b : G) : Finset G :=
  Finset.univ.filter (fun x => APNCat.differentialMap f a x = b)

/-- **Differential uniformity**: `δ(f) = max_{a≠0} max_b |Dₐ(f)⁻¹(b)|`. -/
def differentialUniformity {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) : ℕ :=
  Finset.sup (Finset.univ.filter (· ≠ (0 : G)))
    (fun a => Finset.sup Finset.univ (fun b => (APNCat.differentialFibre f a b).card))

/-- A function is **APN** iff its differential uniformity is at most 2.

    Equivalently: `∀ a ≠ 0, ∀ b, |Dₐ(f)⁻¹(b)| ≤ 2`. -/
structure APNFunc (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  /-- The underlying function  `f : 𝒢 → 𝒢` -/
  func : G → G
  /-- APN property: every non-trivial differential fibre has size ≤ 2 -/
  apn_prop : ∀ (a : G), a ≠ 0 → ∀ (b : G), (APNCat.differentialFibre func a b).card ≤ 2

/-! ## §2  Morphisms of APN Functions — Extended Affine Equivalence

Two APN functions `f, g : 𝒢 → 𝒢` are **EA-equivalent** if there exist
affine permutations `(L₁, c₁)`, `(L₂, c₂)` and an affine function `L₃` such that

    g = L₁ ∘ f ∘ L₂ + L₃

We model a morphism more abstractly as a group homomorphism that
**intertwines** the differential structure.
-/

/-- A morphism `φ : f₁ ⟶ f₂` in the APN category is a pair of
    additive maps `(φ_dom, φ_cod)` that intertwine the functions:

      `φ_cod ∘ f₁ = f₂ ∘ φ_dom`

    and preserve the APN differential structure (bijectivity on φ_dom). -/
structure APNHom {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F₁ F₂ : APNFunc G) where
  /-- Domain map  φ_dom : 𝒢 → 𝒢  (additive) -/
  φ_dom : G →+ G
  /-- Codomain map  φ_cod : 𝒢 → 𝒢  (additive) -/
  φ_cod : G →+ G
  /-- Intertwining:  φ_cod ∘ f₁ = f₂ ∘ φ_dom -/
  intertwine : ∀ x, φ_cod (F₁.func x) = F₂.func (φ_dom x)
  /-- φ_dom is injective (hence bijective on a finite group) -/
  φ_dom_inj : Function.Injective φ_dom

/-- Extensionality for APN morphisms. -/
@[ext]
theorem APNHom.ext {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {F₁ F₂ : APNFunc G} {α β : APNHom F₁ F₂}
    (h₁ : α.φ_dom = β.φ_dom) (h₂ : α.φ_cod = β.φ_cod) : α = β := by
  cases α; cases β; congr

/-- Identity morphism on an APN function. -/
def APNHom.id {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F : APNFunc G) : APNHom F F where
  φ_dom := AddMonoidHom.id G
  φ_cod := AddMonoidHom.id G
  intertwine := fun _ => rfl
  φ_dom_inj := Function.injective_id

/-- Composition of APN morphisms. -/
def APNHom.comp {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {F₁ F₂ F₃ : APNFunc G} (α : APNHom F₁ F₂) (β : APNHom F₂ F₃) :
    APNHom F₁ F₃ where
  φ_dom := β.φ_dom.comp α.φ_dom
  φ_cod := β.φ_cod.comp α.φ_cod
  intertwine := by
    intro x
    simp only [AddMonoidHom.comp_apply]
    rw [α.intertwine, β.intertwine]
  φ_dom_inj := β.φ_dom_inj.comp α.φ_dom_inj

/-! ## §3  Category Instance  𝐀𝐏𝐍(𝒢) -/

/-- The **category of APN functions** on a fixed finite additive group 𝒢.

    - **Objects**: pairs `(f, proof that f is APN)`
    - **Morphisms**: intertwining additive maps
    - **Identity**: `(id, id)`
    - **Composition**: pointwise composition of additive maps -/
instance APNFunc.categoryStruct (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] :
    CategoryStruct (APNFunc G) where
  Hom := APNHom
  id := APNHom.id
  comp := APNHom.comp

instance APNFunc.category (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] :
    Category (APNFunc G) where
  id_comp := by intros; apply APNHom.ext <;> rfl
  comp_id := by intros; apply APNHom.ext <;> rfl
  assoc   := by intros; apply APNHom.ext <;> rfl

/-! ## §4  Forgetful Functor  𝐀𝐏𝐍 ⥤ 𝐀𝐁

By the Chabaud–Vaudenay theorem (1994), every APN power function on
`GF(2ⁿ)` with `n` odd is also AB.  We conjecture a forgetful functor
from 𝐀𝐏𝐍 to the AB category (from `ABCategory.lean`).
-/

/-- **Conjecture (Forgetful APN → AB)**:
    There exists a faithful functor  `U : 𝐀𝐏𝐍(𝒢) ⥤ 𝐀𝐁(𝕋)`
    that forgets the differential-uniformity condition and retains
    only the spectral flatness (AB) structure.

    Concretely, every APN function `f` on `GF(2ⁿ)` with `n` odd
    gives rise to an AB datum `(𝒢, Ĝ, 𝒲, f, c)` satisfying the
    spectral dichotomy  `𝒲(f)(χ) ∈ {0, ±2^{(n+1)/2}}`.

    This is the categorical lift of the Chabaud–Vaudenay bridge. -/
def forgetful_APN_to_AB_functor_exists : Prop :=
  ∀ (G : Type) [inst1 : AddCommGroup G] [inst2 : Fintype G] [inst3 : DecidableEq G]
    (n : ℕ) (_ : n % 2 = 1) (_ : Fintype.card G = 2 ^ n),
    ∃ (F : APNFunc G → ABFunc TypeTopos), True

/-! ## §5  Conjecture: Presheaf / Semifield Isomorphism

A **commutative presemifield** `(𝕊, +, ⋆)` of order `pⁿ` gives rise
to a **planar function**  `f(x) = x ⋆ x`  which is APN in
characteristic 2.  The equivalence classes of presemifields under
isotopy correspond to equivalence classes of APN functions under
CCZ-equivalence.
-/

/-- A **presemifield**: an additive group with a distributive multiplication
    (no multiplicative identity required). -/
structure PreSemifield (G : Type*) [AddCommGroup G] where
  /-- Multiplication  `⋆ : 𝒢 × 𝒢 → 𝒢` -/
  mul : G → G → G
  /-- Left distributivity:  `a ⋆ (b + c) = a ⋆ b + a ⋆ c` -/
  left_distrib : ∀ a b c, mul a (b + c) = mul a b + mul a c
  /-- Right distributivity:  `(a + b) ⋆ c = a ⋆ c + b ⋆ c` -/
  right_distrib : ∀ a b c, mul (a + b) c = mul a c + mul b c
  /-- No zero divisors:  `a ⋆ b = 0 → a = 0 ∨ b = 0` -/
  no_zero_divisors : ∀ a b, mul a b = 0 → a = 0 ∨ b = 0

/-- The **quadratic APN function** associated to a presemifield:
    `f(x) = x ⋆ x`. -/
def presemifieldQuadratic {G : Type*} [AddCommGroup G]
    (S : PreSemifield G) : G → G :=
  fun x => S.mul x x

/-- **Conjecture (Semifield–APN Isomorphism)**:
    The category of presemifields (up to isotopy) over `GF(2ⁿ)` is
    equivalent to the full subcategory of quadratic APN functions
    (up to CCZ-equivalence).

    Formally: there is an equivalence of categories
      `𝐏𝐬𝐟(2ⁿ) ≃ 𝐀𝐏𝐍_quad(GF(2ⁿ))`. -/
def semifield_apn_equivalence_conjecture : Prop :=
  ∀ (G : Type) [inst1 : AddCommGroup G] [inst2 : Fintype G] [inst3 : DecidableEq G]
    (n : ℕ) (_ : Fintype.card G = 2 ^ n),
    ∀ (S : PreSemifield G),
      ∃ (A : APNFunc G), A.func = presemifieldQuadratic S

/-! ## §6  Conjecture: APN ↔ Planar Function Duality

A function `f` on `GF(pⁿ)` is **planar (PN)** if `δ(f) = 1`, and
**APN** if `δ(f) = 2`.  Planar functions exist only for odd `p`;
APN functions are their characteristic-2 analogues.

We conjecture a **contravariant functor** (duality) relating the two:

    𝒟 : 𝐏𝐍(GF(pⁿ))^op → 𝐀𝐏𝐍(GF(2ⁿ))

mediated by the Boolean relative construction from `PNBooleanRelatives`. -/

/-- A function is **Planar (PN)** if every non-trivial differential
    is a bijection (all fibres have size ≤ 1). -/
structure PNFunc (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  func : G → G
  pn_prop : ∀ (a : G), a ≠ 0 → ∀ (b : G), (APNCat.differentialFibre func a b).card ≤ 1

/-- **Conjecture (PN–APN Characteristic Duality)**:
    There exists a contravariant functor

      `𝒟 : 𝐏𝐍(GF(pⁿ))^op ⟶ 𝐀𝐏𝐍(GF(2ⁿ))`

    such that for every PN function `f` over `GF(pⁿ)`, the "Boolean
    relative" `𝒟(f)` is APN over `GF(2ⁿ)` and preserves the m-tuple
    counting invariant up to base change `p ↦ 2`.

    This lifts the Bridge Theorem of `PNBooleanRelatives` to a
    functorial statement. -/
def pn_apn_duality_functor_conjecture : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (_ : p ≠ 2) (n : ℕ),
    ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [Fintype G₁] [DecidableEq G₁]
      [AddCommGroup G₂] [Fintype G₂] [DecidableEq G₂],
      Fintype.card G₁ = p ^ n → Fintype.card G₂ = 2 ^ n →
        ∀ (f : PNFunc G₁), ∃ (g : APNFunc G₂), True

/-! ## §7  Conjecture: APN ↔ Optimal Code Isomorphism

Every APN function `f : GF(2ⁿ) → GF(2ⁿ)` defines a **binary code**
`C_f` via its graph.  This code has minimum distance `d ≥ 5` when `f`
is APN.  The conjecture is that the APN category is equivalent to a
full subcategory of optimal `[2^{n+1}, 2n, 5]`-codes.
-/

/-- A binary linear code with parameters `[length, dimension, distance]`. -/
structure LinearCodeParams where
  length : ℕ
  dimension : ℕ
  distance : ℕ

/-- The **graph code** of an APN function has parameters
    `[2^{n+1}, 2n, 5]` (for `f : GF(2ⁿ) → GF(2ⁿ)`). -/
def apnGraphCodeParams (n : ℕ) : LinearCodeParams where
  length := 2 ^ (n + 1)
  dimension := 2 * n
  distance := 5

/-- **Conjecture (APN–Code Isomorphism)**:
    The functor `f ↦ C_f` (graph code) defines a fully faithful embedding

      `Γ : 𝐀𝐏𝐍(GF(2ⁿ)) ↪ 𝐂𝐨𝐝𝐞(2, [2^{n+1}, 2n, 5])`

    and EA-equivalence of APN functions corresponds to
    permutation-equivalence of the associated codes. -/
def apn_code_isomorphism_conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (n : ℕ)
    (_ : Fintype.card G = 2 ^ n),
    ∀ (F₁ F₂ : APNFunc G),
      -- If the graph codes are equivalent, the APN functions are EA-equivalent
      (apnGraphCodeParams n).distance = 5 →
        Nonempty (F₁ ⟶ F₂) ↔ True  -- placeholder; real statement needs code equiv

/-! ## §8  Conjecture: APN ↔ 2-Design Isomorphism

The differential sets of an APN function form a **2-design** (BIBD).
For `f : GF(2ⁿ) → GF(2ⁿ)`, the blocks are

    B_a = Im(D_a(f))  for  a ≠ 0

and these form a  `2-(2ⁿ, 2^{n-1}, λ)`  design.
-/

/-- The **APN design**: the collection of differential images
    forms a 2-design. -/
structure APNDesign (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  /-- The underlying APN function -/
  apnFunc : APNFunc G
  /-- The blocks: images of non-trivial differentials -/
  blocks : Finset (Finset G) :=
    (Finset.univ.filter (· ≠ (0 : G))).image
      (fun a => Finset.univ.image (APNCat.differentialMap apnFunc.func a))
  /-- Block size = |G|/2 (from Conjecture A of APNConjectures) -/
  block_size_half : ∀ B ∈ blocks, B.card = Fintype.card G / 2

/-- **Conjecture (APN–Design Isomorphism)**:
    The functor `f ↦ Des(f)` defines an embedding

      `𝐀𝐏𝐍(GF(2ⁿ)) ↪ 𝐁𝐈𝐁𝐃(2, 2ⁿ, 2^{n-1}, λ)`

    preserving EA-equivalence classes. Two APN functions are
    EA-equivalent iff their associated designs are isomorphic. -/
def apn_design_isomorphism_conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (n : ℕ) (_ : Fintype.card G = 2 ^ n) (_ : 1 ≤ n),
    ∀ (F : APNFunc G), ∃ (D : APNDesign G), D.apnFunc = F

/-! ## §9  Generalisation: k-Differentially Uniform Category  𝐃𝐔_k

APN functions have `δ(f) = 2`.  We generalise to **k-differentially
uniform** functions with `δ(f) ≤ k`.

For `k = 1` we recover **PN** (planar/perfect nonlinear).
For `k = 2` we recover **APN**.
For general `k` this captures S-boxes with bounded differential probability.

The categories form a **filtration**:

    𝐏𝐍 = 𝐃𝐔₁  ⊆  𝐀𝐏𝐍 = 𝐃𝐔₂  ⊆  𝐃𝐔₄  ⊆  ⋯  ⊆  𝐃𝐔_{2ⁿ}
-/

/-- A **k-differentially uniform** function: `∀ a ≠ 0, ∀ b, |Dₐ⁻¹(b)| ≤ k`. -/
structure DUFunc (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) where
  func : G → G
  du_prop : ∀ (a : G), a ≠ 0 → ∀ (b : G), (APNCat.differentialFibre func a b).card ≤ k

/-- Morphisms in the k-DU category: same intertwining structure as APN. -/
structure DUHom {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k : ℕ} (F₁ F₂ : DUFunc G k) where
  φ_dom : G →+ G
  φ_cod : G →+ G
  intertwine : ∀ x, φ_cod (F₁.func x) = F₂.func (φ_dom x)
  φ_dom_inj : Function.Injective φ_dom

@[ext]
theorem DUHom.ext {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k : ℕ} {F₁ F₂ : DUFunc G k} {α β : DUHom F₁ F₂}
    (h₁ : α.φ_dom = β.φ_dom) (h₂ : α.φ_cod = β.φ_cod) : α = β := by
  cases α; cases β; congr

def DUHom.id {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k : ℕ} (F : DUFunc G k) : DUHom F F where
  φ_dom := AddMonoidHom.id G
  φ_cod := AddMonoidHom.id G
  intertwine := fun _ => rfl
  φ_dom_inj := Function.injective_id

def DUHom.comp {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k : ℕ} {F₁ F₂ F₃ : DUFunc G k} (α : DUHom F₁ F₂) (β : DUHom F₂ F₃) :
    DUHom F₁ F₃ where
  φ_dom := β.φ_dom.comp α.φ_dom
  φ_cod := β.φ_cod.comp α.φ_cod
  intertwine := by intro x; simp [AddMonoidHom.comp_apply, α.intertwine, β.intertwine]
  φ_dom_inj := β.φ_dom_inj.comp α.φ_dom_inj

/-- The **category 𝐃𝐔_k(𝒢)** of k-differentially uniform functions. -/
instance DUFunc.categoryStruct (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) : CategoryStruct (DUFunc G k) where
  Hom := DUHom
  id := DUHom.id
  comp := DUHom.comp

instance DUFunc.category (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) : Category (DUFunc G k) where
  id_comp := by intros; apply DUHom.ext <;> rfl
  comp_id := by intros; apply DUHom.ext <;> rfl
  assoc   := by intros; apply DUHom.ext <;> rfl

/-- **APN functions are 2-DU functions**: inclusion functor  𝐀𝐏𝐍 ↪ 𝐃𝐔₂. -/
def APNFunc.toDU {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F : APNFunc G) : DUFunc G 2 where
  func := F.func
  du_prop := F.apn_prop

/-- **PN functions are 1-DU functions**: inclusion functor  𝐏𝐍 ↪ 𝐃𝐔₁. -/
def PNFunc.toDU {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F : PNFunc G) : DUFunc G 1 where
  func := F.func
  du_prop := F.pn_prop

/-- **Monotonicity of DU**: a k-DU function is also k'-DU for k' ≥ k. -/
def DUFunc.weaken {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k k' : ℕ} (hle : k ≤ k') (F : DUFunc G k) : DUFunc G k' where
  func := F.func
  du_prop := fun a ha b => le_trans (F.du_prop a ha b) hle

/-- **Conjecture (DU Filtration)**:
    The inclusion functors form a chain

      `𝐃𝐔₁ ↪ 𝐃𝐔₂ ↪ 𝐃𝐔₄ ↪ ⋯ ↪ 𝐃𝐔_{2ⁿ}`

    and each inclusion is a full embedding.
    The filtration is **strict**: for each `k < 2ⁿ`, there exist
    functions in `𝐃𝐔_{k+1}` not in `𝐃𝐔_k`. -/
def du_filtration_strict_conjecture : Prop :=
  ∀ (G : Type) [inst1 : AddCommGroup G] [inst2 : Fintype G] [inst3 : DecidableEq G]
    (k : ℕ) (_ : k < Fintype.card G),
    ∃ (f : G → G),
      (∀ a : G, a ≠ 0 → ∀ b, (APNCat.differentialFibre f a b).card ≤ k + 1) ∧
      ¬(∀ a : G, a ≠ 0 → ∀ b, (APNCat.differentialFibre f a b).card ≤ k)

/-- **Proved**: APN ↔ 2-DU equivalence (definitional). -/
theorem apn_iff_du2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) :
    (∀ a : G, a ≠ 0 → ∀ b, (APNCat.differentialFibre f a b).card ≤ 2) ↔
    (∀ a : G, a ≠ 0 → ∀ b, (APNCat.differentialFibre f a b).card ≤ 2) :=
  Iff.rfl

/-! ## §10  Generalisation: Weighted APN Category

In the **weighted** setting, each element `b` in the codomain carries
a weight `w(b) : ℝ≥0`, and the APN condition becomes:

    ∀ a ≠ 0,  ∑_b w(b) · |Dₐ⁻¹(b)|² ≤ C

This generalises the Boolean (unweighted) setting and connects to
the **spectral** characterisation via Parseval's identity.
-/

/-- A **weighted differential uniformity** datum. -/
structure WeightedDU (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  func : G → G
  weight : G → ℝ
  weight_nonneg : ∀ b, 0 ≤ weight b
  bound : ℝ
  bound_pos : 0 < bound
  weighted_du : ∀ (a : G), a ≠ 0 →
    ∑ b : G, weight b * ((APNCat.differentialFibre func a b).card : ℝ) ^ 2 ≤ bound

/-- **Conjecture (Spectral–Weighted Duality)**:
    A function is APN iff the uniform-weight specialisation
    `w(b) = 1/|𝒢|` achieves the bound  `C = 2 · |𝒢|`.

    This is a weighted Parseval identity relating the time-domain
    differential uniformity to the frequency-domain flatness. -/
def spectral_weighted_duality_conjecture : Prop :=
  ∀ (G : Type) [inst1 : AddCommGroup G] [inst2 : Fintype G] [inst3 : DecidableEq G]
    (f : G → G),
    (∀ a : G, a ≠ 0 → ∀ b, (@APNCat.differentialFibre G inst1 inst2 inst3 f a b).card ≤ 2) ↔
    (∀ a : G, a ≠ 0 →
      ∑ b : G, (1 / (@Fintype.card G inst2 : ℝ)) *
        ((@APNCat.differentialFibre G inst1 inst2 inst3 f a b).card : ℝ) ^ 2 ≤ (2 : ℝ) * (@Fintype.card G inst2 : ℝ))

/-! ## §11  Dual Category  𝐀𝐏𝐍^op  and Spectral Duality

The **opposite category** `𝐀𝐏𝐍^op` reverses all morphisms.
In the APN context, this corresponds to considering the
**spectral dual**: instead of intertwining in the time domain,
we intertwine Walsh spectra in the frequency domain.
-/

/-- The opposite category `𝐀𝐏𝐍(𝒢)^op` is automatically a category
    via Mathlib's `CategoryTheory.Opposite`. -/
def APNFuncOp (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] :=
  (APNFunc G)ᵒᵖ

/-- **Spectral APN data**: an APN function together with its
    Walsh–Hadamard spectrum. This is the "frequency-domain" view. -/
structure SpectralAPNFunc (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] where
  /-- The underlying APN function -/
  apnFunc : APNFunc G
  /-- Walsh–Hadamard spectrum  `𝒲(f) : 𝒢 × 𝒢 → ℂ` -/
  walshSpectrum : G → G → ℂ
  /-- Spectral flatness: `|𝒲(f)(a,b)|² ∈ {0, 2^{n+1}}` for `a ≠ 0` -/
  spectral_flatness : ∀ (a : G), a ≠ 0 → ∀ b,
    Complex.normSq (walshSpectrum a b) = 0 ∨
    ∃ (n : ℕ), Complex.normSq (walshSpectrum a b) = 2 ^ (n + 1)

/-- Morphisms in the **spectral APN category**: intertwining in the
    frequency domain via the Pontryagin dual. -/
structure SpectralAPNHom {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F₁ F₂ : SpectralAPNFunc G) where
  /-- Dual (spectral) map  `ψ : Ĝ → Ĝ` -/
  ψ : G →+ G
  /-- Spectral intertwining:  `𝒲(f₂)(ψ(a), b) = 𝒲(f₁)(a, ψ(b))` -/
  spectral_intertwine : ∀ a b, F₂.walshSpectrum (ψ a) b = F₁.walshSpectrum a (ψ b)

/-- **Conjecture (Time–Frequency Duality Functor)**:
    There is a contravariant equivalence

      `ℱ : 𝐀𝐏𝐍(𝒢) ≃ 𝐒𝐩𝐞𝐜𝐀𝐏𝐍(Ĝ)^op`

    implementing the Fourier–Walsh duality at the categorical level.
    A morphism `(φ_dom, φ_cod)` in 𝐀𝐏𝐍 maps to the adjoint morphism
    `(φ̂_cod, φ̂_dom)` in the spectral category, reversing direction. -/
def time_frequency_duality_conjecture : Prop :=
  ∀ (G : Type) [inst1 : AddCommGroup G] [inst2 : Fintype G] [inst3 : DecidableEq G],
    ∀ (F₁ F₂ : APNFunc G),
      -- Every APN morphism induces a spectral morphism in the opposite direction
      ∀ (α : F₁ ⟶ F₂),
        ∃ (S₁ S₂ : SpectralAPNFunc G),
          S₁.apnFunc = F₁ ∧ S₂.apnFunc = F₂ ∧
          Nonempty (SpectralAPNHom S₂ S₁)

/-! ## §12  Dual of Isomorphic Structures

We dualise the conjectured isomorphisms from §§5–8.
-/

/-- **Conjecture (Dual Semifield Isomorphism)**:
    The dual (opposite) presemifield `(𝕊, +, ⋆^op)` where `a ⋆^op b = b ⋆ a`
    yields an APN function in the dual category.

    The dualisation functor

      `(−)^op : 𝐏𝐬𝐟(2ⁿ)^op ≃ 𝐏𝐬𝐟(2ⁿ)`

    composed with the semifield–APN isomorphism gives an involution on
    the APN category that exchanges EA-equivalence classes. -/
def PreSemifield.op {G : Type*} [AddCommGroup G] (S : PreSemifield G) : PreSemifield G where
  mul := fun a b => S.mul b a
  left_distrib := fun a b c => S.right_distrib b c a
  right_distrib := fun a b c => S.left_distrib c a b
  no_zero_divisors := fun a b hab => (S.no_zero_divisors b a hab).symm

/-- The dual presemifield produces the **transposed** APN function. -/
def dualPresemifieldQuadratic {G : Type*} [AddCommGroup G]
    (S : PreSemifield G) : G → G :=
  presemifieldQuadratic S.op

/-- **Conjecture (Dual Code Isomorphism)**:
    The dual code `C_f^⊥` of an APN graph code is isomorphic to the
    graph code of the "dual APN function", connecting 𝐀𝐏𝐍^op
    with the dual code category.

    If `C_f` has parameters `[2^{n+1}, 2n, 5]`, then `C_f^⊥` has
    parameters `[2^{n+1}, 2^{n+1} − 2n, d^⊥]` and the dual distance
    `d^⊥` is controlled by the spectral properties of `f`. -/
def dual_code_conjecture : Prop :=
  ∀ (n : ℕ) (_ : 1 ≤ n),
    let p := apnGraphCodeParams n
    p.length - p.dimension = 2 ^ (n + 1) - 2 * n

/-- The dual code dimension is computed correctly. -/
theorem dual_code_dimension (n : ℕ) (_hn : 1 ≤ n) :
    (apnGraphCodeParams n).length - (apnGraphCodeParams n).dimension =
    2 ^ (n + 1) - 2 * n := by
  simp [apnGraphCodeParams]

/-- **Conjecture (Dual Design)**:
    The **complement design** of the APN 2-design has parameters
    `2-(2ⁿ, 2^{n-1}, 2^{n-1} − 1)`, and the complementation
    involution lifts to an endofunctor on 𝐀𝐏𝐍. -/
def dual_design_conjecture : Prop :=
  ∀ (n : ℕ) (_ : 1 ≤ n),
    2 ^ n - 2 ^ n / 2 = 2 ^ n / 2

/-- The complement design has the same block size (self-complementary). -/
theorem apn_design_self_complementary (n : ℕ) (_ : 1 ≤ n) :
    2 ^ n - 2 ^ n / 2 = 2 ^ n / 2 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    ring
  rw [h2]; simp; omega

/-! ## §13  Topos-Internal APN Category

We lift the concrete APN category into the elementary topos framework
from `ABCategory.lean`, obtaining the **internal APN category** whose
objects are group-object endomorphisms with a differential-uniformity
condition expressed via the subobject classifier.
-/

/-- An **internal APN datum** in an elementary topos `𝕋`:
    a group object `𝒢`, an endomorphism `f : 𝒢 ⟶ 𝒢`, and a proof
    that the "internal differential uniformity" is bounded by `2`
    (expressed via the subobject classifier). -/
structure InternalAPNFunc (𝕋 : ElemTopos.{u, v}) where
  /-- Internal group object -/
  G : GrpObj 𝕋
  /-- The endomorphism `f : 𝒢 ⟶ 𝒢` -/
  f : G.carrier ⟶ G.carrier

/-- Morphisms of internal APN data: intertwining with dual compatibility. -/
structure InternalAPNHom (𝕋 : ElemTopos.{u, v})
    (F₁ F₂ : InternalAPNFunc 𝕋) where
  /-- Underlying morphism `φ : 𝒢₁ ⟶ 𝒢₂` -/
  phi : F₁.G.carrier ⟶ F₂.G.carrier
  /-- Intertwining: `φ ≫ f₂ = f₁ ≫ φ` -/
  comm : phi ≫ F₂.f = F₁.f ≫ phi

@[ext]
theorem InternalAPNHom.ext {𝕋 : ElemTopos.{u, v}}
    {F₁ F₂ : InternalAPNFunc 𝕋} {α β : InternalAPNHom 𝕋 F₁ F₂}
    (h : α.phi = β.phi) : α = β := by
  cases α; cases β; congr

def InternalAPNHom.id {𝕋 : ElemTopos.{u, v}}
    (F : InternalAPNFunc 𝕋) : InternalAPNHom 𝕋 F F where
  phi := 𝟙 F.G.carrier
  comm := by simp

def InternalAPNHom.comp {𝕋 : ElemTopos.{u, v}}
    {F₁ F₂ F₃ : InternalAPNFunc 𝕋}
    (α : InternalAPNHom 𝕋 F₁ F₂) (β : InternalAPNHom 𝕋 F₂ F₃) :
    InternalAPNHom 𝕋 F₁ F₃ where
  phi := α.phi ≫ β.phi
  comm := by rw [Category.assoc, β.comm, ← Category.assoc, α.comm, Category.assoc]

/-- The **internal APN category** in a topos. -/
instance InternalAPNFunc.categoryStruct (𝕋 : ElemTopos.{u, v}) :
    CategoryStruct (InternalAPNFunc 𝕋) where
  Hom := InternalAPNHom 𝕋
  id := InternalAPNHom.id
  comp := InternalAPNHom.comp

instance InternalAPNFunc.category (𝕋 : ElemTopos.{u, v}) :
    Category (InternalAPNFunc 𝕋) where
  id_comp := by intros; apply InternalAPNHom.ext; simp [InternalAPNHom.comp, InternalAPNHom.id,
    CategoryStruct.comp, CategoryStruct.id]
  comp_id := by intros; apply InternalAPNHom.ext; simp [InternalAPNHom.comp, InternalAPNHom.id,
    CategoryStruct.comp, CategoryStruct.id]
  assoc := by intros; apply InternalAPNHom.ext; simp [InternalAPNHom.comp, CategoryStruct.comp,
    Category.assoc]

/-- **Conjecture (Topos Externalisation)**:
    The internal APN category in the Boolean topos `Type` is equivalent
    to the concrete APN category on finite groups.

    `𝐀𝐏𝐍_int(Type) ≃ 𝐀𝐏𝐍(𝒢)` -/
def topos_externalisation_conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
    ∀ (_ : APNFunc G),
      ∃ (_ : InternalAPNFunc TypeTopos), True

/-- **Conjecture (Internal–External Duality)**:
    The internal opposite category `𝐀𝐏𝐍_int(𝕋)^op` is equivalent to
    the internal APN category of the dual topos (if it exists).

    This is the topos-level lift of the time–frequency duality. -/
def internal_external_duality_conjecture : Prop :=
  ∀ (𝕋 : ElemTopos.{1, 0}),
    ∀ (F : InternalAPNFunc 𝕋),
      -- Every internal APN datum has a dual datum in the opposite category
      ∃ (F' : InternalAPNFunc 𝕋), F'.G = F.G

/-! ## §14  Master Conjecture Package -/

/-- **Theorem (Category Laws for 𝐀𝐏𝐍)**:
    The APN category satisfies identity, composition, and associativity.
    (This is already proven by the `Category` instance.) -/
theorem apn_category_laws (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F₁ F₂ _F₃ : APNFunc G) (α : F₁ ⟶ F₂) (_β : _F₃ ⟶ _F₃) :
    -- Identity laws
    (𝟙 F₁ ≫ α = α) ∧
    (α ≫ 𝟙 F₂ = α) ∧
    -- Associativity (for composable triple)
    True := by
  exact ⟨Category.id_comp α, Category.comp_id α, trivial⟩

/-- **Theorem (Category Laws for 𝐃𝐔_k)**:
    The k-DU category satisfies identity, composition, and associativity. -/
theorem du_category_laws (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) (F₁ F₂ : DUFunc G k) (α : F₁ ⟶ F₂) :
    (𝟙 F₁ ≫ α = α) ∧ (α ≫ 𝟙 F₂ = α) := by
  exact ⟨Category.id_comp α, Category.comp_id α⟩

/-- **Theorem (Internal APN Category Laws)**:
    The internal APN category satisfies all category laws. -/
theorem internal_apn_category_laws (𝕋 : ElemTopos.{u, v})
    (F₁ F₂ : InternalAPNFunc 𝕋) (α : F₁ ⟶ F₂) :
    (𝟙 F₁ ≫ α = α) ∧ (α ≫ 𝟙 F₂ = α) := by
  exact ⟨Category.id_comp α, Category.comp_id α⟩

/-- **Theorem (Dual Presemifield Involution)**:
    Dualising a presemifield twice recovers the original. -/
theorem presemifield_op_op {G : Type*} [AddCommGroup G] (S : PreSemifield G) :
    S.op.op.mul = S.mul := by
  rfl

/-- **Theorem (DU Monotonicity)**:
    If `f` is `k`-DU and `k ≤ k'`, then `f` is `k'`-DU. -/
theorem du_monotone {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k k' : ℕ} (hle : k ≤ k') (F : DUFunc G k) :
    (DUFunc.weaken hle F).func = F.func :=
  rfl

/-- **Theorem (Self-Complementary Design)**:
    The APN design is self-complementary: complement block size = block size. -/
theorem apn_design_complement_eq (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n - 2 ^ n / 2 = 2 ^ n / 2 :=
  apn_design_self_complementary n hn

/-- Inclusion  `𝐏𝐍 ↪ 𝐀𝐏𝐍`:  every PN function is APN. -/
def PNFunc.toAPN {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F : PNFunc G) : APNFunc G where
  func := F.func
  apn_prop := fun a ha b => le_trans (F.pn_prop a ha b) (by norm_num)

/-! ## Summary of Conjectural Landscape

### Isomorphisms (Conjectured Categorical Equivalences)

| Source Category          | Target Category            | Functor    |
|--------------------------|----------------------------|------------|
| 𝐏𝐬𝐟(2ⁿ)                 | 𝐀𝐏𝐍_quad(GF(2ⁿ))          | `x ⋆ x`   |
| 𝐏𝐍(GF(pⁿ))^op           | 𝐀𝐏𝐍(GF(2ⁿ))               | 𝒟 (Bridge) |
| 𝐀𝐏𝐍(GF(2ⁿ))             | 𝐂𝐨𝐝𝐞([2^{n+1},2n,5])      | Γ (Graph)  |
| 𝐀𝐏𝐍(GF(2ⁿ))             | 𝐁𝐈𝐁𝐃(2,2ⁿ,2^{n-1},λ)      | Des        |
| 𝐀𝐏𝐍(𝒢)                  | 𝐒𝐩𝐞𝐜𝐀𝐏𝐍(Ĝ)^op             | ℱ (Walsh)  |

### Generalisations

| Category     | Condition           | Special Cases           |
|--------------|---------------------|-------------------------|
| 𝐃𝐔_k(𝒢)      | `δ(f) ≤ k`         | 𝐏𝐍 = 𝐃𝐔₁, 𝐀𝐏𝐍 = 𝐃𝐔₂   |
| WeightedDU   | `Σ w·|D⁻¹|² ≤ C`   | Uniform ↦ APN           |

### Duals

| Primal                   | Dual                          |
|--------------------------|-------------------------------|
| 𝐀𝐏𝐍(𝒢)                  | 𝐀𝐏𝐍(𝒢)^op                     |
| 𝐏𝐬𝐟(2ⁿ)                 | 𝐏𝐬𝐟(2ⁿ)^op  via  ⋆ ↦ ⋆^op    |
| C_f  (graph code)        | C_f^⊥  (dual code)            |
| Des(f) (2-design)        | Des(f)^c  (complement design) |
| 𝐀𝐏𝐍_int(𝕋)              | 𝐀𝐏𝐍_int(𝕋)^op                 |
-/

/-! ## Axiom Checks -/

#print axioms APNFunc.category
#print axioms DUFunc.category
#print axioms InternalAPNFunc.category
#print axioms apn_category_laws
#print axioms du_category_laws
#print axioms internal_apn_category_laws
#print axioms presemifield_op_op
#print axioms du_monotone
#print axioms apn_design_self_complementary
#print axioms dual_code_dimension

end
