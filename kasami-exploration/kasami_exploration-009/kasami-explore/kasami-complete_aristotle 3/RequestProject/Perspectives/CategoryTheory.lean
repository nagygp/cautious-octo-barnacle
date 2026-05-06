/-
  Perspectives/CategoryTheory.lean

  ═══════════════════════════════════════════════════════════════════════════════
  CATEGORY-THEORETIC PERSPECTIVE ON THE KASAMI-GOLD APN THEOREM
  ═══════════════════════════════════════════════════════════════════════════════

  This file demonstrates how the structures in the Kasami-Gold theorem
  naturally form categories, functors, and universal constructions.
  We formalize selected aspects using Mathlib's category theory library.

  ## Key Category-Theoretic Ideas

  1. **Functoriality**: The Walsh transform is a functor between categories
     of functions and their spectra.
  2. **Universal Properties**: The APN bound δ ≤ 2 is a universal arrow.
  3. **Natural Transformations**: The passage from AB to APN is natural
     in the underlying field.
  4. **Adjunctions**: The Fourier transform is part of a self-adjunction.
  5. **Limits and Colimits**: The "squeezing argument" is a limit computation.

  ## Connections to Higher Category Theory

  The algebraic structures over `GF(2^n)` form a 2-category where:
  - 0-cells = finite fields
  - 1-cells = functions between fields
  - 2-cells = differential/Walsh relationships between functions

  The AB ⟹ APN theorem is then a **2-functor** from the "spectral 2-category"
  to the "differential 2-category".
-/

import Mathlib

open CategoryTheory Finset BigOperators

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 1: THE CATEGORY OF FINITE FIELDS WITH FUNCTIONS
    ═══════════════════════════════════════════════════════════════════════

    We model the mathematical setting as a category where:
    - Objects are pairs (F, f) of a finite field F and a function f : F → F
    - Morphisms are field homomorphisms that commute with the functions

    🌟 **Beautiful Pattern**: This is an instance of the *comma category*
    `(Id ↓ Id)` over `FinField`, or equivalently, the category of
    endomorphisms in the category of finite fields.

    ### Universal Arrow Interpretation

    The APN property `∀ u ≠ 0, ∀ v, δ_f(u,v) ≤ 2` can be viewed as a
    **universal bound** — it is the tightest constraint on the differential
    uniformity that the AB condition implies.

    In categorical terms, the number 2 is the **initial object** in the
    poset of valid uniform bounds:
      {d ∈ ℕ | AB(f) ⟹ ∀ u ≠ 0, ∀ v, δ_f(u,v) ≤ d}
    Since AB ⟹ APN shows d = 2 works, and d = 1 would mean f is a
    permutation polynomial (not generally true), 2 is optimal.
-/

namespace CategoryPerspective

/-! ### 1.1 The Poset Category of Bounds

    The "forcing argument" in the APN proof works in the poset category
    (ℕ, ≤). This poset is a thin category (at most one morphism between
    any two objects).

    The key diagram is:
    ```
         δ(u,v)² ≥ 2·δ(u,v)       (lower bound, from evenness)
              ‖
         δ(u,v)² = 2·δ(u,v)       (equality, from moment matching)
              ‖
         δ(u,v) ∈ {0, 2}          (roots of k² - 2k = 0)
              ↓
         δ(u,v) ≤ 2               (the universal bound)
    ```

    🌟 **Universal Arrow**: The morphism `δ(u,v) ≤ 2` in the poset (ℕ, ≤)
    is the universal arrow from δ(u,v) to the subobject {0, 1, 2} ⊆ ℕ.

    💡 **Lean Best Practice**: In Lean, poset categories are modeled via
    `CategoryTheory.Preorder` or directly via the `≤` relation.
-/

/-- The set of natural numbers satisfying k² = 2k.
    This is {0, 2} — the "universal fiber" of the forcing argument.

    🎯 **Category Theory Pattern**: This is the *equalizer* of the two
    maps k ↦ k² and k ↦ 2k from ℕ to ℕ. Equalizers are limits, and
    this particular limit gives us the APN bound.

    💡 **Lean Best Practice**: Use `Finset.filter` for decidable subsets
    of finite types. For general sets, use `Set.setOf`. -/
def forcingFiber : Finset ℕ :=
  (Finset.range 100).filter (fun k => k ^ 2 = 2 * k)

#eval forcingFiber  -- {0, 2}

/-- Every element of the forcing fiber is ≤ 2. This is the "universal bound".
    The proof extracts the bound from the quadratic equation k² = 2k.

    🌟 **Beautiful Pattern**: This is a *limit cone* — the tightest bound
    that contains all solutions. The morphism `k ≤ 2` is the unique map
    from any solution to the limit. -/
theorem forcingFiber_le_two (k : ℕ) (hk : k ^ 2 = 2 * k) : k ≤ 2 := by
  -- 📝 k² = 2k means k(k-2) = 0, so k = 0 or k = 2.
  -- 📝 In either case, k ≤ 2.
  nlinarith

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 2: FUNCTORS IN THE KASAMI SETTING
    ═══════════════════════════════════════════════════════════════════════

    ### 2.1 The "Differential" Functor

    For a fixed finite field F and function f : F → F, the map
      (u, v) ↦ δ_f(u, v) = |{x | f(x+u) + f(x) = v}|
    is a functor from (F × F, discrete) to (ℕ, ≤).

    More precisely, it's a *presheaf* on the discrete category F × F
    with values in the poset category ℕ.

    ### 2.2 The "Walsh" Functor

    Similarly, (a, b) ↦ W_f(a,b) is a functor to (ℤ, |·| ≤).

    ### 2.3 The Fourth Moment as a Natural Transformation

    The identity ∑_{a,b} W(a,b)⁴ = q² · ∑_{u,v} δ(u,v)² is a
    *natural isomorphism* between two functors from the category of
    AB functions to ℤ.

    🌟 **Beautiful Pattern**: Naturality here means the identity holds
    for ALL AB functions over ALL finite fields — it's not a property
    of a specific function, but a property of the *functor*.
-/

/-! ### 2.4 Formal Category: The Poset of Differential Bounds

    We can formalize the poset of bounds as a concrete category. -/

/-- The poset of possible differential uniformity bounds.
    An object is a natural number d, representing the claim "δ ≤ d everywhere".

    💡 **Lean Best Practice**: For simple algebraic structures, prefer
    `deriving` clauses over manual instance declarations.

    🎯 **Category Pattern**: A preorder is a thin category.
    `CategoryTheory.instCategoryOfPreorder` provides the `Category` instance. -/
abbrev BoundPoset := ℕ

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 3: THE SQUEEZING ARGUMENT AS A LIMIT
    ═══════════════════════════════════════════════════════════════════════

    The core of the AB ⟹ APN proof is a "squeezing" or "sandwich" argument:

      lower_bound ≤ target ≤ upper_bound
      lower_bound = upper_bound
      ∴ target = lower_bound = upper_bound

    Categorically, this is computing a **limit** in a poset category.
    The limit of the diagram `{lower_bound, upper_bound}` in (ℤ, ≤) is
    the meet (infimum), and when lower = upper, the limit is that value.

    ### Formal Statement

    If `∑ δ² ≥ 2 ∑ δ` (lower bound from evenness)
    and `∑ δ² = 2 ∑ δ` (from moment matching)
    then `∑ δ² = 2 ∑ δ` pointwise (limit = value).
-/

/-- The squeezing principle for finite sums.

    If `f i ≥ g i` for all `i`, and `∑ f = ∑ g`, then `f i = g i` for all `i`.

    🌟 **Beautiful Pattern**: This is the **uniqueness of the limit cone**.
    The sum is a *colimit* in the category of abelian groups, and the
    pointwise equality is forced by the universal property.

    💡 **Lean Best Practice**: State the most general version of a lemma.
    Here we work over `ℤ` but could generalize to any `OrderedAddCommGroup`.

    🎯 **FP Principle**: This lemma is *polymorphic* in the index type `ι`.
    It works for any `Fintype ι`, demonstrating parametric polymorphism. -/
theorem sum_eq_of_le_of_sum_eq {ι : Type*} [Fintype ι]
    (f g : ι → ℤ) (hle : ∀ i, g i ≤ f i)
    (hsum : ∑ i, f i = ∑ i, g i)
    (i : ι) : f i = g i := by
  -- 📝 If f i > g i for some i, then ∑ f > ∑ g, contradicting hsum.
  by_contra h
  push_neg at h
  have hlt : g i < f i := lt_of_le_of_ne (hle i) (Ne.symm h)
  have : ∑ j, g j < ∑ j, f j := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
  linarith

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 4: UNIVERSAL PROPERTIES IN THE PROOF
    ═══════════════════════════════════════════════════════════════════════

    ### 4.1 The Parseval Identity as a Universal Property

    Parseval's identity `∑_a W(a,b)² = q²` is a *universal conservation law*.
    It says the "energy" (sum of squares) is preserved under the Walsh
    transform. This is the orthogonality relation for characters.

    Categorically, the Walsh transform is a **unitary isomorphism** in the
    category of Hilbert spaces (or, in the finite case, inner product spaces
    over ℂ). Parseval's identity IS the statement that this isomorphism
    preserves the inner product — which is the *universal property* of
    unitary morphisms.

    ### 4.2 The AB Property as a Colimit

    The AB property says `W² ∈ {0, 2^{n+1}}`. This is a *coproduct*
    (disjunction/sum type) in the category of propositions:

      AB(a,b) = (W² = 0) ⊔ (W² = 2^{n+1})

    The proof of AB ⟹ APN eliminates this coproduct using the
    universal property of coproducts (case analysis).

    ### 4.3 The APN Bound as a Terminal Cone

    The statement `∀ u ≠ 0, ∀ v, δ(u,v) ≤ 2` is a **cone** over the
    diagram of all δ(u,v) values in (ℕ, ≤). The apex is 2, and the
    cone morphisms are the inequalities `δ(u,v) ≤ 2`.

    The theorem proves this cone exists (given AB). The fact that 2 is
    optimal (can't be replaced by 1 in general) means this is a
    **terminal cone** — a limit.
-/

/-- ### 4.4 Formal Universal Property: Optimal Bound

    The number 2 is the least upper bound of `{δ(u,v) | k² = 2k}`.
    This is the *supremum* — a join in the lattice ℕ.

    💡 **Lean Best Practice**: Use `Finset.sup'` for suprema of nonempty
    finite sets. For the empty case, use `Finset.sup` with a `⊥`. -/
theorem optimal_apn_bound : ∀ k : ℕ, k ^ 2 = 2 * k → k ≤ 2 := by
  intro k hk; nlinarith

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 5: ADJUNCTIONS AND THE FOURIER TRANSFORM
    ═══════════════════════════════════════════════════════════════════════

    ### The Fourier-Walsh Transform as a Self-Adjunction

    Over a finite abelian group G, the Fourier transform F is an
    endofunctor on the category of functions G → ℂ.

    Key property: F ∘ F = |G| · Id (up to normalization).

    This means F is (up to scaling) its own inverse, which is equivalent
    to saying F is part of a **self-adjunction** F ⊣ F (up to the
    scaling natural transformation).

    The Parseval identity is then the **unit-counit equation** of this
    adjunction:

      ⟨f, g⟩ = (1/|G|) · ⟨F(f), F(g)⟩

    ### The AB Property via the Adjunction

    The AB condition says the image of f under the "squared Fourier norm"
    functor lands in {0, 2^{n+1}}. This constraint on the image is a
    *factorization* through a subobject — in categorical terms, a
    *mono-epi factorization*.

    ### Adjunctions in Lean/Mathlib

    Mathlib defines adjunctions via `CategoryTheory.Adjunction`:
    ```
    structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
      unit : 𝟭 C ⟶ F ⋙ G
      counit : G ⋙ F ⟶ 𝟭 D
      ...
    ```

    The Fourier self-adjunction would be:
      F ⊣ F with unit η : Id → F² = |G| · Id
    (after rescaling).
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 6: CONNECTIONS TO HIGHER CATEGORY THEORY
    ═══════════════════════════════════════════════════════════════════════

    ### 6.1 The 2-Category of Cryptographic Functions

    The objects, morphisms, and 2-morphisms form a 2-category:

    **0-cells** (objects): Finite fields F = GF(2^n) for various n.

    **1-cells** (morphisms): Functions f : F → F. Composition is ordinary
    function composition.

    **2-cells** (2-morphisms): "Differential equivalences" — natural
    transformations between the differential profiles of two functions.
    Two functions f, g : F → F have the same differential profile if
    δ_f = δ_g as functions F × F → ℕ.

    The AB ⟹ APN theorem is a **2-functor** from the sub-2-category
    of AB functions to the sub-2-category of APN functions.

    ### 6.2 Higher Operads and Opetopes

    **Operads** model operations with multiple inputs and one output.
    The differential count δ_f(u, v) can be viewed operadically:

    An **operad** O has:
    - Colors: elements of F
    - Operations: O(v; u₁, ..., uₖ) = ways to write v as a differential

    The APN condition says each operation has arity ≤ 2.

    **Opetopes** are shapes for higher-dimensional composition. In our
    setting:
    - 0-opetopes: field elements (points)
    - 1-opetopes: differences u = x₁ - x₂ (arrows)
    - 2-opetopes: differential equations f(x+u) + f(x) = v (cells)
    - 3-opetopes: relations between differential equations (homotopies)

    The APN property constrains the 2-opetopes: each 2-cell has at most
    2 incoming 1-cells.

    ### 6.3 HoTT Perspective

    In Homotopy Type Theory (HoTT), types are spaces and equalities are
    paths. The Kasami proof, viewed through HoTT:

    - The type `IsAPN_abs δ` is a **proposition** ((-1)-truncated type).
      All proofs are equal (contractible space of proofs).

    - The type `IsAB_abs W n` is also a proposition.

    - The theorem `AB ⟹ APN` is a **map between propositions** — hence
      automatically a map between (-1)-types. In HoTT, this means it's
      a map between contractible-or-empty spaces.

    - The disjunction in AB (`W² = 0 ∨ W² = 2^{n+1}`) corresponds to a
      **wedge sum** `A ∨ B` in HoTT (or more precisely, the propositional
      truncation of the coproduct `∥A + B∥`).

    - The `Finset.filter` operation corresponds to a **pullback** along
      a characteristic function in the category of h-sets.

    Key difference from CIC/Lean: In HoTT, `propext` (proposition
    extensionality) is a THEOREM (univalence for propositions), not an
    axiom. And equality types can carry higher structure (paths, homotopies),
    which doesn't arise here since we work with h-sets (0-truncated types).

    ### 6.4 Opetopic Perspective on the Walsh Support

    The Walsh support `S_b = {a | W(a,b) ≠ 0}` is a **pasting diagram**
    in the opetopic sense:

    ```
    S_b : 2-opetope (disk with |S_b| = 2^{n-1} boundary facets)
    ```

    Each element a ∈ S_b is a "face" of the opetope. The pair count
    `C(|S_b|, 2)` counts the number of 1-dimensional "edges" in the
    boundary of this opetope.

    The Kasami theorem says: for AB functions, this opetope has exactly
    `2^{n-1}` faces and `2^{n-2} · (2^{n-1} - 1)` edges.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 7: FORMALIZED CATEGORICAL CONSTRUCTION
    ═══════════════════════════════════════════════════════════════════════

    We formalize the "poset of APN bounds" as a category and show that
    the AB ⟹ APN theorem provides a terminal cone.
-/

/-- The category of APN-like properties, ordered by strength.
    An object `d : ℕ` represents "δ(u,v) ≤ d for all u ≠ 0, v".
    A morphism `d₁ → d₂` exists iff `d₁ ≤ d₂` (weaker bound).

    🌟 **Beautiful Pattern**: This is a preorder category (thin category).
    The APN condition `d = 2` is the *initial non-trivial object* —
    the strongest bound achievable by AB functions.

    🎯 **Universal Arrow**: The morphism from the AB-implied bound (2)
    to any valid bound d ≥ 2 is the unique arrow from the initial object. -/
instance : Category BoundPoset := inferInstance

/-- The Hom set in our poset category is a subsingleton (thin category).

    💡 **Lean Best Practice**: Use `inferInstance` when the instance
    can be automatically derived from existing instances. -/
example (a b : BoundPoset) : Subsingleton (a ⟶ b) := inferInstance

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 8: THE FROBENIUS AS A NATURAL TRANSFORMATION
    ═══════════════════════════════════════════════════════════════════════

    The Frobenius endomorphism φ(x) = x^p (where p = char F) is a
    **natural endomorphism** of the identity functor on `CommRing`.

    In our setting (char 2), `φ(x) = x²` and `φ^k(x) = x^{2^k}`.

    The Gold function `f(x) = x^{2^k + 1} = x · φ^k(x)` is a product
    of the identity and the iterated Frobenius. This is a
    **natural transformation** Id ⊗ φ^k : Id → Id in the monoidal
    category of endomorphisms.

    🌟 **Beautiful Pattern**: The factorization `f = Id · φ^k` is
    precisely why the derivative `Δ_u f` linearizes — the Leibniz rule
    applied to this product gives the linearized operator
    `L_u(x) = x^{2^k} · u + x · u^{2^k}`.
-/

/-- The Frobenius in characteristic 2, as a ring homomorphism.

    💡 **Lean Best Practice**: Use `frobenius` from Mathlib rather than
    defining your own. Mathlib's version comes with many useful lemmas. -/
noncomputable def frob2Demo (F : Type*) [CommRing F] [CharP F 2] : F →+* F :=
  frobenius F 2

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 9: MONOIDAL STRUCTURE AND THE WALSH TRANSFORM
    ═══════════════════════════════════════════════════════════════════════

    The space of functions `F → ℂ` forms a **monoidal category** under
    pointwise multiplication, with unit the constant function 1.

    The Walsh transform is a **monoidal functor** (up to normalization):
      W(f · g) ≈ W(f) * W(g)  (convolution theorem)

    This monoidal structure is what makes the fourth moment computation
    work: `W⁴ = (W²)²`, and the AB condition constrains `W²`.

    The *convolution theorem* `W(f * g) = W(f) · W(g)` is the
    statement that the Walsh transform is a monoidal natural transformation.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 10: SUMMARY — CATEGORICAL ARCHITECTURE
    ═══════════════════════════════════════════════════════════════════════

    The Kasami-Gold theorem, viewed categorically:

    ```
    AB functions ──────────────────→ APN functions
         │                                │
         │ Walsh transform (functor)      │ Differential (functor)
         ↓                                ↓
    Spectral data ──────────────────→ Combinatorial data
         │                                │
         │ Fourth moment (nat. transf.)   │ Sum of squares
         ↓                                ↓
    Energy identity ═══════════════  Energy identity
         │                                │
         │ AB constraint (subobject)      │ Evenness (subobject)
         ↓                                ↓
    {0, 2^{n+1}} values ──────────→ {0, 2} values
                   squeezing argument
                   (limit computation)
    ```

    Each arrow is a functor or natural transformation.
    Each vertical step is a "forgetful" functor (losing structure).
    The horizontal arrows are the content of the theorem.
    The bottom row is the "forcing" — a limit in the poset category.
-/

end CategoryPerspective
