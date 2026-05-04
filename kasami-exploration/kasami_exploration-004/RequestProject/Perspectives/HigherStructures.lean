/-
  Perspectives/HigherStructures.lean

  ═══════════════════════════════════════════════════════════════════════════════
  HIGHER STRUCTURES: HoTT, ∞-CATEGORIES, OPERADS, AND OPETOPES
  ═══════════════════════════════════════════════════════════════════════════════

  This file explores how the Kasami-Gold APN theorem connects to:
  1. Homotopy Type Theory (HoTT)
  2. Higher category theory (∞-categories)
  3. Higher operads
  4. Opetopic structures

  Since Lean 4 is not natively HoTT (it has UIP/proof irrelevance),
  we discuss these connections informally but illustrate the key ideas
  with Lean formalizations where possible.

  ## Why This Matters

  These perspectives reveal hidden structure in the Kasami proof:
  - HoTT shows why proof irrelevance is appropriate here
  - ∞-categories explain the naturality of the Walsh-differential identity
  - Operads capture the "multi-input" nature of differential equations
  - Opetopes visualize the combinatorial structure of solution sets
-/

import Mathlib

open Finset BigOperators CategoryTheory

namespace HigherStructures

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 1: HOMOTOPY TYPE THEORY (HoTT) PERSPECTIVE
    ═══════════════════════════════════════════════════════════════════════

    ### 1.1 The Truncation Hierarchy

    In HoTT, types are classified by their "homotopy level" (h-level):

    | h-level | Name           | Lean equivalent         |
    |---------|----------------|-------------------------|
    | -2      | Contractible   | `Unique α`              |
    | -1      | Proposition    | `Subsingleton α` / Prop |
    |  0      | Set            | Types with UIP           |
    |  1      | Groupoid       | (no direct equiv.)       |
    |  n      | n-groupoid     | (no direct equiv.)       |
    |  ∞      | ∞-groupoid     | General types            |

    In Lean 4 (CIC + UIP), ALL types are h-sets (level 0).
    This is because Lean has `proof_irrel` and `propext` built in.

    ### 1.2 Why the Kasami Proof Lives in h-Prop

    The key types in the Kasami theorem:
    - `IsAPN_abs δ : Prop` — a (-1)-type (proposition)
    - `IsAB_abs W n : Prop` — a (-1)-type (proposition)
    - The theorem type `IsAB_abs W n → IsAPN_abs δ` — a function between props

    In HoTT, a function between propositions is automatically a
    **(-1)-truncated map** — it preserves the h-level. This means:

    1. The proof is unique (up to homotopy) — any two proofs of
       "AB ⟹ APN" are propositionally equal.
    2. The theorem carries no computational content beyond its truth value.
    3. The "path space" of proofs is contractible.

    ### 1.3 Constructive Content in HoTT

    If we worked in HoTT *without* truncation, the AB property would be:

      AB(a,b) : (W² = 0) + (W² = 2^{n+1})   -- coproduct, NOT truncated

    This carries a *choice function* — for each (a,b), we know WHICH
    case holds. The proof of AB ⟹ APN would then be a function that
    computes the APN bound from this choice data.

    In HoTT with truncation (standard), we truncate to ‖(W² = 0) + (W² = 2^{n+1})‖,
    losing the computational content. This is what Lean's `Prop` does.
-/

/-- ### 1.4 Subsingleton: Lean's Version of (-1)-Truncation

    A `Subsingleton` type has at most one element. This is the
    type-theoretic analogue of an h-prop ((-1)-type) in HoTT.

    🌟 **Beautiful Pattern**: `Prop` in Lean is the universe of
    subsingletons. The `Subsingleton` class captures this at the
    type level.

    💡 **Lean Best Practice**: Prefer `Prop` over `Bool` for
    mathematical properties. `Bool` is computational (decidable);
    `Prop` is logical (possibly undecidable). -/
example : Subsingleton (2 + 2 = 4) := inferInstance

/-- In HoTT terms, this says the "space of proofs" of `2 + 2 = 4`
    is contractible (has exactly one point, up to homotopy). -/
example (h₁ h₂ : 2 + 2 = 4) : h₁ = h₂ := Subsingleton.elim h₁ h₂

/-! ### 1.5 The Univalence Axiom and Our Setting

    HoTT's univalence axiom says: `(A ≃ B) ≃ (A = B)`.
    Equivalences between types ARE equalities between types.

    For our setting:
    - Two finite fields of the same cardinality are isomorphic.
    - By univalence, they are EQUAL as types.
    - So the Kasami theorem, stated for "any finite field of size 2^n",
      is really stated for a SINGLE type (up to univalence).

    Lean doesn't have univalence, but `propext` gives us a fragment:
    `(P ↔ Q) → (P = Q)` for propositions.
    This is "univalence for (-1)-types".
-/

/-- Propositional extensionality: Lean's fragment of univalence.

    🌟 **Beautiful Pattern**: This is the (-1)-truncated version of
    univalence. It says "logically equivalent propositions are equal".
    This is a theorem in HoTT but an axiom in Lean. -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 2: ∞-CATEGORY THEORY
    ═══════════════════════════════════════════════════════════════════════

    ### 2.1 The ∞-Category of Finite Fields

    The collection of all finite fields forms an ∞-category where:
    - Objects: Finite fields (up to isomorphism, one per prime power)
    - 1-morphisms: Field homomorphisms
    - 2-morphisms: Natural transformations between field homomorphisms
    - Higher morphisms: All trivial (since fields form a 1-category)

    So the ∞-category of finite fields is actually a 1-category (all
    higher morphisms are identities). This is because `FieldHom` is
    a structure (no higher coherence needed).

    ### 2.2 The ∞-Category of Functions

    For a fixed field F, the functions f : F → F form a category
    (actually a monoid under composition). The differential and Walsh
    transforms are FUNCTORS from this category.

    In the ∞-categorical setting, we could ask: are there higher
    coherences between these functors? For example:

    - Is the natural transformation "fourth moment identity" part of
      a higher natural transformation?
    - Do the coherence conditions of a monoidal ∞-functor give us
      new identities for Walsh coefficients?

    For our finite setting, the answer is: the higher structure is
    trivial (everything is 1-categorical). But for infinite fields
    or continuous Fourier transforms, higher structure emerges.

    ### 2.3 Stable ∞-Categories and Spectra

    The Walsh transform can be viewed as a map in a **stable ∞-category**.
    In stable ∞-categories:
    - Finite sums = finite products (biproducts exist)
    - The Parseval identity is a statement about biproducts
    - The fourth moment identity is a statement about composition
      of biproduct morphisms

    The "spectrum" associated to the Walsh transform is an object in
    the ∞-category of spectra, and the AB condition constrains its
    homotopy groups.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 3: HIGHER OPERADS
    ═══════════════════════════════════════════════════════════════════════

    ### 3.1 The Differential Operad

    An **operad** is a generalization of a category where morphisms can
    have multiple inputs:

    ```
    O(c; c₁, ..., cₖ) = set of operations with inputs c₁,...,cₖ and output c
    ```

    The differential equation `f(x + u) + f(x) = v` defines an operad:

    **Colors** (objects): Elements of F.
    **Operations**: `O(v; x₁, ..., xₖ)` = the set of solutions
      `{x | f(x + u) + f(x) = v}` for some fixed u.
    **Composition**: Substitution of solutions.

    The **APN condition** says: each operation has arity ≤ 2.
    In operad language: the operad is **binary** — no operation has
    more than 2 inputs.

    ### 3.2 The Associahedra Connection

    The Stasheff associahedra `Kₙ` parameterize ways to parenthesize
    n-ary operations. For a binary operad (APN functions):
    - K₂ = point (only one binary operation)
    - K₃ = interval (two ways to compose three elements)
    - K₄ = pentagon (five ways to compose four elements)

    The AB ⟹ APN theorem says: the differential operad of an AB
    function is binary, so its compositional structure is governed
    by the associahedra K₂ = point.

    ### 3.3 Formalization: A Simple Operad in Lean

    We can model the "differential operad" as a function that
    assigns to each pair (output, inputs) a natural number (the
    count of operations).
-/

/-- A simple model of a "colored operad" with colors in ι and
    arities bounded by some d.

    🎯 **Category Theory Pattern**: This is a *non-symmetric operad*
    in the category of sets. The symmetric group action would
    permute the inputs, but we ignore it here.

    💡 **Lean Best Practice**: Use `structure` for bundled data.
    Use `class` only when you want typeclass inference. -/
structure BoundedOperad (ι : Type*) (d : ℕ) where
  /-- The operation count for a given output and list of inputs. -/
  ops : ι → List ι → ℕ
  /-- The arity bound: no operation has more than d inputs. -/
  arity_bound : ∀ c inputs, d < inputs.length → ops c inputs = 0

/-- The differential operad of an APN function.
    Operations of arity > 2 are zero.

    🌟 **Beautiful Pattern**: The APN condition IS the arity bound
    of the differential operad. The AB ⟹ APN theorem says:
    "AB functions have binary differential operads." -/
noncomputable def apnOperad {ι : Type*} [Fintype ι] [DecidableEq ι] [Add ι]
    (f : ι → ι) (u : ι) : BoundedOperad ι 2 where
  ops v inputs :=
    if inputs.length ≤ 2 then
      (Finset.univ.filter fun x => f (x + u) = v).card
    else 0
  arity_bound := by
    intro c inputs h
    show (if inputs.length ≤ 2 then _ else 0) = 0
    split_ifs with h2
    · omega
    · rfl

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 4: OPETOPES
    ═══════════════════════════════════════════════════════════════════════

    ### 4.1 What Are Opetopes?

    **Opetopes** (Baez-Dolan) are shapes for higher-dimensional
    composition. They generalize:
    - Points (0-opetopes)
    - Arrows (1-opetopes)
    - Disks with multiple input arrows (2-opetopes)
    - Higher-dimensional "pasting diagrams" (n-opetopes)

    An n-opetope has:
    - A single (n-1)-opetope as its "output face"
    - A pasting diagram of (n-1)-opetopes as its "input faces"

    ### 4.2 Opetopes in the Kasami Setting

    The differential equation `f(x + u) + f(x) = v` defines a 2-opetope:

    ```
         x₁ ───→ v
        ╱
       u          (2-opetope: a "cell" with boundary arrows)
        ╲
         x₂ ───→ v
    ```

    - The input arrows are the solutions x₁, x₂ (at most 2 for APN)
    - The output is v
    - The "globular" direction is u

    For an APN function, every 2-opetope has at most 2 input faces.
    This means the opetopic set is "binary" — a strong constraint.

    ### 4.3 The Walsh Support as an Opetope

    The Walsh support `S_b = {a | W(a,b) ≠ 0}` defines a higher opetope:

    ```
    S_b : n-opetope with |S_b| = 2^{n-1} faces
    ```

    The pair count `C(|S_b|, 2)` = number of 1-dimensional "edges"
    in the boundary of this opetope.

    The Kasami theorem determines the shape of this opetope:
    - 2^{n-1} faces
    - 2^{n-2} · (2^{n-1} - 1) edges
    This is the boundary structure of a "simplex-like" opetope.

    ### 4.4 Opetopic Categories and Type Theory

    Opetopic type theory (Finster-Mimram) provides a foundation where:
    - Types are opetopic sets
    - Terms are "elements" of opetopic sets
    - Equality is opetopic composition

    The Kasami theorem, in opetopic type theory, would be a statement
    about the "shape" of the solution type for differential equations
    of AB functions.

    ### 4.5 Connection to Higher Inductive Types (HITs)

    In HoTT, the opetopic structure could be encoded as a **Higher
    Inductive Type** (HIT):

    ```
    inductive DiffOpetope (F : Field) (f : F → F) where
    | point : F → DiffOpetope
    | arrow : (u : F) → (x : F) → DiffOpetope
    | cell  : (u v : F) → (sols : List F) → DiffOpetope
    | ...higher cells...
    ```

    The APN condition would be:
    `∀ u v, (DiffOpetope.cell u v sols).arity ≤ 2`

    This is not directly formalizable in Lean 4 (which lacks HITs),
    but captures the intuition of why the APN bound is "geometric".
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 5: FORMAL ILLUSTRATION — THE SQUEEZING AS A PULLBACK
    ═══════════════════════════════════════════════════════════════════════

    The "squeezing argument" (∑ δ² ≥ 2∑ δ AND ∑ δ² = 2∑ δ ⟹ each
    δ² = 2δ) can be formalized as a **pullback** in the category of
    finite diagrams over (ℤ, ≤).

    The pullback of the two maps:
    ```
    ∑ : Fin n → ℤ  ────→  ℤ     (sum map)
                            ↑
    ∑ : Fin n → ℤ  ────→  ℤ     (sum map)
    ```
    along the diagonal Δ : ℤ → ℤ × ℤ gives us the equalizer —
    the set of sequences where all terms are equal.
-/

/-- ### 5.1 The Squeezing Lemma (Formal)

    If `f i ≥ g i` pointwise and `∑ f i = ∑ g i`, then `f = g` pointwise.

    🌟 **Beautiful Pattern**: This is the **uniqueness of the cone map**
    in the limit computation. The cone over the diagram
    `{∑ f, ∑ g, f, g, ≥}` has a unique compatible assignment.

    🎯 **Opetopic Pattern**: The squeezing is a "composition" of
    2-opetopes (inequalities) into a 3-opetope (equality).

    💡 **Lean Best Practice**: The `Finset.sum_lt_sum` lemma from
    Mathlib is the key tool here. Always search Mathlib before
    writing your own version! -/
theorem squeeze_pointwise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℕ) (hge : ∀ i, f i ≥ g i) (hsum : ∑ i, f i = ∑ i, g i) :
    ∀ i, f i = g i := by
  -- 📝 Strategy: if f i > g i for some i, then ∑ f > ∑ g. Contradiction.
  intro i
  by_contra h
  -- 📝 Since f i ≥ g i and f i ≠ g i, we have f i > g i.
  have hlt : f i > g i := Nat.lt_of_le_of_ne (hge i) (Ne.symm h)
  -- 📝 Pointwise ≥ plus strict at one point gives strict sum inequality.
  have := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hge j) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 6: LEAN BEST PRACTICES FOR HIGHER-LEVEL ABSTRACTIONS
    ═══════════════════════════════════════════════════════════════════════

    ### 6.1 When to Abstract

    The Kasami proof could be stated at several levels of abstraction:
    1. **Concrete**: Over `ZMod (2^n)` with explicit Walsh coefficients.
    2. **Semi-abstract**: Over any finite field with characteristic 2.
    3. **Fully abstract**: Over any finite index type with ℤ-valued
       functions satisfying certain identities (the approach used here).

    The choice (3) is the most general and often the easiest to prove,
    because it separates the algebraic/analytic hypotheses (Parseval,
    fourth moment) from the combinatorial conclusion (APN).

    💡 **Best Practice**: Abstract early, specialize late. Prove the
    combinatorial core in full generality, then instantiate for specific
    fields.

    ### 6.2 Typeclass Design

    For the operad structure, we used `structure` rather than `class`.
    Use `class` only when:
    - The structure is "canonical" (one per type)
    - You want automatic inference
    - Examples: `Group`, `Ring`, `Fintype`

    Use `structure` when:
    - Multiple instances per type are natural
    - You want explicit passing
    - Examples: `BoundedOperad`, custom proof bundles

    ### 6.3 Dependent Type Pitfalls

    The Kasami proof navigates several dependent type issues:
    - `2^(n-1)` when `n = 0`: natural subtraction gives `2^0 = 1`
    - `Fintype.card ι = q`: this is a proposition, not a definition
    - `(q : ℤ)`: coercion from ℕ to ℤ (automatic but can cause issues)

    💡 **Best Practice**: Test edge cases with `#eval` before formalizing.
    The natural number `0` is the most dangerous edge case.

    ### 6.4 Tactic Selection Guide

    | Goal type         | Best tactic(s)                    |
    |-------------------|-----------------------------------|
    | ℕ/ℤ arithmetic    | `omega`, `norm_num`               |
    | Polynomial ineq.  | `nlinarith`, `polyrith`           |
    | Ring equalities   | `ring`, `ring_nf`                 |
    | Finset sums       | `simp`, `Finset.sum_congr`        |
    | Case analysis     | `rcases`, `obtain`, `match`       |
    | Induction         | `induction`, `Nat.rec`            |
    | Contradictions    | `omega`, `linarith`, `absurd`     |
    | Decidable props   | `decide`, `norm_num`              |
    | General rewriting | `rw`, `conv`, `simp only`         |

    ### 6.5 Module Organization

    ```
    project/
    ├── Theorem3/
    │   ├── Normalization.lean    -- One concept per file
    │   └── Factorization.lean    -- Dependencies are explicit imports
    ├── Theorem23/
    │   └── Counting.lean         -- Cross-cutting concerns
    ├── Perspectives/
    │   ├── TypeTheory.lean       -- Educational / expository
    │   ├── CategoryTheory.lean
    │   └── HigherStructures.lean
    └── Kasami_Final_Theorem.lean -- Top-level bridge / main result
    ```

    💡 **Best Practice**: One concept per file. Files should be
    ≤ 500 lines ideally, ≤ 1000 lines maximum. Use descriptive
    filenames. Group related files in directories.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 7: SUMMARY OF PERSPECTIVES
    ═══════════════════════════════════════════════════════════════════════

    | Perspective          | What it reveals                              |
    |----------------------|----------------------------------------------|
    | **Type Theory**      | Proof = program; the theorem is a function   |
    | **Category Theory**  | Universal bounds; naturality of identities   |
    | **HoTT**             | Proof irrelevance; truncation levels         |
    | **∞-Categories**     | Higher coherence (trivial here, nontrivial   |
    |                      | for continuous transforms)                   |
    | **Operads**          | APN = binary operad; arity constraints       |
    | **Opetopes**         | Solution sets as geometric shapes; the Walsh |
    |                      | support as a higher-dim pasting diagram      |

    ### Key Takeaway

    The Kasami-Gold theorem sits at the intersection of algebra,
    combinatorics, and Fourier analysis. Each foundational perspective
    illuminates a different aspect:

    - **Type theory** explains WHY the proof is valid (construction).
    - **Category theory** explains HOW the pieces fit together (naturality).
    - **HoTT** explains WHAT the proof means (homotopy invariance).
    - **Operads** explain WHERE the constraints come from (arity bounds).
    - **Opetopes** explain WHAT SHAPE the solution sets have (geometry).

    Together, they give a multi-dimensional understanding of a beautiful
    theorem in cryptographic function analysis.
-/

end HigherStructures
