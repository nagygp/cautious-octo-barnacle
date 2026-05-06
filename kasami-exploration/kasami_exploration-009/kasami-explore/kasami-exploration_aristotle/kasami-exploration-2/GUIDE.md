# Crystals, Tilings, Knots & Folds

## A Geometric Guide to the Kasami–Gold APN Formalization

> *"Mathematics is the art of giving the same name to different things."* — Henri Poincaré

This guide reads the Lean formalization of the **Kasami–Gold APN theorem** (Bracken–Byrne–Markin–McGuire / Budaghyan Theorem 2.3) through the lens of **crystals, tiling patterns, knots, braids, and folds**. Along the way it draws connections to **category theory**, **type theory**, **HoTT**, **higher category theory**, **higher operads**, and **opetopes**, while offering practical tips for writing clean, beautiful Lean code.

---

## Table of Contents

1. [Overview of the Formalization](#1-overview)
2. [The Crystal Metaphor — Symmetry & Rigidity](#2-crystals)
3. [Tilings — Covering a Space Without Gaps](#3-tilings)
4. [Knots & Braids — Tangling and Untangling Structure](#4-knots-braids)
5. [Folds — Collapsing Dimensions](#5-folds)
6. [Category Theory Connections](#6-category-theory)
7. [Type Theory Patterns](#7-type-theory)
8. [HoTT — Homotopy Type Theory](#8-hott)
9. [Higher Category Theory & Higher Operads](#9-higher-cats)
10. [Opetopes — The Shape of Composition](#10-opetopes)
11. [Universal Arrows — Beauty in Abstraction](#11-universal-arrows)
12. [Lean Best Practices & Clean Code](#12-lean-best-practices)
13. [Functional Programming Principles](#13-fp-principles)
14. [Import Hygiene](#14-import-hygiene)
15. [Annotated Code Walkthrough](#15-walkthrough)

---

<a id="1-overview"></a>
## 1. Overview of the Formalization

The project proves a chain of theorems about **Gold-type APN functions** over finite fields of characteristic 2:

```
Normalization ──→ Factorization ──→ Counting ──→ Kasami Bridge
   (kernel           (root              (Walsh        (combined
    isomorphism)      bound)             support)      theorem)
```

**Key results:**
- **Task 1** (`h_diff_via_walsh`): The Walsh-Differential Identity — the fourth power moment of Walsh coefficients equals q² times the sum of squared differential counts.
- **Task 2** (`AB_implies_APN`): Almost Bent implies Almost Perfect Nonlinear.
- **Task 3** (`triple_count_eq`): The Walsh support has exactly 2^(n−1) elements.
- **Bridge** (`kasami_bridge`): The combined theorem tying it all together.

The mathematical content lives in the world of **finite fields**, **cryptographic Boolean functions**, and **discrete Fourier analysis**. But its *structure* resonates with patterns found throughout mathematics and computer science.

---

<a id="2-crystals"></a>
## 2. The Crystal Metaphor — Symmetry & Rigidity

### The Formalization as Crystal Lattice

A **crystal** is defined by its **unit cell** and **symmetry group**. The unit cell repeats; the symmetry group constrains *how* it can repeat.

In our formalization:

| Crystal Concept | Formalization Analogue |
|---|---|
| **Unit cell** | The Gold function `f(x) = x^(2^k+1)` — a single "atom" of structure |
| **Crystal lattice** | The finite field `𝔽_{2^n}` — the periodic medium |
| **Symmetry group** | The Frobenius automorphism `φ(x) = x²` — the fundamental symmetry |
| **Defect / dislocation** | The derivative `Δ_u f(x)` — measuring how the crystal "shifts" |

The **Frobenius endomorphism** is the crystal's rotational symmetry. It generates a cyclic group of order n acting on `𝔽_{2^n}`. Every computation in the formalization — the factorization of `L₀`, the iterated Frobenius `frobIter`, the characteristic-2 identity `(x+u)^{2^k} = x^{2^k} + u^{2^k}` — is a consequence of this single symmetry.

```lean
-- The crystal's fundamental symmetry: Frobenius
def frob2 : F →+* F := frobenius F 2

-- Iterating the symmetry: the lattice's translational group
def frobIter : F →+* F := (frobenius F 2) ^ k
```

### Rigidity = Type Safety

Crystals are **rigid**: you cannot deform them continuously without breaking bonds. Similarly, Lean's type system enforces **rigidity** — you cannot silently coerce `ℕ` to `ℤ` to `ℝ` without the type checker tracking every step. This rigidity is a *feature*: it prevents "crystallographic defects" in proofs (i.e., subtle errors from implicit coercions).

> **Pattern:** The `CharP F 2` typeclass instance is like specifying the crystal system. Once declared, all ring operations "know" they live in characteristic 2. The identity `-x = x` (see `CharTwo.neg_eq`) is not a proof trick — it's a *structural consequence* of the crystal's symmetry class.

---

<a id="3-tilings"></a>
## 3. Tilings — Covering a Space Without Gaps

### Parseval as Perfect Tiling

A **tiling** covers a space completely with no overlaps and no gaps. The **Parseval identity**

```
∑_a W(a,b)² = q²
```

is a **perfect tiling** of the "energy space" q² by the Walsh spectrum. Each Walsh coefficient W(a,b)² is a tile; together they cover q² exactly.

For **AB functions**, the tiles come in exactly two sizes: **0** and **2^(n+1)**. This is like a **Penrose tiling** with only two tile shapes — yet they cover the plane perfectly. The constraint

```
|S_b| · 2^(n+1) = 2^{2n}
```

forces `|S_b| = 2^(n-1)`: the number of nonzero tiles is completely determined.

### The Differential Table as Mosaic

The differential table `δ(u,v)` is a matrix — a mosaic of numbers. The **APN condition** says every entry (for u ≠ 0) is at most 2. Combined with the row-sum constraint `∑_v δ(u,v) = q`, this means each row is a tiling of q by values in {0, 2}. Exactly q/2 entries are 2; the rest are 0.

```lean
-- The tiling constraint: each row sums to q
(H_row_sum : ∀ u : ι, u ≠ 0 → ∑ v : ι, (δ u v : ℤ) = (q : ℤ))

-- The tile-size constraint: each tile is ≤ 2
def IsAPN_abs : Prop :=
  ∀ u : ι, u ≠ 0 → ∀ v : ι, δ u v ≤ 2
```

### Aperiodic Order

The AB condition creates **long-range order** (global spectral constraints) from **local rules** (the function f). This is exactly how **quasicrystals** work: local matching rules produce global aperiodic tilings with sharp Fourier spectra.

---

<a id="4-knots-braids"></a>
## 4. Knots & Braids — Tangling and Untangling Structure

### The Normalization Lemma as Reidemeister Move

In knot theory, **Reidemeister moves** simplify a knot diagram without changing the knot type. The **Normalization Lemma** (`kernel_iso_normalized`) performs exactly this:

```
Δ_u f(x) = 0   ←→   L_norm(x/u) = 0
```

It "untangles" the derivative equation by the substitution `y = x · u⁻¹`, reducing a seemingly complex equation to a normalized form. The key insight: **the knot type (kernel structure) is invariant under this move**.

```lean
-- Reidemeister move: untangle the derivative
lemma kernel_iso_normalized (u : F) (hu : u ≠ 0) (x : F) :
    deltaGold k F u x = 0 ↔ Lnorm k F (x * u⁻¹) = 0
```

### The Factorization as Braid Decomposition

A **braid** can be decomposed into elementary crossings (generators σ₁, σ₂, …). The factorization

```
L₀(y) = L₁(L₂(y))
```

decomposes the linearized operator into two simpler "crossings":
- `L₁(y) = y² + y` — the **Artin–Schreier map** (a single crossing)
- `L₂(y) = ∑ y^{2^i}` — the **partial trace** (a sequence of parallel strands)

```lean
-- Braid decomposition: complex operator = composition of simple ones
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y
```

This is beautiful: a degree-2^k polynomial factors through a degree-2 polynomial composed with a degree-2^(k-1) polynomial. The **kernel bound** follows from the **crossing number** of each factor.

### Iff as Knot Equivalence

Every `↔` (iff) in the formalization is a statement that two "knots" are equivalent — they look different but represent the same mathematical object. The proof of `↔` has two directions, like showing you can deform one knot into the other and back.

---

<a id="5-folds"></a>
## 5. Folds — Collapsing Dimensions

### The Frobenius Trace as a Fold

In functional programming, a **fold** (or reduce) collapses a sequence into a single value. The partial Frobenius trace

```lean
def L₂ (y : F) : F := ∑ i ∈ range k, y ^ (2 ^ i)
```

is literally a fold over the Frobenius orbit of y:

```
L₂(y) = y + y² + y^4 + ⋯ + y^{2^{k-1}}
       = fold (+) 0 [y, φ(y), φ²(y), …, φ^{k-1}(y)]
```

Each term `y^{2^i} = φ^i(y)` is an iterate of the Frobenius. The fold collapses k dimensions of the Frobenius orbit into a single field element.

### The Walsh Transform as a Grand Fold

The Walsh coefficient itself is a fold over the entire field:

```lean
noncomputable def WalshCoeff (ψ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, ψ (a * x + b * f x)
```

This **folds** the field F into a single complex number, collapsing 2^n dimensions into one. The Parseval identity says this fold preserves total energy.

### Proof by Folding

The proof of `AB_implies_APN` works by a sequence of folds:

1. **Fold** Walsh coefficients into fourth moments: `∑∑ W⁴`
2. **Fold** differential counts into squared sums: `∑∑ δ²`
3. **Fold** the identity `W⁴ = W² · 2^(n+1)` across all (a,b) pairs
4. **Squeeze**: the folded totals match, forcing each δ(u,v) ≤ 2

This is a **catamorphism** — a structure-preserving fold from a complex algebraic object to a simple numerical constraint.

---

<a id="6-category-theory"></a>
## 6. Category Theory Connections

### The Formalization as a Diagram

The entire proof is a **commutative diagram** in the category of propositions:

```
                    kernel_iso_normalized
    {Δ_u f(x) = 0} ─────────────────────→ {L_norm(y) = 0}
          │                                       │
          │ card                                   │ card_roots_Lnorm_le
          ▼                                       ▼
    |ker Δ_u f| ────────────────────────→ |roots L_norm| ≤ 2^k
          │
          │ (char 2 pairing)
          ▼
      δ(u,v) even ──→ δ² ≥ 2δ ──→ ∑δ² ≥ 2∑δ ──→ δ ≤ 2
                                                     │
                                                     ▼
                                                   APN
```

### Functors in the Code

The map `y ↦ y · u` (scaling by a nonzero field element) is a **functor** from the category of roots of L_norm to the category of roots of Δ_u f. It's faithful (injective) and essentially surjective — in fact, it's an **equivalence of categories** (a bijection on objects):

```lean
-- The functor: roots of L_norm → roots of Δ_u f
lemma kernel_deltaGold_eq_image (u : F) (hu : u ≠ 0) :
    {x : F | deltaGold k F u x = 0} =
      (fun y => y * u) '' {y : F | Lnorm k F y = 0}
```

### Natural Transformations

The **Parseval identity** is a **natural transformation** between two functors:
- Functor 1: `b ↦ ∑_a W(a,b)²` (the "energy" functor)
- Functor 2: `b ↦ q²` (the "constant" functor)

Naturality says: no matter which `b` you pick, the energy is the same. This is **uniformity** — a deep structural constraint.

### Adjunctions

The Walsh transform and the inverse Walsh transform form an **adjoint pair**. Parseval's identity is the **unit-counit equation** that characterizes this adjunction:

```
⟨Wf, Wf⟩ = q · ⟨f, f⟩
```

This is the Fourier-theoretic incarnation of the **hom-tensor adjunction** in algebra.

---

<a id="7-type-theory"></a>
## 7. Type Theory Patterns

### Propositions as Types, Proofs as Programs

Every theorem in this formalization is a **type**, and every proof is a **term** inhabiting that type:

```lean
-- The TYPE: "AB implies APN"
theorem AB_implies_APN : ... → IsAPN_abs δ

-- The PROOF: a program that constructs an inhabitant
:= by ...
```

### Dependent Types in Action

The statement of `kasami_bridge` is a **dependent product type** (Π-type):

```lean
theorem kasami_bridge
    (hq : q = 2 ^ n)     -- a proof that q = 2^n
    (hn : 1 ≤ n)          -- a proof that n ≥ 1
    ...
    : IsAPN_abs δ ∧ ... ∧ ...
```

Each hypothesis is a **fiber** — the type of the conclusion depends on the proofs of the hypotheses. This is the essence of dependent type theory: types can mention terms.

### The Curry–Howard Correspondence in Practice

| Logic | Type Theory | This Formalization |
|---|---|---|
| `∀ u, P u` | `Π (u : ι), P u` | `∀ u : ι, u ≠ 0 → δ u v ≤ 2` |
| `P ∧ Q` | `P × Q` | `IsAPN_abs δ ∧ (∀ b, ...) ∧ (∀ b, ...)` |
| `P → Q` | Function type | `hAB : IsAB_abs W n` as input to `AB_implies_APN` |
| `P ↔ Q` | Equivalence | `kernel_iso_normalized` |
| `∃ x, P x` | `Σ (x : _), P x` | Implicit in the image characterization |

### Universe Polymorphism

The use of `{ι : Type*}` is **universe polymorphism**: the theorems work for index types in any universe. This is a type-theoretic analogue of **naturality** — the proofs don't depend on the specific "size" of the types involved.

---

<a id="8-hott"></a>
## 8. HoTT — Homotopy Type Theory

### Paths and Identities

In HoTT, an equality `a = b` is a **path** in a space. The proof of `delta_eq_lin_plus_const`:

```lean
deltaGold k F u x = linPart k F u x + u ^ goldExp k
```

is a **path** in the type `F` — a continuous deformation from one expression to the other. The `ring` tactic constructs this path by chaining elementary algebraic identities.

### Equivalences vs. Equalities

The normalization lemma gives an **equivalence** (↔), not an equality. In HoTT terms, this is a **type equivalence** — a map with a two-sided inverse. The univalence axiom would promote this to an identity of types, but in Lean 4 we work with explicit equivalences.

### Higher Inductive Types

The finite field `𝔽_{2^n}` can be thought of as a **higher inductive type** with:
- Point constructors: the elements 0, 1, α, α², ...
- Path constructors: the field axioms (commutativity, associativity, ...)
- Higher paths: coherence conditions

The Frobenius endomorphism is then a **self-equivalence** of this HIT — an automorphism that respects all the higher structure.

### The Univalence Principle in Practice

The factorization `L₁ ∘ L₂ = L₀` is, from the HoTT perspective, a statement about **paths between functions**. Function extensionality (funext) — which is a consequence of univalence — lets us prove this pointwise:

```lean
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y
```

---

<a id="9-higher-cats"></a>
## 9. Higher Category Theory & Higher Operads

### The Proof as a 2-Category

The formalization has three levels of structure, forming a **2-category**:

| Level | Objects | Morphisms | 2-Morphisms |
|---|---|---|---|
| 0-cells | Types (`F`, `ι`, `ℤ`, `ℕ`) | | |
| 1-cells | Functions (`goldFun`, `L₀`, `W`, `δ`) | | |
| 2-cells | Equations (`delta_eq_lin_plus_const`) | Implications (`AB_implies_APN`) | Proof transformations |

The **Kasami Bridge Theorem** is a **2-morphism**: it witnesses that the composite path (Normalization → Factorization → Counting) equals the direct path (AB → APN + support + pairs).

### Operadic Structure

An **operad** describes operations with multiple inputs and one output, together with composition rules. The proof structure is operadic:

```
         AB_fourth_eq_second_times_pow
         sum_sq_walsh_nonzero_b            ╲
         sum_sq_delta_trivial_row    ────────→  AB_implies_APN
         sum_sq_ge_two_mul_sum_of_even     ╱
         sq_ge_two_mul_of_even
```

Each helper lemma is an **operation** in the operad; `AB_implies_APN` is a **composition** that plugs them together. The operadic axioms (associativity, unitality) correspond to Lean's tactic composition being well-defined.

### The Swiss-Cheese Operad

The formalization has two kinds of operations:
- **Closed operations** (pure algebra): `ring`, `omega`, `nlinarith`
- **Open operations** (with boundary): `intro`, `obtain`, `rcases`

This matches the **Swiss-cheese operad** (Voronov), where closed disks represent algebraic computations and open regions represent logical scaffolding.

### ∞-Categories and Proof Relevance

In a **proof-irrelevant** setting (Lean's `Prop`), all proofs of the same proposition are equal — this is the **(-1)-truncation** in HoTT. The formalization lives in this truncated world: we don't care *which* proof of `δ u v ≤ 2` we have, only *that* one exists.

But the proof *terms* carry computational content (the `by` blocks). In a proof-relevant setting (an ∞-category), different proofs would be different 1-morphisms, and proof transformations would be 2-morphisms. The `convert` tactic, for instance, constructs a 2-morphism between almost-matching proofs.

---

<a id="10-opetopes"></a>
## 10. Opetopes — The Shape of Composition

### What Are Opetopes?

**Opetopes** (Baez–Dolan) are geometric shapes that describe higher-dimensional composition. They generalize:
- **Dimension 0**: A point (a term)
- **Dimension 1**: An arrow (a function / morphism)
- **Dimension 2**: A 2-cell (a proof that two paths are equal)
- **Dimension 3**: A 3-cell (a proof that two proofs are "the same")

### The Kasami Bridge as an Opetope

The `kasami_bridge` theorem has the shape of a **3-dimensional opetope**:

```
          triple_count_eq ─────────╲
                                    ╲
          triple_count_pairs ────────→ kasami_bridge
                                    ╱
          AB_implies_APN ──────────╱
```

The three input faces (the three conjuncts of the conclusion) compose into the single output face (the combined theorem). This is a **corolla opetope** — a tree with one root and three leaves.

### Opetopic Type Theory

In **opetopic type theory** (Finster–Mimram), types are labeled opetopes. The formalization's type structure maps onto opetopic cells:

```
Level 0 (points):    F, ι, ℤ, ℕ, Prop
Level 1 (arrows):    goldFun : F → F,  W : ι → ι → ℤ
Level 2 (fillers):   delta_eq_lin_plus_const : deltaGold = linPart + const
Level 3 (composites): kasami_bridge : AB ⟹ APN ∧ support ∧ pairs
```

Each level "fills in" the boundary specified by the previous level, exactly as opetopic cells fill in opetopic boundaries.

---

<a id="11-universal-arrows"></a>
## 11. Universal Arrows — Beauty in Abstraction

### What Is a Universal Arrow?

A **universal arrow** from an object X to a functor U is a pair (A, η : X → U(A)) such that every other arrow X → U(B) factors uniquely through η. It's the "best" way to map X into the image of U.

### Universal Arrows in This Formalization

**1. The Normalization as a Universal Arrow**

The substitution `y = x · u⁻¹` is a universal arrow from the "raw derivative equation" to the "normalized equation functor":

```
   Δ_u f(x) = 0
       │
       │  y = x · u⁻¹    ← universal arrow
       ▼
   L_norm(y) = 0
```

It's universal because *every* derivative equation (for any u ≠ 0) factors through L_norm via the same construction.

**2. The Frobenius as a Universal Symmetry**

The Frobenius `φ(x) = x²` is the **universal** ring endomorphism of `𝔽_{2^n}` — every other endomorphism is a power of φ. In categorical terms, φ is the **generator** of the automorphism group `Gal(𝔽_{2^n}/𝔽_2)`, and every Galois action factors through it.

**3. The Walsh Transform as an Adjoint**

The Walsh transform is the **unit** of the adjunction between the "spatial" and "spectral" worlds:

```
    Spatial (functions F → F)
       │
       │  Walsh transform    ← unit η
       ▼
    Spectral (Walsh coefficients ι → ι → ℤ)
       │
       │  Inverse Walsh      ← counit ε
       ▼
    Spatial
```

Parseval's identity is the **triangle identity** `ε ∘ η = id` for this adjunction.

**4. The Kasami Bridge as a Universal Property**

The combined theorem `kasami_bridge` is, in a sense, the **universal arrow** from the AB hypothesis to the "applications" functor. Any consequence of AB (APN, support size, pair count) factors through this single theorem.

### Beautiful Patterns

🔮 **The Forcing Argument** — The proof of `AB_implies_APN` uses a beautiful "squeeze" pattern:
```
   δ² ≥ 2δ  (from evenness)
   ∑δ² = 2∑δ (from matching totals)
   ∴ δ² = 2δ pointwise (forced equality)
   ∴ δ ∈ {0, 2}
```
This is the **pigeonhole principle in disguise**: if the average equals the minimum, every value equals the average. It's a universal pattern that appears in information theory (channel capacity), convex optimization (complementary slackness), and statistical mechanics (entropy maximization).

🔮 **The Characteristic-2 Miracle** — In characteristic 2, subtraction equals addition (`x - y = x + y`). This single fact collapses the complexity of many arguments. Solutions to `f(x+u) + f(x) = v` come in pairs `{x, x+u}` because `f((x+u)+u) + f(x+u) = f(x) + f(x+u) = v`. The pairing is *intrinsic* to the characteristic — it's not a proof technique but a structural feature of the mathematical universe.

🔮 **The Root Bound Cascade** — The factorization `L₀ = L₁ ∘ L₂` gives a root bound by the **multiplicativity of degree under composition**: `deg(L₀) = deg(L₁) · deg(L₂)`, and roots of a polynomial over a field are bounded by its degree. This cascade — from algebraic structure to numerical bound — is a recurring motif in algebraic geometry.

---

<a id="12-lean-best-practices"></a>
## 12. Lean Best Practices & Clean Code

### Naming Conventions

```lean
-- ✅ Good: descriptive, follows Mathlib conventions
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1
lemma delta_eq_lin_plus_const ...
theorem AB_implies_APN ...

-- ❌ Avoid: single letters, cryptic abbreviations
def ge (k : ℕ) := 2 ^ k + 1    -- collides with ≥
lemma lem1 ...                    -- meaningless
```

**Mathlib naming convention summary:**
- Lemmas: `subject_predicate_qualifier` (e.g., `card_roots_L₀_le`)
- Types/Defs: `CamelCase` for types, `camelCase` for terms
- Theorem names should be *searchable* — include key concepts

### Structure and Organization

```lean
-- ✅ Good: logical sections with documentation
/-! ### The Gold function and its derivative -/
section GoldFunction
  ...
end GoldFunction

-- ✅ Good: hierarchical file structure
--   Theorem3/Normalization.lean   — one concept per file
--   Theorem3/Factorization.lean   — clear dependency chain
--   Theorem23/Counting.lean       — cross-cutting concerns separate
```

### Tactic Style

```lean
-- ✅ Prefer structured proofs for clarity
theorem example_structured : P ∧ Q := by
  constructor
  · -- First conjunct
    exact proof_of_P
  · -- Second conjunct
    exact proof_of_Q

-- ✅ Use focused tactics
simp only [specific_lemma]     -- better than bare `simp`
nlinarith [specific_bound]     -- provide witnesses

-- ⚠️ Use `simp` with parameters for reproducibility
simp +decide [pow_succ, mul_assoc]   -- explicit simp lemmas

-- ❌ Avoid: opaque tactic blocks with no comments
theorem mystery : ... := by
  simp; ring; omega; aesop     -- what is this doing?
```

### Noncomputable Sections

```lean
-- ✅ Mark noncomputable upfront when using classical logic
noncomputable section
open Finset Classical
```

Working over finite fields with classical logic requires `noncomputable`. Mark this at the section level to avoid per-definition annotations.

### Variable Management

```lean
-- ✅ Good: declare variables once, use everywhere
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ) (δ : ι → ι → ℕ) (q n : ℕ)

-- This avoids repeating type signatures in every theorem
```

### Error Prevention

```lean
-- ✅ Use set_option for complex proofs
set_option maxHeartbeats 400000

-- ✅ Check axioms after proving key theorems
#print axioms kasami_bridge
-- Should only show: propext, Classical.choice, Quot.sound
```

---

<a id="13-fp-principles"></a>
## 13. Functional Programming Principles

### Pure Functions

Every definition in the formalization is a **pure function** — no side effects, no mutable state:

```lean
-- Pure: input → output, nothing else
def goldFun (x : F) : F := x ^ goldExp k
def L₀ (y : F) : F := y ^ (2 ^ k) + y
def diffCount (f : F → F) (u v : F) : ℕ :=
  (Finset.univ.filter fun x => f (x + u) + f x = v).card
```

### Higher-Order Functions

The formalization uses **higher-order functions** extensively:

```lean
-- Functions as arguments (higher-order)
noncomputable def WalshCoeff (ψ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, ψ (a * x + b * f x)
--                                    ↑ f is a function passed as data

-- Predicates as functions to Prop
def IsAPN (f : F → F) : Prop :=
  ∀ u : F, u ≠ 0 → ∀ v : F, diffCount f u v ≤ 2
```

### Composition

The factorization lemma is literally about **function composition**:

```lean
-- L₀ = L₁ ∘ L₂  (the fundamental theorem of the factorization file)
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y
```

### Pattern Matching and Recursion

```lean
-- Pattern matching on natural numbers (structural recursion)
lemma frobIter_apply (x : F) : frobIter k F x = x ^ (2 ^ k) := by
  induction' k with k ih
  · aesop                    -- base case: k = 0
  · convert ...              -- inductive step: k + 1
```

### The `filter` / `map` / `fold` Pipeline

```lean
-- Finset operations mirror functional programming idioms:
-- filter: select elements satisfying a predicate
(Finset.univ.filter fun x => f (x + u) + f x = v)

-- The Walsh support is a filter:
noncomputable def walshSupport (b : ι) : Finset ι :=
  Finset.univ.filter fun a => W a b ≠ 0

-- Summation is a fold:
∑ x : F, ψ (a * x + b * f x)    -- fold (+) 0 (map ψ∘g field_elements)
```

### Algebraic Data Types

Lean's `inductive` types (not used directly here, but underlying everything) are **algebraic data types**. The `∧` (And) is a product type; `∨` (Or) is a sum type; `∃` is a dependent sum (Σ-type).

---

<a id="14-import-hygiene"></a>
## 14. Import Hygiene

The current formalization uses `import Mathlib` (importing the entire library). For production code, prefer **specific imports**:

```lean
-- ✅ Ideal: import only what you need
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Frobenius
import Mathlib.Data.Polynomial.RingDivision

-- ❌ Current: imports everything (slow compilation)
import Mathlib
```

**Why specific imports matter:**
- **Build speed**: `import Mathlib` can add 30+ seconds to compilation
- **Dependency clarity**: readers can see what mathematical machinery is used
- **Maintenance**: changes to unrelated Mathlib files won't break your code

**How to find the right imports:**
1. Start with `import Mathlib`
2. Use `#check` to find which lemmas you use
3. Use `#print` or hover in VS Code to find their source modules
4. Replace the blanket import with specific ones
5. Verify the build still succeeds

**Caveat**: Mathlib module paths change between versions. If specific imports break after a Mathlib update, temporarily revert to `import Mathlib` while you update paths. In this project, since the Mathlib version may differ from the latest, `import Mathlib` is used as a pragmatic choice for stability.

---

<a id="15-walkthrough"></a>
## 15. Annotated Code Walkthrough

### Normalization.lean — The Crystal's Unit Cell

```lean
-- ═══════════════════════════════════════════════════════════════
-- GOLD FUNCTION: The "atom" of the crystal
-- Category Theory: An endomorphism in End(F)
-- Type Theory: A term of type F → F
-- Crystal: The unit cell that generates the lattice
-- ═══════════════════════════════════════════════════════════════
def goldFun (x : F) : F := x ^ goldExp k

-- ═══════════════════════════════════════════════════════════════
-- DERIVATIVE: Measuring the crystal's response to perturbation
-- Knot Theory: The "crossing" created by shifting u
-- FP: A curried binary function (u is a parameter)
-- ═══════════════════════════════════════════════════════════════
def deltaGold (u x : F) : F :=
  goldFun k F (x + u) + goldFun k F x

-- ═══════════════════════════════════════════════════════════════
-- NORMALIZATION: The Reidemeister move
-- Universal Arrow: y = x/u is the universal simplification
-- Fold: Collapses the u-dependence into a canonical form
-- ═══════════════════════════════════════════════════════════════
lemma kernel_iso_normalized (u : F) (hu : u ≠ 0) (x : F) :
    deltaGold k F u x = 0 ↔ Lnorm k F (x * u⁻¹) = 0
```

### Factorization.lean — The Braid's Elementary Crossings

```lean
-- ═══════════════════════════════════════════════════════════════
-- FROBENIUS: The crystal's fundamental symmetry
-- Higher Category: A 1-endomorphism of the field object
-- Opetope: A 1-dimensional opetopic cell (an arrow)
-- ═══════════════════════════════════════════════════════════════
def frob2 : F →+* F := frobenius F 2

-- ═══════════════════════════════════════════════════════════════
-- ARTIN–SCHREIER MAP: The simplest crossing
-- Knot: A single elementary braid generator σ₁
-- Tiling: A single tile shape
-- ═══════════════════════════════════════════════════════════════
def L₁ (y : F) : F := y ^ 2 + y

-- ═══════════════════════════════════════════════════════════════
-- PARTIAL TRACE: The fold over the Frobenius orbit
-- Fold: ∑_{i=0}^{k-1} φ^i(y)  — a literal catamorphism
-- Braid: k-1 parallel strands, each a Frobenius twist
-- ═══════════════════════════════════════════════════════════════
def L₂ (y : F) : F := ∑ i ∈ range k, y ^ (2 ^ i)

-- ═══════════════════════════════════════════════════════════════
-- FACTORIZATION: The braid decomposition theorem
-- Operad: L₀ = μ(L₁, L₂) — operadic composition
-- Crystal: Decomposing the lattice vibration into normal modes
-- ═══════════════════════════════════════════════════════════════
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y
```

### Counting.lean — The Tiling Count

```lean
-- ═══════════════════════════════════════════════════════════════
-- PARSEVAL: The perfect tiling identity
-- Tiling: ∑ (tile areas) = (total area) — no gaps, no overlaps
-- Category: Natural isomorphism between energy functors
-- Universal: The canonical decomposition of q²
-- ═══════════════════════════════════════════════════════════════
(H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)

-- ═══════════════════════════════════════════════════════════════
-- AB → APN: The Grand Forcing Theorem
-- Crystal: Rigidity — the only defect-free crystal is the APN one
-- Knot: All knots simplify to trivial (≤ 2 crossings)
-- Opetope: A 3-cell witnessing the collapse of spectral
--          constraints to differential constraints
-- ═══════════════════════════════════════════════════════════════
theorem AB_implies_APN ... : IsAPN_abs δ

-- ═══════════════════════════════════════════════════════════════
-- WALSH SUPPORT: The crystal's Bragg peaks
-- Tiling: Which tiles are "lit up" in the diffraction pattern
-- HoTT: The fiber of the Walsh transform over nonzero values
-- ═══════════════════════════════════════════════════════════════
noncomputable def walshSupport (b : ι) : Finset ι :=
  Finset.univ.filter fun a => W a b ≠ 0
```

### Kasami_Final_Theorem.lean — The Grand Synthesis

```lean
-- ═══════════════════════════════════════════════════════════════
-- KASAMI BRIDGE: The universal arrow from AB to applications
-- Category: The terminal object in the category of AB consequences
-- Opetope: A corolla opetope with 3 leaves (APN, support, pairs)
-- Crystal: The complete structure determination theorem —
--          knowing the diffraction pattern (AB) determines
--          the crystal structure (APN + geometry)
-- ═══════════════════════════════════════════════════════════════
theorem kasami_bridge ... :
    IsAPN_abs δ ∧
    (∀ b, b ≠ 0 → (walshSupport W b).card = 2 ^ (n - 1)) ∧
    (∀ b, b ≠ 0 → Nat.choose (walshSupport W b).card 2 = ...)
```

---

## Summary of Metaphors

| Formalization Element | Crystal | Tiling | Knot/Braid | Fold | Category |
|---|---|---|---|---|---|
| `goldFun` | Unit cell | Tile shape | — | — | Object |
| `frobenius` | Symmetry group | Rotation | — | — | Automorphism |
| `deltaGold` | Perturbation | — | Crossing | — | Morphism |
| `kernel_iso_normalized` | Coordinate change | — | Reidemeister | Collapse | Equivalence |
| `L₁ ∘ L₂ = L₀` | Normal modes | — | Braid decomp | — | Factorization |
| Parseval | — | Perfect cover | — | Energy fold | Nat. iso. |
| `AB_implies_APN` | Rigidity | Tile count | Unknotting | Grand fold | Universal |
| `walshSupport` | Bragg peaks | Lit tiles | — | — | Fiber |
| `kasami_bridge` | Structure theorem | — | — | — | Terminal |

---

## Further Reading

- **Crystals & Fourier Analysis**: The connection between diffraction patterns and Fourier spectra is the foundation of X-ray crystallography.
- **Category Theory**: Mac Lane, *Categories for the Working Mathematician*
- **HoTT**: The HoTT Book (*Homotopy Type Theory: Univalent Foundations of Mathematics*)
- **Opetopes**: Baez & Dolan, "Higher-Dimensional Algebra III: n-Categories and the Algebra of Opetopes"
- **APN Functions**: Budaghyan, *Construction and Analysis of Cryptographic Functions*
- **Lean 4**: *Theorem Proving in Lean 4* (official documentation)
- **Mathlib**: The Mathlib documentation at https://leanprover-community.github.io/mathlib4_docs/

---

*This guide was created to illuminate the deep structural patterns connecting formal mathematics, theoretical computer science, and the visual arts of symmetry. The formalization is not just a proof — it's a crystal, a tiling, a knot, a fold, and a universal arrow, all at once.*
