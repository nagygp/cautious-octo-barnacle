-- ══════════════════════════════════════════════════════════════════
-- TARGETED IMPORTS: each line brings in exactly what we need
-- ══════════════════════════════════════════════════════════════════
import Mathlib.Data.Finset.Card           -- Finset, card, filter
import Mathlib.Data.Fintype.Basic         -- Fintype class
import Mathlib.Data.Nat.Choose.Basic      -- Nat.choose
import Mathlib.Algebra.BigOperators.Group.Finset.Basic  -- ∑ notation
import Mathlib.Algebra.Order.Ring.Defs  -- ordered ring lemmas
import Mathlib.Tactic                     -- simp, ring, omega, etc.

/-!
# Patterns.lean — An Annotated Gallery of Lean, Type Theory & Category Theory

This file is a self-contained tutorial for new learners of Lean 4.
It demonstrates key patterns from type theory, category theory, functional
programming, and proof engineering — all illustrated with ideas from the
Kasami/Bracken–McGuire formalization in this project.

## How to Read This File

Each section is a mini-lesson. Read the comments, study the code, and
modify things to see what happens. Lean is best learned interactively!

## Import Philosophy

We import only the specific Mathlib modules we need.
This makes dependencies explicit and compilation faster.

**Tip:** To find which module a lemma lives in, use:
  `#check @Finset.card_filter_le_iff` → hover to see the module path,
  or search in the Mathlib docs at https://leanprover-community.github.io/mathlib4_docs/
-/

-- ══════════════════════════════════════════════════════════════════
-- Open scoped namespaces for notation
-- ══════════════════════════════════════════════════════════════════
open Finset BigOperators

-- ══════════════════════════════════════════════════════════════════
-- SECTION 1: TYPES AS PROPOSITIONS (Curry–Howard)
-- ══════════════════════════════════════════════════════════════════

/-!
## §1 The Curry–Howard Correspondence

The most fundamental idea: **types are propositions, terms are proofs**.

In Lean, `theorem` and `def` are the same thing — both construct a term
of a given type. The only difference is that `theorem` lives in `Prop`
(proof-irrelevant) while `def` lives in `Type` (computationally relevant).

**Category theory connection:** This is the internal language of a
*Cartesian closed category*. `Prop` is the subobject classifier,
function types `A → B` are exponential objects, and `∀` is a
dependent product (right adjoint to pullback).
-/

-- A proposition is a type in Prop
-- A proof is a term of that type
theorem two_plus_two : 2 + 2 = 4 := rfl
-- `rfl` is the reflexivity proof — the simplest possible term.
-- It works because 2 + 2 *reduces* to 4 by computation.
-- This is called DEFINITIONAL EQUALITY or JUDGEMENTAL EQUALITY.

-- A more interesting proof: a function that transforms evidence
-- "If n ≥ 1, then 2^n ≥ 2."
-- Read the TYPE as a logical statement, the TERM as a proof.
theorem pow_two_ge_two (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≥ 2 := by
  -- `by` enters TACTIC MODE: we build the term interactively.
  -- Tactic mode is like a dialogue with the proof assistant.
  calc 2 ^ n ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 2 := by norm_num
  -- `calc` is a CALCULATIONAL PROOF: a chain of inequalities.
  -- Each step is justified by a lemma or tactic.
  -- This is clean, readable, and mirrors how mathematicians write.

-- ══════════════════════════════════════════════════════════════════
-- SECTION 2: DEPENDENT TYPES & UNIVERSE POLYMORPHISM
-- ══════════════════════════════════════════════════════════════════

/-!
## §2 Dependent Types

In Lean, types can depend on values. This is strictly more powerful
than simple types (like in Haskell or OCaml).

**HoTT connection:** Dependent types are *fibrations*.
`(x : A) → B x` is a section of the fibration `B` over `A`.
The total space is `Σ x : A, B x` (sigma type = dependent pair).
-/

-- A dependent function: the RETURN TYPE depends on the INPUT VALUE
-- "Given n, produce a proof that n + 0 = n"
-- The type `n + 0 = n` changes as n changes — it's a family of types.
example : (n : ℕ) → n + 0 = n := fun n => Nat.add_zero n

-- Universe polymorphism: `Type*` means "any universe level"
-- This is ESSENTIAL for reusable mathematics
-- ✅ Good: works for ℕ (in Type 0), for Type itself (in Type 1), etc.
def myId {α : Type*} (x : α) : α := x

-- ══════════════════════════════════════════════════════════════════
-- SECTION 3: TYPE CLASSES — LEAN'S MOST POWERFUL ABSTRACTION
-- ══════════════════════════════════════════════════════════════════

/-!
## §3 Type Classes as Algebraic Structure

Type classes encode mathematical structure. They are Lean's version of
*algebraic theories* from universal algebra.

**Category theory pattern:** A type class is a FUNCTOR from the category
of types to the category of structures. Instance resolution is functorial
composition: `CommRing R` gives `Ring R` gives `AddCommGroup R`, etc.

**Universal algebra pattern:** Each type class is a *Lawvere theory* —
an algebraic theory specified by operations and equations.

**Beautiful pattern 🌟:** The hierarchy of algebraic structures in Mathlib
forms a LATTICE (partially ordered set), and Lean's instance resolution
traverses this lattice automatically. You write `[Field F]` and get
hundreds of derived instances for free!
-/

-- A simple custom type class: "types with a distinguished element"
class Pointed (α : Type*) where
  point : α

-- Instances: ℕ has a point (zero), so does Bool (true)
instance : Pointed ℕ where point := 0
instance : Pointed Bool where point := true

-- Using the type class: α is constrained but not specified
def defaultValue (α : Type*) [Pointed α] : α := Pointed.point

#eval defaultValue ℕ     -- outputs: 0
#eval defaultValue Bool   -- outputs: true
-- Lean automatically resolves which instance to use!

-- ══════════════════════════════════════════════════════════════════
-- SECTION 4: FUNCTIONAL PROGRAMMING PRINCIPLES
-- ══════════════════════════════════════════════════════════════════

/-!
## §4 Higher-Order Functions and Composition

Lean is a purely functional language. Every mathematical operation is
a function, and functions are first-class citizens.

**Category theory pattern:** Functions are morphisms in the category `Type`.
Composition `g ∘ f` is THE fundamental operation of category theory.
The `Finset.filter`, `Finset.map`, `Finset.sum` API is a FUNCTOR from
the category of predicates/functions to the category of finsets/values.
-/

-- HIGHER-ORDER FUNCTIONS: functions that take functions as arguments

-- filter: takes a predicate and keeps matching elements
-- This is the SET COMPREHENSION {x ∈ S | P(x)} made computable.
#eval (Finset.range 10).filter (· % 2 = 0)
-- {0, 2, 4, 6, 8}

-- map: applies a function to each element (FUNCTORIAL action)
-- This is the IMAGE f(S) = {f(x) | x ∈ S}.
#eval (Finset.range 5).image (· ^ 2)
-- {0, 1, 4, 9, 16}

-- sum: folds a function over a finset (a CATAMORPHISM / fold)
-- This is ∑_{x ∈ S} f(x).
#eval ∑ x ∈ Finset.range 5, x ^ 2
-- 30 = 0 + 1 + 4 + 9 + 16

-- COMPOSITION: the heart of category theory
-- "Factor through an intermediate computation"
-- This mirrors the factorization L₀ = L₁ ∘ L₂ in Factorization.lean!
def double (n : ℕ) : ℕ := 2 * n
def addOne (n : ℕ) : ℕ := n + 1
def doubleAddOne : ℕ → ℕ := addOne ∘ double  -- composition!
#eval doubleAddOne 3  -- 7 = 2*3 + 1

-- ══════════════════════════════════════════════════════════════════
-- SECTION 5: THE ABSTRACT FRAMEWORK PATTERN
-- ══════════════════════════════════════════════════════════════════

/-!
## §5 Abstraction as a Universal Arrow

The most important design pattern in this project: ABSTRACT AWAY
from concrete objects and prove theorems about interfaces.

**Category theory pattern:** This is a UNIVERSAL ARROW.
We define an abstract interface (type class constraints on ι, W, δ)
and prove theorems about ANY implementation. Concrete theorems are
obtained by INSTANTIATION — which is the unit of the adjunction
between abstract and concrete categories.

**Opetopic pattern 🔷:** The abstract framework is a higher-dimensional
cell: it takes multiple inputs (Walsh coefficients, differential counts,
Parseval identity, ...) and produces a single output (APN property).
The shape of this cell is an OPETOPE.

**Beautiful pattern 🌟:** Notice how `variable` introduces parameters
that are shared across an entire section. This is MODULAR PROGRAMMING
for mathematics — each section is a module with explicit imports.
-/

section AbstractExample

-- The abstract interface: ι is ANY finite type with a zero
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- A "spectrum" is any function from pairs to integers
-- (abstraction of Walsh coefficients)
variable (S : ι → ι → ℤ)

-- The "support" for a fixed second argument
-- Beautiful pattern: this is a FIBER of the map S over nonzero values.
-- In category theory, fibers are PULLBACKS.
noncomputable def support (b : ι) : Finset ι :=
  Finset.univ.filter fun a => S a b ≠ 0

-- A theorem about the abstract interface:
-- "If every value is bounded, then the support is bounded"
-- This holds for ANY S, ANY ι — it's UNIVERSAL.
omit [DecidableEq ι] in
theorem support_card_le_of_bound
    (b : ι) (M : ℤ) (_hM : M ≠ 0)
    (hbound : ∀ a : ι, S a b ≠ 0 → S a b ^ 2 = M)
    (hparseval : ∑ a : ι, S a b ^ 2 = (Fintype.card ι : ℤ) ^ 2) :
    (support S b).card * M = (Fintype.card ι : ℤ) ^ 2 := by
  -- KEY INSIGHT: Split the Parseval sum into support and non-support
  -- On the support: S(a,b)² = M (by hypothesis)
  -- Off the support: S(a,b) = 0, so S(a,b)² = 0
  have : ∑ a : ι, S a b ^ 2 = ∑ a ∈ support S b, M := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    · exact Finset.sum_congr rfl fun x hx => hbound x (by simp [support] at hx; exact hx)
    · intro x _ hx; simp [support] at hx; simp [hx]
  -- Now: |support| · M = q²
  simp [Finset.sum_const] at this
  linarith

-- ✨ REMARK: This is exactly the structure of `triple_count_eq` in
-- Counting.lean! The concrete version instantiates S := W (Walsh),
-- M := 2^(n+1) (from AB), and derives |S_b| = 2^(n-1).

end AbstractExample

-- ══════════════════════════════════════════════════════════════════
-- SECTION 6: PROOF TECHNIQUES & TACTICS
-- ══════════════════════════════════════════════════════════════════

/-!
## §6 Essential Tactic Catalog

Tactics are programs that build proof terms. Here are the most important
ones, with category-theoretic intuitions.

| Tactic | What it does | Category theory analogy |
|--------|-------------|------------------------|
| `exact` | Provide the full proof term | Give the morphism directly |
| `apply` | Use a lemma, leaving goals for its hypotheses | Compose with a morphism |
| `intro` | Introduce a hypothesis | Curry a morphism |
| `have` | Prove an intermediate fact | Factor through an object |
| `rw` | Rewrite using an equality | Transport along a path |
| `simp` | Simplify using rewrite rules | Apply a confluent rewrite system |
| `ring` | Prove ring equalities | Use the free ring's universal property |
| `omega` | Prove linear arithmetic over ℕ/ℤ | Decide in Presburger arithmetic |
| `nlinarith` | Nonlinear arithmetic | Positivstellensatz certificate |
| `calc` | Chain of equalities/inequalities | Compose a sequence of morphisms |
| `cases` | Case split on a disjunction | Coproduct elimination |
| `constructor` | Split a conjunction goal | Product introduction |
| `induction` | Structural induction | Initial algebra recursion |
-/

-- EXAMPLE: The "squeezing argument" from AB_implies_APN
-- This is a beautiful proof pattern: upper bound meets lower bound.

-- "If k is even and k² ≤ 2k, then k ≤ 2."
-- This is the FORCING STEP that pins down δ(u,v) ∈ {0, 2}.
theorem forcing_argument (k : ℕ) (_heven : 2 ∣ k) (hsq : k ^ 2 ≤ 2 * k) :
    k ≤ 2 := by
  -- The proof is pure arithmetic, but the PATTERN is categorical:
  -- We have k trapped between two constraints:
  --   LOWER: k² ≥ 2k  (because k is even and ≥ 0)
  --   UPPER: k² ≤ 2k  (given)
  -- Equality forces k ∈ {0, 2}.
  --
  -- In category theory, this is an EQUALIZER:
  -- k is the equalizer of the two maps k ↦ k² and k ↦ 2k.
  nlinarith

-- EXAMPLE: The `calc` proof style — chains of reasoning
-- Beautiful because it mirrors mathematical writing perfectly.
theorem sum_formula (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    -- After unfolding one step, we use the induction hypothesis
    linarith [ih]

-- ══════════════════════════════════════════════════════════════════
-- SECTION 7: THE CATEGORY OF PROOFS
-- ══════════════════════════════════════════════════════════════════

/-!
## §7 Proofs as Morphisms — The Proof Category

Every Lean file defines a category:
- **Objects:** the theorems and definitions
- **Morphisms:** the dependencies (which lemma uses which)

**Higher category theory pattern:** This is a 2-category!
- 0-cells: files (modules)
- 1-cells: import relationships
- 2-cells: individual lemma dependencies

**Opetopic pattern 🔷:** Each theorem with multiple hypotheses is an
opetope — a cell with multiple input faces and one output face.

The project's dependency structure:

```
  Normalization ──┐
                  ├──► Kasami_Final_Theorem
  Factorization ──┤
                  │
  Counting ───────┘
```

This is a COLIMIT (pushout) in the category of proofs:
the final theorem is the universal way to combine the three components.
-/

-- EXAMPLE: Building a proof from components (product in Prop)
-- This mirrors `kasami_bridge` which combines three results.
theorem combined_example (n : ℕ) (hn : 2 ≤ n) :
    -- Three conclusions combined with ∧ (conjunction = categorical product)
    (2 ^ n ≥ 4) ∧ (n * n ≥ 4) ∧ (2 * n ≥ 4) := by
  -- `refine ⟨?_, ?_, ?_⟩` splits the product into three goals
  -- This is the PRODUCT INTRODUCTION RULE (universal property of ×)
  refine ⟨?_, ?_, ?_⟩
  · -- Component 1
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 4 := by norm_num
  · -- Component 2
    nlinarith
  · -- Component 3
    omega

-- ══════════════════════════════════════════════════════════════════
-- SECTION 8: COOL PATTERNS & UNIVERSAL ARROWS
-- ══════════════════════════════════════════════════════════════════

/-!
## §8 Beautiful Patterns in This Project

### 🌟 Pattern 1: The Frobenius Miracle

In characteristic 2, the Frobenius map `x ↦ x²` is a RING HOMOMORPHISM.
This means `(a + b)² = a² + b²` — the "freshman's dream"!

This is why the Gold function's derivative is LINEARIZED:
the Frobenius kills all cross terms, leaving a clean additive structure.

**Category theory:** The Frobenius is an endofunctor on the category of
F-vector spaces. It's the identity on objects but acts on morphisms by
squaring coefficients. This endofunctor is EXACT (preserves kernels and
cokernels), which is why the kernel analysis works so cleanly.

### 🌟 Pattern 2: The Parseval Duality

Parseval's identity `∑ |W(a,b)|² = q²` is a form of ADJUNCTION:
the Walsh transform W is an isometry, meaning it preserves the inner
product. In categorical terms:

```
  (spatial domain, ∑ f·g)  ←──W──→  (frequency domain, ∑ Wf·Wg)
```

W is a functor that preserves the "metric" structure.
The Parseval identity says W is a UNITARY NATURAL TRANSFORMATION.

### 🌟 Pattern 3: The Characteristic 2 Pairing

Solutions to `f(x+u) + f(x) = v` come in pairs `{x, x+u}` because
adding u is an involution (u + u = 0 in char 2). This means:
- δ(u,v) is always even (for u ≠ 0)
- The solution set has a FREE ℤ/2-ACTION

In category theory, this is a QUOTIENT by a group action:
`Solutions / (ℤ/2)` is the set of orbits, and |orbits| = δ/2.

### 🌟 Pattern 4: Universal Properties Everywhere

The abstract framework `{ι : Type*} [Fintype ι] ...` is the
UNIVERSAL PROPERTY of the theorem: it factors through the "free"
finite type. Every concrete instance (GF(2^n) for specific n)
is obtained by the unique map from the universal object.

This is the Yoneda perspective: the abstract theorem represents
ALL concrete theorems simultaneously.
-/

-- ══════════════════════════════════════════════════════════════════
-- SECTION 9: CLEAN CODE CHECKLIST
-- ══════════════════════════════════════════════════════════════════

/-!
## §9 Clean Lean Code Checklist

Before submitting any Lean file, verify:

### Structure
- [ ] Each file proves ONE main result
- [ ] Helper lemmas are in logical order (bottom-up)
- [ ] Sections group related variables and lemmas
- [ ] Namespaces prevent name collisions

### Naming
- [ ] Follows Mathlib conventions (`X_of_Y`, `X_iff_Y`, `X_eq_Y`)
- [ ] Descriptive names (not `h1`, `h2`, `h3`)
- [ ] No Greek letters that shadow Mathlib (`φ`, `π`, `ε`)

### Documentation
- [ ] Module docstring (`/-! ... -/`) at the top
- [ ] Each theorem has a doc comment (`/-- ... -/`)
- [ ] Proof sketch in comments for complex proofs
- [ ] References to source material

### Proof Style
- [ ] Structured tactics (`have`, `calc`, `show`) for readability
- [ ] No leftover `sorry` (except intentional)
- [ ] No suppressed linter warnings
- [ ] `noncomputable` where needed

### Imports
- [ ] Only import what you use
- [ ] Group imports by mathematical area
- [ ] No circular imports

### Performance
- [ ] `set_option maxHeartbeats` only where necessary
- [ ] No unnecessarily large `simp` calls
- [ ] Consider `simp only [...]` over bare `simp`
-/

-- ══════════════════════════════════════════════════════════════════
-- SECTION 10: EXERCISES FOR THE READER
-- ══════════════════════════════════════════════════════════════════

/-!
## §10 Exercises

Try these to build your Lean skills:

### Exercise 1 (Warm-up)
Prove that for any natural number n, `n + n = 2 * n`.
-/

theorem ex1 (n : ℕ) : n + n = 2 * n := by omega

/-!
### Exercise 2 (Type class)
Define a type class `HasSize` with a function `size : α → ℕ`,
and give instances for `List` and `String`.
-/

class HasSize (α : Type*) where
  size : α → ℕ

instance : HasSize (List α) where size := List.length
instance : HasSize String where size := String.length

/-!
### Exercise 3 (Induction)
Prove that `∑_{i=0}^{n} 2^i = 2^(n+1) - 1`.
Hint: use `Finset.sum_range_succ` and the induction hypothesis.
-/

-- Try it yourself! Replace `sorry` with a proof.
-- theorem geometric_sum (n : ℕ) :
--   ∑ i ∈ Finset.range (n + 1), 2 ^ i = 2 ^ (n + 1) - 1 := by
--   sorry

/-!
### Exercise 4 (Challenge)
Prove that the number of subsets of a finite set of size n is 2^n.
This requires `Fintype.card_set` or `Finset.card_powerset` from Mathlib.

### Exercise 5 (Project)
Formalize YOUR favorite theorem! Start with the statement, add `sorry`,
and work on the proof one step at a time.
-/
