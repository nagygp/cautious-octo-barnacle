/-
  Perspectives/TypeTheory.lean

  ═══════════════════════════════════════════════════════════════════════════════
  TYPE-THEORETIC PERSPECTIVE ON THE KASAMI-GOLD APN THEOREM
  ═══════════════════════════════════════════════════════════════════════════════

  This file demonstrates how the Kasami-Gold "AB ⟹ APN" theorem naturally
  embodies deep principles of the Calculus of Inductive Constructions (CIC)
  — Lean 4's foundational type theory. We also connect to functional programming
  principles, and show how to write clean, idiomatic Lean code.

  ## Foundational Context

  Lean 4 is based on the **Calculus of Inductive Constructions** (CIC), which
  extends Martin-Löf Type Theory (MLTT) with:
    • An impredicative universe `Prop` (propositions as types, with proof
      irrelevance)
    • Inductive types (natural numbers, lists, etc.)
    • A universe hierarchy `Type 0 : Type 1 : Type 2 : ...`

  The key CIC insight: **propositions are types, proofs are terms**.
  When we write `theorem foo : P := proof`, we are constructing a term
  `proof` of type `P`. This is the Curry-Howard correspondence.

  ## Constructive vs Classical

  CIC is inherently constructive — `em : ∀ P, P ∨ ¬P` is NOT provable.
  Lean adds `Classical.choice` as an axiom, making it classical.
  The Kasami proof uses classical reasoning (e.g., `Decidable` instances,
  `Finset.filter`, case splits on equality).

  However, the *core arithmetic* of the proof is entirely constructive:
  the bounds `δ² ≥ 2δ` and `δ² = 2δ ⟹ δ ≤ 2` are decidable propositions
  about natural numbers.

  ## File Overview

  1. Propositions-as-Types: the AB ⟹ APN theorem as a function type
  2. Dependent Types: parameterized structures and proofs
  3. Universe Polymorphism: how the abstraction generalizes
  4. Functional Programming: composition, higher-order functions, purity
  5. Lean Best Practices: naming, structure, documentation

  Reference: Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN
  Functions", Theorem 3.
-/

import Mathlib

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 1: MINIMAL IMPORTS — BEST PRACTICE
    ═══════════════════════════════════════════════════════════════════════

    ### 🏗️ Best Practice: Import Discipline

    Ideally, one imports only the Mathlib modules actually needed. For a
    project of this complexity (Finsets, BigOperators, number theory), the
    dependency graph is deep. Below we use `import Mathlib` for reliability,
    but document what we actually need:

      • `Mathlib.Data.Finset.Basic`     — finite sets
      • `Mathlib.Data.Fintype.Basic`    — finite types
      • `Mathlib.Data.Int.Basic`        — integer arithmetic
      • `Mathlib.Data.Nat.Choose.Basic` — binomial coefficients
      • `Mathlib.Algebra.BigOperators.Group.Finset` — ∑ notation
      • `Mathlib.Tactic`               — omega, nlinarith, etc.

    In practice, Mathlib's transitive import structure means you often need
    `import Mathlib` anyway. The key best practice is: **document your actual
    dependencies even if you import broadly**.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 2: PROPOSITIONS AS TYPES — CURRY-HOWARD IN ACTION
    ═══════════════════════════════════════════════════════════════════════

    The Curry-Howard correspondence maps:
      • Propositions ↦ Types
      • Proofs ↦ Terms (inhabitants)
      • Implication (P → Q) ↦ Function type (P → Q)
      • Conjunction (P ∧ Q) ↦ Product type (P × Q)  [in Prop: And P Q]
      • Disjunction (P ∨ Q) ↦ Sum type (P ⊕ Q)    [in Prop: Or P Q]
      • Universal (∀ x, P x) ↦ Dependent function (Π x, P x)
      • Existential (∃ x, P x) ↦ Dependent pair (Σ x, P x) [in Prop]

    The Kasami theorem is a FUNCTION from AB-evidence to APN-evidence.
-/

open Finset BigOperators

namespace TypeTheoryPerspective

/-! ### 2.1 The Theorem as a Function Type

    `AB_implies_APN` has type:

      (hypotheses about W, δ, q, n) → IsAPN_abs δ

    Under Curry-Howard, this IS a function. The proof literally constructs
    an APN witness from AB evidence. This is the computational content of
    the theorem.

    🌟 **Beautiful Pattern**: The proof is a *program* that transforms
    spectral data (Walsh coefficients) into combinatorial data (differential
    bounds). This transformation is the mathematical content of the theorem.
-/

/-- ### 2.2 Dependent Types: Parameterized Properties

    `IsAPN_abs` is a *dependent predicate*: its type depends on the value `δ`.
    In CIC, this is a Pi-type: `δ : (ι → ι → ℕ) → Prop`.

    💡 **Lean Best Practice**: Use `def` for computational definitions,
    `structure` for bundled data + properties, `class` for typeclass inference.
    Here `IsAPN_abs` is a `def` returning `Prop` — the simplest choice for
    a property. -/
def IsAPN_demo (δ : ℕ → ℕ → ℕ) : Prop :=
  ∀ u, u ≠ 0 → ∀ v, δ u v ≤ 2

/-- ### 2.3 Propositions as Types: Proof Irrelevance

    In Lean's `Prop` universe, all proofs of the same proposition are
    definitionally equal. This means:

      If `h₁ h₂ : 2 + 2 = 4`, then `h₁ = h₂` by proof irrelevance.

    This is crucial for the Kasami proof: we don't care *which* proof of
    `δ(u,v) ≤ 2` we have, only that one exists.

    🔑 **Key Difference from HoTT**: In HoTT, proofs of equality carry
    computational content (paths in a space). In CIC/Lean, they don't.
    See the HoTT section for more on this.

    🎯 **Functional Programming Principle**: Proof irrelevance is analogous
    to *referential transparency* — the "value" (truth) of a proposition
    doesn't depend on which proof you provide. -/
example : ∀ (h₁ h₂ : 2 + 2 = 4), h₁ = h₂ := fun _ _ => rfl

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 3: THE CORE ARITHMETIC AS CONSTRUCTIVE CONTENT
    ═══════════════════════════════════════════════════════════════════════

    The heart of "AB ⟹ APN" is a chain of arithmetic inequalities:

      1. δ(u,v) is even       (characteristic 2 pairing: solutions {x, x+u})
      2. k even ⟹ k² ≥ 2k   (algebraic fact)
      3. ∑ δ² ≥ 2 · ∑ δ      (pointwise, from 1 + 2)
      4. ∑ δ² = 2 · ∑ δ      (from the Walsh fourth moment identity)
      5. Equality in 3 ⟹ each δ² = 2δ ⟹ δ ∈ {0, 2}

    This is ENTIRELY constructive over ℕ. No axiom of choice needed.

    🌟 **Beautiful Pattern**: The proof is a "squeezing argument" —
    we show both `∑ δ² ≥ 2 · ∑ δ` and `∑ δ² = 2 · ∑ δ`, forcing
    equality at every point. This is a universal pattern in analysis
    and combinatorics.
-/

/-- Step 2: The key arithmetic lemma. Entirely constructive.

    💡 **Lean Best Practice**: Name lemmas descriptively.
    `sq_ge_two_mul_of_even` reads as: "square ≥ two times, given even".
    Mathlib convention: conclusion first, hypotheses after `_of_`.

    💡 **FP Principle**: This is a *pure function* — no side effects,
    no state. Given `k` and a proof of `2 ∣ k`, it returns a proof of
    `k² ≥ 2k`. Total, deterministic, referentially transparent. -/
theorem sq_ge_two_mul_of_even (k : ℕ) (hk : 2 ∣ k) : k ^ 2 ≥ 2 * k := by
  -- 📝 Obtain the witness: k = 2m for some m
  obtain ⟨m, rfl⟩ := hk
  -- 📝 Now k = 2m, so k² = 4m² and 2k = 4m. Need 4m² ≥ 4m, i.e., m² ≥ m.
  -- 📝 `nlinarith` handles nonlinear arithmetic over ordered rings.
  --    This is one of Lean's most powerful "hammer" tactics.
  cases m with
  | zero => simp
  | succ m => nlinarith

/-- Step 5: The "forcing" lemma. Also constructive.

    🌟 **Universal Arrow Pattern**: This lemma is a *universal property*
    in disguise. The set {k ∈ ℕ | k² ≤ 2k} = {0, 1, 2}. The bound
    k ≤ 2 is the *universal bound* — the tightest possible conclusion.

    In category-theoretic language, 2 is the *terminal object* in the
    poset of valid upper bounds for elements satisfying k² ≤ 2k. -/
theorem le_two_of_sq_le_two_mul (k : ℕ) (hk : k ^ 2 ≤ 2 * k) : k ≤ 2 := by
  -- 📝 `nlinarith` again — it can solve polynomial inequalities over ℕ/ℤ/ℚ/ℝ
  nlinarith

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 4: FUNCTIONAL PROGRAMMING PATTERNS
    ═══════════════════════════════════════════════════════════════════════

    The Kasami formalization exhibits several FP design patterns:

    ### 4.1 Higher-Order Functions
    `Finset.sum`, `Finset.filter`, `Finset.card` are all higher-order:
    they take functions as arguments.

    ```
    Finset.filter (fun x => f (x + u) + f x = v) Finset.univ
    ```
    This is a `filter` over a predicate — a classic FP operation.

    ### 4.2 Composition
    The proof chains:  AB → Walsh bounds → fourth moment → δ bounds → APN
    Each step is a function; the theorem is their composition.
    This mirrors the FP principle of *function composition*.

    ### 4.3 Algebraic Data Types
    `Or` (disjunction) is an algebraic data type:
    ```
    inductive Or (a b : Prop) : Prop
    | inl : a → Or a b
    | inr : b → Or a b
    ```
    The AB property `W² = 0 ∨ W² = 2^{n+1}` is a sum type.
    Pattern matching on this sum is the core of the Walsh fourth moment
    computation.

    ### 4.4 Totality
    Every Lean function is total — no exceptions, no undefined behavior.
    This is why natural number subtraction is truncating:
    `3 - 5 = 0` in ℕ. The Kasami proof must handle this carefully
    (e.g., `2^(n-1)` when `n = 0`).
-/

/-- ### 4.5 Example: Filter as Higher-Order Function

    💡 **Lean Best Practice**: Use `Finset.filter` with decidable predicates.
    The `[DecidableEq F]` instance is needed for `· ≠ 0` to be decidable.

    🎯 **FP Principle**: `filter` is a *functor action* on the category
    of types with decidable predicates. It preserves identity and
    composition of predicates (up to propositional equality). -/
example : (Finset.range 10).filter (· % 2 = 0) = {0, 2, 4, 6, 8} := by decide

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 5: UNIVERSE POLYMORPHISM AND GENERALITY
    ═══════════════════════════════════════════════════════════════════════

    The abstract framework uses `{ι : Type*}` — universe-polymorphic.
    This means the theorem works for any finite type, not just `ZMod (2^n)`.

    In CIC, `Type*` means `Type u` for some universe variable `u`.
    The theorem lives in:
      `∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Zero ι], ...`

    This is a dependent function over universe-polymorphic types.

    🌟 **Beautiful Pattern**: Universe polymorphism is the type-theoretic
    analogue of *naturality* in category theory. The theorem is "natural"
    in the index type `ι` — it commutes with any structure-preserving
    map between finite types with zero.
-/

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 6: LEAN BEST PRACTICES DEMONSTRATED
    ═══════════════════════════════════════════════════════════════════════
-/

/-! ### 6.1 Naming Conventions

    Mathlib follows a systematic naming scheme:
    • **Theorem names**: `conclusion_of_hypothesis`
      e.g., `le_two_of_sq_le_two_mul`
    • **Namespace**: group related lemmas under a common namespace
      e.g., `KasamiFinal.delta_card_fixed`
    • **Type class instances**: `instance : Foo Bar`
    • **Definitions**: `camelCase` for defs, `snake_case` for lemmas

    ### 6.2 Documentation
    • Use `/-- ... -/` for doc strings (visible in hover info)
    • Use `/-! ... -/` for module-level documentation
    • Use `-- ...` for inline proof commentary

    ### 6.3 Proof Style
    • Prefer term-mode for simple proofs: `fun h => h.2`
    • Use tactic mode for complex proofs: `by intro h; exact h.2`
    • Use structured proofs (`have`, `suffices`, `calc`) for readability
    • Avoid deep nesting — extract helper lemmas

    ### 6.4 Variable Management
    • Use `variable` for recurring hypotheses
    • Use `section ... end` to scope variables
    • Use `omit` to exclude unused section variables from specific theorems
-/

/-- ### 6.5 Example: Clean Structured Proof

    This demonstrates a "calc-style" proof — the most readable format
    for chains of equalities/inequalities.

    💡 **Best Practice**: `calc` blocks make the proof structure visible
    at a glance. Each step is independently verifiable. -/
theorem pow_sq_identity_clean (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ (n - 1)) ^ 2 = 2 ^ (2 * n - 2) := by
  -- 📝 The key insight: (2^a)^2 = 2^(2a), and 2(n-1) = 2n - 2.
  -- 📝 We use `pow_mul` to rewrite (x^a)^b = x^(a*b).
  rw [← pow_mul]
  -- 📝 Now we need: n - 1 * 2 = 2 * n - 2, which is `omega`-decidable.
  congr 1; omega

/-- ### 6.6 Example: Term-Mode Proof (Functional Style)

    For simple lemmas, term-mode proofs are preferred — they are
    more "functional" and often more readable.

    🎯 **FP Principle**: A term-mode proof is literally a lambda term.
    It's a function from hypotheses to conclusion. -/
theorem and_comm_demo (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 7: CONSTRUCTIVE CONTENT AND DECIDABILITY
    ═══════════════════════════════════════════════════════════════════════

    ### The Decidability Hierarchy

    In constructive type theory, not every proposition is decidable.
    Lean uses the `Decidable` typeclass to track decidability:

    ```
    class Decidable (p : Prop) where
    | isTrue  : p → Decidable p
    | isFalse : ¬p → Decidable p
    ```

    For the Kasami proof, we need:
    • `DecidableEq ι` — equality on the index type is decidable
    • This gives us `Decidable (W a b ≠ 0)` — so we can filter
    • And `Decidable (δ u v ≤ 2)` — so we can state APN

    Without `DecidableEq`, we couldn't even *state* `|{a | W(a,b) ≠ 0}|`
    as a natural number!

    ### What's Constructive vs Classical

    The following parts are constructive:
    • All arithmetic lemmas (over ℕ, ℤ)
    • The "squeezing" argument
    • The definition of APN, AB

    The following use classical logic:
    • `Finset.filter` with arbitrary predicates (needs `Decidable`)
    • Case splits via `Or.elim` on AB property
    • Existence of counters in the forcing argument

    💡 **Best Practice**: Lean's `open Classical in` enables global
    decidability. For formalization, this is fine. For extraction of
    algorithms, one would want to stay constructive.
-/

/-! ### 7.1 Decidable Computation: `#eval`-able Proofs

    When definitions are computable, Lean can evaluate them.
    This is the bridge between proofs and programs.

    💡 **Best Practice**: Use `#eval` to test definitions before proving. -/
#eval (Finset.range 10).filter (fun k => k ^ 2 ≤ 2 * k)
-- Output: {0, 1, 2} — confirming our `le_two_of_sq_le_two_mul`!

#eval Nat.choose (2 ^ 4) 2  -- = 120 = 2^3 * (2^4 - 1) = 8 * 15 ✓

/-! ═══════════════════════════════════════════════════════════════════════
    SECTION 8: SUMMARY — THE KASAMI PROOF AS TYPE THEORY
    ═══════════════════════════════════════════════════════════════════════

    The Kasami bridge theorem, viewed type-theoretically:

    ```
    kasami_bridge : Σ-type (product of three components)
      = (IsAPN_abs δ)                              -- APN property
      × (∀ b, b ≠ 0 → card (walshSupport W b) = 2^(n-1))  -- support size
      × (∀ b, b ≠ 0 → choose (card ...) 2 = ...)  -- pair count
    ```

    The proof constructs this triple by:
    1. Building an APN proof from the AB hypothesis (a function)
    2. Computing support sizes from Parseval (arithmetic)
    3. Computing pair counts from support sizes (combinatorics)

    Each component is a **term** (program) in the CIC.
    The whole theorem is a **dependent function** from hypotheses to
    the conjunction of conclusions.

    This is the Curry-Howard correspondence at work: mathematical
    reasoning IS programming in a sufficiently rich type system.
-/

end TypeTheoryPerspective
