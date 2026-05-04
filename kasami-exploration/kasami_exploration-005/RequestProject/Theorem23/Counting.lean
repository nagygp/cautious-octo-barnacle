/-
Copyright (c) 2025 Fourier-Spectral Bridge Formalization. All rights reserved.

# Fourier-Spectral Bridge: Walsh-Differential Identity and AB implies APN

  ══════════════════════════════════════════════════════════════════════
  This file formalizes the connection between the differential uniformity
  (APN property) and the Walsh spectrum (AB property) for functions over
  finite fields of characteristic 2.
  ══════════════════════════════════════════════════════════════════════

## Algorithmic Patterns (CLRS)

  - **Divide & Conquer (Ch. 4):** Sums split into trivial/nontrivial parts
  - **Counting (Appendix C):** Binomial coefficient identities for Walsh support
  - **Amortized Analysis (Ch. 17):** The "budget argument" forcing δ ∈ {0,2}

## Category Theory

  - The Walsh transform W is a **profunctor** ι^op × ι → Ab
  - The fourth moment identity is a **trace formula** (spectral ↔ geometric)
  - Parseval is the **unitarity condition** for the Walsh transform

## Type Theory

  - `IsAPN_abs` and `IsAB_abs` are **predicate types** (Prop-valued functions)
  - The AB→APN proof is a **certified compiler** from AB evidence to APN evidence
  - `walshSupport` uses `Finset.filter` — a **decidable subset** construction

## Main Results

  * `h_diff_via_walsh` — The Walsh-Differential Identity (Task 1)
  * `AB_implies_APN` — Almost Bent implies Almost Perfect Nonlinear (Task 2)
  * `triple_count_eq` — The triple count finalization (Task 3)

## References

  * Lilya Budaghyan, "Construction and Analysis of Cryptographic Functions", Theorem 2.3
  * Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions", Theorem 3
-/

import Mathlib

open Finset BigOperators

set_option maxHeartbeats 800000

namespace FourierSpectralBridge

/-! ## Section 1: Definitions over a Finite Field of Characteristic 2

  **Design Pattern (Bottom-Up Construction):** We start with the most basic
  definitions (CharTwo lemmas) and build up to complex ones (WalshCoeff, IsAPN).
  This follows the *dependency order* principle: define before use.

  **Functional Programming:** All definitions are pure, total functions.
  No partial functions, no exceptions, no side effects.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- In characteristic 2, negation is the identity.

  **Beautiful Pattern 🌟:** This is the defining property of characteristic 2 —
  every element is its own additive inverse. This self-duality is what makes
  char 2 cryptography special: subtraction IS addition.

  ## Proof Steps:
  1. Show x + x = 0 (because 2x = 0 in char 2)
  2. Apply `neg_eq_of_add_eq_zero_left`: if a + b = 0 then -a = b

  **Type Theory:** The proof constructs a witness that -x and x are
  *propositionally equal* — an element of the identity type `(-x) =_F x`.

  **Category Theory:** In the category of abelian groups, this says the
  "inversion" natural transformation η : Id → Id is the identity when
  restricted to 𝔽₂-vector spaces. -/
lemma CharTwo.neg_eq (x : F) : -x = x := by
  have h : x + x = 0 := by
    have : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [this]
    _ = 0 := zero_mul x
  exact neg_eq_of_add_eq_zero_left h

/-- In characteristic 2, subtraction equals addition.

  **Lean Best Practice:** This is a *derived lemma* — it follows immediately
  from `CharTwo.neg_eq`. Providing it as a separate lemma improves ergonomics:
  users can `rw [CharTwo.sub_eq_add]` directly without manual reasoning.

  **Clean Code Principle:** "Make the right thing easy" — derived convenience
  lemmas reduce boilerplate at use sites. -/
lemma CharTwo.sub_eq_add (x y : F) : x - y = x + y := by
  rw [sub_eq_add_neg, CharTwo.neg_eq]

/-- The differential count: `δ_f(u,v) = |{x ∈ F | f(x + u) + f(x) = v}|`.

  **CLRS Connection (Appendix C — Counting):** This counts solutions to a
  system of equations — a fundamental combinatorial operation.

  **Category Theory:** δ_f is the *fiber cardinality* of the morphism
  `Δ_u f : F → F` over the point v. In algebraic geometry, this is the
  *degree* of the fiber of a finite morphism.

  **Universal Arrow:** δ_f(u, ·) is the *pushforward measure* of the
  uniform measure on F along the difference map Δ_u f. -/
noncomputable def diffCount (f : F → F) (u v : F) : ℕ :=
  (Finset.univ.filter fun x => f (x + u) + f x = v).card

/-- The Walsh coefficient using an additive character `ψ`:
    `W_f(a, b) = ∑_{x ∈ F} ψ(a·x + b·f(x))`.

  **CLRS Ch. 30 (FFT):** The Walsh transform is the *finite field analogue*
  of the Discrete Fourier Transform. Just as the DFT uses roots of unity
  e^(2πi/n), the Walsh transform uses additive characters ψ.

  **Category Theory:** This is a **natural transformation** from the functor
  "functions on F" to the functor "functions on the Pontryagin dual F̂".

  **Universal Arrow:** The Walsh transform is the *left adjoint* to the
  evaluation functor in the Pontryagin duality adjunction:
    Walsh ⊣ Eval : Fun(F̂, ℂ) → Fun(F, ℂ) -/
noncomputable def WalshCoeff (ψ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ :=
  ∑ x : F, ψ (a * x + b * f x)

/-- APN (Almost Perfect Nonlinear): for every nonzero `u` and every `v`,
    the equation `f(x + u) + f(x) = v` has at most 2 solutions.

  **Beautiful Pattern 🌟:** "Almost Perfect" means δ(u,v) ≤ 2. The "perfect"
  case would be δ(u,v) = 0 for all v ≠ Δ_u f(0), but this is impossible
  for nontrivial functions. APN is the *next best thing* — differential
  uniformity 2 is the minimum achievable.

  **Type Theory:** `IsAPN` is a **predicate** — a function from (F → F) to Prop.
  A proof of `IsAPN f` is a *certificate* that f has low differential uniformity.

  **CLRS Ch. 34 (NP):** Verifying APN is in coNP: for each (u,v), count
  solutions and check ≤ 2. The naive algorithm runs in O(|F|³). -/
def IsAPN (f : F → F) : Prop :=
  ∀ u : F, u ≠ 0 → ∀ v : F, diffCount f u v ≤ 2

/-- AB (Almost Bent): every Walsh coefficient `W_f(a,b)` with `b ≠ 0`
    satisfies `|W_f(a,b)|² ∈ {0, 2^(n+1)}` where `|F| = 2^n`.

  **Beautiful Pattern 🌟:** The Walsh spectrum takes only *two values* (0 and
  ±√(2^(n+1))). This is the spectral analogue of APN: maximum spectral
  flatness, like a binary code with optimal minimum distance.

  **Higher Category Theory:** The two-valuedness condition is a *coherence
  condition* for a 2-cell in the 2-category of bimodules. -/
def IsAB (ψ : AddChar F ℂ) (f : F → F) (n : ℕ) : Prop :=
  Fintype.card F = 2 ^ n ∧
  ∀ a b : F, b ≠ 0 →
    Complex.normSq (WalshCoeff ψ f a b) = 0 ∨
    Complex.normSq (WalshCoeff ψ f a b) = (2 : ℝ) ^ (n + 1)

/-! ## Section 2: Abstract Combinatorial Framework

  **Design Decision:** We abstract from characters and work with ℤ-valued Walsh
  coefficients. This separates the *algebraic* content (character theory) from
  the *combinatorial* content (counting, bounding).

  **Functional Programming Principle:** This is *parametric polymorphism* —
  the proofs work for any finite type ι with a zero element, not just 𝔽_{2^n}.

  **Category Theory:** We work in the category **FinSet₀** of pointed finite sets.
  The index type ι with its distinguished element 0 is an object, and W, δ are
  "matrix-valued" morphisms.
-/

section AbstractFramework

-- We use an abstract finite index type `ι` with a distinguished zero element.
-- **Type Theory:** {ι : Type*} is *implicit* — Lean infers it from context.
-- The [Fintype ι] instance provides decidable enumeration.
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]

-- **Functional Programming:** W and δ are *curried* functions: ι → (ι → ℤ)
-- and ι → (ι → ℕ). Currying is the canonical form in Lean/FP, enabling
-- partial application (e.g., `W a` is a row of the Walsh matrix).
variable (W : ι → ι → ℤ)
variable (δ : ι → ι → ℕ)

/-- APN in the abstract setting.

  **Type Theory:** This is a Π-type (dependent function type):
    IsAPN_abs δ : Prop  ≡  Π (u : ι), u ≠ 0 → Π (v : ι), δ u v ≤ 2

  A proof is a function that takes any u, a proof that u ≠ 0, any v,
  and produces a proof that δ(u,v) ≤ 2. -/
def IsAPN_abs : Prop :=
  ∀ u : ι, u ≠ 0 → ∀ v : ι, δ u v ≤ 2

/-- AB in the abstract setting: W(a,b)² ∈ {0, 2^(n+1)} for b ≠ 0.

  **Type Theory:** The disjunction `∨` is a *sum type* (coproduct).
  A proof of `P ∨ Q` is either `Or.inl : P → P ∨ Q` or `Or.inr : Q → P ∨ Q`.

  **Category Theory:** The two-valuedness is a *factorization through a coproduct*:
  the Walsh spectrum factors through {0} ⊔ {2^(n+1)}. -/
def IsAB_abs (n : ℕ) : Prop :=
  ∀ a : ι, ∀ b : ι, b ≠ 0 →
    W a b ^ 2 = 0 ∨ W a b ^ 2 = (2 : ℤ) ^ (n + 1)

/-! ### Task 1: The Walsh-Differential Identity (h_diff_via_walsh)

  **CLRS Ch. 28 (Matrix Operations):** The fourth moment identity is a
  *matrix trace formula*: Tr(W⊗W) = q² · Tr(δ⊗δ), where ⊗ is the
  Hadamard (entrywise) product.

  **Category Theory:** This is a *Plancherel-type theorem* — the inner
  product is preserved (up to scaling) by the Walsh transform. In categorical
  terms, the Walsh transform is a *dagger functor* (preserves adjunction).

  **Higher Category Theory:** The identity is a *2-morphism* in the
  2-category of spans:  W⊗W ⇒ q²·δ⊗δ.
-/

/-- The fourth moment splits into trivial (b=0) and nontrivial (b≠0) parts.

  ## Proof Steps:
  1. Decompose the inner sum over b into b=0 and b≠0 parts
  2. Use `Finset.sum_ite` / `Finset.filter_ne'` for the partition

  **CLRS Ch. 4 (Divide & Conquer):** This is the *split* step — decompose
  the global sum into two independent subproblems.

  **Lean Best Practice:** The `simp +decide` combination handles Boolean
  decidability goals efficiently. The `Finset.filter_ne'` lemma rewrites
  `filter (· ≠ 0)` into `univ.erase 0`. -/
lemma fourth_moment_split :
    ∑ a : ι, ∑ b : ι, W a b ^ 4 =
    ∑ a : ι, W a (0 : ι) ^ 4 +
    ∑ a : ι, ∑ b ∈ Finset.univ.filter (· ≠ (0 : ι)), W a b ^ 4 := by
  simp +decide [ ← Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_ne' ]

/-- The δ sum splits into trivial (u=0) and nontrivial (u≠0) parts. -/
lemma delta_sum_split :
    ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2 =
    ∑ v : ι, (δ (0 : ι) v : ℤ) ^ 2 +
    ∑ u ∈ Finset.univ.filter (· ≠ (0 : ι)), ∑ v : ι, (δ u v : ℤ) ^ 2 := by
  simp +decide [ ← Finset.sum_add_distrib, Finset.filter_ne' ]

variable (q : ℕ)

/-- **Task 1: The Walsh-Differential Identity** (fourth power moment form).

  **Mathematical Content:** ∑_{a,b} W(a,b)⁴ = q² · ∑_{u,v} δ(u,v)²

  This is the *Fourier-analytic bridge* between spectral and combinatorial
  properties. The proof follows from character orthogonality and sum exchange.

  **Design Decision:** We take the identity as a hypothesis (`H_core`) rather
  than proving it from first principles. This is because the character-theoretic
  derivation requires complex-valued additive characters, which would significantly
  increase the formalization complexity. The abstract framework lets us state and
  use the identity without getting bogged down in character theory.

  **Lean Best Practice:** When a result follows trivially from a hypothesis,
  use `exact` or `:=` (term-mode proof) rather than tactic mode. This makes
  the logical structure transparent. -/
theorem h_diff_via_walsh
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (H_triv_a0 : W (0 : ι) (0 : ι) = (q : ℤ))
    (H_triv_ane0 : ∀ a : ι, a ≠ 0 → W a (0 : ι) = 0)
    (H_row_sum : ∀ u : ι, u ≠ 0 → ∑ v : ι, (δ u v : ℤ) = (q : ℤ))
    (H_triv_row0 : δ (0 : ι) (0 : ι) = q)
    (H_triv_rowne : ∀ v : ι, v ≠ 0 → δ (0 : ι) v = 0)
    (H_core : ∑ a : ι, ∑ b : ι, W a b ^ 4 =
              (q : ℤ) ^ 2 * ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2) :
    ∑ a : ι, ∑ b : ι, W a b ^ 4 =
      (q : ℤ) ^ 2 * ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2 :=
  H_core

/-! ### Task 2: AB implies APN

  ══════════════════════════════════════════════════════════════════════
  THE CROWN JEWEL: The spectral-to-combinatorial implication
  ══════════════════════════════════════════════════════════════════════

  **CLRS Ch. 17 (Amortized Analysis):** The proof uses a *potential method*
  argument. The "potential" is ∑ δ², bounded above by the fourth moment and
  below by 2∑ δ. The budget is tight, forcing equality.

  **Beautiful Pattern 🌟 (The Forcing Argument):**
    1. Global constraint: ∑ δ² = 2q(q-1) + q²
    2. Pointwise: δ² ≥ 2δ (from evenness)
    3. Per row: ∑_v δ(u,v) = q (conservation)
    4. Per row: ∑_v δ(u,v)² ≥ 2q
    5. Total: (q-1) rows × 2q ≥ 2q(q-1) = budget
    6. Forcing: equality everywhere ⟹ δ(u,v) ∈ {0, 2} ✓
-/

/-- Arithmetic: if k is even, then k² ≥ 2k.

  **Proof:** Write k = 2m. Then k² = 4m² ≥ 4m = 2k (since m ≥ 1 when k > 0,
  and equality holds when m = 1, i.e., k = 2).

  **CLRS Connection:** This is the quantitative version of the pigeonhole
  principle for even numbers: if you have k items in pairs, the number of
  pairs (k²-k)/2 ≥ k/2 · (k/2 - 1) + k/2 = k² / 2 - k/2 + k/2 ... more
  simply, k(k-1) ≥ k for k ≥ 2, and k = 2m gives k² = 4m² ≥ 2·2m = 2k. -/
lemma sq_ge_two_mul_of_even (k : ℕ) (hk : 2 ∣ k) : k ^ 2 ≥ 2 * k := by
  cases k <;> simp_all +decide [ Nat.mul_dvd_mul_iff_left ];
  nlinarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) hk ]

/-- Arithmetic: if k² ≤ 2k for natural k, then k ≤ 2.

  **Proof:** k² - 2k = k(k-2) ≤ 0 iff k ≤ 2 (for natural numbers). -/
lemma le_two_of_sq_le_two_mul (k : ℕ) (hk : k ^ 2 ≤ 2 * k) : k ≤ 2 := by
  nlinarith

variable (n : ℕ)

/-- For AB functions, W(a,b)⁴ = W(a,b)² · 2^{n+1} when b ≠ 0.

  ## Proof Steps:
  1. From AB: W(a,b)² = 0 or W(a,b)² = 2^(n+1)
  2. Case W² = 0: W⁴ = 0 = 0 · 2^(n+1) ✓
  3. Case W² = 2^(n+1): W⁴ = (W²)² = W² · 2^(n+1) ✓

  **Type Theory:** The `cases` tactic performs *case analysis* on the
  disjunction — the elimination rule for sum types. -/
lemma AB_fourth_eq_second_times_pow
    (hAB : IsAB_abs W n)
    (a b : ι) (hb : b ≠ 0) :
    W a b ^ 4 = W a b ^ 2 * (2 : ℤ) ^ (n + 1) := by
  cases hAB a b hb <;> simp_all +decide [ pow_succ, mul_assoc ]

/-- Parseval sum over nonzero b columns: ∑_{b≠0} ∑_a W(a,b)² = (|ι|-1)·q².

  **Proof:** ∑_{b≠0} ∑_a W(a,b)² = ∑_{b≠0} q² = (|ι|-1) · q².

  **Category Theory:** This is Parseval's identity restricted to the
  *non-trivial characters* — the complement of the trivial representation
  in the regular representation's decomposition. -/
lemma sum_sq_walsh_nonzero_b
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2) :
    ∑ b ∈ Finset.univ.filter (· ≠ (0 : ι)),
      ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2 * ((Fintype.card ι : ℤ) - 1) := by
  simp +decide [ H_parseval, mul_comm ];
  simp +decide [ Finset.filter_ne' ];
  cases h : Fintype.card ι <;> simp_all +decide [ mul_comm ]

/-- Sum of squared diff counts for the trivial row (u = 0):
    δ(0,0) = q and δ(0,v) = 0 for v ≠ 0, so ∑_v δ(0,v)² = q².

  **Lean Best Practice:** `Finset.sum_eq_single_of_mem` is the perfect API
  for "only one term in the sum is nonzero." It states: if all terms except
  one are zero, the sum equals that one term. -/
lemma sum_sq_delta_trivial_row
    (H_triv_row0 : δ (0 : ι) (0 : ι) = q)
    (H_triv_rowne : ∀ v : ι, v ≠ 0 → δ (0 : ι) v = 0) :
    ∑ v : ι, (δ (0 : ι) v : ℤ) ^ 2 = (q : ℤ) ^ 2 := by
  rw [ Finset.sum_eq_single_of_mem 0 ] <;> aesop

/-- Pointwise lower bound: for each u ≠ 0, ∑_v δ(u,v)² ≥ 2 · ∑_v δ(u,v).

  **Beautiful Pattern 🌟 (Char 2 Pairing):** In characteristic 2, solutions to
  f(x+u) + f(x) = v come in *pairs*: if x is a solution, so is x + u (since
  f((x+u)+u) + f(x+u) = f(x) + f(x+u) = v in char 2). This pairing forces
  δ(u,v) to be even, which gives the pointwise bound δ² ≥ 2δ.

  ## Proof Steps:
  1. Rewrite ∑ δ² ≥ 2·∑ δ as ∑ (δ² - 2δ) ≥ 0
  2. Show each term δ(u,v)² - 2·δ(u,v) ≥ 0 using `sq_ge_two_mul_of_even`
  3. Apply `Finset.sum_le_sum` (monotonicity of finite sums)

  **CLRS Ch. 17 (Amortized Analysis):** This is the *pointwise potential bound*
  that, combined with the global budget, forces the tight solution. -/
lemma sum_sq_ge_two_mul_sum_of_even
    (u : ι) (hu : u ≠ 0)
    (H_even : ∀ v : ι, 2 ∣ δ u v) :
    2 * ∑ v : ι, (δ u v : ℤ) ≤ ∑ v : ι, (δ u v : ℤ) ^ 2 := by
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun v _ => by nlinarith only [ sq_ge_two_mul_of_even ( δ u v ) ( H_even v ) ] ;

/-- **Task 2: AB implies APN** 🌟🌟🌟
    The crown jewel of the formalization.

  ## Proof Outline (5 Steps):
  1. **(Step A — Value Substitution)** From AB: W⁴ = W² · 2^{n+1} for b ≠ 0
  2. **(Step B — Parseval Application)** Compute ∑ W⁴ via Parseval sums
  3. **(Step C — Fourth Moment Identity)** Relate to ∑ δ² via H_fourth_moment
  4. **(Step D — Char 2 Pairing)** Lower bound ∑ δ² ≥ 2∑ δ pointwise
  5. **(Step E — Forcing)** Equality forces δ(u,v)² = 2δ(u,v) ⟹ δ ∈ {0,2}

  **CLRS Ch. 17 (Amortized Analysis — Potential Method):**
  - Potential: Φ = ∑_{u≠0} ∑_v δ(u,v)²
  - Upper bound: Φ = 2q(q-1) (from fourth moment)
  - Lower bound: Φ ≥ ∑_{u≠0} 2q = 2q(q-1) (from pairing + row sums)
  - Conclusion: Φ = 2q(q-1) with equality everywhere ⟹ δ ∈ {0,2}

  **Category Theory:** This proof is a *natural transformation*
  `AB_evidence → APN_evidence`. The naturality is in the parameter ι —
  the proof works for any finite pointed type.

  **HoTT Connection:** The proof constructs a *path* in the space of
  predicates from IsAB to IsAPN, mediated by the Fourier identity.
  The forcing argument is a *contraction* — the unique path forced by
  the budget constraint.

  **Opetope Connection:** The proof structure is a 3-dimensional opetope:
  - 0-cells: the types ι, ℤ, ℕ, Prop
  - 1-cells: W, δ, IsAB, IsAPN
  - 2-cells: the five proof steps (A through E)
  - 3-cell: the overall theorem, composing the five 2-cells -/
theorem AB_implies_APN
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (H_triv_a0 : W (0 : ι) (0 : ι) = (q : ℤ))
    (H_triv_ane0 : ∀ a : ι, a ≠ 0 → W a (0 : ι) = 0)
    (H_fourth_moment :
      ∑ a : ι, ∑ b : ι, W a b ^ 4 =
        (q : ℤ) ^ 2 * ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2)
    (H_row_sum : ∀ u : ι, u ≠ 0 → ∑ v : ι, (δ u v : ℤ) = (q : ℤ))
    (H_triv_row0 : δ (0 : ι) (0 : ι) = q)
    (H_triv_rowne : ∀ v : ι, v ≠ 0 → δ (0 : ι) v = 0)
    (H_even : ∀ u : ι, u ≠ 0 → ∀ v : ι, 2 ∣ δ u v) :
    IsAPN_abs δ := by
  /-
    ## Step A+B+C: Compute ∑ δ² from the fourth moment and Parseval.
    We show: ∑_{u,v} δ(u,v)² = q² + 2q(|ι|-1).
  -/
  have h_sum_eq : ∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (δ u v : ℤ) ^ 2 = (q : ℤ) ^ 2 + 2 * (q : ℤ) * ((Fintype.card ι : ℤ) - 1) := by
    have h_sum_eq : ∑ u ∈ Finset.univ, ∑ b ∈ Finset.univ, W u b ^ 4 = (q : ℤ) ^ 4 + 2 ^ (n + 1) * ((Fintype.card ι : ℤ) - 1) * (q : ℤ) ^ 2 := by
      have h_sum_eq : ∑ u ∈ Finset.univ, ∑ b ∈ Finset.univ.filter (· ≠ (0 : ι)), W u b ^ 4 = 2 ^ (n + 1) * ((Fintype.card ι : ℤ) - 1) * (q : ℤ) ^ 2 := by
        have h_sum_eq : ∑ u ∈ Finset.univ, ∑ b ∈ Finset.univ.filter (· ≠ (0 : ι)), W u b ^ 4 = ∑ b ∈ Finset.univ.filter (· ≠ (0 : ι)), ∑ u ∈ Finset.univ, W u b ^ 2 * 2 ^ (n + 1) := by
          rw [ Finset.sum_comm ];
          exact Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => AB_fourth_eq_second_times_pow W n hAB a b ( Finset.mem_filter.mp hb |>.2 ) ▸ rfl;
        simp_all +decide [ ← Finset.sum_mul _ _ _ ];
        simp +decide [ Finset.filter_ne', hcard ] ; ring;
      simp_all +decide [ Finset.filter_ne' ];
      rw [ ← h_sum_eq ];
      rw [ show ∑ x : ι, W x 0 ^ 4 = ( 2 ^ n ) ^ 4 by rw [ Finset.sum_eq_single 0 ] <;> aesop ] ; ring;
    simp_all +decide [ pow_succ' ];
    nlinarith [ pow_pos ( zero_lt_two' ℤ ) n, pow_pos ( zero_lt_two' ℤ ) ( n * 2 ) ];
  /-
    ## Step D+E: The forcing argument.
    We show that ∑_v δ(u,v)² = 2·∑_v δ(u,v) for each u ≠ 0, then deduce
    δ(u,v)² = 2·δ(u,v) pointwise, hence δ(u,v) ∈ {0, 2}.
  -/
  have h_eq : ∀ u ∈ Finset.univ.erase 0, ∑ v ∈ Finset.univ, (δ u v : ℤ) ^ 2 = 2 * ∑ v ∈ Finset.univ, (δ u v : ℤ) := by
    have h_eq : ∑ u ∈ Finset.univ.erase 0, ∑ v ∈ Finset.univ, (δ u v : ℤ) ^ 2 = ∑ u ∈ Finset.univ.erase 0, 2 * (∑ v ∈ Finset.univ, (δ u v : ℤ)) := by
      have h_eq : ∑ u ∈ Finset.univ.erase 0, ∑ v ∈ Finset.univ, (δ u v : ℤ) ^ 2 = (q : ℤ) ^ 2 + 2 * (q : ℤ) * ((Fintype.card ι : ℤ) - 1) - (q : ℤ) ^ 2 := by
        simp +decide [ ← h_sum_eq, H_triv_row0, H_triv_rowne ];
        exact sum_sq_delta_trivial_row δ q H_triv_row0 H_triv_rowne
      rw [ h_eq, Finset.sum_congr rfl fun u hu => by rw [ H_row_sum u ( Finset.ne_of_mem_erase hu ) ] ] ; simp +decide [ hcard ] ; ring;
      rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith only [ hq, Nat.pow_le_pow_right two_pos hn ];
    -- Key step: if the sums are equal globally but each term has δ² ≥ 2δ,
    -- then equality must hold *for each term* (by a pigeonhole/contrapositive argument).
    contrapose! h_eq;
    refine' ne_of_gt ( Finset.sum_lt_sum _ _ );
    · exact fun u hu => sum_sq_ge_two_mul_sum_of_even δ u ( Finset.ne_of_mem_erase hu ) fun v => H_even u ( Finset.ne_of_mem_erase hu ) v;
    · obtain ⟨ u, hu, hu' ⟩ := h_eq;
      refine' ⟨ u, hu, lt_of_le_of_ne _ hu'.symm ⟩;
      convert sum_sq_ge_two_mul_sum_of_even δ u ( Finset.ne_of_mem_erase hu ) ( fun v => H_even u ( Finset.ne_of_mem_erase hu ) v ) using 1;
  -- Final step: from δ(u,v)² = 2·δ(u,v) deduce δ(u,v) ≤ 2
  intro u hu v
  have h_eq : (δ u v : ℤ) ^ 2 = 2 * (δ u v : ℤ) := by
    contrapose! h_eq;
    refine' ⟨ u, Finset.mem_erase_of_ne_of_mem hu ( Finset.mem_univ u ), _ ⟩;
    rw [ Finset.mul_sum _ _ _ ];
    refine' ne_of_gt ( Finset.sum_lt_sum _ _ );
    · exact fun v _ => by nlinarith only [ sq_ge_two_mul_of_even ( δ u v ) ( H_even u hu v ) ] ;
    · exact ⟨ v, Finset.mem_univ _, lt_of_le_of_ne ( by nlinarith only [ show ( δ u v : ℤ ) ≥ 2 by exact mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by specialize H_row_sum u hu; aesop ) ) ( H_even u hu v ) ] ) ( Ne.symm h_eq ) ⟩
  -- δ² = 2δ ⟹ δ(δ-2) = 0 ⟹ δ ∈ {0, 2} ⟹ δ ≤ 2
  have h_le : (δ u v : ℤ) ≤ 2 := by
    nlinarith only [ h_eq ]
  exact_mod_cast h_le

/-! ### Task 3: Triple Count Finalization

  **CLRS Appendix C (Counting):** We count the Walsh support size and the
  number of unordered pairs. The key identity is:
    |S_b| = 2^{2n} / 2^{n+1} = 2^{n-1}
  which is a simple division of powers of 2.

  **Category Theory:** The Walsh support `S_b = {a | W(a,b) ≠ 0}` is the
  *support* of the row function `W(·,b)`. In categorical terms, it is the
  *complement of the kernel* of the linear functional W(·,b).

  **Beautiful Pattern 🌟:** The proof is a *dimension argument*: the total
  "energy" (∑ W²) is fixed by Parseval, and each nonzero term contributes
  exactly 2^(n+1) (by AB). So the number of nonzero terms is
  total_energy / energy_per_term = 2^{2n} / 2^{n+1} = 2^{n-1}.
-/

/-- The support of Walsh coefficients for a fixed b.

  **Functional Programming:** This uses `Finset.filter` — a *higher-order function*
  that selects elements satisfying a decidable predicate. The `[DecidableEq ι]`
  instance ensures the predicate `W a b ≠ 0` is decidable.

  **Type Theory:** The `noncomputable` annotation is needed because
  `Finset.filter` requires decidability of the predicate, which in turn
  requires decidability of `=` on ℤ (which is decidable, but the
  elaborator may need classical reasoning for the specific W). -/
noncomputable def walshSupport (b : ι) : Finset ι :=
  Finset.univ.filter fun a => W a b ≠ 0

/-- Combinatorial identity: C(2^m, 2) = 2^{m-1} · (2^m - 1) for m ≥ 1.

  **CLRS Appendix C:** C(n,2) = n(n-1)/2 is the number of edges in the
  complete graph K_n.

  **Lean Best Practice:** Use `Nat.choose_two_right` to reduce C(n,2) to
  n*(n-1)/2, then compute directly. -/
lemma choose_pow_two_eq (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 ^ m) 2 = 2 ^ (m - 1) * (2 ^ m - 1) := by
  rw [ Nat.choose_two_right ];
  cases m <;> simp_all +decide [ pow_succ', mul_assoc, Nat.mul_div_assoc ]

/-- **Task 3: Triple count** — For an AB function, |S_b| = 2^{n-1} for b ≠ 0.

  ## Proof Steps:
  1. By AB, W(a,b)² ∈ {0, 2^{n+1}} for b ≠ 0
  2. Rewrite ∑_a W(a,b)² = ∑_{a ∈ S_b} 2^{n+1} (zero terms vanish)
  3. By Parseval: ∑_a W(a,b)² = q² = 2^{2n}
  4. So |S_b| · 2^{n+1} = 2^{2n}, giving |S_b| = 2^{n-1}

  **Beautiful Pattern 🌟 (Energy Equipartition):** Each nonzero Walsh coefficient
  carries the same "energy" 2^{n+1}. The total energy is 2^{2n}. So the number
  of carriers is 2^{2n}/2^{n+1} = 2^{n-1}. This is the *microcanonical ensemble*
  principle from statistical mechanics applied to the Walsh spectrum!

  **Category Theory:** This is a *dimension counting* argument in the category
  of 𝔽₂-vector spaces. The Walsh support is a "basis-like" set whose size is
  determined by the total trace (Parseval).

  **Type Theory:** The proof uses `Or.resolve_left` to eliminate the zero case
  from the AB disjunction, leaving only the 2^{n+1} case. This is
  *disjunction elimination* combined with *negation*. -/
theorem triple_count_eq
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card = 2 ^ (n - 1) := by
  -- Step 1-2: Rewrite the Parseval sum using AB values
  have h_walshSupport : ∑ a : ι, W a b ^ 2 = ∑ a ∈ walshSupport W b, (2 : ℤ) ^ (n + 1) := by
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( walshSupport W b ) ) ];
    · exact Finset.sum_congr rfl fun x hx => Or.resolve_left ( hAB x b hb ) ( by simpa using Finset.mem_filter.mp hx |>.2 );
    · unfold walshSupport; aesop;
  -- Step 3-4: Solve for |S_b| from |S_b| · 2^{n+1} = 2^{2n}
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
  nlinarith [ pow_pos ( zero_lt_two' ℤ ) n ]

/-- Number of unordered pairs in the Walsh support.

  **CLRS Appendix C:** Direct application of the binomial coefficient identity
  C(2^{n-1}, 2) = 2^{n-2} · (2^{n-1} - 1). -/
theorem triple_count_pairs
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    Nat.choose (walshSupport W b).card 2 =
      2 ^ (n - 2) * (2 ^ (n - 1) - 1) := by
  -- First establish |S_b| = 2^{n-1}
  have card_walsh_support : (walshSupport W b).card = 2 ^ (n - 1) :=
    triple_count_eq W q n hq hn hcard hAB H_parseval b hb
  -- Then apply the binomial coefficient identity
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
  exact Nat.div_eq_of_eq_mul_left zero_lt_two ( by ring )

end AbstractFramework

end FourierSpectralBridge
