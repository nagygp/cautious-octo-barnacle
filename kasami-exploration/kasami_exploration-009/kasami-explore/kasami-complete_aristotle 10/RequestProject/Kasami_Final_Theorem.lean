/-
  Kasami_Final_Theorem.lean

  ══════════════════════════════════════════════════════════════════════
  HIGH-LEVEL BRIDGE THEOREM connecting the three component files:
  1. Normalization.lean — kernel isomorphism and root bound
  2. Factorization.lean — polynomial factorization and root count
  3. Counting.lean — Walsh support size and combinatorial pair counting
  ══════════════════════════════════════════════════════════════════════

  ## Algorithmic Pattern (CLRS Ch. 15 — Dynamic Programming)

  This file is the *final assembly* step in a dynamic programming pipeline:
  each sub-file solves an independent subproblem, and this file combines
  them into the overall solution. The "optimal substructure" is:
    - Normalization: reduce kernel problem to normalized form
    - Factorization: bound roots via polynomial degree
    - Counting: compute Walsh support size via Parseval
    - Bridge: combine all three into the Kasami theorem

  ## Category Theory Pattern

  This file constructs a *product morphism* (conjunction) from three
  component morphisms:
    kasami_bridge = ⟨AB_implies_APN, triple_count_eq, triple_count_pairs⟩
  In categorical terms, this is the universal arrow into the product
    IsAPN × (|S_b| = 2^{n-1}) × (C(|S_b|, 2) = ...)
  given by the three projections.

  ## Opetope Pattern

  The proof structure is a 3-dimensional opetope:
  - Source: three 2-cells (the three component proofs)
  - Target: one 2-cell (the combined statement)
  - 3-cell: the conjunction `⟨_, _, _⟩`

  ## Reference
  Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions",
  Theorem 3; Budaghyan, "Construction and Analysis of Cryptographic Functions",
  Theorem 2.3.
-/

import RequestProject.Theorem3.Normalization
import RequestProject.Theorem3.Factorization
import RequestProject.Theorem23.Counting

open Finset BigOperators FourierSpectralBridge

set_option maxHeartbeats 400000

namespace KasamiFinal

/-! ## Step 1: Define the Differential Set Δ and restate its cardinality.

  **Design Pattern (Facade / API Layer):** This file acts as a *facade*
  (GoF pattern) — it presents a clean, unified API to the client while
  hiding the complexity of the three sub-modules.

  **Functional Programming:** The `delta_card_fixed` and `delta_pair_count`
  lemmas are *thin wrappers* — they add no logic, just re-export the
  sub-module results with a consistent interface. This is the *adapter*
  pattern in FP.
-/

section BridgeTheorems

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ) (δ : ι → ι → ℕ) (q n : ℕ)

/-- **Step 1 (Delta cardinality).**
    The Walsh support `S_b = {a | W(a,b) ≠ 0}` has exactly `2^(n-1)` elements
    for any nonzero `b`, when the function is Almost Bent.

  **Lean Best Practice:** This is a *direct delegation* — the proof is just
  `triple_count_eq` applied with the right arguments. Using `:=` (term-mode)
  instead of `by exact ...` makes this transparent.

  **Type Theory:** This is *function application* in the Curry-Howard
  correspondence — applying the triple_count_eq "program" to its inputs. -/
lemma delta_card_fixed
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card = 2 ^ (n - 1) :=
  triple_count_eq W q n hq hn hcard hAB H_parseval b hb

/-- **Step 2 (Pair relation).**
    The number of unordered pairs in the Walsh support equals
    `2^(n-2) · (2^(n-1) - 1)`.

  **CLRS Appendix C:** This is the final *counting* result — C(|S_b|, 2)
  expressed in closed form. -/
lemma delta_pair_count
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    Nat.choose (walshSupport W b).card 2 =
      2 ^ (n - 2) * (2 ^ (n - 1) - 1) :=
  triple_count_pairs W q n hq hn hcard hAB H_parseval b hb

end BridgeTheorems

/-! ## Step 2: Arithmetic Bridge Lemmas

  **Design Decision:** These lemmas are *pure arithmetic* — they involve
  only natural number exponentiation and have no dependence on the APN/AB
  theory. Separating them makes the proof modular and testable.

  **Refactoring Suggestion:** Move these to a dedicated `Arithmetic.lean`
  utility file (see ANALYSIS.md §10.3).

  **CLRS Ch. 4 (Master Theorem):** The arithmetic identities relate different
  "levels" of the power-of-2 hierarchy, analogous to the Master Theorem
  relating T(n) to T(n/2).
-/

/-- Arithmetic: `(2^(n-1))^2 = 2^(2n - 2)` for `n ≥ 1`.

  ## Proof Steps:
  1. Rewrite (2^(n-1))² as 2^(2(n-1)) using `pow_mul'`
  2. Simplify 2(n-1) = 2n-2 using `Nat.mul_sub_left_distrib`

  **Beautiful Pattern 🌟:** The identity (a^m)^n = a^(mn) is the
  *exponential law* for the natural numbers monoid action on itself.
  In category theory, this is the *tensor-hom adjunction* for ℕ-sets. -/
lemma pow_sq_identity (n : ℕ) (_hn : 1 ≤ n) :
    (2 ^ (n - 1)) ^ 2 = 2 ^ (2 * n - 2) := by
  rw [← pow_mul', Nat.mul_sub_left_distrib, mul_one]

/-- Arithmetic: `2^(n-2) * (2^(n-1) - 1) = 2^(2n-3) - 2^(n-2)` for `n ≥ 2`.

  ## Proof Steps:
  1. Distribute: 2^(n-2) * (2^(n-1) - 1) = 2^(n-2) * 2^(n-1) - 2^(n-2)
  2. Combine exponents: 2^(n-2) * 2^(n-1) = 2^(2n-3)
  3. Verify the exponent: (n-2) + (n-1) = 2n-3

  **Lean Best Practice:** The proof uses `Nat.mul_sub_left_distrib` for
  distributing multiplication over natural number subtraction (which requires
  the subtrahend to be ≤ the minuend). -/
lemma pairs_to_final_const (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 2) * (2 ^ (n - 1) - 1) = 2 ^ (2 * n - 3) - 2 ^ (n - 2) := by
  rw [ Nat.mul_sub_left_distrib, mul_one ];
  rw [ ← pow_add, show 2 * n - 3 = n - 2 + ( n - 1 ) by omega ]

/-- Arithmetic: `(2^(n-1))^2 / 2 = 2^(2n - 3)` for `n ≥ 2`.

  ## Proof Steps:
  1. Case split on n: n=0, n=1 are excluded by hypothesis
  2. For n = k+2: compute (2^(k+1))² / 2 = 2^(2k+2) / 2 = 2^(2k+1)
  3. Verify 2(k+2) - 3 = 2k+1

  **Lean Best Practice:** The `rcases n with (_ | _ | n)` pattern handles
  three cases: n=0, n=1, n≥2. The first two are dispatched by `simp_all +arith`.
  This is more robust than `omega` for goals mixing exponentiation and
  natural number arithmetic. -/
lemma half_sq_pow (n : ℕ) (hn : 2 ≤ n) :
    (2 ^ (n - 1)) ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mul_succ, pow_succ' ];
  norm_num [ mul_assoc, pow_mul' ];
  ring

/-! ## Step 3: Final Combined "Kasami Bridge" Theorem

  ══════════════════════════════════════════════════════════════════════
  THE GRAND FINALE: Combining all three tasks into a single theorem.
  ══════════════════════════════════════════════════════════════════════

  **Category Theory (Universal Arrow):** The bridge theorem is the
  *universal arrow* from the AB hypothesis to the product of conclusions.
  It is universal because it provides ALL consequences simultaneously.

  **Opetope:** The proof is a 3-opetope whose boundary consists of:
  - Three source 2-cells: AB_implies_APN, triple_count_eq, triple_count_pairs
  - One target 2-cell: the conjunction
  - The 3-cell interior: `refine' ⟨_, _, _⟩`

  **CLRS Ch. 15 (Dynamic Programming — Final Assembly):**
  Like the final step of a DP algorithm, we combine pre-computed sub-results:
  - Table entry 1: APN status (from AB_implies_APN)
  - Table entry 2: Support size (from triple_count_eq)
  - Table entry 3: Pair count (from triple_count_pairs)
  The "lookup" is just function application — no re-computation needed.
-/

section FinalTheorem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ) (δ : ι → ι → ℕ) (q n : ℕ)

/-- **Kasami Bridge Theorem.** 🌟🌟🌟

    For an AB function over `GF(2^n)`:
    1. The function is APN (differential uniformity ≤ 2).
    2. Each Walsh support `S_b` (for `b ≠ 0`) has exactly `2^(n-1)` elements.
    3. The number of unordered pairs in `S_b` equals `2^(n-2) · (2^(n-1) - 1)`.

  ## Proof Structure:
  The proof is a *triple introduction* `⟨_, _, _⟩`:
  - Component 1: `AB_implies_APN` (the spectral-to-combinatorial implication)
  - Component 2: `delta_card_fixed` (Walsh support cardinality)
  - Component 3: `delta_pair_count` (pair counting)

  **Type Theory:** The goal type is a *product type* (conjunction):
    `IsAPN_abs δ ∧ (∀ b, ...) ∧ (∀ b, ...)`
  The proof constructs a *triple* — a term of type A × B × C.
  In the Curry-Howard correspondence, this is *pair introduction*.

  **Category Theory:** This is the *diagonal morphism* into a product:
    Δ : H → A × B × C
  where H is the AB hypothesis and A, B, C are the three conclusions.

  **HoTT:** The conjunction is a *product type* in HoTT. The proof
  is a *section* of the projection fibration. -/
theorem kasami_bridge
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (H_triv_a0 : W (0 : ι) (0 : ι) = (q : ℤ))
    (H_triv_ane0 : ∀ a : ι, a ≠ 0 → W a (0 : ι) = 0)
    (H_fourth_moment : ∑ a : ι, ∑ b : ι, W a b ^ 4 =
      (q : ℤ) ^ 2 * ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2)
    (H_row_sum : ∀ u : ι, u ≠ 0 → ∑ v : ι, (δ u v : ℤ) = (q : ℤ))
    (H_triv_row0 : δ (0 : ι) (0 : ι) = q)
    (H_triv_rowne : ∀ v : ι, v ≠ 0 → δ (0 : ι) v = 0)
    (H_even : ∀ u : ι, u ≠ 0 → ∀ v : ι, 2 ∣ δ u v) :
    -- Conclusion: APN + support size + pair count
    IsAPN_abs δ ∧
    (∀ b : ι, b ≠ 0 → (walshSupport W b).card = 2 ^ (n - 1)) ∧
    (∀ b : ι, b ≠ 0 →
      Nat.choose (walshSupport W b).card 2 = 2 ^ (n - 2) * (2 ^ (n - 1) - 1)) := by
  -- Construct the triple: each component is an independent sub-proof
  refine' ⟨ _, _, _ ⟩;
  · -- Component 1: AB → APN (the hard part, proved in Counting.lean)
    exact AB_implies_APN W δ q n hq hn hcard hAB H_parseval H_triv_a0 H_triv_ane0 H_fourth_moment H_row_sum H_triv_row0 H_triv_rowne H_even;
  · -- Component 2: Walsh support cardinality
    exact fun b a => delta_card_fixed W q n hq hn hcard hAB H_parseval b a
  · -- Component 3: Pair count
    exact fun b a => delta_pair_count W q n hq hn hcard hAB H_parseval b a

/-- **Corollary: Half the square of the support size equals `2^(2n-3)`.**

  This is the "final constant" from the Kasami analysis.
  Logic: |S_b|² / 2 = (2^(n-1))² / 2 = 2^(2n-2) / 2 = 2^(2n-3).

  **Beautiful Pattern 🌟:** This corollary connects the *combinatorial*
  quantity (support size) to the *arithmetic* quantity (power of 2) via
  a chain of two rewriting steps. The entire Kasami theory boils down to
  this one elegant identity.

  **CLRS Connection:** This is the *output* of the algorithm — the final
  computed value, obtained by composing all sub-computations. -/
theorem delta_triple_count_final
    (hq : q = 2 ^ n) (hn : 2 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  -- Step 1: Replace |S_b| with 2^{n-1} using the triple count
  rw [triple_count_eq W q n hq (by omega) hcard hAB H_parseval b hb]
  -- Step 2: Apply the arithmetic identity (2^{n-1})² / 2 = 2^{2n-3}
  exact half_sq_pow n hn

end FinalTheorem

end KasamiFinal
