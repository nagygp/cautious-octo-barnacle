/-
  Kasami_Final_Theorem.lean

  High-level summary and bridge theorem connecting the three component files:
  1. Normalization.lean — kernel isomorphism and root bound for the normalized operator
  2. Factorization.lean — factorization of the linearized polynomial and root count
  3. Counting.lean — Walsh support size and combinatorial pair counting

  This file:
  - Restates key results from the component files in a unified setting.
  - Proves auxiliary arithmetic identities connecting 2^(n-1) to 2^(2n-3).
  - States the combined Kasami bridge theorem: AB ⟹ APN + support size + pair count.

  Reference: Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions",
             Theorem 3; Budaghyan, "Construction and Analysis of Cryptographic Functions",
             Theorem 2.3.
-/

import Theorem3.Normalization
import Theorem3.Factorization
import Theorem23.Counting

open Finset BigOperators FourierSpectralBridge

set_option maxHeartbeats 400000

namespace KasamiFinal

/-! ## Step 1: Define the Differential Set Δ and restate its cardinality.

  The "differential set" Δ is the Walsh support `walshSupport W b` for a fixed
  nonzero `b`.  From `Counting.lean`, we know `|Δ| = 2^(n-1)`.
-/

section BridgeTheorems

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ) (δ : ι → ι → ℕ) (q n : ℕ)

omit [DecidableEq ι] in
/-- **Step 1 (Delta cardinality).**
    The Walsh support `S_b = {a | W(a,b) ≠ 0}` has exactly `2^(n-1)` elements
    for any nonzero `b`, when the function is Almost Bent.
    This is a direct application of `triple_count_eq` from `Counting.lean`. -/
lemma delta_card_fixed
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card = 2 ^ (n - 1) :=
  triple_count_eq W q n hq hn hcard hAB H_parseval b hb

omit [DecidableEq ι] in
/-- **Step 2 (Pair relation).**
    The number of unordered pairs in the Walsh support equals
    `2^(n-2) · (2^(n-1) - 1)`.
    This is a direct application of `triple_count_pairs` from `Counting.lean`. -/
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

  These connect the cardinality `2^(n-1)` to the final constant `2^(2n-3)`.
-/

/-
Arithmetic: `(2^(n-1))^2 = 2^(2n - 2)` for `n ≥ 1`.
-/
lemma pow_sq_identity (n : ℕ) (_hn : 1 ≤ n) :
    (2 ^ (n - 1)) ^ 2 = 2 ^ (2 * n - 2) := by
  rw [← pow_mul', Nat.mul_sub_left_distrib, mul_one]

/-
Arithmetic: `2^(n-2) * (2^(n-1) - 1) = 2^(2n-3) - 2^(n-2)` for `n ≥ 2`.
-/
lemma pairs_to_final_const (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 2) * (2 ^ (n - 1) - 1) = 2 ^ (2 * n - 3) - 2 ^ (n - 2) := by
  rw [ Nat.mul_sub_left_distrib, mul_one ];
  rw [ ← pow_add, show 2 * n - 3 = n - 2 + ( n - 1 ) by omega ]

/-
Arithmetic: `(2^(n-1))^2 / 2 = 2^(2n - 3)` for `n ≥ 2`,
    using natural number division.
    (Note: requires `n ≥ 2`; for `n = 1` Nat subtraction gives `2^0 = 1` on the RHS
    but `1/2 = 0` on the LHS.)
-/
lemma half_sq_pow (n : ℕ) (hn : 2 ≤ n) :
    (2 ^ (n - 1)) ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mul_succ, pow_succ' ];
  norm_num [ mul_assoc, pow_mul' ];
  ring

/-! ## Step 3: Final Combined "Kasami Bridge" Theorem

  Combining all three tasks:
  - Task 1 (Walsh-Differential Identity) → `h_diff_via_walsh`
  - Task 2 (AB ⟹ APN) → `AB_implies_APN`
  - Task 3 (Triple Count) → `triple_count_eq`, `triple_count_pairs`
  with the root bound from Normalization/Factorization.
-/

section FinalTheorem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
variable (W : ι → ι → ℤ) (δ : ι → ι → ℕ) (q n : ℕ)

/-
**Kasami Bridge Theorem.**

    For an AB function over `GF(2^n)`:
    1. The function is APN (differential uniformity ≤ 2).
    2. Each Walsh support `S_b` (for `b ≠ 0`) has exactly `2^(n-1)` elements.
    3. The number of unordered pairs in `S_b` equals `2^(n-2) · (2^(n-1) - 1)`.

    This combines `AB_implies_APN` (Task 2) with `triple_count_eq` and
    `triple_count_pairs` (Task 3), building on the Walsh-Differential Identity
    (Task 1) and the root bound from the Normalization/Factorization pipeline.
-/
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
  refine' ⟨ _, _, _ ⟩;
  · exact AB_implies_APN W δ q n hq hn hcard hAB H_parseval H_triv_a0 H_triv_ane0 H_fourth_moment H_row_sum H_triv_row0 H_triv_rowne H_even;
  · exact fun b a => delta_card_fixed W q n hq hn hcard hAB H_parseval b a
  · exact fun b a => delta_pair_count W q n hq hn hcard hAB H_parseval b a

omit [DecidableEq ι] in
/-- **Corollary: Half the square of the support size equals `2^(2n-3)`.**

    This is the "final constant" from the Kasami analysis.
    Logic: |S_b|² / 2 = (2^(n-1))² / 2 = 2^(2n-2) / 2 = 2^(2n-3). -/
theorem delta_triple_count_final
    (hq : q = 2 ^ n) (hn : 2 ≤ n)
    (hcard : Fintype.card ι = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2)
    (b : ι) (hb : b ≠ 0) :
    (walshSupport W b).card ^ 2 / 2 = 2 ^ (2 * n - 3) := by
  rw [triple_count_eq W q n hq (by omega) hcard hAB H_parseval b hb]
  exact half_sq_pow n hn

end FinalTheorem

end KasamiFinal