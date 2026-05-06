# Summary of changes for run f77acb70-f473-404b-a8a6-0546fe6d5e49
I've created a detailed guide at `MATHLIB_CONTRIBUTION_GUIDE.md` analyzing your project for Mathlib contribution potential. Here's the summary:

## Best First Contributions (Tier 1 — Easy, High Acceptance Rate)

1. **`choose_pow_two_eq`** — The identity `C(2^m, 2) = 2^(m-1) · (2^m - 1)`. This is the ideal first PR: self-contained, pure Nat arithmetic, no domain knowledge needed by reviewers, and it fills a gap in `Mathlib.Data.Nat.Choose`. It may even generalize to remove the `1 ≤ m` hypothesis.

2. **`sq_ge_two_mul_of_even` / `le_two_of_sq_le_two_mul`** — Simple arithmetic lemmas useful beyond cryptography.

## Strong Contributions (Tier 2 — Medium, Opens New Area)

3. **APN/AB definitions + `AB_implies_APN`** — Mathlib currently has *zero* coverage of cryptographic function theory. Contributing `diffCount`, `IsAPN`, `WalshCoeff`, `IsAB` definitions would open an entirely new area. The `AB ⟹ APN` theorem is a classical result (Chabaud–Vaudenay 1995). This requires refactoring: the current abstract framework (`IsAB_abs` with 12 hypotheses) should be replaced with concrete definitions using Mathlib's `AddChar`.

4. **Gold function normalization** and **Frobenius factorization** — clean algebraic results, but should use Mathlib's existing `frobenius` and `iterate_frobenius` instead of redefining them.

## Four Approaches to Contributing

- **Approach A (Bottom-Up, Recommended):** Start with Tier 1 arithmetic lemmas to learn the PR workflow, then build up.
- **Approach B (Definition-First):** Propose API definitions on Zulip first, get community buy-in, then add theorems.
- **Approach C (Theory Module):** Propose a whole `Mathlib.Combinatorics.APN` directory — ambitious but coherent.
- **Approach D (Gap-Filling Only):** Contribute only lemmas that fit into existing Mathlib files (lowest risk).

## Key Refactoring Needed

- Remove local `CharTwo.neg_eq` and `CharTwo.sub_eq_add` — these already exist in Mathlib.
- Eliminate `set_option maxHeartbeats` (Mathlib enforces 200000).
- Replace `grind` with stable tactics.
- Add proper copyright headers, module docstrings, and follow Mathlib naming conventions.
- Post on the Leanprover Zulip `#mathlib4` channel before larger PRs.

See `MATHLIB_CONTRIBUTION_GUIDE.md` for the full analysis with a summary table, style guidelines, and practical steps.

# Summary of changes for run 552b38c5-6f86-4e69-9c25-82e26dac4ea0
Successfully implemented `RequestProject/Kasami_Final_Theorem.lean` — the high-level summary/bridge file connecting the three component files (Normalization, Factorization, Counting).

**What was created:**

The file contains the following fully-proved declarations (zero `sorry` statements):

1. **`delta_card_fixed`** — Restates the Walsh support cardinality `|S_b| = 2^(n-1)` by directly applying `triple_count_eq` from `Counting.lean`.

2. **`delta_pair_count`** — Restates the unordered pair count `C(|S_b|, 2) = 2^(n-2) · (2^(n-1) - 1)` by applying `triple_count_pairs` from `Counting.lean`.

3. **`pow_sq_identity`** — Arithmetic bridge: `(2^(n-1))² = 2^(2n-2)`.

4. **`pairs_to_final_const`** — Arithmetic bridge: `2^(n-2) · (2^(n-1) - 1) = 2^(2n-3) - 2^(n-2)` for `n ≥ 2`.

5. **`half_sq_pow`** — Arithmetic bridge: `(2^(n-1))² / 2 = 2^(2n-3)` for `n ≥ 2`.

6. **`kasami_bridge`** — The main combined theorem: for an AB function, (a) the function is APN, (b) each Walsh support has `2^(n-1)` elements, and (c) the pair count equals `2^(n-2) · (2^(n-1) - 1)`. This combines `AB_implies_APN` (Task 2) with `triple_count_eq` and `triple_count_pairs` (Task 3).

7. **`delta_triple_count_final`** — Corollary reaching the final constant `2^(2n-3)`: `|S_b|² / 2 = 2^(2n-3)`.

**Note on the `n ≥ 2` requirement:** The original template used `n ≥ 1` for `half_sq_pow` and `delta_triple_count_final`, but this is false for `n = 1` due to natural number division truncation (`1/2 = 0 ≠ 1`). The hypothesis was corrected to `n ≥ 2`, which is consistent with the Kasami context (where `n` is odd and `n ≥ 3`).

All proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The file builds cleanly with no warnings.

# Summary of changes for run b51c62af-7880-4f47-8d22-0bfd7420b1a5
All three sorry'd theorems in `RequestProject/Theorem23/Counting.lean` have been successfully proved:

1. **`AB_implies_APN`** (Task 2): Proved that Almost Bent implies Almost Perfect Nonlinear. The proof computes the fourth moment of Walsh coefficients two ways — via the AB property and via the fourth moment identity — showing equality forces each differential count δ(u,v) to satisfy δ² = 2δ, hence δ ≤ 2.

2. **`triple_count_eq`** (Task 3): Proved that for an AB function, the Walsh support `|{a | W(a,b) ≠ 0}|` equals `2^(n-1)` for each nonzero `b`. The proof uses Parseval's identity with the AB dichotomy to get `card * 2^(n+1) = 2^(2n)`.

3. **`triple_count_pairs`**: Proved the combinatorial corollary that the number of unordered pairs in the Walsh support is `2^(n-2) * (2^(n-1) - 1)`, by combining `triple_count_eq` with `choose_pow_two_eq`.

The file builds cleanly with no `sorry` statements remaining, and all proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).