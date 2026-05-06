# Summary of changes for run 3ab8793f-8e71-4b8e-a4dc-f448a11faad4
## Analysis of the Kasami / AB-implies-APN Formalization

I've written a comprehensive analysis in `ANALYSIS.md` covering all three of your questions. Here's a summary:

### 1. History and Significance

This formalization concerns the classical theorem that **Almost Bent (AB) functions are Almost Perfect Nonlinear (APN)** over finite fields of characteristic 2 — a foundational result in symmetric cryptography. The theorem connects optimal resistance to linear cryptanalysis (AB) with optimal resistance to differential cryptanalysis (APN). It was originally established by Chabaud–Vaudenay (1994) and Carlet–Charpin–Zinoviev (1998), and appears as Theorem 2.3 in Budaghyan's monograph. The "Kasami" connection refers to the Kasami power functions, one of the known infinite families of APN/AB functions. The Gold function analysis (in `Normalization.lean` and `Factorization.lean`) follows Bracken–Byrne–Markin–McGuire's treatment.

### 2. What the Formalization Proves

The formalization **fully proves** (no `sorry` statements remain, all axioms are standard):
- **AB ⟹ APN** via fourth-moment analysis of Walsh coefficients
- **Walsh support cardinality** = 2^(n-1) for AB functions
- **Pair counting** in Walsh supports
- **Kernel isomorphism** for Gold function derivatives
- **Polynomial root bounds** for the normalized operator
- A combined **Kasami bridge theorem** packaging everything together

The proof architecture uses an abstract combinatorial framework (Walsh coefficients as ℤ, differential counts as ℕ) with Fourier-analytic identities as hypotheses — a pragmatic choice that avoids formalizing full character theory.

### 3. Refactoring Recommendations (detailed in `ANALYSIS.md`)

Key suggestions include:
- **Extract arithmetic lemmas** into a separate file for modularity
- **Unify or bridge** the concrete and abstract APN/AB definitions (concrete ones are defined but unused)
- **Rename directories** from opaque `Theorem3/`, `Theorem23/` to meaningful names like `Gold/`, `WalshSpectral/`
- **Address `h_diff_via_walsh`** which trivially returns its hypothesis
- **Close the formalization gap** by connecting the Gold function analysis to the APN/AB theorems

### Changes Made

I also made minor cleanups to the codebase:
- Fixed linter warnings in `Normalization.lean` (unused simp args, unused section variable)
- Replaced `exact?` calls in `Counting.lean` with their actual proof terms (`sum_sq_delta_trivial_row` and `triple_count_eq`)
- Verified the entire project builds cleanly with no `sorry` statements

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