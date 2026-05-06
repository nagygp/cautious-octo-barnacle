# Analysis of the Kasami / AB-implies-APN Formalization

## 1. History and Significance of the Conjecture

### Background

This formalization concerns the relationship between two fundamental cryptographic properties of functions over finite fields of characteristic 2 (i.e., **GF(2ⁿ)**):

- **APN (Almost Perfect Nonlinear):** A function `f : GF(2ⁿ) → GF(2ⁿ)` is APN if for every nonzero `u` and every `v`, the differential equation `f(x + u) + f(x) = v` has at most 2 solutions. APN functions provide optimal resistance against *differential cryptanalysis*, one of the most powerful attacks on block ciphers.

- **AB (Almost Bent):** A function is AB if its Walsh spectrum takes only the values `{0, ±2^((n+1)/2)}`. AB functions provide optimal resistance against *linear cryptanalysis*. AB functions can only exist when `n` is odd.

### The Core Result: AB ⟹ APN

The theorem that **every AB function is APN** is a classical result in Boolean function theory, originally due to **Chabaud and Vaudenay (1994)** and later exposited by **Carlet, Charpin, and Zinoviev (1998)**. It appears as Theorem 2.3 in **Lilya Budaghyan's monograph** *"Construction and Analysis of Cryptographic Functions"* (Springer, 2014).

The significance is profound: it says that optimal resistance to linear cryptanalysis *automatically implies* optimal resistance to differential cryptanalysis — a deep connection between two seemingly different security notions.

### The Kasami Connection

The project title references **Kasami power functions**, which are functions of the form `f(x) = x^d` where `d = 2^(2k) - 2^k + 1` over GF(2ⁿ) with `gcd(k, n) = 1`. These are one of the known infinite families of APN functions, proved by **Kasami (1971)** in the context of error-correcting codes, and later shown to be AB (when `n` is odd) by **Canteaut, Charpin, and Dobbertin (2000)**.

The **Gold functions** `f(x) = x^(2^k+1)` (formalized in `Normalization.lean` and `Factorization.lean`) are the simplest family of APN/AB functions, studied by **Gold (1968)** and **Nyberg (1993)**. The formalization of the derivative analysis for Gold functions (normalization to `y^(2^k) + y + 1 = 0`, polynomial root bounds) follows the treatment in **Bracken, Byrne, Markin, and McGuire** *"Fourier Spectra of Binomial APN Functions"*.

### Historical Significance

The AB-implies-APN theorem is not a conjecture — it is a well-established theorem. However, to our knowledge, **this is one of the first (if not the first) machine-verified formalizations** of this result and the surrounding Walsh-spectral theory in a proof assistant. This is significant because:

1. The proof involves delicate interplay between Fourier analysis, combinatorics, and number theory.
2. Formal verification eliminates any possibility of subtle errors in the intricate bookkeeping of exponents and summation bounds.
3. It establishes foundational infrastructure for formalizing more advanced results in cryptographic function theory.

---

## 2. What the Formalization Proves and How

### Structure

The project is organized into four files:

| File | Content |
|------|---------|
| `Theorem3/Normalization.lean` | Kernel isomorphism for Gold function derivatives: `Δ_u f(x) = 0 ⟺ y^(2^k) + y + 1 = 0` |
| `Theorem3/Factorization.lean` | Factorization of linearized polynomials, root count bounds via polynomial degree |
| `Theorem23/Counting.lean` | **Main results**: Walsh-Differential Identity, AB⟹APN, Walsh support cardinality |
| `Kasami_Final_Theorem.lean` | Bridge theorem combining all components, arithmetic corollaries |

### Key Theorems Proved

1. **`h_diff_via_walsh`** (Task 1 — Walsh-Differential Identity): The fourth moment of the Walsh spectrum equals `q²` times the sum of squared differential counts. This is stated axiomatically (the character-theoretic derivation is taken as a hypothesis `H_core`).

2. **`AB_implies_APN`** (Task 2): The central theorem. The proof works by:
   - Computing ∑W⁴ two ways: via AB (each W⁴ = W² · 2^(n+1)) and via the fourth moment identity.
   - Showing equality forces ∑δ² = 2∑δ for each nonzero row.
   - Using the char-2 pairing argument (δ values are even, so δ² ≥ 2δ pointwise).
   - Equality pointwise forces δ² = 2δ, hence δ ∈ {0, 2}, giving APN.

3. **`triple_count_eq`** (Task 3): For AB functions, the Walsh support `|{a : W(a,b) ≠ 0}|` = 2^(n-1) for each nonzero `b`, via Parseval + AB dichotomy.

4. **`kernel_iso_normalized`**: The normalization lemma for Gold functions — the derivative kernel is equivalent to roots of `y^(2^k) + y + 1`.

5. **`card_roots_shifted_le`**: Root count bound via polynomial degree.

6. **`kasami_bridge`**: The combined theorem packaging APN + support size + pair count.

### Proof Architecture

The formalization uses an **abstract combinatorial framework**: rather than working directly with finite field characters and the Walsh transform, it abstracts to:
- `W : ι → ι → ℤ` (Walsh coefficients as integers)
- `δ : ι → ι → ℕ` (differential counts)
- Fourier-analytic identities (Parseval, fourth moment) as **hypotheses**

This is a pragmatic design choice — formalizing the full character theory would require substantially more Mathlib infrastructure. The core mathematical content (the combinatorial/algebraic argument that AB forces APN) is fully verified.

---

## 3. Refactoring Recommendations

### 3.1 Linter Warnings (Easy Fixes)

**`Normalization.lean:89`** — Remove unused `simp` arguments `mul_pow`, `mul_assoc`, `mul_left_comm`:
```lean
simp_all +decide [mul_comm]
```

**`Normalization.lean:122`** — Add `omit [CharP F 2]` before `card_roots_Lnorm_le` since it doesn't use the `CharP` instance.

### 3.2 Structural Improvements

1. **Extract arithmetic lemmas into a separate file** (`Arithmetic.lean` or `PowerArith.lean`). The lemmas `pow_sq_identity`, `pairs_to_final_const`, `half_sq_pow`, `sq_ge_two_mul_of_even`, `le_two_of_sq_le_two_mul`, and `choose_pow_two_eq` are pure number theory and don't depend on Walsh/APN definitions. Separating them improves modularity and reusability.

2. **Unify the two "APN/AB" definition layers.** Currently there are:
   - Concrete definitions over fields (`IsAPN`, `IsAB` in `Counting.lean`)
   - Abstract definitions over index types (`IsAPN_abs`, `IsAB_abs` in `Counting.lean`)

   The concrete definitions are never used in any theorem. Either:
   - Remove them (if the goal is purely abstract), or
   - Add a **bridge lemma** connecting them (e.g., showing that the concrete `IsAB` implies `IsAB_abs` for the appropriate Walsh coefficient function), which would close the formalization gap.

3. **`h_diff_via_walsh` is trivial.** The theorem just returns its hypothesis `H_core`. Either:
   - Make it a proper theorem by actually proving the identity from more primitive hypotheses, or
   - Remove it and use `H_core` directly, or
   - At minimum, add a docstring noting it's a placeholder for future work.

4. **Reduce `maxHeartbeats`.** The file-level `set_option maxHeartbeats 800000` in `Counting.lean` is very high. Consider localizing it to specific proofs that need it (via `set_option maxHeartbeats 400000 in theorem ...`), as a global high limit can mask performance problems.

### 3.3 Style and Naming

1. **Namespace consistency.** `Theorem3/` and `Theorem23/` are opaque directory names. Consider renaming to `Gold/` (for Normalization + Factorization) and `WalshSpectral/` (for Counting), or similar mathematically meaningful names.

2. **Remove trailing semicolons.** Many tactic proofs end lines with `;` (e.g., `ring;`, `grind`). While valid Lean, this is non-idiomatic and can cause confusion with the tactic combinator `;` (which applies the next tactic to all remaining goals). Replace with newlines.

3. **Replace `exact?` calls.** In `triple_count_pairs`, the proof contains `exact?;` — this should be replaced with the actual term it found (likely `triple_count_eq W q n hq hn hcard hAB H_parseval b hb`).

4. **Use `Nat.choose_two_right` directly.** The `choose_pow_two_eq` lemma manually unfolds `Nat.choose _ 2`; consider whether the existing Mathlib API makes this cleaner.

### 3.4 Mathematical Completeness

The formalization has two significant **gaps** between the abstract framework and the concrete mathematics:

1. **No concrete instantiation.** The abstract framework takes Walsh coefficients and differential counts as parameters with Fourier identities as hypotheses. There is no proof that *actual* Walsh transforms over GF(2ⁿ) satisfy these hypotheses (Parseval, fourth moment identity, row sums). Filling this gap would require formalizing:
   - Additive characters of GF(2ⁿ)
   - The Walsh transform as a concrete sum
   - Character orthogonality
   - Parseval's identity for this transform

2. **The Gold/Kasami connection is incomplete.** `Normalization.lean` and `Factorization.lean` analyze the derivative of Gold functions, but this analysis is never connected to the APN/AB theorems in `Counting.lean`. A natural next step would be a theorem: "The Gold function `x^(2^k+1)` over GF(2ⁿ) with `gcd(k,n) = 1` is APN."

### 3.5 Proposed Refactored File Structure

```
RequestProject/
├── Arithmetic.lean          -- Pure ℕ/ℤ arithmetic lemmas
├── Defs.lean                -- IsAPN, IsAB, walshSupport, diffCount definitions
├── Gold/
│   ├── Normalization.lean   -- Kernel isomorphism for Gold derivatives
│   └── Factorization.lean   -- Polynomial root bounds
├── WalshSpectral/
│   ├── FourthMoment.lean    -- Walsh-Differential Identity
│   ├── ABImpliesAPN.lean    -- The main theorem
│   └── SupportCount.lean    -- Triple count, pair counting
└── Bridge.lean              -- Combined Kasami bridge theorem
```

This would keep each file focused and under 300 lines, improving readability and build times.
