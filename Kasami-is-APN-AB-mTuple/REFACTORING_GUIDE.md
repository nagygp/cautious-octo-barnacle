# Refactoring Guide — Kasami APN/AB Library

## What Was Done

### 1. New Modules Created

#### `RequestProject/CharTwoAPI.lean` — Unified Char-2 Arithmetic API
- **Problem solved**: The original library had char-2 lemmas scattered across `CharTwo.lean` (in `MTupleCount` namespace) and `CharTwoBasics.lean` (in `CollisionAnalysis` namespace), with many identical lemmas proved twice (e.g., `add_self_zero` vs `char2_add_self`, `neg_eq_self` vs `char2_neg`).
- **Solution**: A single, well-organized module with:
  - §1 Basic ring arithmetic (`add_self`, `neg_eq`, `sub_eq_add`, `shift_cancel`, `two_eq_zero`)
  - §2 Frobenius map (`frob_add`, `sq_add`, `frob_one`, `frob_mul`, `frob_comp`)
  - §3 Frobenius bijectivity (`frob_bijective`, `frob_period`)
- **Design**: Uses minimal hypotheses (`[CommSemiring R] [CharP R 2]` when possible, `[Field F]` only when needed). `@[simp]` tags on key lemmas.

#### `RequestProject/APNClass.lean` — Unified APN Theory
- **Problem solved**: Two incompatible APN definitions existed:
  - `MTupleCount.APN` (cardinality form): `|{x | D f a x = b}| ≤ 2`
  - `KasamiAPN.IsAPN` (collision form): collisions ⟹ `y ∈ {x, x+a}`
  
  The bridge `KasamiTripleCount.kasami_is_mtuple_apn` was 20+ lines converting between them.
- **Solution**: Both forms defined in one file with a proven equivalence (`apn_iff_collision`), plus all structural lemmas:
  - `deriv_shift`, `ne_shift` — char-2 derivative symmetry
  - `collision_to_card`, `card_to_collision` — bidirectional conversion
  - `apn_comp_additive_bij` — APN preserved under additive bijections
  - `apn_frob_twist` — APN preserved under Frobenius twist
  - `fiber_card_two`, `sum_fibers`, `card_times_two`, `deriv_image_half` — fiber analysis

#### `RequestProject/StressTests.lean` — Comprehensive Verification
- 15 test sections covering:
  1. **Axiom audit**: Every theorem uses only standard axioms (no `sorryAx`)
  2. **Kasami exponent**: Numerical verification of d_k values
  3. **APN non-triviality**: Zero function is not APN; identity is APN on ZMod 2
  4. **Character consistency**: Concrete Chi on ZMod 2 satisfying all axioms
  5. **m-tuple count numerics**: Formula spot-checks for multiple (n,m) pairs
  6. **Exponent arithmetic**: Cross-validation of the cancellation identity
  7. **Frobenius twist**: Congruence d_k ≡ d_{n-k}·2^{2k} (mod 2^n-1) for many parameters
  8. **Hypothesis satisfiability**: All theorem hypotheses are simultaneously satisfiable
  9. **Conclusion non-triviality**: Formula values are non-zero, non-constant
  10. **Definition transparency**: Key defs unfold to expected content
  11. **Cryptographic significance**: Walsh spectrum values, differential uniformity
  12. **Structural integrity**: Components are independently useful
  13. **APN consistency**: Two definitions are equivalent
  14. **Edge cases**: Boundary parameter values
  15. **Anti-tautology**: Each hypothesis is necessary

### 2. Linter Warnings Fixed
- All `unusedSectionVars` warnings resolved using `omit` declarations
- Hypotheses minimized (e.g., `apn_comp_additive_bij` doesn't require `Fintype` or `CharP`)

---

## How to Verify the Library Is Solid

### Quick verification (run these commands)

```bash
# 1. Full build — must succeed with zero errors
lake build

# 2. Check for sorry — must find none in actual code
grep -rn "sorry" RequestProject/*.lean | grep -v "^.*:.*--"

# 3. Axiom audit — look at #print axioms output in build log
# Should only show: propext, Classical.choice, Quot.sound
```

### What the axiom audit proves

When you see `#print axioms MTupleCount.m_tuple_count` producing:
```
'MTupleCount.m_tuple_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This means:
- **No `sorryAx`**: The entire proof tree is complete — no unproven steps
- **No custom axioms**: No `axiom` declarations smuggling in assumptions
- **Standard axioms only**: `propext` (proposition extensionality), `Classical.choice` (law of excluded middle), `Quot.sound` (quotient soundness) are the standard Lean 4 axioms

### What the stress tests prove

The `StressTests.lean` file verifies:
- **The theorems are not vacuously true** — hypotheses are satisfiable
- **The conclusions are non-trivial** — they produce specific numerical values
- **Each hypothesis is necessary** — removing any one breaks the result
- **The formulas match known cryptographic values** — alignment with the literature

---

## Cryptographic Significance of the Results

### APN (Almost Perfect Nonlinear)
- **What it means**: The Kasami function `x^d` on `GF(2^n)` has **differential uniformity 2** — the theoretical minimum for any function on `GF(2^n)` when `n ≥ 3`
- **Why it matters**: Optimal resistance to **differential cryptanalysis**, the most important attack on block ciphers
- **Formalized as**: `KasamiAPN.kasami_is_apn` and `KasamiEvenK.kasami_is_apn_general`

### AB (Almost Bent)
- **What it means**: The Walsh spectrum takes values in `{0, ±2^{(n+1)/2}}` only
- **Why it matters**: Optimal resistance to **linear cryptanalysis**, the second most important attack
- **Formalized as**: `KasamiAB.kasami_is_ab`

### m-Tuple Count
- **What it means**: For APN functions with flat derivative spectrum, the number of m-tuples satisfying a linear constraint over the derivative image is exactly `2^{(m-1)n - m}`
- **Why it matters**: Determines higher-order differential properties — relevant for **higher-order differential attacks** and **algebraic attacks**
- **Formalized as**: `MTupleCount.m_tuple_count`

### Triple Count (κ₃ = 2^{2n-3})
- **What it means**: The specialization to m=3, giving the exact intersection multiplicity of three cosets
- **Why it matters**: Used in analyzing **boomerang attacks** and **impossible differential constructions**
- **Formalized as**: `KasamiTripleCount.kasami_triple_count`

---

## How to Refactor Further

### Priority 1: Extract general theory from Kasami-specific code

**For Mathlib contribution**, separate into:

| General theory (Mathlib-ready) | Kasami-specific (external) |
|------|------|
| APN definition + `deriv_image_half` | Kasami exponent, `L`, `Cross`, `N` |
| Walsh transform + AB definition | Dempwolff-Müller (Thm 3.2, Lemma 3.1) |
| Fourier inversion (`KR2`) | `kasami_is_apn`, even-k extension |
| `FlatSpectrum → Vanish` | `kasami_is_ab` via moments |
| `exp_cancel` (pure arithmetic) | `kasami_triple_count` bridge |

The key principle: **Mathlib wants the abstract interfaces** (what is APN? what general facts hold?) while your library's value is the **concrete instantiation** (Kasami satisfies these properties).

### Priority 2: Reduce the two largest files

- **`WalshAB.lean` (596 lines)**: Split into 3 files:
  - `WalshTransform.lean`: trace, sign character, Walsh definition
  - `WalshMoments.lean`: Parseval, fourth moment, moment method
  - `WalshAB.lean`: AB definition, `ab_from_moments` theorem

- **`Thm32.lean` (475 lines)**: Split into 3 files:
  - `TruncTrace.lean`: truncated trace additivity, telescoping, kernel triviality
  - `DicksonPoly.lean`: Dickson polynomial, functional equation, injectivity
  - `Thm32.lean`: main bijectivity theorem (now ~100 lines)

### Priority 3: Consolidate duplicate definitions

The library currently has **two parallel Kasami exponent definitions**:
- `CollisionAnalysis.d` in `Defs.lean`
- `KasamiAPN.kasamiExp` in `KasamiAPN.lean`

These should be unified into a single definition imported by both proof chains.

### Priority 4: Use `CharTwoAPI` and `APNClass` downstream

Replace scattered char-2 proofs in existing files with imports from the new unified modules. This is a gradual refactor — change one file at a time, rebuild after each change.

### Priority 5: Add `@[simp]` and `@[ext]` lemmas

Key simplification lemmas (like `D f a (x+a) = D f a x`) should be tagged `@[simp]` so that `simp` can handle routine char-2 simplifications automatically.

### Priority 6: Factor long proofs into named lemmas

In files like `KasamiAPN.lean` and `Thm32.lean`, some proofs are 50+ lines with deeply nested `have` chains. Each logical step should be a named lemma:

```lean
-- Instead of a 50-line proof:
theorem big_theorem ... := by
  have step1 ... := by ...  -- 15 lines
  have step2 ... := by ...  -- 20 lines
  ...

-- Factor into:
lemma step1 ... := by ...
lemma step2 ... := by ...
theorem big_theorem ... := by
  exact step2 (step1 ...)
```

This makes each piece independently testable and reusable.
