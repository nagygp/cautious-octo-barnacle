# Refactoring Notes — Clean Code Principles Applied

This document explains every change made during the refactoring, written for someone learning clean code practices in Lean 4.

---

## 1. Fixed All Linter Warnings at Their Root

**Principle:** *Don't suppress warnings — fix the underlying issue.*

Lean's linter catches real problems. Instead of adding `set_option linter... false`, we fixed each warning properly.

### a) Unused `simp` Arguments

**Before:**
```lean
simp_all +decide [Nat.mul_dvd_mul_iff_left]
simp +decide [← h_sum_eq, H_triv_row0, H_triv_rowne]
simp +decide [← Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_ne']
simp_all +decide [mul_pow, mul_assoc, mul_comm, mul_left_comm]
```

**After:**
```lean
simp_all +decide
simp +decide [← h_sum_eq]
simp +decide [Finset.filter_ne']
simp_all +decide
```

**Why:** Passing arguments to `simp` that it doesn't actually use is misleading — it suggests those lemmas are important to the proof when they aren't. Removing them makes the proof's actual dependencies clearer.

### b) Unused Section Variables (`omit`)

**Before:**
```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]

-- This theorem doesn't use DecidableEq, but Lean includes it anyway
theorem triple_count_eq ... := ...
```

**After:**
```lean
omit [DecidableEq ι] in
theorem triple_count_eq ... := ...
```

**Why:** When you declare `variable [DecidableEq ι]` in a section, Lean auto-includes it in every theorem — even ones that don't need it. This pollutes the theorem's type signature. `omit` tells Lean "don't include this variable here."

**Important syntax note:** `omit` must come *before* the docstring (`/-- ... -/`), not after it.

### c) Unused Hypothesis Names

**Before:**
```lean
(hu : u ≠ 0)        -- 'hu' is never referenced in the proof body
(H_triv_rowne : ...) -- unused parameter in h_diff_via_walsh
```

**After:**
```lean
(_hu : u ≠ 0)         -- underscore prefix signals "intentionally unused"
(_H_triv_rowne : ...)  -- same
```

**Why:** The underscore prefix `_` tells both the reader and the linter "I know this parameter is unused — it's here for API compatibility or documentation purposes." This is cleaner than ignoring warnings.

---

## 2. Replaced `exact?` with Actual Proof Terms

**Principle:** *Don't leave search tactics in final code.*

**Before:**
```lean
exact?  -- Lean searches for a proof at compile time
```

**After:**
```lean
exact sum_sq_delta_trivial_row δ q H_triv_row0 H_triv_rowne
exact triple_count_eq W q n hq hn hcard hAB H_parseval b hb
```

**Why:** `exact?` is a development tool — it asks Lean to search for a matching lemma. While it works, it:
- Slows compilation (search happens every build)
- Hides what the proof actually uses
- Makes the code harder to understand for readers

Always replace `exact?` with the term it found (shown in the `Try this:` output).

---

## 3. Replaced `ring` with `ring_nf` Where Needed

**Before:**
```lean
simp +decide [hcard]; ring;
```

**After:**
```lean
simp +decide [hcard]; ring_nf;
```

**Why:** `ring` tries to close a goal completely. If the goal isn't exactly a ring identity (e.g., it has remaining subgoals), `ring` fails. `ring_nf` normalizes the expression without requiring a complete proof — it's the right tool when `ring` is used as an intermediate simplification step.

---

## 4. Replaced Deprecated `refine'` with Modern `refine`

**Before (in Kasami_Final_Theorem.lean):**
```lean
refine' ⟨ _, _, _ ⟩;
```

**After:**
```lean
exact ⟨..., ..., ...⟩
```

**Why:** `refine'` is a deprecated tactic from an older Lean version. `refine` is its replacement, but in this case, the proof was simple enough to use `exact` with an anonymous constructor directly.

---

## 5. Cleaned Up `Main.lean` — Removed Unused Options

**Before (24 lines of `set_option`):**
```lean
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false
-- ... plus many open scoped declarations
```

**After (7 lines total):**
```lean
import Mathlib
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

**Why:**
- **Pretty-printing options** (`pp.*`) only affect how Lean displays terms in the Info View. They don't affect the proofs and shouldn't live in production code.
- **`grind.warning false`** suppresses useful warnings from a tactic — not recommended.
- **`open scoped` declarations** were unused since `Main.lean` has no theorems.
- The remaining options (`maxHeartbeats`, `maxRecDepth`, `autoImplicit false`) are genuinely needed for project-wide configuration.

---

## 6. Improved Documentation & Removed Redundant Comments

**Principle:** *Doc-strings should describe "what" and "why", not repeat the code.*

**Before:**
```lean
/-
The fourth moment splits into trivial (b=0) and nontrivial (b≠0) parts.
    Ref: Budaghyan Theorem 2.3, sum decomposition step.
-/
```

**After:**
```lean
/-- The fourth moment splits into trivial (b=0) and nontrivial (b≠0) parts. -/
```

**Changes:**
- Converted block comments (`/- ... -/`) to doc-strings (`/-- ... -/`) where appropriate — doc-strings show up in hover tooltips
- Removed verbose inline reference citations that repeated the module header
- Kept the header references since they apply to the whole file
- Removed the stale comment about `sorry` in Normalization.lean since it's no longer relevant

---

## 7. Preserved Semantically Important Semicolons

**Principle:** *Understand your tools before changing code.*

In Lean 4, semicolons (`;`) are **not** just stylistic — they mean "apply the next tactic to **all** remaining goals." This is critical in proofs that generate multiple subgoals:

```lean
rw [h_eq, ...]; simp +decide [hcard]; ring_nf;
rw [Nat.cast_sub] <;> push_cast <;> nlinarith [...]
```

Here, `ring_nf` applies to a subgoal generated by the preceding `rw`/`simp`, and `<;>` means "apply to all goals." Removing these semicolons would break the proof by leaving subgoals unsolved.

**Lesson:** In Lean (unlike most languages), semicolons carry semantic meaning. Don't remove them without understanding the proof structure.

---

## Summary of Changes by File

| File | Changes |
|------|---------|
| `Main.lean` | Removed 17 unused `set_option`/`open scoped` lines |
| `Counting.lean` | Fixed 8+ linter warnings, replaced `exact?`, fixed `ring` → `ring_nf`, added `omit` annotations |
| `Normalization.lean` | Added 5 `omit` annotations, removed 3 unused `simp` args, removed stale comment |
| `Factorization.lean` | Added 7 `omit` annotations, removed 2 unused `simp` args, used `induction'` consistently |
| `Kasami_Final_Theorem.lean` | Replaced `refine'` with `exact`, added 3 `omit` annotations |

**All changes preserve the mathematical content and proof correctness.** The project builds with zero warnings and zero sorries.
