# Mathlib Contribution Guide for This Project

## Overview

This project formalizes results from cryptographic Boolean function theory, specifically:
- **APN (Almost Perfect Nonlinear)** and **AB (Almost Bent)** functions
- The **AB ⟹ APN** theorem (Budaghyan Theorem 2.3)
- Walsh spectrum support counting (triple count)
- Gold function normalization and Frobenius factorization (Bracken–Byrne–Markin–McGuire Theorem 3)

Below is an analysis of which parts are suitable for Mathlib contribution, ranked from most to least suitable, with concrete refactoring advice.

---

## Tier 1: Excellent First Contributions (Small, Self-Contained, High Value)

### 1. **Combinatorial Identity: `choose_pow_two_eq`**

```lean
lemma choose_pow_two_eq (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 ^ m) 2 = 2 ^ (m - 1) * (2 ^ m - 1)
```

**Why this is ideal for a first PR:**
- Completely self-contained — no domain-specific definitions needed.
- Pure Nat arithmetic; fits naturally in `Mathlib.Combinatorics.Choose` or `Mathlib.Data.Nat.Choose.Basic`.
- Small enough for a single-lemma PR (Mathlib prefers small, focused PRs).
- Easy to review: the statement is obviously correct and useful.

**How to refactor:**
- Remove the `1 ≤ m` hypothesis if possible (check if it holds for `m = 0` — it does: `C(1,2) = 0 = 1 * 0`). Actually `Nat.choose 1 2 = 0` and `2^0 * (2^0 - 1) = 0 * 1 = 0`... wait, `2^(0-1) = 2^0 = 1` (Nat subtraction), so `1 * (1 - 1) = 0`. Yes, it holds for `m = 0`! You could generalize to all `m : ℕ`.
- Place in `Mathlib.Combinatorics.Choose.Basic` or `Mathlib.Data.Nat.Choose.Factorization`.
- Follow Mathlib naming: something like `Nat.choose_two_pow_two` or `Nat.choose_pow_two_right`.
- Add a docstring referencing the general identity `C(2^m, 2) = 2^(m-1)(2^m - 1)`.

### 2. **Arithmetic Lemmas: `sq_ge_two_mul_of_even` and `le_two_of_sq_le_two_mul`**

```lean
lemma sq_ge_two_mul_of_even (k : ℕ) (hk : 2 ∣ k) : k ^ 2 ≥ 2 * k
lemma le_two_of_sq_le_two_mul (k : ℕ) (hk : k ^ 2 ≤ 2 * k) : k ≤ 2
```

**Why:**
- Self-contained, pure Nat arithmetic.
- Useful in combinatorial/number-theoretic contexts beyond cryptography.
- The first one generalizes: for any `d ∣ k`, `k^2 ≥ d * k` when `k > 0`.

**How to refactor:**
- Consider stating more generally: `k * (k - 1) ≥ 0` implies `k^2 ≥ k` etc.
- The second lemma might be better stated as `k * (k - 2) ≤ 0 → k ≤ 2` or directly.
- Place in `Mathlib.Data.Nat.Basic` or `Mathlib.Algebra.Order.Ring`.
- These are small enough that they might be accepted as additions to existing files.

---

## Tier 2: Good Contributions (Medium Size, Some Domain Knowledge Needed)

### 3. **APN and AB Definitions + `AB_implies_APN`**

This is the crown jewel theorem of the project, but it requires more setup:

**Definitions to contribute:**
```lean
def diffCount (f : F → F) (u v : F) : ℕ   -- differential count
def IsAPN (f : F → F) : Prop                -- Almost Perfect Nonlinear
def WalshCoeff (ψ : AddChar F ℂ) (f : F → F) (a b : F) : ℂ  -- Walsh coefficient
def IsAB (ψ : AddChar F ℂ) (f : F → F) (n : ℕ) : Prop       -- Almost Bent
```

**Main theorem:**
```lean
theorem AB_implies_APN : IsAB → IsAPN
```

**Why this is valuable:**
- APN and AB functions are fundamental in symmetric cryptography (S-box design).
- The `AB ⟹ APN` theorem is a classical result (Chabaud–Vaudenay 1995).
- Mathlib has **zero** coverage of cryptographic function theory — this would open a new area.
- The definitions are mathematically natural and well-established.

**How to refactor for Mathlib:**
- **Separate definitions from theorems.** Create a file `Mathlib.Cryptography.APN` (or `Mathlib.Combinatorics.APN`) with just the definitions and basic API.
- **Use Mathlib's `AddChar` directly** rather than abstracting to ℤ-valued Walsh coefficients. The abstract framework (`IsAB_abs`, `IsAPN_abs`) is useful for the proof but not for the final API.
- **Reduce hypotheses.** The current `AB_implies_APN` takes 12 hypotheses because the abstract framework requires manually passing Parseval, fourth moment, etc. For Mathlib, you'd want to:
  - Either prove these Fourier-analytic identities from first principles (using `Mathlib.Analysis.Fourier` or `Mathlib.NumberTheory.LSeriesHasSum`), or
  - State the theorem with the concrete `AddChar`-based definitions where these identities can be derived.
- **Remove `set_option maxHeartbeats`.** Mathlib has strict heartbeat limits (200000). Refactor proofs to be more efficient.
- **Follow Mathlib style:** use `where` instead of `:= by`, use `fun` not `λ`, structure proofs with `calc` blocks, etc.

**Suggested PR sequence:**
1. PR 1: `diffCount`, `IsAPN` definitions + basic API lemmas
2. PR 2: `WalshCoeff`, `IsAB` definitions + basic properties
3. PR 3: `AB_implies_APN` theorem

### 4. **Gold Function and Normalization**

```lean
def goldFun (x : F) : F := x ^ (2^k + 1)
def deltaGold (u x : F) : F := goldFun k F (x + u) + goldFun k F x
lemma kernel_iso_normalized : deltaGold = 0 ↔ Lnorm(x/u) = 0
```

**Why:**
- Gold functions (power functions `x^d` with `d = 2^k + 1`) are fundamental in finite field theory.
- The normalization/kernel isomorphism is a clean algebraic result.
- Connects to the theory of linearized polynomials over finite fields.

**How to refactor:**
- Use Mathlib's `frobenius` and `iterate_frobenius` instead of defining `frob2`/`frobIter`.
- The `goldExp` definition is trivial; inline it or put it in a `where` clause.
- The `delta_eq_lin_plus_const` lemma uses `grind` — replace with more standard tactics for Mathlib compatibility.
- Place in `Mathlib.FieldTheory.Finite.GoldFunction` or similar.

### 5. **Frobenius Factorization of Linearized Polynomials**

```lean
def L₀ (y : F) : F := y ^ (2^k) + y
def L₁ (y : F) : F := y^2 + y            -- Artin-Schreier map
def L₂ (y : F) : F := ∑ i in range k, y^(2^i)  -- partial Frobenius trace
lemma L₁_comp_L₂ : L₁(L₂(y)) = L₀(y)
```

**Why:**
- The Artin–Schreier map `y^2 + y` (trace map in char 2) is mathematically important.
- The factorization `(y^p + y) = AS(Tr_k(y))` is a standard result in finite field theory.
- Root-count bounds via degree arguments are clean and reusable.

**How to refactor:**
- Mathlib already has `frobenius` and the Artin–Schreier polynomial. Connect to those.
- The `L₀_add` (additivity) lemma should use `AddMonoidHom` or show `L₀` is `𝔽_p`-linear.
- Root count bounds should use `Polynomial.card_roots` more directly.

---

## Tier 3: Harder to Contribute Directly (But Valuable as Motivation)

### 6. **Walsh Support Counting (`triple_count_eq`)**

```lean
theorem triple_count_eq : (walshSupport W b).card = 2^(n-1)
```

This is valuable but deeply dependent on the abstract framework. It would need significant refactoring to use concrete Fourier analysis over finite fields.

### 7. **The Full Kasami Bridge Theorem**

The bridge theorem (`kasami_bridge`) combines everything and is the mathematical culmination, but it's too large and specialized for a single Mathlib PR. It would be the eventual goal after the foundational pieces are in Mathlib.

---

## Different Approaches to Contributing

### Approach A: Bottom-Up (Recommended for First-Timers)

1. Start with **Tier 1** items — pure arithmetic/combinatorial lemmas.
2. These require no domain expertise from reviewers.
3. They teach you the Mathlib PR workflow (CI, linting, review process).
4. **Timeline:** 1–2 weeks per PR.

### Approach B: Definition-First

1. Propose the **definitions** (`IsAPN`, `diffCount`, `WalshCoeff`, `IsAB`) first.
2. Get community buy-in on the API design before proving theorems.
3. Post on [Zulip](https://leanprover.zulipchat.com/) in `#mathlib4` to discuss naming and placement.
4. **Risk:** Reviewers may want different design choices (e.g., bundling into a structure).

### Approach C: Theory Module

1. Propose an entire new directory `Mathlib.Cryptography` or `Mathlib.Combinatorics.APN`.
2. Include definitions + key theorems together.
3. This is more ambitious but gives a complete, coherent addition.
4. **Requires:** RFC discussion on Zulip first. Mathlib maintainers need to agree on scope.

### Approach D: Upstream Missing Lemmas Only

1. Focus only on lemmas that fill gaps in existing Mathlib files.
2. Examples: `choose_pow_two_eq` in `Nat.Choose`, root count bounds in `Polynomial.Roots`.
3. Lowest risk, highest acceptance rate.

---

## Practical Steps for Your First PR

1. **Read the [Mathlib contribution guide](https://leanprover-community.github.io/contribute/).**
2. **Set up the Mathlib dev environment** (`lake exe cache get`, branch from `master`).
3. **Pick `choose_pow_two_eq`** as your first PR — it's the easiest win.
4. **Run the Mathlib linter** (`lake env lean --run Mathlib/Tactic/Linter.lean`) before submitting.
5. **Post on Zulip** before larger PRs to get early feedback on design.

### Key Mathlib Style Points

- **No `set_option maxHeartbeats`** — proofs must be efficient.
- **No `grind`** — it's not stable/accepted in Mathlib (as of now).
- **Use `simp` lemmas judiciously** — tag appropriate lemmas with `@[simp]`.
- **Docstrings are mandatory** for all public definitions and key theorems.
- **Module docstrings** (`/-! ... -/`) at the top of each file.
- **Copyright headers** with the standard Mathlib format.
- **No `Classical` unless necessary** — use `Decidable` instances where possible.
- **Namespace everything** — `APN.diffCount`, not bare `diffCount`.

---

## Summary Table

| Component | Mathlib Suitability | Difficulty | Prerequisite PRs |
|-----------|-------------------|------------|------------------|
| `choose_pow_two_eq` | ⭐⭐⭐⭐⭐ | Easy | None |
| `sq_ge_two_mul_of_even` | ⭐⭐⭐⭐ | Easy | None |
| `IsAPN`/`diffCount` defs | ⭐⭐⭐⭐ | Medium | Zulip discussion |
| `IsAB`/`WalshCoeff` defs | ⭐⭐⭐⭐ | Medium | Zulip discussion |
| `AB_implies_APN` | ⭐⭐⭐⭐ | Hard | Definition PRs |
| Gold function + normalization | ⭐⭐⭐ | Medium | `frobenius` API |
| Frobenius factorization | ⭐⭐⭐ | Medium | `frobenius` API |
| `triple_count_eq` | ⭐⭐⭐ | Hard | Definition PRs |
| `kasami_bridge` | ⭐⭐ | Very Hard | All above |

---

## What Reviewers Will Care About

1. **Is this mathematically established?** Yes — APN/AB theory is textbook material (Budaghyan 2014, Carlet 2010).
2. **Is anyone else working on this?** Check Zulip and the Mathlib project board.
3. **Is the API well-designed?** The abstract framework (`IsAB_abs`, `IsAPN_abs`) is a proof tool, not an API. For Mathlib, you'd want concrete definitions over finite fields.
4. **Are proofs efficient?** Several proofs use `800000` heartbeats — these must be optimized.
5. **Does it duplicate existing work?** The `CharTwo.neg_eq` and `CharTwo.sub_eq_add` lemmas already exist in Mathlib — remove the local copies and use the Mathlib versions.
