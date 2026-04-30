/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Formalization of:
  T. Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
  2nd Order Binary Reed-Muller Codes",
  Information and Control 18, 369-394 (1971).

This file contains the core definitions used throughout the paper.
-/
import Mathlib

open Polynomial Finset BigOperators

noncomputable section

/-!
# Core Definitions for Kasami's Paper

## Main Definitions

We set up the algebraic framework for studying cyclic codes of length `n` over `GF(q)`,
where `α` is an element of order `n` in `GF(q^m)`.

### Binary Gaussian binomial coefficients

The bracket notation `[l; h]_j` used in the weight enumerator formulas.

### Code families

The code families B_j^(u), D_j^(u), F_j^(u), H_j^(u), J_j^(u) and their duals.
-/

/-- The "binary q-binomial coefficient" `[l; h]_j` used by Kasami, defined as
    `∏_{t=1}^{h} (1 - 2^{2j(l+1-t)}) / (1 - 2^{2jt})` for `h > 0`, and `1` for `h = 0`.
    Here `halfL` represents the parameter `l` (which may be a half-integer in context,
    but we use integer arithmetic). -/
def kasami_bracket (j : ℕ) (halfL : ℕ) (h : ℕ) : ℚ :=
  if h = 0 then 1
  else ∏ t : Fin h, ((1 - (2 : ℚ) ^ (2 * (j : ℤ) * ((halfL : ℤ) + 1 - ((t : ℤ) + 1)))) /
                      (1 - (2 : ℚ) ^ (2 * (j : ℤ) * ((t : ℤ) + 1))))

/-- The product `[t]_j = ∏_{i=1}^{t} (1 - 2^{2ij})` for `t > 0`, and `1` for `t = 0`. -/
def kasami_prod (j : ℕ) (t : ℕ) : ℚ :=
  if t = 0 then 1
  else ∏ i : Fin t, (1 - (2 : ℚ) ^ (2 * (j : ℤ) * ((i : ℤ) + 1)))

/-- The binary weight function `W₂(i)`: sum of binary digits of a natural number. -/
def binaryWeight : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + binaryWeight ((n + 1) / 2)

/-- `u₁(m, j)` as defined in the paper: `⌊m / (2(m,j))⌋ + 1`. -/
def u₁ (m j : ℕ) : ℕ := m / (2 * Nat.gcd m j) + 1

/-- `u₂(m, j)` as defined in the paper:
    if `m/(m,j)` is odd, then `u₂ = u₁`;
    if `m/(m,j)` is even, then `u₂ = ⌈m / (4(m,j))⌉`. -/
def u₂ (m j : ℕ) : ℕ :=
  if m / Nat.gcd m j % 2 = 1 then u₁ m j
  else (m + 4 * Nat.gcd m j - 1) / (4 * Nat.gcd m j)

/-!
## Cyclic Codes as Submodules

We model a binary cyclic code of length `n` as a submodule of `Fin n → GF(2)`.
-/

/-- A binary codeword of length `n`. -/
abbrev Codeword (n : ℕ) := Fin n → ZMod 2

/-- The Hamming weight of a codeword: the number of nonzero coordinates. -/
def hammingWt {n : ℕ} (v : Codeword n) : ℕ :=
  Finset.card (Finset.univ.filter (fun i => v i ≠ 0))

/-- A cyclic code of length `n > 0` over `GF(2)` is a submodule of `(Fin n → ZMod 2)`
    that is closed under cyclic shifts. -/
structure CyclicCode (n : ℕ) (hn : 0 < n) extends Submodule (ZMod 2) (Codeword n) where
  cyclic_shift : ∀ v ∈ toSubmodule,
    (fun i : Fin n => v ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) ∈ toSubmodule

/-- The weight enumerator of a code: `A_w` is the number of codewords of weight `w`. -/
def weightEnumerator {n : ℕ} (C : Submodule (ZMod 2) (Codeword n)) (w : ℕ) : ℕ :=
  Set.ncard {v : C | hammingWt v.val = w}

/-!
## The set K(t,j) for Theorem 2
-/

/-- The set `K(t,j)` used in Theorem 2 for weight restriction. -/
def kasami_K (t j : ℕ) : Set ℕ :=
  {i | i > 0 ∧ binaryWeight i > t} ∪
  {i | binaryWeight i = t ∧ i ≥ 2 ^ (t + 2)} ∪
  {i | ∃ h l : ℕ, h > 0 ∧ l > 0 ∧ l * j < h ∧ h < t + 2 ∧
       i = 2 ^ (t + 2) - 2 ^ h - 2 ^ (h - l * j) - 1}

end
