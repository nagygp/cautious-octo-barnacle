/-
Copyright (c) 2024 Kasami-71 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Kasami-71 Function: Core Definitions

Core definitions for the analysis of the Kasami power function
`F(x) = x^d` on `𝔽_{2^n}` where `d = 2^(2k) − 2^k + 1` and `n = 2k + 1`.

## Main definitions

* `kasamiExp` – The Kasami exponent `d = 2^(2k) − 2^k + 1`
* `kasamiDeriv` – The derivative `D_a F(x) = (x+a)^d + x^d + a^d`
* `WalshCoeff` – Walsh–Hadamard coefficient of a function
* `IsAlmostBent` – The Almost-Bent (AB) property
* `walshNonzeroCount` – Count of nonzero Walsh coefficients for a fixed `b`

## References

* [Budaghyan–Carlet–Leander, *Two classes of quadratic APN binomials…*,
  arXiv:0803.3781](https://arxiv.org/abs/0803.3781), Theorem 3
* Budaghyan, *Construction and Analysis of Cryptographic Functions*, Theorem 23
-/

noncomputable section

open Finset BigOperators

/-! ### The Kasami exponent -/

/-- The Kasami exponent `d = 2^(2k) − 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

@[simp] lemma kasamiExp_zero : kasamiExp 0 = 1 := by decide

@[simp] lemma kasamiExp_one : kasamiExp 1 = 3 := by decide

lemma kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp; omega

lemma two_pow_two_mul_k_ge (k : ℕ) : 2 ^ k ≤ 2 ^ (2 * k) := by
  apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
  omega

/-! ### The derivative of the Kasami function -/

/-- The derivative of the Kasami power function:
  `D_a F(x) = (x + a)^d + x^d + a^d`
  where `d = kasamiExp k` and `F(x) = x^d`. In characteristic 2 this equals
  `F(x + a) − F(x) − F(a) + F(0)` since subtraction equals addition and `F(0) = 0`. -/
def kasamiDeriv {F : Type*} [Ring F] (k : ℕ) (a x : F) : F :=
  (x + a) ^ kasamiExp k + x ^ kasamiExp k + a ^ kasamiExp k

/-- The kernel of the Kasami derivative: the set of `x` with `D_a F(x) = 0`. -/
def kasamiKernel {F : Type*} [Ring F] [Fintype F] [DecidableEq F]
    (k : ℕ) (a : F) : Finset F :=
  Finset.univ.filter fun x => kasamiDeriv k a x = 0

/-! ### Walsh–Hadamard transform (abstract) -/

/-- An additive character on a finite field of characteristic 2:
  a function `χ : F → ℤ` satisfying
  - `χ(x) ∈ {−1, 1}` for all `x`
  - `χ(0) = 1`
  - `χ(x + y) = χ(x) * χ(y)` (multiplicative over addition)
  - Orthogonality: `∑ x, χ(a * x) = 0` for `a ≠ 0` -/
structure AdditiveChar (F : Type*) [Add F] [Mul F] [Zero F] where
  toFun : F → ℤ
  map_val : ∀ x, toFun x = 1 ∨ toFun x = -1
  map_zero : toFun 0 = 1
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y

instance {F : Type*} [Add F] [Mul F] [Zero F] : CoeFun (AdditiveChar F) (fun _ => F → ℤ) :=
  ⟨AdditiveChar.toFun⟩

/-- Walsh–Hadamard coefficient of `G : F → F` with respect to additive character `χ`:
  `W(a, b) = ∑_{x ∈ F} χ(b * G(x) + a * x)` -/
def WalshCoeff {F : Type*} [Ring F] [Fintype F] (χ : AdditiveChar F)
    (G : F → F) (a b : F) : ℤ :=
  ∑ x : F, χ (b * G x + a * x)

/-- A function `G : F → F` is **Almost Bent** (AB) if every Walsh coefficient
  with `b ≠ 0` lies in `{0, ±2^{(n+1)/2}}` where `|F| = 2^n`. -/
def IsAlmostBent {F : Type*} [Ring F] [Fintype F] [DecidableEq F]
    (χ : AdditiveChar F) (G : F → F) (n : ℕ) : Prop :=
  (Fintype.card F = 2 ^ n) ∧
  ∀ a b : F, b ≠ 0 →
    WalshCoeff χ G a b = 0 ∨
    WalshCoeff χ G a b = (2 : ℤ) ^ ((n + 1) / 2) ∨
    WalshCoeff χ G a b = -((2 : ℤ) ^ ((n + 1) / 2))

/-- Count of nonzero Walsh coefficients for a fixed nonzero `b`:
  `|{a ∈ F | W(a, b) ≠ 0}|`. -/
def walshNonzeroCount {F : Type*} [Ring F] [Fintype F] [DecidableEq F]
    (χ : AdditiveChar F) (G : F → F) (b : F) : ℕ :=
  (Finset.univ.filter fun a => WalshCoeff χ G a b ≠ 0).card

end
