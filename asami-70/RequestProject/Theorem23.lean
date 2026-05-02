/-
Copyright (c) 2025. All rights reserved.
Formalization of Theorem 23 from Budaghyan et al. (arXiv:0803.3781):
"Construction and Analysis of Cryptographic Functions"

This file defines the APN/AB binomial family from Equation (5.1) of the paper
and states the main result (Theorem 23).
-/
import Mathlib
import RequestProject.Defs

/-! # Theorem 23: APN/AB Binomial Construction

## Overview

We formalize the construction of the binomial family:
  `f(x) = x^{2^s+1} + w · x^d`
where:
- `n = 3k` with `k ≥ 1`
- `gcd(s, 3k) = 1`
- `t ∈ {1, 2}`, `i = 3 - t`
- `d = 2^{i·k} + 2^{t·k + s} - (2^s + 1)`
- `w` is an element of `𝔽_{2^n}` of multiplicative order `2^{2k} + 2^k + 1`

## Main Results

- `budaghyanBinomial`: Definition of the APN/AB binomial function.
- `budaghyan_theorem23_apn`: The function is APN under the GCD conditions.
- `budaghyan_theorem23_ab`: If additionally `k` is odd, the function is AB.
- `ab_walsh_spectrum`: The AB property implies the Walsh spectrum is `{0, ±2^{(n+1)/2}}`.
-/

open Finset BigOperators

noncomputable section

/-! ## Parameters and Exponents -/

/-- Parameters for the Budaghyan binomial construction.
  Bundles `k ≥ 1`, `s` with `gcd(s, 3k) = 1`, and `t ∈ {1, 2}`. -/
structure BudaghyanParams where
  /-- The parameter `k ≥ 1` such that `n = 3k`. -/
  k : ℕ
  /-- `k` is positive. -/
  hk : k ≥ 1
  /-- The shift parameter `s`. -/
  s : ℕ
  /-- `gcd(s, 3k) = 1`, ensuring the Gold exponent `2^s + 1` gives an APN monomial. -/
  hs : Nat.Coprime s (3 * k)
  /-- The parameter `t`, which is either 1 or 2. -/
  t : ℕ
  /-- `t` is 1 or 2. -/
  ht : t = 1 ∨ t = 2

namespace BudaghyanParams

/-- The field extension degree `n = 3k`. -/
def n (p : BudaghyanParams) : ℕ := 3 * p.k

/-- `n ≥ 3` since `k ≥ 1`. -/
theorem n_ge_three (p : BudaghyanParams) : p.n ≥ 3 := by
  unfold n; have := p.hk; omega

/-- `n ≠ 0`. -/
theorem n_ne_zero (p : BudaghyanParams) : p.n ≠ 0 := by
  unfold n; have := p.hk; omega

/-- The complementary index `i = 3 - t`. -/
def i (p : BudaghyanParams) : ℕ := 3 - p.t

/-- `i + t = 3`. -/
theorem i_add_t (p : BudaghyanParams) : p.i + p.t = 3 := by
  simp only [i]; rcases p.ht with h | h <;> omega

/-- The Gold exponent `2^s + 1`. -/
def goldExp (p : BudaghyanParams) : ℕ := 2 ^ p.s + 1

/-- The "correction" exponent
  `d = 2^{i·k} + 2^{t·k + s} - (2^s + 1)`.

  Since we are working modulo `2^n - 1`, this is well-defined as a natural number
  when reduced mod `2^n - 1`. We define it as an integer first. -/
def dExp_int (p : BudaghyanParams) : ℤ :=
  2 ^ (p.i * p.k) + 2 ^ (p.t * p.k + p.s) - (2 ^ p.s + 1)

/-- The exponent `d` reduced modulo `2^n - 1` (the multiplicative order of `𝔽_{2^n}*`).
  Since elements of `𝔽_{2^n}^*` have order dividing `2^n - 1`, the power `x^d`
  depends only on `d mod (2^n - 1)`. -/
def dExp (p : BudaghyanParams) : ℕ :=
  (p.dExp_int % (2 ^ p.n - 1 : ℤ)).toNat

/-- The order of the element `w` in the multiplicative group: `2^{2k} + 2^k + 1`.
  This divides `2^{3k} - 1 = (2^k - 1)(2^{2k} + 2^k + 1)`. -/
def wOrder (p : BudaghyanParams) : ℕ := 2 ^ (2 * p.k) + 2 ^ p.k + 1

/-
`wOrder` divides `2^n - 1`. This follows from the factorization
  `2^{3k} - 1 = (2^k - 1)(2^{2k} + 2^k + 1)`.
-/
theorem wOrder_dvd (p : BudaghyanParams) : p.wOrder ∣ 2 ^ p.n - 1 := by
  rw [ BudaghyanParams.n, BudaghyanParams.wOrder ];
  exact ⟨ 2 ^ p.k - 1, by zify; norm_num; ring ⟩

end BudaghyanParams

/-! ## The Binomial Function -/

/-- Predicate: `w` has multiplicative order exactly `2^{2k} + 2^k + 1` in `𝔽_{2^n}^*`.
  Equivalently, `w = α^{2^k - 1}` for a primitive element `α` of `𝔽_{2^n}`. -/
def hasCorrectOrder (p : BudaghyanParams) [Fact (Nat.Prime 2)]
    (w : GaloisField 2 p.n) : Prop :=
  w ≠ 0 ∧ orderOf w = p.wOrder

/-- The **Budaghyan binomial** `f(x) = x^{2^s+1} + w · x^d` over `𝔽_{2^n}`.

  This is Equation (5.1) from Budaghyan et al. (arXiv:0803.3781). -/
def budaghyanBinomial (p : BudaghyanParams) [Fact (Nat.Prime 2)]
    (w : GaloisField 2 p.n) (x : GaloisField 2 p.n) : GaloisField 2 p.n :=
  x ^ p.goldExp + w * x ^ p.dExp

/-! ## GCD Conditions (g₁ ≠ g₂) -/

/-- The GCD condition `g₁` from Theorem 23.
  `g₁ = gcd(2^{ik} + 1, 2^n - 1)`. -/
def g₁ (p : BudaghyanParams) : ℕ :=
  Nat.gcd (2 ^ (p.i * p.k) + 1) (2 ^ p.n - 1)

/-- The GCD condition `g₂` from Theorem 23.
  `g₂ = gcd(2^{(t-i)k+s} + 1, 2^n - 1)`. -/
def g₂ (p : BudaghyanParams) : ℕ :=
  -- Note: (t-i)k + s can be negative when t < i, so we work modulo n
  Nat.gcd (2 ^ ((p.t * p.k + p.s) % p.n) + 1) (2 ^ p.n - 1)

/-! ## Main Theorem: APN Property -/

/-- **Theorem 23 (APN part)** from Budaghyan et al.

  If `g₁ ≠ g₂` (the GCD conditions from the polynomial elimination argument),
  then the binomial `f(x) = x^{2^s+1} + w·x^d` is APN on `𝔽_{2^n}`.

  The proof in the paper proceeds by analyzing the differential equation
  `f(x+a) + f(x) = b` and showing, via polynomial elimination over `𝔽_{2^n}`,
  that it has at most 2 solutions for every nonzero `a`. -/
theorem budaghyan_theorem23_apn (p : BudaghyanParams) [hprime : Fact (Nat.Prime 2)]
    (w : GaloisField 2 p.n) (hw : hasCorrectOrder p w)
    (hg : g₁ p ≠ g₂ p) :
    @IsAPN (GaloisField 2 p.n) (instFieldGaloisField 2 p.n)
      (Fintype.ofFinite _) (Classical.decEq _) (budaghyanBinomial p w) := by
  sorry

/-! ## Corollary: AB Property when k is odd -/

/-- **Theorem 23 (AB corollary)** from Budaghyan et al.

  If additionally `k` is odd, then the binomial is **Almost Bent (AB)**.
  This follows because:
  1. The function is APN (from the main theorem).
  2. When `k` is odd, `n = 3k` is odd.
  3. For odd `n`, the quadratic APN function has the property that all
     nonzero Walsh coefficients have absolute value `2^{(n+1)/2}`.
  4. This is precisely the AB property. -/
theorem budaghyan_theorem23_ab (p : BudaghyanParams) [hprime : Fact (Nat.Prime 2)]
    (w : GaloisField 2 p.n) (hw : hasCorrectOrder p w)
    (hg : g₁ p ≠ g₂ p)
    (hk_odd : Odd p.k) :
    IsAB p.n p.n_ne_zero (budaghyanBinomial p w) := by
  sorry

/-! ## Integration with Spectral Properties -/

/-
The AB property is equivalent to the Walsh spectrum being `{0, ±2^{(n+1)/2}}`.
  This is essentially the definition, stated as a biconditional for clarity.
-/
theorem ab_iff_walsh_spectrum (n : ℕ) [hprime : Fact (Nat.Prime 2)] (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n) :
    IsAB n hn f ↔
    ∀ a b : GaloisField 2 n,
      walshTransform n hn f a b ∈ ({0, (2 ^ ((n + 1) / 2) : ℤ),
        -(2 ^ ((n + 1) / 2) : ℤ)} : Set ℤ) := by
  unfold IsAB; aesop;

/-- For the Budaghyan binomial with odd `k`, the Walsh spectrum is exactly
  `{0, ±2^{(n+1)/2}}`, confirming the AB property through spectral analysis. -/
theorem budaghyan_walsh_spectrum (p : BudaghyanParams) [hprime : Fact (Nat.Prime 2)]
    (w : GaloisField 2 p.n) (hw : hasCorrectOrder p w)
    (hg : g₁ p ≠ g₂ p) (hk_odd : Odd p.k)
    (a b : GaloisField 2 p.n) :
    walshTransform p.n p.n_ne_zero (budaghyanBinomial p w) a b ∈
      ({0, (2 ^ ((p.n + 1) / 2) : ℤ), -(2 ^ ((p.n + 1) / 2) : ℤ)} : Set ℤ) := by
  have hab := budaghyan_theorem23_ab p w hw hg hk_odd
  rw [ab_iff_walsh_spectrum] at hab
  exact hab a b

/-! ## Concrete Example: k = 1, s = 1, t = 1

  The simplest instance: `n = 3`, `s = 1`, `t = 1`, giving
  `f(x) = x^3 + w·x^d` on `𝔽_8`, where `d ≡ 2^2 + 2^2 - 3 = 5 (mod 7)`. -/

/-- Example parameters: `k = 1, s = 1, t = 1`. -/
def exampleParams : BudaghyanParams where
  k := 1
  hk := le_refl 1
  s := 1
  hs := by decide
  t := 1
  ht := Or.inl rfl

#check @budaghyan_theorem23_apn exampleParams

end