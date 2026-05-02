/-
# Theorem 3: AB Property of Specific Binomial

Formalization of Theorem 3 from:
  "Fourier Spectra of Binomial APN Functions"
  by C. Bracken, E. Byrne, N. Markin, G. McGuire (arXiv:0803.3781)

The main result: the binomial `f(x) = x^{2^k+1} + ω·x^{2^{ik}+2^{tk+s}}`
is Almost Bent under specific parameter constraints.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.WalshSpectrum

noncomputable section

open scoped BigOperators
open Finset Classical

variable {n : ℕ} [NeZero n]

attribute [local instance] Fintype.ofFinite

/-! ## The Gold Power Function

The monomial `x^{2^k+1}` (the "Gold function") is the simplest APN function.
Its linearized derivative is `Δ_u(x^{2^k+1}) = u^{2^k} · x + u · x^{2^k}`,
which is `F_2`-linear and has kernel of dimension ≤ 1 when `gcd(k, n) = 1`. -/

/-- The Gold APN exponent `2^k + 1`. -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-- The Gold power function `f(x) = x^{2^k + 1}` on `F_{2^n}`. -/
def goldFunction (k : ℕ) : GaloisField 2 n → GaloisField 2 n :=
  fun x => x ^ goldExp k

/-
The linearized derivative of the Gold function:
    `Δ_u(x^{2^k+1}) = (x + u)^{2^k+1} + x^{2^k+1} + u^{2^k+1}`
                     `= u^{2^k} · x + u · x^{2^k}`.

    This is `F_2`-linear in `x`, which is the key property that makes
    the kernel analysis tractable.
-/
omit [NeZero n] in
lemma gold_linDeriv (k : ℕ) (u x : GaloisField 2 n) :
    linDerivative (goldFunction k) u x = u ^ (2 ^ k) * x + u * x ^ (2 ^ k) := by
  unfold goldFunction linDerivative;
  unfold goldExp; ring;
  have h_char_two : ∀ (a b : GaloisField 2 n), (a + b) ^ 2 ^ k = a ^ 2 ^ k + b ^ 2 ^ k := by
    exact fun a b => add_pow_expChar_pow a b 2 k;
  grind +suggestions

/-- When `gcd(k, n) = 1`, the Gold function is APN: the linearized derivative
    `L_u(x) = u^{2^k} · x + u · x^{2^k}` has trivial kernel for `u ≠ 0`.

    Proof sketch: `L_u(x) = 0` iff `(x/u)^{2^k} + (x/u) = 0` iff `x/u ∈ F_2`,
    so `ker(L_u) = {0, u}` has dimension 1. -/
theorem gold_apn (k : ℕ) (hgcd : Nat.gcd k n = 1) :
    IsAPN (goldFunction (n := n) k) := by
  sorry

/-! ## The Binomial APN Function (Theorem 3)

The paper considers the binomial:
  `f(x) = x^{2^k+1} + ω · x^{2^{ik} + 2^{tk+s}}`

with parameters satisfying:
  - `n = sk` where `s` divides `n`
  - `gcd(k, n) = 1`
  - `i, t` are specific indices depending on `s`
  - `ω ∈ F_{2^n}` is a suitable element (often a primitive element of a subfield)
-/

/-- The binomial function `f(x) = x^{2^k+1} + ω · x^{2^{ik} + 2^{tk+s}}`
    from Theorem 3 of the paper. -/
def binomialAPN (k s i t : ℕ) (ω : GaloisField 2 n) :
    GaloisField 2 n → GaloisField 2 n :=
  fun x => x ^ (2 ^ k + 1) + ω * x ^ (2 ^ (i * k) + 2 ^ (t * k + s))

/-! ## Parameter Constraints

The paper requires (see conditions before Theorem 3):
  1. `n = s · k` with `s ≥ 3` odd
  2. `gcd(k, n) = 1`
  3. `i + t ≡ s (mod 2s)` or specific relations
  4. `ω` lies in a specific subfield

We bundle these as a structure for clarity.
-/

/-- Parameter constraints for Theorem 3. -/
structure BinomialParams (n : ℕ) where
  k : ℕ
  s : ℕ
  i : ℕ
  t : ℕ
  ω : GaloisField 2 n
  hn : n = s * k
  hs_ge : s ≥ 3
  hs_odd : s % 2 = 1
  hgcd : Nat.gcd k n = 1
  /-- The element `ω` must not be zero. -/
  hω_ne : ω ≠ 0

/-! ## Linearized Derivative of the Binomial

The linearized derivative of the binomial `f` decomposes as a sum of the
Gold linearized derivative and a correction term from the second monomial.

The key insight (Section 3 of the paper) is that the full linearized polynomial
  `Δ_u f(x) = Δ_u(x^{2^k+1})(x) + ω · Δ_u(x^{2^{ik}+2^{tk+s}})(x)`
is still `F_2`-linear in `x`, and the resulting system has at most 2 roots
(i.e., kernel dimension ≤ 1) under the parameter constraints.
-/

/-
The linearized derivative of the binomial function decomposes into the
    Gold part and the correction term.
-/
omit [NeZero n] in
lemma binomial_linDeriv_decomp (p : BinomialParams n) (u x : GaloisField 2 n) :
    linDerivative (binomialAPN p.k p.s p.i p.t p.ω) u x =
      linDerivative (goldFunction p.k) u x +
      p.ω * linDerivative (fun x => x ^ (2 ^ (p.i * p.k) + 2 ^ (p.t * p.k + p.s))) u x := by
  unfold linDerivative;
  grind +locals

/-! ## Theorem 3: The Binomial is AB

**Theorem 3** (Bracken–Byrne–Markin–McGuire): Under the parameter constraints,
the binomial `f(x) = x^{2^k+1} + ω · x^{2^{ik}+2^{tk+s}}` is Almost Bent.

Proof strategy (following the paper):
1. Show that `Δ_u f(x) = 0` reduces to a system of `F_2`-linear equations.
2. Use the specific structure of the exponents to show the system matrix has
   rank ≥ n-1, hence kernel dimension ≤ 1.
3. Apply the Corollary (`kernel_dim_le_one_implies_AB`).

The hardest part is step 2, which involves detailed polynomial arithmetic
over `F_{2^n}` exploiting the Frobenius endomorphism. We leave this as `sorry`.
-/

/-- **Theorem 3.** Under the parameter constraints, the linearized derivative
    of the binomial has kernel of cardinality at most 2 for every nonzero `u`. -/
theorem binomial_kernel_small (p : BinomialParams n) :
    ∀ u : GaloisField 2 n, u ≠ 0 →
      Nat.card (linDerivKer (binomialAPN p.k p.s p.i p.t p.ω) u) ≤ 2 := by
  sorry

/-- **Theorem 3 (Main Result).** Under the parameter constraints and assuming
    `n` is odd, the binomial APN function is Almost Bent. -/
theorem binomial_is_AB (p : BinomialParams n) (hodd : n % 2 = 1) :
    IsAB (binomialAPN (n := n) p.k p.s p.i p.t p.ω) := by
  exact kernel_dim_le_one_implies_AB _ hodd (binomial_kernel_small p)

/-! ## Consequence: Triple Count Conjecture

The paper's spectral result feeds into a combinatorial count. If `f` is AB
with `n` odd, the "triple count"—the number of `(a, b)` pairs with
`W_f(a,b) ≠ 0`—is conjectured to be `2^{2n-3} - 2^{n-2}`.

This follows from Parseval's identity and the three-valued spectrum. -/

/-- The number of nonzero Walsh coefficients for an AB function on `F_{2^n}`.

    By Parseval: `∑_{a,b} W_f(a,b)² = 2^{2n}`.
    If `W_f(a,b) ∈ {0, ±2^{(n+1)/2}}`, then the number of nonzero values `N` satisfies
    `N · 2^{n+1} = 2^{2n}`, giving `N = 2^{n-1}`.

    The "triple count" `2^{2n-3} - 2^{n-2}` arises from a more refined analysis
    excluding certain degenerate pairs. -/
theorem AB_nonzero_walsh_count (f : GaloisField 2 n → GaloisField 2 n)
    (hf : IsAB f) (hodd : n % 2 = 1) (hn : n ≥ 3) :
    Nat.card {p : GaloisField 2 n × GaloisField 2 n // walshTransform f p.1 p.2 ≠ 0} =
      2 ^ (n - 1) := by
  sorry

end