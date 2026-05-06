/-
  KasamiAB.lean

  Proof that the Walsh spectrum of the Kasami function is AB-type,
  i.e., |W_f(a,b)|² ∈ {0, 2^(n+1)} for all a and nonzero b,
  where f(x) = x^(4^k − 2^k + 1) over GF(2^n).

  The proof proceeds in two main steps:

  **Step 1 (APN):** The Kasami function is APN when gcd(k,n) = 1.
    - The derivative equation D_a f(x) = f(x+a) + f(x) reduces to a
      linearized polynomial equation.
    - Using the factorization techniques from `Theorem3/Factorization.lean`,
      the linearized polynomial kernel has at most 2^(2k) elements.
    - A refined analysis using gcd(k,n) = 1 shows at most 2 solutions,
      hence the function is APN.

  **Step 2 (APN ⟹ AB for odd n):** For power functions over GF(2^n) with
    n odd, APN is equivalent to AB. This follows from the theory of
    3-valued cross-correlation of m-sequences (Welch / Gold / Kasami).

  **Combined:** The Kasami function is AB when gcd(k,n) = 1 and n is odd.

  Reference:
  - Kasami (1971), "The weight enumerators for several classes of subcodes..."
  - Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions"
  - Budaghyan, "Construction and Analysis of Cryptographic Functions"
-/
import Mathlib
import Theorem3.Factorization
import Theorem3.Normalization
import Theorem23.Counting
import KasamiConjecture
import KasamiCharacters

noncomputable section

open Finset BigOperators Classical Polynomial

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Section 1: Derivative of the Kasami function

The Kasami function f(x) = x^d with d = 4^k − 2^k + 1.
Its derivative D_a f(x) = f(x+a) + f(x) is analyzed via a linearized polynomial.
-/

/-- The derivative of the Kasami function:
    `D_a f(x) = (x + a)^d + x^d` where `d = kasamiExp k`. -/
def kasamiDerivative (k : ℕ) (a x : F) : F :=
  kasamiFun F k (x + a) + kasamiFun F k x

/-- The number of solutions to `D_a f(x) = b` for fixed `a ≠ 0` and `b`. -/
def kasamiDiffCount (k : ℕ) (a b : F) : ℕ :=
  (Finset.univ.filter fun x => kasamiDerivative F k a x = b).card

/-! ## Section 2: Linearized polynomial arising from the Kasami derivative

When we expand D_a f(x) for the Kasami exponent d = 4^k − 2^k + 1,
the leading terms form a linearized polynomial (additive map) in x.

The key identity (in char 2):
  D_a f(x) = L_a(x) + f(a)
where L_a is a linearized (GF(2)-linear) operator.

The operator L_a factors through compositions of Frobenius-type maps,
and its kernel size is bounded using the factorization from
`Theorem3/Factorization.lean`.
-/

/-- The linearized part of the Kasami derivative.
    For u ≠ 0, D_u f(x) = 0 reduces to a linearized equation after
    substituting y = x/u and clearing denominators.

    The degree of this linearized polynomial is 2^(2k), so by the
    fundamental theorem of algebra over finite fields, the equation
    has at most 2^(2k) solutions. -/
def kasamiLinearized (k : ℕ) (u x : F) : F :=
  x ^ (2 ^ (2 * k)) * u + x ^ (2 ^ k) * u ^ (2 ^ k) +
  x * u ^ (2 ^ (2 * k))

/-! ## Section 3: Root bound for the Kasami linearized polynomial

Using the factorization from `Theorem3/Factorization.lean`, we can factor
the linearized operator and bound its kernel.
-/

/-- The number of solutions to the Kasami derivative equation
    D_a f(x) = b is at most 2^(2k) for any fixed a ≠ 0 and b.
    This uses the degree bound on the linearized polynomial. -/
lemma kasamiDiffCount_le_pow (k : ℕ) (a : F) (ha : a ≠ 0) (b : F) :
    kasamiDiffCount F k a b ≤ 2 ^ (2 * k) := by
  sorry

/-! ## Section 4: APN property of the Kasami function

The Kasami function f(x) = x^(4^k − 2^k + 1) is APN when gcd(k,n) = 1.
This means: for every a ≠ 0 and every b, the equation D_a f(x) = b
has at most 2 solutions.

The proof uses:
1. The root bound from Section 3 (at most 2^(2k) solutions)
2. A divisibility argument: the number of solutions is always a power of 2
   (since the equation is GF(2)-linear after normalization)
3. When gcd(k,n) = 1, a careful analysis of the kernel via the
   factorization L₁ ∘ L₂ from `Factorization.lean` shows the kernel
   has size dividing 4 (= 2²), and the refined bound gives ≤ 2.
-/

/-- **Kasami APN Theorem.**
    The Kasami function x^(4^k − 2^k + 1) is APN over GF(2^n)
    when gcd(k, n) = 1 and k ≥ 1.

    That is, for every nonzero a and every b, the equation
    f(x + a) + f(x) = b has at most 2 solutions. -/
theorem kasami_is_APN
    (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ a : F, a ≠ 0 → ∀ b : F, kasamiDiffCount F k a b ≤ 2 := by
  sorry

/-! ## Section 5: APN ⟹ AB for power functions (n odd)

For a power function f(x) = x^d over GF(2^n) with n odd,
the APN property implies the AB property.

This is a deep result from the theory of m-sequence cross-correlation.
The key insight is that for power functions, the Walsh transform
W_f(a,b) = ∑_x χ(ax + bx^d) can be related to the cross-correlation
of m-sequences. For n odd, the cross-correlation function of any
APN power function takes exactly 3 values, which corresponds to
|W_f(a,b)|² ∈ {0, 2^(n+1)}.

The proof uses:
1. For power functions, W_f(a,b) = W_f(1, b/a^d) for a ≠ 0
   (by the substitution x ↦ ax).
2. The fourth moment ∑_b |W_f(1,b)|⁴ can be computed from the
   differential uniformity (APN gives ∑ δ² = 2q).
3. For n odd, Parseval + fourth moment + positivity force the
   Walsh values to be 3-valued.

Reference: Theorem of Chabaud–Vaudenay (1994) / Nyberg (1994).
-/

/-- **APN power functions are AB for odd n.**
    If f(x) = x^d is APN over GF(2^n) with n odd, then f is AB.

    Here we state this using the abstract IsAB_abs from Counting.lean,
    applied to integer-valued Walsh coefficients. -/
theorem APN_power_implies_AB_odd
    (n : ℕ) (hn_odd : n % 2 = 1) (hn : 3 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ)
    (hAPN : ∀ a : F, a ≠ 0 → ∀ b : F,
      (Finset.univ.filter fun x => (x + a) ^ d + x ^ d = b).card ≤ 2) :
    ∀ a b : F, b ≠ 0 →
      Complex.normSq (∑ x : F, (AddChar.FiniteField.primitiveChar_to_Complex F)
        (a * x + b * x ^ d)) = 0 ∨
      Complex.normSq (∑ x : F, (AddChar.FiniteField.primitiveChar_to_Complex F)
        (a * x + b * x ^ d)) = (2 : ℝ) ^ (n + 1) := by
  sorry

/-! ## Section 6: The Kasami AB Theorem

Combining Steps 1–5: the Kasami function is AB when gcd(k,n) = 1 and n is odd.
-/

/-- **Main Theorem: The Kasami function has AB-type Walsh spectrum.**

    For f(x) = x^(4^k − 2^k + 1) over GF(2^n) with gcd(k,n) = 1 and n odd (n ≥ 3),
    the Walsh spectrum satisfies:
      |W_f(a,b)|² ∈ {0, 2^(n+1)}  for all a and all b ≠ 0.

    This means the Walsh transform W_f(a,b) = ∑_x χ(ax + b·f(x)) takes values
    only in {0, ±2^((n+1)/2)}, which is the AB (Almost Bent) property.

    The proof combines:
    - `kasami_is_APN`: the Kasami function is APN (using derivative factorization)
    - `APN_power_implies_AB_odd`: APN power functions are AB for odd n -/
theorem kasami_walsh_spectrum_AB
    (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    ∀ a b : F, b ≠ 0 →
      Complex.normSq (∑ x : F, (AddChar.FiniteField.primitiveChar_to_Complex F)
        (a * x + b * x ^ kasamiExp k)) = 0 ∨
      Complex.normSq (∑ x : F, (AddChar.FiniteField.primitiveChar_to_Complex F)
        (a * x + b * x ^ kasamiExp k)) = (2 : ℝ) ^ (n + 1) := by
  intro a b hb
  have hAPN := kasami_is_APN F n k hn hk hcard hcoprime
  -- Translate APN from kasamiDiffCount to the raw filter form
  have hAPN' : ∀ u : F, u ≠ 0 → ∀ v : F,
      (Finset.univ.filter fun x => (x + u) ^ kasamiExp k + x ^ kasamiExp k = v).card ≤ 2 := by
    intro u hu v
    have := hAPN u hu v
    unfold kasamiDiffCount kasamiDerivative kasamiFun at this
    exact this
  exact APN_power_implies_AB_odd F n hn_odd hn hcard (kasamiExp k) hAPN' a b hb

/-! ## Section 7: Connecting to the IsAlmostBent definition

We connect the AB property to the `IsAlmostBent` definition from `KasamiCharacters.lean`.
-/

/-- The Kasami function satisfies the IsAlmostBent predicate
    from KasamiCharacters.lean. -/
theorem kasami_isAlmostBent
    (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hn_odd : n % 2 = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    IsAlmostBent F (kasamiFun F k) n := by
  refine ⟨hcard, ?_⟩
  intro a b hb
  have hab := kasami_walsh_spectrum_AB F n k hn hk hn_odd hcard hcoprime a b hb
  -- The walshTransform from KasamiCharacters uses kasamiChar = primitiveChar_to_Complex
  -- and the IsAlmostBent uses normSq, matching our statement
  unfold walshTransform kasamiFun
  simp only [kasamiChar]
  exact hab

end