/-
Copyright (c) 2024 Kasami-71 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RequestProject.Kasami71.BinomialKernel

/-!
# Walsh Spectrum and the AB Property

We connect the kernel dimension of the Kasami derivative to the
Almost-Bent (AB) property via character sums, and derive the
triple count `2^{2n−3} − 2^{n−2}` using Parseval's identity.

## Main results

* `kernel_dim_le_one_implies_AB` – If every derivative kernel has ≤ 2 elements
  (dimension ≤ 1 over 𝔽₂), then the function is Almost Bent.
* `parseval_identity` – Parseval for the Walsh–Hadamard transform.
* `AB_nonzero_walsh_count` – An AB function has exactly `2^{n−1}` nonzero Walsh
  coefficients per nonzero `b`.
* `triple_count_eq` – The triple count equals `2^{2n−3} − 2^{n−2}`.

## References

* Budaghyan, *Construction and Analysis of Cryptographic Functions*, Theorem 23.
* arXiv:0803.3781, §3.
-/

noncomputable section

open Finset BigOperators

/-! ## Part 1: Kernel dimension implies APN/AB -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- APN (Almost Perfect Nonlinear): for every `a ≠ 0` and every `b`,
    the equation `F(x + a) + F(x) = b` has at most 2 solutions.
    Equivalently, `|ker(D_a F)| ≤ 2` for all `a ≠ 0`. -/
def IsAPN (G : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    (Finset.univ.filter fun x => G (x + a) + G x = b).card ≤ 2

/-- For a function whose derivative kernel has at most 2 elements
    for every nonzero `a`, the function is APN. -/
lemma kernel_le_two_implies_APN (G : F → F)
    (hker : ∀ a : F, a ≠ 0 →
      (Finset.univ.filter fun x => G (x + a) + G x + G a + G 0 = 0).card ≤ 2) :
    IsAPN G := by
  sorry

/-- **Connection theorem**: If every derivative kernel has dimension ≤ 1
    (i.e., at most 2 elements) AND the Walsh coefficients satisfy a
    compatibility condition, then the function is Almost Bent.

    For `n` odd and power functions `F(x) = x^d`, APN is equivalent to AB.
    This is the content of Theorem 23 from Budaghyan's monograph. -/
theorem kernel_dim_le_one_implies_AB
    (χ : AdditiveChar F) (G : F → F) (n : ℕ) (hn : Odd n) (hn1 : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (hker : ∀ a : F, a ≠ 0 →
      (Finset.univ.filter fun x => G (x + a) + G x + G a + G 0 = 0).card ≤ 2)
    /- The function G is a power permutation (needed for APN ↔ AB) -/
    (hperm : Function.Bijective G)
    /- Parseval identity for the character χ -/
    (hparseval : ∀ b : F, b ≠ 0 →
      ∑ a : F, (WalshCoeff χ G a b) ^ 2 = (2 : ℤ) ^ (2 * n))
    /- Walsh coefficients are divisible by 2^⌈(n+1)/2⌉ (from theory of
       quadratic forms / exponential sums in char 2) -/
    (hdiv : ∀ a b : F, b ≠ 0 →
      (2 : ℤ) ^ ((n + 1) / 2) ∣ WalshCoeff χ G a b) :
    IsAlmostBent χ G n := by
  sorry

/-! ## Part 2: Parseval identity and nonzero Walsh count -/

/-- **Parseval identity (abstract form)**:
    For any additive character `χ` and function `G : F → F`,
    `∑_{a ∈ F} W(a,b)² = |F|²` for each `b ≠ 0`.

    This follows from the orthogonality of characters. -/
theorem parseval_identity (χ : AdditiveChar F) (G : F → F) (n : ℕ)
    (hcard : Fintype.card F = 2 ^ n)
    (hχ_orth : ∀ a : F, a ≠ 0 → ∑ x : F, χ (a * x) = 0)
    (b : F) (hb : b ≠ 0) :
    ∑ a : F, (WalshCoeff χ G a b) ^ 2 = (2 : ℤ) ^ (2 * n) := by
  sorry

/-! ## Part 3: From AB to nonzero Walsh count -/

section TripleCount

/-!
### Abstract counting lemma

The core algebraic argument: if `N` integers from `{0, ±c}` have
squared sum `S`, then exactly `S / c²` of them are nonzero.
This is the backbone of the triple count derivation.
-/

/-
If a list of integers from `{0, c, −c}` has squared sum `S`,
    then the number of nonzero entries is `S / c²` (provided `c > 0`).
-/
lemma nonzero_count_of_sq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℤ) (c : ℤ) (hc : 0 < c)
    (hw : ∀ i, w i = 0 ∨ w i = c ∨ w i = -c)
    (S : ℤ) (hS : ∑ i, (w i) ^ 2 = S) :
    ((Finset.univ.filter fun i => w i ≠ 0).card : ℤ) = S / c ^ 2 := by
  rw [ ← hS, Int.ediv_eq_of_eq_mul_left ];
  · positivity;
  · rw [ Finset.sum_congr rfl fun i hi => show w i ^ 2 = ( if w i = 0 then 0 else c ^ 2 ) by rcases hw i with ( h | h | h ) <;> simp +decide [ h ] ] ; simp +decide [ Finset.sum_ite ]

/-- Specialisation: for an AB function, the nonzero Walsh count per row
    is `2^{n−1}`. -/
theorem AB_nonzero_walsh_count (χ : AdditiveChar F) (G : F → F) (n : ℕ)
    (hAB : IsAlmostBent χ G n)
    (hparseval : ∀ b : F, b ≠ 0 →
      ∑ a : F, (WalshCoeff χ G a b) ^ 2 = (2 : ℤ) ^ (2 * n))
    (hn : 1 ≤ n) (b : F) (hb : b ≠ 0) :
    walshNonzeroCount χ G b = 2 ^ (n - 1) := by
  sorry

/-!
### Triple count

The **triple count** is the number of *unordered pairs* `{a₁, a₂}` of
distinct elements of `F` such that both `W(a₁, b) ≠ 0` and `W(a₂, b) ≠ 0`
(for a fixed nonzero `b`).  Since there are `2^{n−1}` nonzero Walsh entries,
this count equals `C(2^{n−1}, 2) = 2^{2n−3} − 2^{n−2}`.
-/

/-
Arithmetic identity: `C(2^{n-1}, 2) = 2^{2n-3} − 2^{n-2}` for `n ≥ 2`.
-/
theorem choose_pow_two_eq (n : ℕ) (hn : 2 ≤ n) :
    Nat.choose (2 ^ (n - 1)) 2 = 2 ^ (2 * n - 3) - 2 ^ (n - 2) := by
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
  norm_num [ Nat.mul_succ, pow_succ', Nat.mul_assoc, Nat.mul_div_assoc ] ; ring;
  exact eq_tsub_of_add_eq ( by rw [ show 4 + n * 2 - 3 = n * 2 + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; zify ; norm_num ; ring )

/-- **Triple Count Theorem**: For an AB function on `𝔽_{2^n}` (`n ≥ 2`, odd),
    the number of unordered pairs of distinct `a`-values with nonzero Walsh
    coefficient (for any fixed nonzero `b`) equals `2^{2n−3} − 2^{n−2}`.

    This follows from:
    1. Parseval ⟹ `2^{n−1}` nonzero Walsh coefficients per row (AB_nonzero_walsh_count)
    2. Choosing 2 from `2^{n−1}` gives `C(2^{n−1}, 2) = 2^{2n−3} − 2^{n−2}`
-/
theorem triple_count_eq (χ : AdditiveChar F) (G : F → F) (n : ℕ)
    (hAB : IsAlmostBent χ G n) (hn : 2 ≤ n) (hn_odd : Odd n)
    (hparseval : ∀ b : F, b ≠ 0 →
      ∑ a : F, (WalshCoeff χ G a b) ^ 2 = (2 : ℤ) ^ (2 * n))
    (b : F) (hb : b ≠ 0) :
    Nat.choose (walshNonzeroCount χ G b) 2 = 2 ^ (2 * n - 3) - 2 ^ (n - 2) := by
  have h1 := AB_nonzero_walsh_count χ G n hAB hparseval (by omega) b hb
  rw [h1]
  exact choose_pow_two_eq n hn

end TripleCount

end