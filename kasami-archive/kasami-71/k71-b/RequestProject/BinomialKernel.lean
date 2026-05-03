/-
  Tasks 2 & 3: Algebraic Reduction and Root Counting for the
  Bracken-McGuire binomial.

  Following pages 9-10 of arXiv:0803.3781:
  - Divide Δ_u f(x) = 0 by u^d and substitute y = x/u
  - Obtain a linearized polynomial L(y) = y^(2^k) + A·y + B = 0
  - Prove L(y) has at most 2 roots, hence kernel dimension ≤ 1
-/
import Mathlib
import RequestProject.Defs
import RequestProject.GoldAPN

set_option maxHeartbeats 1600000

open Polynomial Finset

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Task 2: Algebraic Reduction (Part A)

The derivative of the second term ω·x^(2^(ik) + 2^(tk+s)):

Expanding using char 2 Frobenius and cancelling diagonal terms yields:
  x^(2^(ik)) · u^(2^(tk+s)) + u^(2^(ik)) · x^(2^(tk+s))
-/

theorem second_term_derivative (x u : F) (i t s k : ℕ) (ω : F) :
    deltaDerivative (fun x => ω * x ^ (2 ^ (i * k) + 2 ^ (t * k + s))) u x =
    ω * (x ^ (2 ^ (i * k)) * u ^ (2 ^ (t * k + s)) +
         u ^ (2 ^ (i * k)) * x ^ (2 ^ (t * k + s))) := by
  unfold deltaDerivative;
  have h_expand : (x + u) ^ (2 ^ (i * k) + 2 ^ (t * k + s)) = (x ^ (2 ^ (i * k)) + u ^ (2 ^ (i * k))) * (x ^ (2 ^ (t * k + s)) + u ^ (2 ^ (t * k + s))) := by
    rw [ pow_add, add_pow_char_pow, add_pow_char_pow ];
  grind

/-
The full derivative of the Bracken-McGuire binomial:
    Δ_u f(x) = u^(2^k)·x + u·x^(2^k)
             + ω·(x^(2^(ik))·u^(2^(tk+s)) + u^(2^(ik))·x^(2^(tk+s)))
-/
theorem binomial_derivative (x u : F) (k i t s : ℕ) (ω : F) :
    deltaDerivative (brackenMcGuireBinomial k i t s ω) u x =
    (u ^ (2 ^ k) * x + u * x ^ (2 ^ k)) +
    ω * (x ^ (2 ^ (i * k)) * u ^ (2 ^ (t * k + s)) +
         u ^ (2 ^ (i * k)) * x ^ (2 ^ (t * k + s))) := by
  convert congr_arg₂ ( · + · ) ( gold_apn x u k ) ( second_term_derivative x u i t s k ω ) using 1;
  unfold deltaDerivative brackenMcGuireBinomial goldFunction; ring;

/-! ## Task 3: Root Counting (Part B)

A linearized polynomial over GF(2^n) of degree 2^k has at most 2^k roots.
For the Bracken-McGuire binomial, the order condition on ω ensures the
resulting polynomial is nonzero, giving the root bound.
-/

/-- Key auxiliary: a nonzero polynomial of natDegree d over an integral domain
    has at most d roots. -/
lemma roots_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) : p.roots.card ≤ p.natDegree :=
  Polynomial.card_roots' p

/-
The substitution y = x · u⁻¹ is a bijection F → F when u ≠ 0.
-/
lemma subst_bijective (u : F) (hu : u ≠ 0) :
    Function.Bijective (fun x : F => x * u⁻¹) := by
  exact ⟨ fun x y h => by simpa [ hu ] using h, fun x => ⟨ x * u, by simp +decide [ hu ] ⟩ ⟩

/-- **Theorem 3 (Bracken-McGuire)**: For the binomial
    f(x) = x^(2^k+1) + ω·x^(2^(ik) + 2^(tk+s))
    over F_{2^n}, if ω has multiplicative order 2^(2k) + 2^k + 1,
    then for every nonzero u, the kernel of Δ_u f has at most 2 elements. -/
theorem binomial_kernel_small (k i t s n : ℕ) (ω : F) (u : F)
    (hu : u ≠ 0)
    (hcard : Fintype.card F = 2 ^ n)
    (horder : orderOf ω = 2 ^ (2 * k) + 2 ^ k + 1)
    (hk : 0 < k) (hn : 0 < n) :
    ∀ (S : Finset F), (↑S : Set F) ⊆ deltaKernel (brackenMcGuireBinomial k i t s ω) u →
      S.card ≤ 2 := by
  sorry

end