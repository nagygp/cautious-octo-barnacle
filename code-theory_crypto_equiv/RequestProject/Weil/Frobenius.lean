import RequestProject.Weil.CharSum

/-!
# Frobenius and the arithmetic of `𝔽_q`

This module collects the elementary field-arithmetic facts about a finite field `F = 𝔽_q` of
characteristic `p = ringChar F` that the Stepanov route relies on.  None of these are deep — they
are the Frobenius identities and the "every element is a root of `X^q - X`" packaging — but isolating
them keeps the later modules (`Hasse`, `AuxPoly`, `Trace`) readable, and they are exactly the
ingredients of the Stepanov construction's key step `x^q = x`.

## Main statements (skeletons)
* `Weil.Frobenius.pow_card_eq_self` — `x^q = x` for every `x ∈ 𝔽_q`.
* `Weil.Frobenius.frobenius_add` — `(a+b)^p = a^p + b^p` (additivity of Frobenius).
* `Weil.Frobenius.frobenius_pow_iterate_add` — additivity of the iterated Frobenius `x ↦ x^{pⁱ}`.
* `Weil.Frobenius.prod_X_sub_C_eq` — `∏_{a∈𝔽_q} (X - a) = X^q - X` (separability of `X^q - X`).
* `Weil.Frobenius.card_eq_char_pow` — `q = pⁿ` for some `n ≥ 1`, with `n` the degree of `𝔽_q/𝔽_p`.
* `Weil.Frobenius.eval_pow_card_X_sub_X` — every `x` is a root of `X^q - X`.
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil
namespace Frobenius

variable {F : Type*} [Field F] [Fintype F]

/-
`x^q = x` for every element of `𝔽_q`: the defining Frobenius identity of a finite field.
-/
lemma pow_card_eq_self (x : F) : x ^ (Fintype.card F) = x := by
  exact FiniteField.pow_card x

/-
The Frobenius endomorphism `x ↦ x^p` is additive.
-/
lemma frobenius_add (a b : F) :
    (a + b) ^ (ringChar F) = a ^ (ringChar F) + b ^ (ringChar F) := by
  convert add_pow_char a b;
  constructor;
  · intro h p hp hF
    have := add_pow_char a b
    aesop;
  · intro h;
    convert h ( ringChar F );
    exact ⟨ CharP.char_is_prime F ( ringChar F ) ⟩

/-
The iterated Frobenius `x ↦ x^{pⁱ}` is additive.
-/
lemma frobenius_pow_iterate_add (i : ℕ) (a b : F) :
    (a + b) ^ (ringChar F ^ i) = a ^ (ringChar F ^ i) + b ^ (ringChar F ^ i) := by
  induction' i with i ih generalizing a b <;> simp_all +decide [ add_pow_char, pow_succ, pow_mul ];
  grind +suggestions

/-
`X^q - X` is separable and splits completely: `∏_{a∈𝔽_q} (X - a) = X^q - X`.
-/
lemma prod_X_sub_C_eq :
    (∏ a : F, (Polynomial.X - Polynomial.C a))
      = Polynomial.X ^ (Fintype.card F) - Polynomial.X := by
  refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
  exact Finset.univ;
  · convert Polynomial.degree_sub_lt _ _ _ <;> norm_num [ Polynomial.degree_prod, Polynomial.degree_X_pow_sub_C ];
    · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num;
      exact Fintype.one_lt_card;
    · exact Finset.prod_ne_zero_iff.mpr fun x _ => Polynomial.X_sub_C_ne_zero x;
    · rw [ Polynomial.leadingCoeff_prod, Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num;
      exact Fintype.one_lt_card;
  · intro x; rw [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ x ) ] ; simp +decide [ pow_card_eq_self ] ;

/-
The cardinality of `𝔽_q` is a positive power of the characteristic `p`, `q = pⁿ` with `n ≥ 1`;
here `n = [𝔽_q : 𝔽_p]` is the degree of the field over its prime subfield.
-/
lemma card_eq_char_pow :
    ∃ n : ℕ, 1 ≤ n ∧ Fintype.card F = (ringChar F) ^ n := by
  obtain ⟨ n, hn ⟩ := FiniteField.card F ( ringChar F );
  exact ⟨ n, n.2, hn.2 ⟩

/-
Every element of `𝔽_q` is a root of `X^q - X`.
-/
lemma eval_pow_card_X_sub_X (x : F) :
    (Polynomial.X ^ (Fintype.card F) - Polynomial.X : F[X]).eval x = 0 := by
  simp +decide [ FiniteField.pow_card ]

end Frobenius
end Weil