import Mathlib
import CodeTheoryCryptoEquiv.CodingTheory.Krawtchouk

/-!
# Krawtchouk reciprocity and orthogonality

This module continues the coding-theory development of
`CodeTheoryCryptoEquiv/CodingTheory/Krawtchouk.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977 (Ch. 5).

It proves the two structural relations of the Krawtchouk polynomials
`K_k(x; n, q)` that the Delsarte linear-programming bound rests on:

* the **reciprocity relation** (MacWilliams–Sloane, Ch. 5, eq. (53))
  `(q-1)^i C(n,i) K_k(i) = (q-1)^k C(n,k) K_i(k)`; and
* the **orthogonality relation** (MacWilliams–Sloane, Ch. 5, Thm 16)
  `Σ_{i=0}^{n} C(n,i) (q-1)^i K_k(i) K_l(i) = q^n (q-1)^k C(n,k) [k = l]`.

Both are obtained from the generating function
`Σ_k K_k(x) z^k = (1 + (q-1) z)^{n-x} (1 - z)^x`
(`CodingTheory.krawtchouk_generating_function`).

## Main results

* `krawtchouk_reciprocity` — the reciprocity relation above.
* `krawtchouk_orthogonality` — the orthogonality relation above.

## Auxiliary results

* `choose_trinomial` — the trinomial revision identity for binomial coefficients.
* `krawtchouk_master_poly` — the master polynomial identity that powers the
  orthogonality relation.
* `krawtchouk_orthogonality_scalar` — the `coeff_k`-extracted scalar form.
-/

namespace CodingTheory

open Finset Polynomial

/-
**Trinomial revision identity** for binomial coefficients:
`C(n,i) C(i,j) C(n-i,k-j) = C(n,k) C(k,j) C(n-k,i-j)` for `j ≤ i`, `j ≤ k`,
`i ≤ n`, `k ≤ n`.  (Both sides vanish together when `k - j > n - i`.)
-/
theorem choose_trinomial (n i k j : ℕ) (hi : i ≤ n) (hk : k ≤ n)
    (hji : j ≤ i) (hjk : j ≤ k) :
    n.choose i * i.choose j * (n - i).choose (k - j)
      = n.choose k * k.choose j * (n - k).choose (i - j) := by
  have h1 : n.choose i * i.choose j = n.choose j * (n - j).choose (i - j) :=
    Nat.choose_mul hji
  have h2 : n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) :=
    Nat.choose_mul hjk
  have h3 : (n - j).choose (i - j) * (n - i).choose (k - j) = (n - j).choose (k - j) * (n - k).choose (i - j) := by
    have h_trinom : (n - j).choose (i - j) * (n - i).choose (k - j) = (n - j).choose (i - j + (k - j)) * (i - j + (k - j)).choose (i - j) := by
      simp +decide [ Nat.add_sub_of_le ( by omega : i ≤ n ), Nat.add_sub_of_le ( by omega : k ≤ n ), Nat.choose_mul ];
      exact Or.inl ( by rw [ show n - j - ( i - j ) = n - i by omega ] )
    rw [ h_trinom, Nat.choose_symm_add ];
    rw [ Nat.choose_mul ];
    · grind;
    · exact Nat.le_add_left _ _;
  grind

/-
**Master polynomial identity.** For every integer `z`, as a polynomial in `X`,
`Σ_i C(n,i)(q-1)^i ((1+(q-1)z)^{n-i}(1-z)^i) (1+(q-1)X)^{n-i}(1-X)^i
   = q^n (1 + (q-1)z·X)^n`.
This is the binomial theorem applied to the base
`(1+(q-1)z)(1+(q-1)X) + (q-1)(1-z)(1-X) = q(1+(q-1)z X)`.
-/
theorem krawtchouk_master_poly (q n : ℕ) (z : ℤ) :
    ∑ i ∈ Finset.range (n + 1),
        Polynomial.C ((n.choose i : ℤ) * ((q : ℤ) - 1) ^ i *
            ((1 + ((q : ℤ) - 1) * z) ^ (n - i) * (1 - z) ^ i)) *
          ((1 + ((q : ℤ) - 1) • Polynomial.X) ^ (n - i) * (1 - Polynomial.X) ^ i)
      = Polynomial.C ((q : ℤ) ^ n) *
          (1 + Polynomial.C (((q : ℤ) - 1) * z) * Polynomial.X) ^ n := by
  convert add_pow _ _ _ using 2 ; norm_num ; ring;
  rw [ add_pow ];
  rotate_left;
  rotate_left;
  exact ( Polynomial.C ( ( q : ℤ ) - 1 ) * ( 1 - Polynomial.X ) ) * ( 1 - Polynomial.C ( z : ℤ ) );
  exact ( 1 + Polynomial.C ( ( q : ℤ ) * z - z ) ) * ( 1 + Polynomial.C ( ( q : ℤ ) - 1 ) * Polynomial.X );
  exact n;
  · rw [ add_comm ] ; refine' Finset.sum_congr rfl fun i hi => _ ; norm_num [ mul_pow, ← mul_assoc, ← Polynomial.C_mul ] ; ring;
  · convert add_pow _ _ _ using 2 ; norm_num ; ring;
    rw [ ← mul_pow ] ; ring

/-
**Orthogonality, scalar form.** For `k ≤ n` and every integer `z`,
`Σ_i C(n,i)(q-1)^i K_k(i) (1+(q-1)z)^{n-i}(1-z)^i = q^n (q-1)^k C(n,k) z^k`.
Obtained by reading the coefficient of `X^k` in `krawtchouk_master_poly`
(using `krawtchouk_eq_coeff` on the left and the binomial expansion on the
right).
-/
theorem krawtchouk_orthogonality_scalar (q n k : ℕ) (hk : k ≤ n) (z : ℤ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℤ) * ((q : ℤ) - 1) ^ i * krawtchouk q n k i *
          ((1 + ((q : ℤ) - 1) * z) ^ (n - i) * (1 - z) ^ i)
      = (q : ℤ) ^ n * ((q : ℤ) - 1) ^ k * (n.choose k : ℤ) * z ^ k := by
  simp +decide [ krawtchouk, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  convert congr_arg ( fun p => Polynomial.coeff p k ) ( krawtchouk_master_poly q n z ) using 1;
  · rw [ Polynomial.finset_sum_coeff, Finset.sum_congr rfl ];
    intro i hi; rw [ Polynomial.coeff_C_mul ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Polynomial.coeff_X_pow ] ;
    convert congr_arg ( fun x : ℤ => ( n.choose i : ℤ ) * ( ( q - 1 : ℤ ) ^ i * ( ( 1 + z * ( q - 1 ) ) ^ ( n - i ) * ( ( 1 - z ) ^ i * x ) ) ) ) ( krawtchouk_eq_coeff q n k i ) using 1;
    · unfold krawtchouk; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    · norm_num [ Polynomial.smul_eq_C_mul ];
  · convert congr_arg ( fun x : ℤ => x * ( q ^ n : ℤ ) ) ( coeff_linear_pow ( ( q - 1 ) * z ) 1 n k ) using 1 ; ring;
    · rw [ coeff_linear_pow ] ; ring;
      rw [ show ( -z + z * q : ℤ ) = z * ( -1 + q ) by ring, mul_pow ] ; ring;
    · convert congr_arg ( fun x : ℤ => x * ( q ^ n : ℤ ) ) ( coeff_linear_pow ( ( q - 1 ) * z ) 1 n k ) using 1;
      rw [ add_comm, Polynomial.coeff_C_mul ] ; norm_num ; ring

/-
**Krawtchouk reciprocity** (MacWilliams–Sloane, Ch. 5):
`(q-1)^i C(n,i) K_k(i) = (q-1)^k C(n,k) K_i(k)`, for `i ≤ n` and `k ≤ n`.
-/
theorem krawtchouk_reciprocity (q n k i : ℕ) (hi : i ≤ n) (hk : k ≤ n) :
    ((q : ℤ) - 1) ^ i * (n.choose i : ℤ) * krawtchouk q n k i
      = ((q : ℤ) - 1) ^ k * (n.choose k : ℤ) * krawtchouk q n i k := by
  simp +decide only [krawtchouk, mul_assoc];
  simp +decide only [mul_left_comm, Finset.mul_sum _ _ _];
  rw [ ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ ( Nat.min_le_left i k ) ) ), ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ ( Nat.min_le_right i k ) ) ) ];
  · refine Finset.sum_congr rfl fun x hx => ?_;
    convert congr_arg ( fun z : ℕ => ( z : ℤ ) * ( -1 ) ^ x * ( q - 1 ) ^ i * ( q - 1 ) ^ ( k - x ) ) ( choose_trinomial n i k x hi hk ( by linarith [ Finset.mem_range.mp hx, min_le_left i k ] ) ( by linarith [ Finset.mem_range.mp hx, min_le_right i k ] ) ) using 1 <;> push_cast [ Nat.cast_choose ] <;> ring;
    rw [ show ( -1 + q : ℤ ) ^ i = ( -1 + q : ℤ ) ^ ( i - x ) * ( -1 + q : ℤ ) ^ x by rw [ ← pow_add, Nat.sub_add_cancel ( by linarith [ Finset.mem_range.mp hx, min_le_left i k, min_le_right i k ] ) ], show ( -1 + q : ℤ ) ^ k = ( -1 + q : ℤ ) ^ ( k - x ) * ( -1 + q : ℤ ) ^ x by rw [ ← pow_add, Nat.sub_add_cancel ( by linarith [ Finset.mem_range.mp hx, min_le_left i k, min_le_right i k ] ) ] ] ; ring;
  · simp +contextual [ Nat.choose_eq_zero_of_lt ];
  · simp +zetaDelta at *;
    exact fun x hx₁ hx₂ => Or.inr <| Or.inl <| Nat.choose_eq_zero_of_lt <| hx₂ hx₁

/-
**Krawtchouk orthogonality** (MacWilliams–Sloane, Ch. 5, Thm 16):
`Σ_{i=0}^{n} C(n,i) (q-1)^i K_k(i) K_l(i) = q^n (q-1)^k C(n,k)` when `k = l`,
and `0` otherwise.
-/
theorem krawtchouk_orthogonality (q n k l : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℤ) * ((q : ℤ) - 1) ^ i *
          krawtchouk q n k i * krawtchouk q n l i
      = if k = l then (q : ℤ) ^ n * ((q : ℤ) - 1) ^ k * (n.choose k : ℤ) else 0 := by
  -- By the polynomial identity, we know that the polynomial on the left-hand side is equal to the polynomial on the right-hand side.
  have h_poly_eq : (∑ i ∈ Finset.range (n + 1), Polynomial.C ((n.choose i : ℤ) * ((q : ℤ) - 1) ^ i * krawtchouk q n k i) * ((1 + ((q : ℤ) - 1) • Polynomial.X) ^ (n - i) * (1 - Polynomial.X) ^ i)) = Polynomial.C ((q : ℤ) ^ n * ((q : ℤ) - 1) ^ k * (n.choose k : ℤ)) * Polynomial.X ^ k := by
    refine' Polynomial.funext fun x => _;
    convert krawtchouk_orthogonality_scalar q n k hk x using 1 <;> norm_num [ Polynomial.eval_finset_sum ];
  convert congr_arg ( fun p => Polynomial.coeff p l ) h_poly_eq using 1;
  · rw [ Polynomial.finset_sum_coeff, Finset.sum_congr rfl ] ; intros ; rw [ Polynomial.coeff_C_mul ] ;
    rw [ ← krawtchouk_eq_coeff ];
  · grind +qlia

end CodingTheory