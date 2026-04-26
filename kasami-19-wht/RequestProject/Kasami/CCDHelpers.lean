/-
# CCD Helper Lemmas

Pure algebraic lemmas in characteristic 2 needed for the CCD factorization.
-/

import Mathlib
import RequestProject.Kasami.Basic

namespace Kasami

open scoped BigOperators
noncomputable section

variable {n : ℕ}

/-! ### Char 2 factorization of sum of (2^k+1)-powers -/

/-- In char 2: `(a+b)*(a^(2^k)+b^(2^k)) = a^(2^k+1) + b^(2^k+1) + a*b^(2^k) + a^(2^k)*b`. -/
theorem char2_expand_prod (a b : F2n n) (k : ℕ) :
    (a + b) * (a ^ (2^k) + b ^ (2^k)) =
    a ^ (2^k + 1) + b ^ (2^k + 1) + a * b ^ (2^k) + a ^ (2^k) * b := by
  ring

/-
In char 2: `a^(2^k+1) + b^(2^k+1) = (a+b)^(2^k+1) + a*b^(2^k) + a^(2^k)*b`.
    This uses the Freshman's dream: `(a+b)^(2^k) = a^(2^k) + b^(2^k)`.
-/
theorem char2_sum_powers (a b : F2n n) (k : ℕ) :
    a ^ (2^k + 1) + b ^ (2^k + 1) =
    (a + b) ^ (2^k + 1) + a * b ^ (2^k) + a ^ (2^k) * b := by
  -- By expanding $(a + b)^{2^k + 1}$ using the Freshman's dream, we get $(a + b)^{2^k + 1} = (a + b)(a^{2^k} + b^{2^k})$.
  have h_expand : (a + b) ^ (2 ^ k + 1) = (a + b) * (a ^ (2 ^ k) + b ^ (2 ^ k)) := by
    have h_expand : ∀ (x y : F2n n) (k : ℕ), (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
      exact?;
    rw [ pow_succ', h_expand ];
  grind

/-! ### Gold function derivative -/

/-
The derivative of the Gold function `x^(2^m+1)` at direction `z`:
    `D_z(x^(2^m+1)) = x^(2^m)*z + x*z^(2^m) + z^(2^m+1)`.
-/
theorem gold_deriv (x z : F2n n) (m : ℕ) :
    (x + z) ^ (2^m + 1) + x ^ (2^m + 1) =
    x ^ (2^m) * z + x * z ^ (2^m) + z ^ (2^m + 1) := by
  have h_freshman : (x + z) ^ 2 ^ m = x ^ 2 ^ m + z ^ 2 ^ m := by
    exact?;
  grind +qlia

/-
The second derivative of the Gold function at directions `(z, 1)`:
    `D_1 D_z (x^(2^m+1)) = z^(2^m) + z`, independent of `x`.
-/
theorem gold_second_deriv (x z : F2n n) (m : ℕ) :
    ((x + z + 1) ^ (2^m + 1) + (x + z) ^ (2^m + 1)) +
    ((x + 1) ^ (2^m + 1) + x ^ (2^m + 1)) =
    z ^ (2^m) + z := by
  convert congr_arg₂ ( · + · ) ( gold_deriv ( x + z ) 1 m ) ( gold_deriv x 1 m ) using 1 ; ring;
  rw [ add_pow_char_pow ] ; ring;
  grobner

/-! ### Norm factorization -/

/-
The bilinear form `B(a,b) = a*b^(2^k) + a^(2^k)*b` factors as
    `B(a,b) = (a/b)^(2^k) * b^(2^k+1) + (a/b) * b^(2^k+1)` for b ≠ 0,
    i.e., `B(a,b) = b^(2^k+1) * M_k(a/b)` where `M_k(r) = r^(2^k) + r`.
-/
theorem bilinear_form_factor (a b : F2n n) (k : ℕ) (hb : b ≠ 0) :
    a * b ^ (2^k) + a ^ (2^k) * b =
    b ^ (2^k + 1) * (((a / b) ^ (2^k)) + (a / b)) := by
  have h_eq : a = (a / b) * b := by
    rw [ div_mul_cancel₀ _ hb ];
  convert congr_arg ( · * b ^ 2 ^ k + · ^ 2 ^ k * b ) h_eq using 1 ; ring;
  simp +decide [ hb, mul_assoc, mul_comm b ]

end
end Kasami