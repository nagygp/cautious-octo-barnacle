import RequestProject.Walsh.WalshDivisibility
import RequestProject.APN.Defs
import Mathlib

/-!
# Gold/Kasami Quadratic Structure — Walsh Divisibility Layer

## Key Result

For the Gold function `x^{2^k+1}`, the Walsh transform has vanishing
third discrete derivative (algebraic degree 2 in char 2), so
`quadratic_gauss_sum_div` gives `2^{(n+1)/2} | W(a,b)` directly.

For `k = 1`, the Kasami exponent `d(1) = 3 = 2^1 + 1` equals the Gold exponent.
-/

set_option maxHeartbeats 3200000

namespace AutocorrQuadratic

open Finset Fintype BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Layer 0: Third Derivative of Gold Power Vanishes -/

/-- Third derivative of `x^{2^k+1}` vanishes in char 2. -/
theorem third_deriv_gold_zero (k : ℕ) (x y z : F) :
    (x + y + z) ^ (2 ^ k + 1) + (x + y) ^ (2 ^ k + 1) +
    (x + z) ^ (2 ^ k + 1) + (y + z) ^ (2 ^ k + 1) +
    x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) + z ^ (2 ^ k + 1) = 0 := by
  have hfr : ∀ u v : F, (u + v) ^ (2 ^ k + 1) =
      u ^ (2 ^ k + 1) + u ^ (2 ^ k) * v + v ^ (2 ^ k) * u + v ^ (2 ^ k + 1) := by
    intro u v
    rw [pow_succ, add_pow_char_pow_of_commute 2 k (Commute.all u v), add_mul, mul_add, mul_add]; ring
  rw [show x + y + z = (x + y) + z from by ring]
  rw [hfr (x + y) z, hfr x y, hfr x z, hfr y z]
  simp only [add_pow_char_pow_of_commute 2 k (Commute.all x y)]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h4 : (4 : F) = 0 := by
    rw [show (4:F) = 2 + 2 from by norm_num]; exact CharTwo.add_self_eq_zero 2
  ring_nf; simp [h2, h4]

/-! ## Layer 1: Gold Walsh Divisibility -/

/-- The Walsh function has vanishing third derivative for Gold. -/
theorem gold_walsh_third_deriv_zero (a b : F) (k : ℕ) (x y z : F) :
    let Q := fun t => a * t + b * t ^ (2 ^ k + 1)
    Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
    + Q x + Q y + Q z + Q 0 = 0 := by
  simp only
  suffices h : (a * (x + y + z) + a * (x + y) + a * (x + z) + a * (y + z) +
    a * x + a * y + a * z + a * 0) +
    b * ((x + y + z) ^ (2 ^ k + 1) + (x + y) ^ (2 ^ k + 1) +
    (x + z) ^ (2 ^ k + 1) + (y + z) ^ (2 ^ k + 1) +
    x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) + z ^ (2 ^ k + 1) +
    0 ^ (2 ^ k + 1)) = 0 by linear_combination h
  
  have hlin : a * (x + y + z) + a * (x + y) + a * (x + z) + a * (y + z) +
    a * x + a * y + a * z + a * 0 = 0 := by
    ring_nf; simp [show (4:F) = 0 from by
      rw [show (4:F) = 2 + 2 from by norm_num]; exact CharTwo.add_self_eq_zero 2]
  simp only [zero_pow (by positivity : 2 ^ k + 1 ≠ 0), add_zero]
  rw [hlin, zero_add, show (x + y + z) ^ (2 ^ k + 1) + (x + y) ^ (2 ^ k + 1) +
    (x + z) ^ (2 ^ k + 1) + (y + z) ^ (2 ^ k + 1) +
    x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) + z ^ (2 ^ k + 1) = 0 from
    third_deriv_gold_zero k x y z, mul_zero]

/-- **Gold Walsh Divisibility**: `2^{(n+1)/2} | W(a,b)` for `x^{2^k+1}`. -/
theorem gold_walsh_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hodd : Odd n) (a b : F) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh (· ^ (2 ^ k + 1) : F → F) a b := by
  unfold walsh
  apply WalshDivisibility.quadratic_gauss_sum_div hcard hodd
  intro x y z
  have := gold_walsh_third_deriv_zero a b k x y z
  convert this using 1

/-! ## Layer 2: Gold Autocorrelation Divisibility -/

/-- Gold autocorrelation (d=3) third derivative vanishes. -/
theorem gold_autocorr_third_deriv_zero (b u : F) (x y z : F) :
    let Q := fun t => b * ((t + u) ^ 3 + t ^ 3)
    Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
    + Q x + Q y + Q z + Q 0 = 0 := by
  simp only
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf
  have h8 : (8 : F) = 0 := by rw [show (8:F) = 2 * 4 from by norm_num]; rw [h2]; ring
  have h12 : (12 : F) = 0 := by rw [show (12:F) = 2 * 6 from by norm_num]; rw [h2]; ring
  simp [h8, h12]

/-- Gold autocorrelation is divisible by `2^{(n+1)/2}`. -/
theorem gold_autocorr_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hodd : Odd n) (b u : F) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ autocorrScaled (· ^ (3 : ℕ) : F → F) b u := by
  unfold autocorrScaled
  apply WalshDivisibility.quadratic_gauss_sum_div hcard hodd
  intro x y z
  have := gold_autocorr_third_deriv_zero b u x y z
  convert this using 1

/-! ## Layer 3: Gold AB Theorem -/

/-- **Gold AB**: For n odd, `x^{2^k+1}` is Almost Bent. -/
theorem gold_is_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ)
    (hbij : Function.Bijective (· ^ (2 ^ k + 1) : F → F))
    (hodd : Odd n) (hn : n ≥ 1)
    (hapn : IsAPN (· ^ (2 ^ k + 1) : F → F)) :
    IsAB hcard (· ^ (2 ^ k + 1) : F → F) := by
  apply ab_from_moments hcard _ hodd hn
  · exact fun a ha => parseval_perm hcard _ hbij a ha
  · exact fun a ha => fourth_moment_apn hcard (2 ^ k + 1) hbij hapn a ha
  · exact fun a b => gold_walsh_div hcard k hodd a b

end AutocorrQuadratic
