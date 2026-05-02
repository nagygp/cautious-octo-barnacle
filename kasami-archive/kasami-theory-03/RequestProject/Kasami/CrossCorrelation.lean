/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cross-Correlation and Delta Character Sums

This module relates the character sums over the Kasami difference set
to Walsh-Hadamard transform values.

## Main results
- `weightedCharSum`: the sum ∑_b χ(c * g(b)) where g generates Δ
- `deltaCharSum_eq_weightedCharSum_of_injective`: when g is injective, these agree
- `autoCorr`: the autocorrelation function C_F(a, c)

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.DifferenceSet

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

set_option maxHeartbeats 800000

/-! ### Weighted character sum over all elements -/

/-- The weighted character sum: `S'(c) = ∑_b χ(c * g(b))` where `g = kasamiDeltaGen`. -/
def weightedCharSum (n k : ℕ) (c : F2n n) : ℤ :=
  ∑ b : F2n n, chi n (c * kasamiDeltaGen n k b)

/-- Expanding the weighted character sum. -/
theorem weightedCharSum_expand (n k : ℕ) (c : F2n n) :
    weightedCharSum n k c =
    ∑ b : F2n n, chi n (c * kasamiF n k b) * chi n (c * kasamiF n k (b + 1)) * chi n c := by
  unfold weightedCharSum kasamiDeltaGen
  congr 1; ext b
  rw [show c * (kasamiF n k b + kasamiF n k (b + 1) + 1) =
    c * kasamiF n k b + c * kasamiF n k (b + 1) + c * 1 by ring]
  rw [mul_one, chi_add, chi_add]

/-- When kasamiDeltaGen is injective, deltaCharSum = weightedCharSum. -/
theorem deltaCharSum_eq_weightedCharSum_of_injective (n k : ℕ) (c : F2n n)
    (hinj : Function.Injective (kasamiDeltaGen n k)) :
    deltaCharSum n k c = weightedCharSum n k c := by
  unfold deltaCharSum weightedCharSum kasamiDelta
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact hinj hab

/-! ### Autocorrelation function -/

/-- The autocorrelation of the character sum:
    `C_F(a, c) = ∑_x χ(c*(F(x+a) + F(x)))` -/
def autoCorr (n k : ℕ) (a c : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (c * (kasamiF n k (x + a) + kasamiF n k x))

/-- The autocorrelation at a = 0 is 2^n. -/
theorem autoCorr_zero (n k : ℕ) (hn : n ≠ 0) (c : F2n n) :
    autoCorr n k 0 c = 2 ^ n := by
  unfold autoCorr
  simp [kasamiF, F2n.powMap, F2n.add_self, chi_zero, F2n.card n hn]

/-! ### Derivative distribution -/

/-- The number of solutions to `F(x+a) + F(x) = b`. -/
def derivCount (n k : ℕ) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card

/-! ### WHT convolution -/

/-- The WHT convolution sum at `c`. -/
def whtConvolution {n : ℕ} (f : F2n n → F2n n) (c : F2n n) : ℤ :=
  ∑ a : F2n n, wht f a * wht f (a + c)

end
end Kasami
