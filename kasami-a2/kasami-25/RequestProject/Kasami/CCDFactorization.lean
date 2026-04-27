/-
# CCD (Canteaut-Charpin-Dobbertin) Factorization

Key algebraic identities for the Kasami exponent d = 4^k - 2^k + 1.

## References
- Canteaut, Charpin, Dobbertin (2000), SIAM J. Discrete Math. 13(1), 105-138
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiFunction

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 400000

/-! ### Key number-theoretic identity -/

/-- `d * (2^k + 1) = 2^(3*k) + 1` where `d = 4^k - 2^k + 1`. -/
theorem kasamiExp_mul_identity (k : ℕ) :
    kasamiExp k * (2^k + 1) = 2^(3*k) + 1 := by
  unfold kasamiExp
  have h4 : (4 : ℕ)^k = (2^k)^2 := by
    rw [show (4 : ℕ) = 2^2 from by norm_num, ← pow_mul]; ring_nf
  have h3k : (2 : ℕ)^(3*k) = (2^k)^3 := by rw [← pow_mul]; ring_nf
  have h2k : 2^k ≤ 4^k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [h4] at h2k ⊢; rw [h3k]; zify [h2k]; ring

/-! ### Freshman's dream in characteristic 2 -/

/-- In characteristic 2, `(a + b)^(2^k) = a^(2^k) + b^(2^k)`. -/
theorem char2_add_pow {n : ℕ} (a b : F2n n) (k : ℕ) :
    (a + b) ^ (2^k) = a ^ (2^k) + b ^ (2^k) :=
  add_pow_char_pow a b 2 k

/-! ### Frobenius fixed point identity -/

/-- In F_{2^n}, every element satisfies `x^(2^n) = x`. -/
theorem F2n_frobenius {n : ℕ} (hn : n ≠ 0) (x : F2n n) : x ^ (2^n) = x := by
  have hcard : Fintype.card (F2n n) = 2^n := F2n.card n hn
  rw [← hcard]
  exact FiniteField.pow_card x

end
end Kasami
