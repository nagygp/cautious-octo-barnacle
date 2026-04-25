/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Function

Defines the Kasami power function `F(b) = b^d` where `d = 4^k - 2^k + 1`.

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-- The Kasami function: `F(b) = b^d` where `d = kasamiExp k`. -/
def kasamiF (n k : ℕ) : F2n n → F2n n :=
  F2n.powMap n (kasamiExp k)

/-- `F(0) = 0`. -/
@[simp]
theorem kasamiF_zero (n k : ℕ) : kasamiF n k 0 = 0 := by
  have hd : kasamiExp k ≠ 0 := Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)
  simp [kasamiF, F2n.powMap, zero_pow hd]

/-- `F(1) = 1`. -/
@[simp]
theorem kasamiF_one (n k : ℕ) : kasamiF n k 1 = 1 := by
  simp [kasamiF, F2n.powMap]

/-- **The Kasami function is almost bent** when `gcd(k,n) = 1` and `n` is odd. -/
theorem kasami_is_ab (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    IsAlmostBent (kasamiF n k) := by
  sorry

end
end Kasami
