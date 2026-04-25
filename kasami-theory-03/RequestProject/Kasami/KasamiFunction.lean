/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Function

Defines the Kasami power function `F(b) = b^d` where `d = 4^k - 2^k + 1`.

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
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

/-- P₂: `F(b) = b^{4^k - 2^k + 1}` (definitional). -/
theorem kasami_P2 (n k : ℕ) (b : F2n n) :
    kasamiF n k b = b ^ (kasamiExp k) := rfl

/-- `F(0) = 0`. -/
@[simp]
theorem kasamiF_zero (n k : ℕ) : kasamiF n k 0 = 0 := by
  have hd : kasamiExp k ≠ 0 := Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)
  simp [kasamiF, F2n.powMap, zero_pow hd]

/-- `F(1) = 1`. -/
@[simp]
theorem kasamiF_one (n k : ℕ) : kasamiF n k 1 = 1 := by
  simp [kasamiF, F2n.powMap]

/-! ### Derivative of the Kasami function -/

/-- The derivative `D_a F(x) = F(x + a) + F(x)`. -/
def kasamiDeriv (n k : ℕ) (a : F2n n) : F2n n → F2n n :=
  fun x => kasamiF n k (x + a) + kasamiF n k x

/-- The function `b ↦ F(b) + F(b+1) + 1` that generates the difference set Δ. -/
def kasamiDeltaGen (n k : ℕ) : F2n n → F2n n :=
  fun b => kasamiF n k b + kasamiF n k (b + 1) + 1

/-! ### Almost bent property -/

/-- **The Kasami function is almost bent** when `gcd(k,n) = 1` and `n` is odd.
    This is the deep result from Kasami (1971) / Canteaut-Charpin-Dobbertin (2000). -/
theorem kasami_is_ab (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    IsAlmostBent (kasamiF n k) := by
  sorry

end
end Kasami
