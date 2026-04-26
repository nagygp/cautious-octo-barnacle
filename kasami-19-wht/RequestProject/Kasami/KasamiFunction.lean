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
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-- The Kasami function: `F(b) = b^d` where `d = kasamiExp k`. -/
def kasamiF (n k : ℕ) : F2n n → F2n n :=
  F2n.powMap n (kasamiExp k)

/-- P₂: `F(b) = b^{4^k - 2^k + 1}` (definitional). -/
theorem kasami_P2 (n k : ℕ) (b : F2n n) :
    kasamiF n k b = b ^ (kasamiExp k) := by
  rfl

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

/-! ### Walsh transform at 0 -/

/-- The Walsh transform of the Kasami function at `a = 0` is 0.
    Since `x ↦ x^d` is a bijection, `∑_x χ(x^d) = ∑_x χ(x) = 0`. -/
theorem wht_kasamiF_zero (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    wht (kasamiF n k) 0 = 0 := by
  simp only [wht, zero_mul, zero_add]
  have hbij := kasamiExp_permutation k n hk hn hn_odd hgcd
  have : ∑ x : F2n n, chi n (kasamiF n k x) = ∑ x : F2n n, chi n x := by
    exact Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun x => chi n x)
  rw [this]
  exact chi_sum_all_zero hn

/-! ### Almost bent property -/

/-- **The Kasami function is almost bent** when `gcd(k,n) = 1` and `n` is odd.
    This is the deep result from Kasami (1971) / Canteaut-Charpin-Dobbertin (2000).

    The proof decomposes into two cases:
    - For `a = 0`: `W_f(0) = 0` since `x ↦ x^d` is a bijection (proved above).
    - For `a ≠ 0`: The deep algebraic result using quadratic form rank analysis
      over F_2, the CCD factorization connecting the Kasami derivative to linearized
      polynomials, and the kernel dimension theory.

For `a ≠ 0`, the Walsh transform squared of the Kasami function is either 0 or `2^(n+1)`.
    This is the deep algebraic part of the Kasami AB theorem.
    Proof requires CCD factorization and quadratic form rank analysis. -/
theorem wht_kasamiF_sq_nonzero (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (a : F2n n) (ha : a ≠ 0) :
    wht (kasamiF n k) a ^ 2 = 0 ∨ wht (kasamiF n k) a ^ 2 = (2 ^ (n + 1) : ℤ) := by
  sorry

theorem kasami_is_ab (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    IsAlmostBent (kasamiF n k) := by
  intro a
  by_cases ha : a = 0
  · left; subst ha; simp [wht_kasamiF_zero n k hk hn hn_odd hgcd]
  · exact wht_kasamiF_sq_nonzero n k hk hn hn_odd hgcd a ha

end
end Kasami
