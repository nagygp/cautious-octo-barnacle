import RequestProject.Foundations.KasamiAxKatz
import RequestProject.APN.Defs
import Mathlib

/-!
# Foundations, Layer AK2 — the base-2 digit-sum engine, towards Stickelberger / CCD

This module implements the **next layer of the Ax–Katz / McEliece sub-path for
input (A)** laid out in `Docs/VanishFutureDirections.md` §7.

Layer AK1 (`KasamiAxKatz.lean`) introduced the binary digit sum
`binDigitSum n = (Nat.digits 2 n).sum` (`= s₂(n)`, the number of `1`-bits of `n`)
and the two `2`-adic valuation identities it controls (Legendre / Kummer in base
`2`).  The Stickelberger congruence (Layer AK3) expresses the `2`-adic valuation
of a Gauss sum `g(χ)` through `s₂` of the exponent of `χ`, and the
Canteaut–Charpin–Dobbertin specialization (Layer AK4) then evaluates `s₂` at the
**Kasami exponent** `d k = 2^{2k} − 2^k + 1`.  Both consume the elementary
**arithmetic of the digit sum**, which this layer develops in full (sorry-free):

* the bit-recursion `s₂(2n) = s₂(n)`, `s₂(2n+1) = s₂(n)+1`
  (`binDigitSum_two_mul`, `binDigitSum_two_mul_add_one`);
* the bound `s₂(n) ≤ n` and the vanishing criterion `s₂(n) = 0 ↔ n = 0`
  (`binDigitSum_le_self`, `binDigitSum_eq_zero_iff`);
* **subadditivity** `s₂(a+b) ≤ s₂(a) + s₂(b)` (the carry inequality, the engine of
  the McEliece weight congruence) (`binDigitSum_add_le`);
* the values on the "extreme" arguments `s₂(2^k) = 1`, `s₂(2^k − 1) = k`
  (`binDigitSum_two_pow`, `binDigitSum_two_pow_sub_one`);
* the **Kasami-exponent digit sum** `s₂(d k) = k + 1`
  (`binDigitSum_kasami_exponent`) — the concrete arithmetic input that the CCD /
  McEliece weight-divisibility bound (Layer AK4) reads off to produce `hdiv` for
  general `k`.

## Scope

This layer is sorry-free and completes the **digit-sum engine** of the route.
The two *deep* steps that consume it — the Stickelberger congruence for Gauss
sums (AK3) and the full Ax–Katz `p^μ`-divisibility / CCD specialization (AK4) —
require machinery absent from Mathlib (the `2`-adic valuation of Gauss sums; the
iterated Chevalley–Warning estimate) and remain open; they are deliberately not
axiomatized.

## Sources

McEliece, *Weight congruences for p-ary cyclic codes* (Discrete Math., 1972);
Ax (1964) / Katz (1971); Canteaut–Charpin–Dobbertin (SIAM J. Discrete Math.,
2000); Lidl–Niederreiter, *Finite Fields*, Ch. 6 (digit sums and Gauss-sum
valuations).
-/

namespace Vanish.Foundations

open Finset BigOperators

/-! ## 1. Bit recursion for the binary digit sum -/

/-
`s₂(0) = 0`.
-/
@[simp] theorem binDigitSum_zero : binDigitSum 0 = 0 := rfl

/-
**Bit recursion (even case):** `s₂(2n) = s₂(n)`.  A trailing `0`-bit does not
change the digit sum.
-/
theorem binDigitSum_two_mul (n : ℕ) : binDigitSum (2 * n) = binDigitSum n := by
  unfold binDigitSum;
  cases n <;> norm_num

/-
**Bit recursion (odd case):** `s₂(2n+1) = s₂(n) + 1`.  A trailing `1`-bit adds
one to the digit sum.
-/
theorem binDigitSum_two_mul_add_one (n : ℕ) :
    binDigitSum (2 * n + 1) = binDigitSum n + 1 := by
  unfold binDigitSum; rw [ Nat.add_comm, Nat.digits_eq_cons_digits_div ] ;
  · norm_num [ add_comm, Nat.add_mul_div_left ];
  · decide;
  · grind

/-! ## 2. Elementary bounds -/

/-
`s₂(n) ≤ n`: each bit contributes at most its place value.
-/
theorem binDigitSum_le_self (n : ℕ) : binDigitSum n ≤ n := by
  convert Nat.digit_sum_le _ _ using 1

/-
`s₂(n) = 0 ↔ n = 0`.
-/
theorem binDigitSum_eq_zero_iff (n : ℕ) : binDigitSum n = 0 ↔ n = 0 := by
  induction' n using Nat.strongRecOn with n ih;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ binDigitSum_two_mul, binDigitSum_two_mul_add_one ];
  cases k <;> simp_all +decide

/-! ## 3. Subadditivity — the carry inequality -/

/-
**Subadditivity of the binary digit sum:** `s₂(a + b) ≤ s₂(a) + s₂(b)`.  The
defect `s₂(a) + s₂(b) − s₂(a+b)` is exactly the number of carries when adding `a`
and `b` in base `2` (Kummer), the quantity governing the McEliece weight
congruence.
-/
theorem binDigitSum_add_le (a b : ℕ) :
    binDigitSum (a + b) ≤ binDigitSum a + binDigitSum b := by
  induction' n : a + b using Nat.strong_induction_on with n ih generalizing a b;
  subst n;
  rcases Nat.even_or_odd' a with ⟨ a', rfl | rfl ⟩ <;> rcases Nat.even_or_odd' b with ⟨ b', rfl | rfl ⟩;
  · simp_all +decide [ ← mul_add, binDigitSum_two_mul ];
    exact if h : a' + b' = 0 then by aesop else ih _ ( by omega ) _ _ rfl;
  · simp_all +arith +decide [ binDigitSum_two_mul, binDigitSum_two_mul_add_one ];
    rw [ show 2 * a' + 2 * b' + 1 = 2 * ( a' + b' ) + 1 by ring, binDigitSum_two_mul_add_one ];
    grind;
  · simp_all +arith +decide [ binDigitSum_two_mul, binDigitSum_two_mul_add_one ];
    rw [ show 2 * a' + 2 * b' + 1 = 2 * ( a' + b' ) + 1 by ring, binDigitSum_two_mul_add_one ];
    grind;
  · simp +arith +decide [ * ];
    rw [ show 2 * a' + 2 * b' + 2 = 2 * ( a' + b' + 1 ) by ring, binDigitSum_two_mul ];
    convert le_trans ( ih ( a' + b' + 1 ) ( by linarith ) ( a' ) ( b' + 1 ) ( by linarith ) ) _ using 1;
    simp +arith +decide [ binDigitSum_two_mul_add_one ];
    convert le_trans ( ih ( b' + 1 ) ( by linarith ) b' 1 ( by linarith ) ) _ using 1 ; simp +arith +decide

/-! ## 4. Values on extreme arguments -/

/-
`s₂(2^k) = 1`: a single `1`-bit.
-/
theorem binDigitSum_two_pow (k : ℕ) : binDigitSum (2 ^ k) = 1 := by
  induction k <;> simp_all +decide [ pow_succ', binDigitSum_two_mul ]

/-
`s₂(2^k − 1) = k`: the all-ones word of length `k`.
-/
theorem binDigitSum_two_pow_sub_one (k : ℕ) : binDigitSum (2 ^ k - 1) = k := by
  induction k <;> simp_all +decide [ Nat.pow_succ' ];
  rename_i k hk;
  rw [ show 2 * 2 ^ k - 1 = 2 * ( 2 ^ k - 1 ) + 1 by zify ; norm_num ; ring, binDigitSum_two_mul_add_one, hk ]

/-
**Shift invariance:** `s₂(2^k · m) = s₂(m)`.  Appending `k` trailing
`0`-bits does not change the digit sum.  (Iterate `binDigitSum_two_mul`.)
-/
theorem binDigitSum_two_pow_mul (k m : ℕ) :
    binDigitSum (2 ^ k * m) = binDigitSum m := by
  exact Nat.recOn k ( by norm_num ) fun n ihn => by rw [ pow_succ', mul_assoc, @Vanish.Foundations.binDigitSum_two_mul ] ; aesop;

/-! ## 5. The Kasami-exponent digit sum -/

/-
**The Kasami-exponent digit sum: `s₂(d k) = k + 1`.**  Writing the Kasami
exponent `d k = 2^{2k} − 2^k + 1 = 2^k·(2^k − 1) + 1`, its binary expansion is
the all-ones block of length `k` shifted up by `k` (contributing `k` bits) plus
the unit bit (contributing `1`), for a total digit sum `k + 1`.  This is the
concrete arithmetic input that the Canteaut–Charpin–Dobbertin / McEliece weight
divisibility (Layer AK4) reads off.
-/
theorem binDigitSum_kasami_exponent (k : ℕ) :
    binDigitSum (CollisionAnalysis.d k) = k + 1 := by
  rcases k with ( _ | k ) <;> simp_all +decide [ CollisionAnalysis.d ];
  convert congr_arg ( · + 1 ) ( binDigitSum_two_pow_mul k ( 2 ^ ( k + 1 ) - 1 ) ) using 1;
  · rw [ show 2 ^ ( 2 * ( k + 1 ) ) - 2 ^ ( k + 1 ) = 2 ^ k * ( 2 ^ ( k + 1 ) - 1 ) * 2 by
          exact Nat.sub_eq_of_eq_add <| by zify ; norm_num ; ring; ];
    convert binDigitSum_two_mul_add_one ( 2 ^ k * ( 2 ^ ( k + 1 ) - 1 ) ) using 1;
    ring_nf;
  · rw [ binDigitSum_two_pow_sub_one ]

end Vanish.Foundations