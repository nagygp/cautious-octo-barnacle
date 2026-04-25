/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Exponent

Number-theoretic properties of the Kasami exponent `d = 4^k - 2^k + 1`.

## Main definitions
- `kasamiExp k` — the Kasami exponent `4^k - 2^k + 1`

## Main results
- `kasamiExp_pos`: `d > 0`
- `kasamiExp_gcd`: `gcd(d, 2^n - 1) = 1` when `gcd(k, n) = 1` and `n` is odd

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
-/
import Mathlib
import RequestProject.Kasami.Basic

set_option maxHeartbeats 800000

namespace Kasami

open scoped BigOperators

/-! ### Definition -/

/-- The Kasami exponent: `d = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-! ### Basic properties -/

theorem kasamiExp_zero : kasamiExp 0 = 1 := by simp [kasamiExp]

theorem kasamiExp_one : kasamiExp 1 = 3 := by simp [kasamiExp]

/-- `4^k ≥ 2^k` for all k (needed for ℕ subtraction). -/
theorem four_pow_ge_two_pow (k : ℕ) : 4 ^ k ≥ 2 ^ k := by
  have : 2 ≤ (4 : ℕ) := by norm_num
  exact Nat.pow_le_pow_left this k

theorem kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp; omega

/-- Alternative formula: `d = (2^{2k} - 2^k + 1)`. -/
theorem kasamiExp_eq (k : ℕ) : kasamiExp k = 2 ^ (2 * k) - 2 ^ k + 1 := by
  unfold kasamiExp
  congr 1; congr 1
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, mul_comm]

/-
`d` is always odd.
-/
theorem kasamiExp_odd (k : ℕ) : Odd (kasamiExp k) := by
  rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.one_le_iff_ne_zero, parity_simps ];
  grind +locals

/-! ### GCD analysis -/

/-
When `gcd(k, n) = 1` and `n` is odd, `gcd(d, 2^n - 1) = 1`.
-/
theorem kasamiExp_coprime (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  refine Nat.coprime_of_dvd ?_;
  intro p pp dk dn; haveI := Fact.mk pp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( Nat.one_le_pow _ _ zero_lt_two ) ] ;
  -- From $2^{3k} \equiv -1 \pmod{p}$, we get $2^{6k} \equiv 1 \pmod{p}$.
  have h_order_div : orderOf (2 : ZMod p) ∣ 6 * k ∧ ¬(orderOf (2 : ZMod p) ∣ 3 * k) := by
    have h_order_div : 2 ^ (3 * k) ≡ -1 [ZMOD p] := by
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, pow_mul' ];
      rw [ show kasamiExp k = 4 ^ k - 2 ^ k + 1 from rfl ] at dk; rw [ Nat.cast_add, Nat.cast_sub ( show 2 ^ k ≤ 4 ^ k from Nat.pow_le_pow_left ( by decide ) _ ) ] at dk; norm_num [ pow_mul', ← mul_pow ] at *;
      rw [ show ( 4 : ZMod p ) = 2 ^ 2 by norm_num, pow_right_comm ] at dk ; linear_combination' dk * ( 2 ^ k + 1 );
    simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, orderOf_dvd_iff_pow_eq_one ];
    rw [ show 6 * k = 3 * k + 3 * k by ring, pow_add ] ; by_cases h : ( 2 : ZMod p ) = 0 <;> simp_all +decide [ pow_mul' ];
    rw [ neg_eq_iff_add_eq_zero ] ; ring ; aesop;
  -- Since $n$ is odd, $orderOf (2 : ZMod p)$ must be odd.
  have h_order_odd : Odd (orderOf (2 : ZMod p)) := by
    have h_order_odd : orderOf (2 : ZMod p) ∣ n := by
      exact orderOf_dvd_iff_pow_eq_one.mpr ( sub_eq_zero.mp dn );
    exact hn_odd.of_dvd_nat h_order_odd;
  -- Since $orderOf (2 : ZMod p)$ is odd and divides $6k$, it must divide $3k$.
  have h_order_div_3k : orderOf (2 : ZMod p) ∣ 3 * k := by
    exact ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime ( orderOf ( 2 : ZMod p ) ) 2 from by obtain ⟨ m, hm ⟩ := h_order_odd; aesop ) <| by simpa only [ show 6 * k = 2 * ( 3 * k ) by ring ] using h_order_div.1 );
  aesop

/-
When `gcd(k,n) = 1`, the power map `x ↦ x^d` is a permutation of F_{2^n}.
-/
theorem kasamiExp_permutation (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Function.Bijective (F2n.powMap n (kasamiExp k)) := by
  -- Since gcd(d, 2^n - 1) = 1 (from kasamiExp_coprime), the power map x ↦ x^d is a bijection on F_{2^n}.
  have h_bijection : ∀ x : F2n n, x ≠ 0 → ∀ y : F2n n, y ≠ 0 → x ^ (kasamiExp k) = y ^ (kasamiExp k) → x = y := by
    intros x hx y hy hxy
    have h_order : orderOf (x / y) ∣ 2 ^ n - 1 := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      have h_order : ∀ z : F2n n, z ≠ 0 → z ^ (2 ^ n - 1) = 1 := by
        have h_order : ∀ z : F2n n, z ≠ 0 → z ^ (Fintype.card (F2n n) - 1) = 1 := by
          exact fun z hz => FiniteField.pow_card_sub_one_eq_one z hz;
        rwa [ F2n.card n hn ] at h_order;
      exact h_order _ ( div_ne_zero hx hy );
    have h_order_div : orderOf (x / y) ∣ kasamiExp k := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      rw [ div_pow, hxy, div_self ( pow_ne_zero _ hy ) ];
    have h_order_one : orderOf (x / y) ∣ Nat.gcd (kasamiExp k) (2 ^ n - 1) := by
      exact Nat.dvd_gcd h_order_div h_order;
    have := kasamiExp_coprime k n hk hn hn_odd hgcd; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ;
    exact eq_of_div_eq_one h_order_one;
  -- Since the power map is injective on the units, it is also injective on the entire field.
  have h_injective : Function.Injective (F2n.powMap n (kasamiExp k)) := by
    intro x y hxy; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ Kasami.F2n.powMap ] ;
    · rw [ zero_pow ( by exact Nat.succ_ne_zero _ ) ] at hxy; exact absurd hxy.symm ( pow_ne_zero _ hy ) ;
    · rw [ zero_pow ( by linarith [ show kasamiExp k > 0 from kasamiExp_pos k ] ) ] at hxy ; aesop;
    · exact h_bijection x hx y hy hxy;
  exact ⟨ h_injective, Finite.injective_iff_surjective.mp h_injective ⟩

end Kasami