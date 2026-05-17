/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Exponent

Number-theoretic properties of the Kasami exponent `d = 4^k - 2^k + 1`.

## Main definitions
- `kasamiExp k` — the Kasami exponent `4^k - 2^k + 1`

## Main results
- `kasamiExp_pos`: `d > 0`
- `kasamiExp_formula`: `d = 4^k - 2^k + 1`
- `kasamiExp_gcd`: `gcd(d, 2^n - 1) = 1` when `gcd(k, n) = 1` and `n` is odd

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic

namespace Kasami

open scoped BigOperators

/-! ### Definition -/

/-- The Kasami exponent: `d = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`.
    We work in ℕ, noting that `4^k ≥ 2^k` for all `k ≥ 0`,
    so the subtraction is well-defined. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-! ### Basic properties -/

theorem kasamiExp_zero : kasamiExp 0 = 1 := by
  simp [kasamiExp]

theorem kasamiExp_one : kasamiExp 1 = 3 := by
  simp [kasamiExp]

/-- `4^k ≥ 2^k` for all k (needed for ℕ subtraction). -/
theorem four_pow_ge_two_pow (k : ℕ) : 4 ^ k ≥ 2 ^ k := by
  have : 2 ≤ (4 : ℕ) := by norm_num
  exact Nat.pow_le_pow_left this k

theorem kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp
  omega

/-- Alternative formula: `d = (2^{2k} - 2^k + 1)`. -/
theorem kasamiExp_eq (k : ℕ) : kasamiExp k = 2 ^ (2 * k) - 2 ^ k + 1 := by
  unfold kasamiExp
  congr 1; congr 1
  rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, mul_comm]

/-
`d` is always odd.
-/
theorem kasamiExp_odd (k : ℕ) : Odd (kasamiExp k) := by
  unfold kasamiExp;
  cases k <;> simp_all +decide [ Nat.pow_succ', parity_simps ];
  exact even_iff_two_dvd.mpr ( Nat.dvd_sub ( dvd_mul_of_dvd_left ( by decide ) _ ) ( dvd_mul_right _ _ ) )

/-! ### GCD analysis -/

/-
**Key number-theoretic result**: When `gcd(k, n) = 1` and `n` is odd,
    `gcd(d, 2^n - 1) = 1`, meaning `x ↦ x^d` is a permutation of F_{2^n}^×.
    This follows from the theory of cyclotomic cosets modulo `2^n - 1`.

    Proof sketch (from Kasami 1971):
    The multiplicative order of 2 modulo any prime factor of `d` divides `2k` but not `k`,
    hence divides `gcd(2k, n)`. When `gcd(k,n) = 1` and `n` is odd, this forces the
    order to divide `gcd(2k, n) = gcd(2, n) · gcd(k, n) = 1 · 1 = 1`, contradiction.
    Actually: `gcd(2k, n) = gcd(k, n) * gcd(2, n/gcd(k,n))`. Since `gcd(k,n)=1` and `n`
    is odd, `gcd(2k, n) = gcd(2, n) = 1`.
    So no prime factor of `2^n - 1` can divide `d`.
-/
theorem kasamiExp_coprime (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  refine' Nat.coprime_of_dvd' _;
  intro p pp dk dn;
  -- Then $p$ divides $2^{3k} + 1$, which implies $2^{3k} \equiv -1 \pmod{p}$.
  have h_order : 2 ^ (3 * k) ≡ -1 [ZMOD p] := by
    have h_order : (2 ^ k + 1) * (4 ^ k - 2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
      zify;
      rw [ Nat.cast_sub ( by gcongr ; norm_num ) ] ; push_cast ; ring;
      norm_num [ pow_mul', ← mul_pow ] ; ring;
    exact Eq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using dvd_trans dk <| show 4 ^ k - 2 ^ k + 1 ∣ 2 ^ ( 3 * k ) + 1 from h_order ▸ dvd_mul_left _ _;
  -- Since $p$ divides $2^n - 1$, we have $2^n \equiv 1 \pmod{p}$.
  have h_order_n : 2 ^ n ≡ 1 [ZMOD p] := by
    exact Eq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using dn;
  -- Since $p$ divides $2^n - 1$, we have $2^n \equiv 1 \pmod{p}$. Therefore, $2^{3kn} \equiv 1 \pmod{p}$.
  have h_order_3kn : 2 ^ (3 * k * n) ≡ 1 [ZMOD p] := by
    convert h_order_n.pow ( 3 * k ) using 1 <;> ring;
  simp_all +decide [ ← ZMod.intCast_eq_intCast_iff, pow_mul ];
  rw [ neg_eq_iff_add_eq_zero ] at h_order_3kn;
  rcases p with ( _ | _ | _ | p ) <;> cases h_order_3kn <;> simp_all +decide

/-
When `gcd(k,n) = 1`, the power map `x ↦ x^d` is a permutation of F_{2^n}.
-/
theorem kasamiExp_permutation (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Function.Bijective (F2n.powMap n (kasamiExp k)) := by
  have h_perm : Nat.Coprime (kasamiExp k) (Fintype.card (F2n n) - 1) := by
    convert kasamiExp_coprime k n hk hn hn_odd hgcd using 1;
    rw [ F2n.card n hn ];
  -- Since $d$ is coprime to $2^n - 1$, the map $x \mapsto x^d$ is a bijection on the multiplicative group $F_{2^n}^*$.
  have h_bij : Function.Bijective (fun x : (F2n n)ˣ => x ^ kasamiExp k) := by
    have h_bij : ∀ x : (F2n n)ˣ, x ^ kasamiExp k = 1 → x = 1 := by
      intro x hx
      have h_order : orderOf x ∣ kasamiExp k := by
        exact orderOf_dvd_iff_pow_eq_one.mpr hx;
      have h_order_div : orderOf x ∣ Fintype.card (F2n n) - 1 := by
        rw [ orderOf_dvd_iff_pow_eq_one ] at *;
        rw [ ← Units.val_eq_one ] at *;
        simp +decide [ ← ZMod.natCast_eq_zero_iff ];
        rw [ FiniteField.pow_card_sub_one_eq_one ] ; aesop;
      have := Nat.dvd_gcd h_order h_order_div; aesop;
    have h_bij : Function.Injective (fun x : (F2n n)ˣ => x ^ kasamiExp k) := by
      intros x y hxy;
      specialize h_bij ( x * y⁻¹ ) ; simp_all +decide [ mul_pow ];
      simpa using eq_inv_of_mul_eq_one_left h_bij;
    exact ⟨ h_bij, Finite.injective_iff_surjective.mp h_bij ⟩;
  obtain ⟨ x, hx ⟩ := h_bij;
  refine' ⟨ _, _ ⟩;
  · intro a b hab;
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ F2n.powMap ];
    · rw [ zero_pow ( by exact Nat.ne_of_gt ( kasamiExp_pos k ) ) ] at hab;
      rw [ eq_comm ] at hab ; aesop;
    · simp_all +decide [ kasamiExp ];
    · have := @x ( Units.mk0 a ha ) ( Units.mk0 b hb ) ; aesop;
  · intro y;
    by_cases hy : y = 0;
    · use 0; simp [hy];
      exact F2n.powMap_zero n ( kasamiExp k ) ( Nat.ne_of_gt ( kasamiExp_pos k ) );
    · obtain ⟨ z, hz ⟩ := hx ( Units.mk0 y hy );
      exact ⟨ z, by simpa [ Units.ext_iff ] using hz ⟩

end Kasami