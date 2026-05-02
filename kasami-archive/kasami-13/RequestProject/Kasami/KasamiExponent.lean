/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami Exponent

Number-theoretic properties of the Kasami exponent `d = 4^k - 2^k + 1`.

## Main definitions
- `kasamiExp k` — the Kasami exponent `4^k - 2^k + 1`

## Main results
- `kasamiExp_pos`: `d > 0`
- `kasamiExp_coprime`: `gcd(d, 2^n - 1) = 1` when `gcd(k, n) = 1` and `n` is odd

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic

namespace Kasami

open scoped BigOperators

/-! ### Definition -/

/-- The Kasami exponent: `d = 4^k - 2^k + 1 = 2^{2k} - 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-! ### Basic properties -/

theorem kasamiExp_zero : kasamiExp 0 = 1 := by simp [kasamiExp]

theorem kasamiExp_one : kasamiExp 1 = 3 := by simp [kasamiExp]

theorem kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp; omega

/-- `4^k ≥ 2^k` for all k (needed for ℕ subtraction). -/
theorem four_pow_ge_two_pow (k : ℕ) : 4 ^ k ≥ 2 ^ k := by
  have : 2 ≤ (4 : ℕ) := by norm_num
  exact Nat.pow_le_pow_left this k

/-
`d` is always odd.
-/
theorem kasamiExp_odd (k : ℕ) : Odd (kasamiExp k) := by
  unfold kasamiExp;
  cases le_total ( 4 ^ k ) ( 2 ^ k ) <;> simp_all +decide [ parity_simps ]

/-! ### GCD analysis -/

/-
When `gcd(k, n) = 1` and `n` is odd, `gcd(d, 2^n - 1) = 1`.
-/
theorem kasamiExp_coprime (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  -- Assume there exists a prime $p$ such that $p \mid d$ and $p \mid 2^n - 1$.
  by_contra h_contra
  obtain ⟨p, hp_prime, hp_div_d, hp_div_2n_minus_1⟩ : ∃ p, Nat.Prime p ∧ p ∣ kasamiExp k ∧ p ∣ 2 ^ n - 1 := by
    exact Nat.Prime.not_coprime_iff_dvd.mp h_contra;
  -- Since $p \mid 2^{3k} + 1$, we have $2^{3k} \equiv -1 \pmod{p}$.
  have hp_mod_2_3k : 2 ^ (3 * k) ≡ -1 [ZMOD p] := by
    have hp_mod_2_3k : (2 ^ k + 1) * (kasamiExp k) = 2 ^ (3 * k) + 1 := by
      zify [ kasamiExp ];
      rw [ Nat.cast_sub ( by gcongr ; norm_num ) ] ; push_cast ; ring;
      norm_num [ pow_mul', ← mul_pow ] ; ring;
    exact Eq.symm <| Int.modEq_of_dvd <| by simpa using mod_cast hp_mod_2_3k ▸ dvd_mul_of_dvd_right hp_div_d _;
  -- Since $p \mid 2^n - 1$, we have $2^n \equiv 1 \pmod{p}$.
  have hp_mod_2_n : 2 ^ n ≡ 1 [ZMOD p] := by
    exact Eq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hp_div_2n_minus_1;
  -- Since $p \mid 2^{3k} + 1$, we have $2^{3kn} \equiv (-1)^n \equiv -1 \pmod{p}$.
  have hp_mod_2_3kn : 2 ^ (3 * k * n) ≡ -1 [ZMOD p] := by
    convert hp_mod_2_3k.pow n using 1 <;> ring;
    rw [ hn_odd.neg_one_pow ];
  -- Since $p \mid 2^n - 1$, we have $2^{3kn} \equiv 1 \pmod{p}$.
  have hp_mod_2_3kn_one : 2 ^ (3 * k * n) ≡ 1 [ZMOD p] := by
    convert hp_mod_2_n.pow ( 3 * k ) using 1 <;> ring;
  have := hp_mod_2_3kn.symm.trans hp_mod_2_3kn_one; norm_num [ Int.modEq_iff_dvd ] at this; norm_cast at *; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
  simp_all +decide [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ]

/-
When `gcd(k,n) = 1`, the power map `x ↦ x^d` is a permutation of F_{2^n}.
-/
theorem kasamiExp_permutation (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    Function.Bijective (F2n.powMap n (kasamiExp k)) := by
  -- Since $d$ is coprime to $2^n - 1$, the power map $x \mapsto x^d$ is injective on the units $F_{2^n}^*$.
  have h.injective : Function.Injective (fun x : (F2n n)ˣ => x ^ (kasamiExp k)) := by
    have h_coprime : Nat.Coprime (kasamiExp k) (Nat.card (F2n n) - 1) := by
      convert kasamiExp_coprime k n hk hn hn_odd hgcd;
      exact?;
    intro x y hxy
    have h_order : orderOf (x * y⁻¹) ∣ Nat.card (F2n n) - 1 := by
      have h_order : orderOf (x * y⁻¹) ∣ Nat.card (F2n n)ˣ := by
        exact?;
      convert h_order using 1;
      rw [ Nat.card_units ];
    have h_order_div : orderOf (x * y⁻¹) ∣ kasamiExp k := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      simp_all +decide [ mul_pow, pow_right_comm ];
    have := Nat.dvd_gcd h_order_div h_order; simp_all +decide [ orderOf_dvd_iff_pow_eq_one ] ;
    simpa using eq_inv_of_mul_eq_one_left this;
  -- Since the units of $F_{2^n}$ are exactly the non-zero elements, the injectivity on the units implies injectivity on all of $F_{2^n}$.
  have h.injective_all : Function.Injective (fun x : F2n n => x ^ (kasamiExp k)) := by
    intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide;
    · rw [ zero_pow ( Nat.ne_of_gt ( kasamiExp_pos k ) ) ] at hxy;
      exact absurd hxy.symm ( pow_ne_zero _ hy );
    · simp_all +decide [ zero_pow ( show kasamiExp k ≠ 0 from Nat.succ_ne_zero _ ) ];
    · have := @h.injective ( Units.mk0 x hx ) ( Units.mk0 y hy ) ; simp_all +decide [ Units.ext_iff ] ;
  exact ⟨ h.injective_all, Finite.injective_iff_surjective.mp h.injective_all ⟩

end Kasami