import RequestProject.Walsh.WalshDivisibility
import RequestProject.APN.Defs
import RequestProject.Support.AutocorrQuadratic
import RequestProject.Core.KasamiMCM
import Mathlib

/-!
# Kasami Walsh Divisibility via Quadratic Substitution

## Key Result

For the Kasami function `x^d` with `d = 2^{2k} - 2^k + 1`, the Walsh
transform is divisible by `2^{(n+1)/2}`.

## Proof Strategy

The substitution `x = y^{2^k+1}` transforms the Kasami Walsh sum into a
sum over a quadratic form, which has the required divisibility by
`quadratic_gauss_sum_div`.
-/

set_option maxHeartbeats 3200000

namespace KasamiWalshDiv

open Finset Fintype BigOperators WalshAB CollisionAnalysis AutocorrQuadratic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Gold power bijectivity -/

/-
The Gold power map `y ↦ y^{2^k+1}` is bijective on F when `gcd(k,n) = 1`
and `n` is odd.
-/
theorem gold_pow_bijective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : n ≥ 1) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) := by
  have h_gold_perm : Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
    convert gold_coprime k n hcop hnodd using 1;
  have h_gold_perm : ∀ (y : F), y ≠ 0 → ∀ (x : F), x ^ (2 ^ k + 1) = y ^ (2 ^ k + 1) → x = y := by
    intro y hy x hx;
    have h_order : orderOf (x / y) ∣ 2 ^ k + 1 ∧ orderOf (x / y) ∣ Fintype.card F - 1 := by
      rw [ orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one ];
      by_cases hx : x = 0 <;> simp_all +decide [ div_pow, pow_add ];
      simp_all +decide [ div_mul_div_comm, ← hcard, FiniteField.pow_card_sub_one_eq_one ];
    have := Nat.dvd_gcd h_order.1 ( h_order.2.trans ( by simp +decide [ hcard ] : Fintype.card F - 1 ∣ 2 ^ n - 1 ) ) ; simp_all +decide ;
    exact eq_of_div_eq_one this;
  have h_gold_perm : Function.Injective (fun y : F => y ^ (2 ^ k + 1)) := by
    intro x y; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide ;
    · exact fun h => absurd h.symm ( pow_ne_zero _ hy );
    · exact h_gold_perm y hy x;
  exact ⟨ h_gold_perm, Finite.injective_iff_surjective.mp h_gold_perm ⟩

/-! ## Third derivative of combined Gold monomials -/

/-
Third derivative of `a·y^{2^j+1} + b·y^{2^m+1}` vanishes for any j, m.
This follows from `third_deriv_gold_zero` applied to both monomials.
-/
theorem sum_gold_third_deriv_zero (a b : F) (j m : ℕ) (x y z : F) :
    let Q := fun t => a * t ^ (2 ^ j + 1) + b * t ^ (2 ^ m + 1)
    Q (x + y + z) + Q (x + y) + Q (x + z) + Q (y + z)
    + Q x + Q y + Q z + Q 0 = 0 := by
  linear_combination' third_deriv_gold_zero j x y z * a + third_deriv_gold_zero m x y z * b

/-! ## Walsh sum rewriting via substitution -/

/-
Rewrite Walsh sum using the bijective substitution `x = y^{2^k+1}`.
-/
theorem walsh_kasami_eq_quadratic {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : n ≥ 1)
    (a b : F) :
    walsh (· ^ d k : F → F) a b =
    ∑ y : F, χ (a * y ^ (2 ^ k + 1) + b * y ^ (2 ^ (3 * k) + 1)) := by
  obtain ⟨g, hg⟩ := gold_pow_bijective hcard k hcop hnodd hn;
  apply Finset.sum_bij (fun x _ => Classical.choose (hg x));
  · exact fun _ _ => Finset.mem_univ _;
  · grind;
  · exact fun x _ => ⟨ _, Finset.mem_univ _, by have := Classical.choose_spec ( hg ( x ^ ( 2 ^ k + 1 ) ) ) ; aesop ⟩;
  · intro x hx
    have := Classical.choose_spec (hg x)
    simp_all +decide;
    rw [ ← this, ← d_mul_gold k hk ] ; ring;
    grind +ring

/-! ## Main result: Kasami Walsh divisibility -/

/-- **Kasami Walsh Divisibility**: `2^{(n+1)/2} ∣ W(a,b)` for `x^{d(k)}`.

This is proved directly from the quadratic structure of the Kasami exponent,
WITHOUT requiring APN or bijectivity as hypotheses. -/
theorem kasami_walsh_div {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : n ≥ 1)
    (a b : F) :
    (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh (· ^ d k : F → F) a b := by
  rw [walsh_kasami_eq_quadratic hcard k hk hcop hnodd hn]
  apply WalshDivisibility.quadratic_gauss_sum_div hcard hnodd
  exact sum_gold_third_deriv_zero a b k (3 * k)

end KasamiWalshDiv