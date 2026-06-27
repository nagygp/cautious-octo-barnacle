import ConjecturesMTupleTripleCount.APN.CharTwoBasics

/-!
# Cross Form Analysis and Collision Equation

This file proves the collision equation and the power-injectivity properties
needed for the cross-pair analysis.

## Educational Notes

### Algebraic Identity Proofs

The collision equation is an algebraic identity. The proof strategy:
1. Expand all definitions
2. Use `d(k) · (2^k + 1) = 2^(3k) + 1` to relate exponents
3. Use Freshman's Dream to simplify powers of sums
4. Use `ring` to verify the resulting polynomial identity

### Tip: `zify` and `push_cast`

When dealing with natural number arithmetic involving subtraction
(like `2^(2k) - 2^k + 1`), use:
- `zify` to lift to integers (where subtraction is well-behaved)
- `push_cast` to push coercions inside
- `ring` to verify the integer identity

### Tip: `field_simp`

When working with division in fields, `field_simp` clears denominators.
Combine with `ring` for powerful algebraic simplification.
-/

set_option maxHeartbeats 800000

namespace CollisionAnalysis

open Finset Fintype

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Power Injectivity

When `d` is coprime to `|F| - 1`, the power map `x ↦ x^d` is a bijection
on the multiplicative group F*.
-/

/-
`d(k)` is coprime to `2^n - 1` under the Kasami conditions.
-/
theorem d_coprime_card_sub_one {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) :
    Nat.Coprime (d k) (Fintype.card F - 1) := by
  -- Since $d(k)$ divides $2^{6k} - 1$, we have $\gcd(d(k), 2^n - 1) \mid \gcd(2^{6k} - 1, 2^n -  �1�)$.
  have h_div : Nat.gcd (2 ^ (2 * k) - 2 ^ k + 1) (2 ^ n - 1) ∣ Nat.gcd (2 ^ (6 * k) - 1) (2 ^ n - 1) := by
    refine' Nat.dvd_gcd ( dvd_trans ( Nat.gcd_dvd_left _ _ ) _ ) ( Nat.gcd_dvd_right _ _ );
    zify;
    rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ pow_mul' ];
    · exact ⟨ ( 2 ^ k ) ^ 4 + ( 2 ^ k ) ^ 3 - ( 2 ^ k ) - 1, by ring ⟩;
    · exact Nat.one_le_pow _ _ ( by positivity );
    · nlinarith [ pow_pos ( zero_lt_two' ℕ ) k ];
  -- Since gcd(6k, n) = gcd(6, n) and n is odd, we have gcd(6k, n) = gcd(6, n).
  have h_gcd : Nat.gcd (6 * k) n = Nat.gcd 6 n := by
    exact Nat.Coprime.gcd_mul_right_cancel _ hcop;
  have := Nat.gcd_dvd_left 6 n; ( have := Nat.le_of_dvd ( by decide ) this; interval_cases _ : Nat.gcd 6 n <;> simp_all +decide ; );
  · exact h_div;
  · have := Nat.gcd_dvd_right 6 n; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
    exact absurd this ( by simpa using hnodd );
  · have := Nat.gcd_dvd_right ( 2 ^ ( 2 * k ) - 2 ^ k + 1 ) ( 2 ^ n - 1 ) ; simp_all +decide [ Nat.dvd_prime ] ;
    cases h_div <;> simp_all +decide [ Nat.dvd_prime ];
    · assumption;
    · have := Nat.gcd_dvd_left ( 2 ^ ( 2 * k ) - 2 ^ k + 1 ) ( 2 ^ n - 1 ) ; simp_all +decide [ Nat.dvd_prime ] ;
      rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k ) ) 7, ← Nat.mod_add_div ( 2 ^ k ) 7 ] at this; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this;
      rw [ ← Nat.mod_add_div k 6 ] at this; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this; have := Nat.mod_lt k ( by decide : 6 > 0 ) ; interval_cases k % 6 <;> norm_num at *;
      all_goals omega;
  · have := Nat.gcd_dvd_right 6 n; simp_all +decide [ Nat.dvd_prime ] ;
    exact absurd ( hnodd.of_dvd_nat this ) ( by decide )

/-
The power map `x ↦ x^d` is injective on units.
-/
theorem pow_d_injective_units {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) :
    Function.Injective (fun x : Fˣ => x ^ d k) := by
  -- Since $d(k)$ is coprime to $|F^*| = 2^n - 1$, the power map $x \mapsto x^d$ is injective on $F^*$.
  have h_coprime : Nat.Coprime (d k) (Fintype.card Fˣ) := by
    rw [ Fintype.card_units ] ; exact d_coprime_card_sub_one hcard k hk hcop hnodd hn;
  -- Since $d(k)$ is coprime to $|F^*| = 2^n - 1$, the power map $x \mapsto x^d$ is injective on $F^*$ by the properties of cyclic groups.
  have h_inj : ∀ x : Fˣ, x ^ d k = 1 → x = 1 := by
    intro x hx;
    have := orderOf_dvd_iff_pow_eq_one.mpr hx;
    have := Nat.dvd_gcd this ( orderOf_dvd_card ) ; aesop;
  intro x y hxy; specialize h_inj ( x * y⁻¹ ) ; simp_all +decide [ mul_pow ] ;
  simpa using eq_inv_of_mul_eq_one_left h_inj

/-
Power map `x ↦ x^d` is injective on nonzero field elements.
-/
theorem pow_d_injective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (heq : x ^ d k = y ^ d k) : x = y := by
  -- Since $x$ and $y$ are units, we can apply the injectivity of the power map on units.
  have h_unit : (Units.mk0 x hx) ^ d k = (Units.mk0 y hy) ^ d k := by
    exact Units.ext heq;
  exact Units.ext_iff.mp ( pow_d_injective_units hcard k hk hcop hnodd hn h_unit )

/-! ## The Collision Equation -/

/-
**Collision equation**: When `sVal(k, t₁) = sVal(k, t₂)`,
the cross form satisfies `Cross(s₀, P) = L_{3k}(c)`.
-/
theorem collision_equation (k : ℕ) (hk : k ≥ 1) (t₁ t₂ : F)
    (hs : sVal k t₁ = sVal k t₂) :
    Cross k (sVal k t₁) (t₁ ^ d k + t₂ ^ d k) =
    L (3 * k) (t₁ + t₂) := by
  have h_expand : (t₁ + 1) ^ (2 ^ (3 * k) + 1) + t₁ ^ (2 ^ (3 * k) + 1) + (t₂ + 1) ^ (2 ^ (3 * k) + 1) + t₂ ^ (2 ^ (3 * k) + 1) = (t₁ + t₂) ^ (2 ^ (3 * k)) + (t₁ + t₂) := by
    simp_all +decide [ pow_add, pow_mul', add_pow_char_pow ];
    simp_all +decide [ pow_succ, pow_mul, add_pow_char_pow ];
    grind;
  have h_expand : (t₁ + 1) ^ (d k * (2 ^ k + 1)) + t₁ ^ (d k * (2 ^ k + 1)) + (t₂ + 1) ^ (d k * (2 ^ k + 1)) + t₂ ^ (d k * (2 ^ k + 1)) = (t₁ + t₂) ^ (2 ^ (3 * k)) + (t₁ + t₂) := by
    rw [ ← h_expand, d_mul_gold k hk ];
  simp_all +decide [ pow_mul, Cross, L, sVal ];
  grind +suggestions

/-! ## sVal Nonvanishing -/

/-
**sVal never vanishes**: `sVal(k, t) ≠ 0` for all `t`.
-/
theorem sVal_ne_zero {k n : ℕ} (hk : k ≥ 1) (hn : 0 < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) (t : F) :
    sVal k t ≠ 0 := by
  by_cases ht : t = 0 <;> by_cases ht' : t + 1 = 0 <;> simp_all +decide [ sVal ];
  · rw [ zero_pow ( d_pos k hk |> ne_of_gt ) ] ; norm_num;
  · rw [ zero_pow ( by linarith [ d_pos k hk ] ) ] ; simp_all +decide [ add_eq_zero_iff_eq_neg ];
  · have := pow_d_injective hcard k hk hcop hnodd hn ( t + 1 ) t ht' ht;
    grind +ring

end CollisionAnalysis