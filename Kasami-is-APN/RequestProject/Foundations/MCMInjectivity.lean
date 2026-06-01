/-
# Layer 40: MCM Injectivity & Gold APN

The MCM (Modified Cubing Map) with Gold exponent `x ↦ x^{2^k + 1}` is
injective on F_{2^n} \ {0} when gcd(k,n) = 1 and n is odd.

## Proof Architecture — A Concrete Bridge

The proof demonstrates the bridge technique at a concrete level:

```
  Number Theory:  gcd(2^k+1, 2^n-1) = 1   [coprimality invariant]
        ↓  transfer via ZMod
  Group Theory:   powCoprime bijection on F×  [Mathlib]
        ↓  lift via Units.mk0
  Field Theory:   x ↦ x^{2^k+1} injective
```

This is the same invariant-transfer pattern as the abstract Morita bridge,
but instantiated concretely for finite field arithmetic.

## Connection to APN Theory (Layer 38)

The Gold exponent 2^k + 1 gives an APN power function on F_{2^n} when
gcd(k,n) = 1. MCM injectivity is one of the key ingredients.

## DAG Structure (depends on Layers 37, 38, 39)
-/
import Mathlib
import RequestProject.Foundations.DynamicsAlgebraBridge

namespace Caramello.MCMInjectivity

open Fintype Nat

/-! ## Section 1: MCM Map Definition -/

/-- The MCM map with Gold exponent: x ↦ x^{2^k + 1}. -/
def mcmMap {F : Type*} [Monoid F] (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)

@[simp]
theorem mcmMap_zero {F : Type*} [MonoidWithZero F] (k : ℕ) :
    mcmMap k (0 : F) = 0 := by simp [mcmMap]

@[simp]
theorem mcmMap_one {F : Type*} [Monoid F] (k : ℕ) :
    mcmMap k (1 : F) = 1 := by simp [mcmMap]

theorem mcmMap_ne_zero {F : Type*} [Field F] (k : ℕ) {a : F} (ha : a ≠ 0) :
    mcmMap k a ≠ 0 := pow_ne_zero _ ha

/-- The MCM map is multiplicative. -/
theorem mcmMap_mul {F : Type*} [CommMonoid F] (k : ℕ) (a b : F) :
    mcmMap k (a * b) = mcmMap k a * mcmMap k b := by
  simp [mcmMap, mul_pow]

/-! ## Section 2: Number-Theoretic Core

gcd(2^k + 1, 2^n - 1) = 1 when gcd(k, n) = 1 and n is odd.
-/

theorem coprime_gold_mersenne {k n : ℕ} (_hk : 0 < k) (_hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) :
    Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
  -- Since $2^k + 1$ divides $2^{2k} - 1$ and $\gcd(2k, n) = 1$, it follows that $\gcd(2^k + 1, 2^n - 1) = 1$.
  have h_div : Nat.gcd (2 ^ k + 1) (2 ^ n - 1) ∣ 2 ^ Nat.gcd (2 * k) n - 1 := by
    have h_div : Nat.gcd (2 ^ k + 1) (2 ^ n - 1) ∣ Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) := by
      exact Nat.dvd_gcd ( dvd_trans ( Nat.gcd_dvd_left _ _ ) ( by use 2 ^ k - 1; zify ; norm_num ; ring ) ) ( Nat.gcd_dvd_right _ _ );
    exact h_div.trans ( by simp [ Nat.gcd_comm ] );
  -- Since $\gcd(2k, n) = 1$, we have $2^{\gcd(2k, n)} - 1 = 2^1 - 1 = 1$.
  have h_gcd_one : Nat.gcd (2 * k) n = 1 := by
    exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using hn_odd ) hgcd;
  aesop

/-! ## Section 3: Group-Theoretic Bridge -/

/-- The power map on field units. -/
noncomputable def mcmUnitMap {F : Type*} [Field F] [Fintype F]
    (k : ℕ) (u : Fˣ) : Fˣ :=
  u ^ (2 ^ k + 1)

theorem mcmUnitMap_val {F : Type*} [Field F] [Fintype F]
    (k : ℕ) (u : Fˣ) :
    ↑(mcmUnitMap k u) = mcmMap k (↑u : F) := by
  simp [mcmUnitMap, mcmMap, Units.val_pow_eq_pow_val]

theorem card_units_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (_hn : 0 < n) (hcard : Fintype.card F = 2 ^ n) :
    Nat.card Fˣ = 2 ^ n - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]

/-- The MCM unit map is bijective when gcd(k,n) = 1 and n is odd. -/
theorem mcmUnitMap_bijective {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    Function.Bijective (mcmUnitMap k : Fˣ → Fˣ) := by
  have hcop : Nat.Coprime (Nat.card Fˣ) (2 ^ k + 1) := by
    rw [card_units_eq hn hcard]
    exact (coprime_gold_mersenne hk hn hgcd hn_odd).symm
  exact (powCoprime hcop).bijective

/-! ## Section 4: Main Theorem -/

/-- **MCM Injectivity**: x ↦ x^{2^k + 1} is injective on F \ {0}
    when gcd(k,n) = 1 and n is odd. -/
theorem mcm_injective {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk_pos : 0 < k) (hn_pos : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hn_card : Fintype.card F = 2 ^ n) :
    ∀ a b : F, a ≠ 0 → b ≠ 0 → mcmMap k a = mcmMap k b → a = b := by
  intro a b ha hb hab
  have h_eq : mcmUnitMap k (Units.mk0 a ha) = mcmUnitMap k (Units.mk0 b hb) := by
    rw [← Units.val_inj]; aesop
  have h_inj : Units.mk0 a ha = Units.mk0 b hb :=
    (mcmUnitMap_bijective hk_pos hn_pos hgcd hn_odd (by simpa using hn_card)).injective h_eq
  exact congrArg Units.val h_inj

/-! ## Section 5: Permutation -/

/-- The MCM map as a permutation of Fˣ. -/
noncomputable def mcmPerm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) : Equiv.Perm Fˣ :=
  Equiv.ofBijective _ (mcmUnitMap_bijective hk hn hgcd hn_odd hcard)

/-! ## Section 6: Connection to the Dynamics-Algebra Bridge

The MCM proof demonstrates the bridge pattern concretely:
1. Coprimality is the transferred invariant (like Morita invariance)
2. The transfer crosses number theory → group theory → field theory
3. At each level, the "same" property (coprimality) has different forms

This mirrors the abstract bridge technique:
- MoritaInvariant.prop corresponds to "coprime exponent"
- bridge_transfer corresponds to "powCoprime"
- The concrete application corresponds to "mcm_injective"
-/

/-- The Gold exponent from APNTheory. -/
theorem gold_eq_mcm (k : ℕ) :
    APNTheory.goldExponent k = 2 ^ k + 1 := rfl

/-- MCM injectivity implies the power map x^d is a permutation of F*,
    which is a key step toward showing d is an APN exponent. -/
theorem mcm_implies_power_perm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    Function.Bijective (fun u : Fˣ => u ^ APNTheory.goldExponent k) := by
  rw [gold_eq_mcm]
  exact mcmUnitMap_bijective hk hn hgcd hn_odd hcard

/-! ## Section 7: Toward Kasami APN

The Kasami exponent d = 2^{2k} - 2^k + 1 requires a more sophisticated
version of MCM injectivity. The key differences:

1. **Gold**: x ↦ x^{2^k+1} — direct power map, coprimality suffices
2. **Kasami**: involves the Frobenius sum S_k(x) = x + x^2 + ... + x^{2^{k-1}}
   and the MCM-style function u ↦ S_k(u)^{2^k+1} / u^{2^k}

The Kasami proof reduces to showing this MCM-style function is injective,
which requires:
- Linearized polynomial theory (kernel of S_k has size 2^{gcd(k,n)})
- The coprimality condition gcd(2^{2k}-2^k+1, 2^n-1) = 1
- Case analysis on whether v = 0 or v ≠ 0 in the collision equation

The bridge pattern is the same: coprimality transfers across contexts.
-/

/-- The Frobenius sum from APNTheory. -/
noncomputable def frobSum {F : Type*} [Semiring F] (k : ℕ) (u : F) : F :=
  APNTheory.frobeniusSum k u

/-- Kasami exponent from APNTheory. -/
def kasamiExp (k : ℕ) : ℕ := APNTheory.kasamiExponent k

/-
The Kasami GCD condition: when gcd(k,n) = 1 and **n is odd**,
    gcd(2^{2k}-2^k+1, 2^n-1) = 1.
    Note: fails for n even (e.g. k=1, n=2: gcd(3,3)=3).
-/
theorem kasami_coprime_mersenne {k n : ℕ} (_hk : 0 < k) (_hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  -- Assume it's false; then d divides both (so ≠ 0) and d includes some prime factor q dividing 2^n - 1 (so 2^n ≡ 1 mod q).
  by_contra h
  obtain ⟨q, hq_prime, hq_dvd⟩ : ∃ q, Nat.Prime q ∧ q ∣ kasamiExp k ∧ q ∣ 2 ^ n - 1 := by
    exact Nat.Prime.not_coprime_iff_dvd.mp h;
  -- Then q divides 2^{3k}+1, so 2^{3k} ≡ -1 mod q (q ≠ 2), and q divides 2^{6k}-1 (so ord(q) divides gcd(6k,n)).
  have hq_div_6k : q ∣ 2 ^ (6 * k) - 1 := by
    have hq_div_6k : q ∣ 2 ^ (3 * k) + 1 := by
      have hq_div_3k : 2 ^ (3 * k) + 1 = (2 ^ k + 1) * (2 ^ (2 * k) - 2 ^ k + 1) := by
        zify;
        rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
      exact hq_div_3k.symm ▸ dvd_mul_of_dvd_right ( by simpa [ APNTheory.kasamiExponent ] using hq_dvd.1 ) _;
    convert hq_div_6k.mul_right ( 2 ^ ( 3 * k ) - 1 ) using 1 ; rw [ ← Nat.sq_sub_sq ] ; ring
  have hq_div_gcd : q ∣ 2 ^ Nat.gcd (6 * k) n - 1 := by
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add ]
  have hq_div_gcd_cases : Nat.gcd (6 * k) n = 1 ∨ Nat.gcd (6 * k) n = 3 := by
    have hq_div_gcd_cases : Nat.gcd (6 * k) n ∣ 6 := by
      convert Nat.Coprime.dvd_of_dvd_mul_right _ ( Nat.gcd_dvd_left ( 6 * k ) n ) using 1;
      exact Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_right _ _ ) ( Nat.Coprime.symm hgcd );
    have := Nat.le_of_dvd ( by decide ) hq_div_gcd_cases; interval_cases _ : Nat.gcd ( 6 * k ) n <;> simp_all +decide ;
    · have := Nat.gcd_dvd_right ( 6 * k ) n; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
      grind +qlia;
    · have := Nat.gcd_dvd_right ( 6 * k ) n; simp_all +decide [ Nat.dvd_prime ] ;
      exact absurd ( hn_odd.of_dvd_nat this ) ( by decide );
  rcases hq_div_gcd_cases with h | h <;> simp_all +decide [ Nat.pow_succ' ];
  have := Nat.le_of_dvd ( by decide ) hq_div_gcd; interval_cases q <;> simp_all +decide ;
  -- Since $7 \mid 2^n - 1$, we have $n \equiv 0 \pmod{3}$.
  have hn_mod_3 : n % 3 = 0 := by
    rw [ ← Nat.mod_add_div n 3 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.dvd_iff_mod_eq_zero ] at *; have := Nat.mod_lt n zero_lt_three; interval_cases n % 3 <;> norm_num at *;
    · exact absurd ( ‹Nat.gcd ( 6 * k ) ( 1 + 3 * ( n / 3 ) ) = 3› ▸ Nat.gcd_dvd_right _ _ ) ( by norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] );
    · exact absurd ( Nat.gcd_dvd_right ( 6 * k ) ( 2 + 3 * ( n / 3 ) ) ) ( by norm_num [ *, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] );
  -- Since $n \equiv 0 \pmod{3}$, we have $k \equiv 1 \pmod{3}$ or $k \equiv 2 \pmod{3}$.
  have hk_mod_3 : k % 3 = 1 ∨ k % 3 = 2 := by
    exact not_not.mp fun contra => by have := Nat.dvd_gcd ( show 3 ∣ k from Nat.dvd_of_mod_eq_zero <| by omega ) ( show 3 ∣ n from Nat.dvd_of_mod_eq_zero hn_mod_3 ) ; simp_all +decide ;
  rcases hk_mod_3 with ( hk_mod_3 | hk_mod_3 ) <;> rw [ ← Nat.mod_add_div k 3, hk_mod_3 ] at hq_dvd <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.add_mod, kasamiExp ] at hq_dvd;
  · norm_num [ APNTheory.kasamiExponent ] at hq_dvd;
    rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * ( 1 + 3 * ( k / 3 ) ) ) ) 7, ← Nat.mod_add_div ( 2 ^ ( 1 + 3 * ( k / 3 ) ) ) 7 ] at hq_dvd ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at hq_dvd;
    omega;
  · norm_num [ APNTheory.kasamiExponent ] at hq_dvd;
    rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * ( 2 + 3 * ( k / 3 ) ) ) ) 7, ← Nat.mod_add_div ( 2 ^ ( 2 + 3 * ( k / 3 ) ) ) 7 ] at hq_dvd ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at hq_dvd;
    omega

/-- If the Kasami exponent is coprime to 2^n-1, then x ↦ x^d is
    a permutation of F_{2^n}*. -/
theorem kasami_power_perm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1)
    (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime (kasamiExp k) (2 ^ n - 1)) :
    Function.Bijective (fun u : Fˣ => u ^ kasamiExp k) := by
  have hcop' : Nat.Coprime (Nat.card Fˣ) (kasamiExp k) := by
    rw [card_units_eq hn hcard]; exact hcop.symm
  exact (powCoprime hcop').bijective

/-! ## Section 8: Summary

1. **mcmMap**: x ↦ x^{2^k+1} (Gold power function)
2. **coprime_gold_mersenne**: gcd(2^k+1, 2^n-1) = 1
3. **mcmUnitMap_bijective**: power map bijects F×
4. **mcm_injective**: injectivity on F\{0} — fully proved!
5. **mcmPerm**: the MCM permutation
6. **gold_eq_mcm**: connects to APNTheory exponents
7. **kasami_coprime_mersenne**: Kasami GCD (sorry — needs Mersenne GCD theory)
8. **kasami_power_perm**: Kasami permutation from coprimality

### Bridge Pattern

The proof demonstrates the concrete bridge:
- **Invariant**: coprimality of exponent with group order
- **Source context**: number theory (Nat.gcd, ZMod)
- **Target context**: group theory (powCoprime) → field theory (injectivity)
- **Transfer mechanism**: Mathlib's powCoprime lemma

This is the same pattern as Caramello's bridge technique:
- **Invariant**: a topos-theoretic property
- **Source context**: theory T₁
- **Target context**: Morita-equivalent theory T₂
- **Transfer mechanism**: classifying topos equivalence
-/

end Caramello.MCMInjectivity