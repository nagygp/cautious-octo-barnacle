import Mathlib
import RequestProject.FrobAlg

/-!
# Foundational Layer F3: Exponent Arithmetic Engine

A systematic theory of the multiplicative group `F*` of a finite field,
modular exponent calculus, and Mersenne-number coprimality.

**Motivation.** Many `sorry`s in the Dempwolff–Müller formalization reduce to
"the power map `x ↦ x^a` is bijective because `gcd(a, |F|−1) = 1`" or
"exponents that are congruent mod `|F|−1` give equal powers on units."
This layer provides the complete toolkit for such arguments.

## Main results

1. **Units group** (F3.1): `|F*| = |F| − 1`, Fermat's little theorem.
2. **Power map bijectivity** (F3.2): `x ↦ x^a` bijective on `F*` iff
   `gcd(a, |F|−1) = 1`; extension to all of `F`.
3. **Inverse power** (F3.3): if `ab ≡ 1 (mod |F|−1)` then `(x^a)^b = x`.
4. **Mersenne GCD** (F3.4): `gcd(p^a − 1, p^b − 1) = p^{gcd(a,b)} − 1`.
5. **Mersenne coprimality** (F3.5): `gcd(a,b) = 1 ⟹ gcd(p^a − 1, p^b − 1) = p − 1`.
6. **Exponent arithmetic** (F3.6): modular congruence tools for `ℕ` exponents.
7. **Congruent exponents** (F3.7): `a ≡ b (mod |F|−1) ⟹ x^a = x^b` on `F*`.

## DAG structure

```
  F3.1 (units group)
    │
    ├──► F3.2 (power bijection) ◄── Mathlib (Coprime.pow_left_bijective)
    │      │
    │      └──► F3.3 (inverse power)
    │
    └──► F3.7 (congruent exponents)

  F3.4 (Mersenne GCD) [independent, pure ℕ arithmetic]
    │
    └──► F3.5 (Mersenne coprimality)
           │
           └──► future: coprimality of k with 2^n−1
```

**Dependencies:** Layer F1 (`FrobAlg.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

-- ═══════════════════════════════════════════
-- F3.1 : Units group facts
-- ═══════════════════════════════════════════

variable {F : Type*} [Field F] [Fintype F]

/-- **Cardinality of units.** `|F*| = |F| − 1`. -/
lemma card_units_eq : Fintype.card Fˣ = Fintype.card F - 1 :=
  Fintype.card_units F

/-- **Nat.card of units.** `Nat.card F* = |F| − 1`. -/
lemma natCard_units_eq : Nat.card Fˣ = Fintype.card F - 1 := by
  rw [Nat.card_eq_fintype_card, card_units_eq]

/-
**Fermat's little theorem (unit form).** For `u : F*`, `u^{|F|−1} = 1`.
-/
lemma units_pow_card_sub_one (u : Fˣ) :
    u ^ (Fintype.card F - 1) = 1 := by
      rw [ ← card_units_eq, ← orderOf_dvd_iff_pow_eq_one ];
      exact orderOf_dvd_card.trans ( by simp +decide [ card_units_eq ] )

/-
**Order divides |F*|.** For any `u : F*`, `orderOf u ∣ |F| − 1`.
-/
lemma orderOf_units_dvd (u : Fˣ) :
    orderOf u ∣ Fintype.card F - 1 := by
      grind +suggestions

/-
═══════════════════════════════════════════
F3.2 : Power map bijectivity on units
═══════════════════════════════════════════

**Power map bijective on units.** If `gcd(a, |F|−1) = 1` then
    `u ↦ u^a` is bijective on `F*`.
    Uses `Nat.Coprime.pow_left_bijective` from Mathlib.
-/
lemma pow_units_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a) :
    Function.Bijective (fun u : Fˣ => u ^ a) := by
      have h_coprime : Nat.Coprime (Nat.card Fˣ) a := by
        rwa [ natCard_units_eq ];
      convert Nat.Coprime.pow_left_bijective h_coprime

/-- **Power map injective on units.** -/
lemma pow_units_injective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a) :
    Function.Injective (fun u : Fˣ => u ^ a) :=
  (pow_units_bijective ha).1

/-- **Power map surjective on units.** -/
lemma pow_units_surjective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a) :
    Function.Surjective (fun u : Fˣ => u ^ a) :=
  (pow_units_bijective ha).2

omit [Fintype F] in
/-- **Zero raised to positive power.** `0^a = 0` for `a ≥ 1`. -/
lemma zero_pow_of_pos {a : ℕ} (ha : 0 < a) : (0 : F) ^ a = 0 :=
  zero_pow ha.ne'

/-
**Power map injective on field (nonzero).** If `gcd(a, |F|−1) = 1` and `a ≥ 1`,
    and `x^a = y^a` with `x, y ≠ 0`, then `x = y`.
-/
lemma pow_injective_of_coprime_ne_zero {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (_ha_pos : 0 < a) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ a = y ^ a) :
    x = y := by
      convert Units.ext_iff.mp ( pow_units_injective ( show Nat.Coprime ( Fintype.card F - 1 ) a from ha ) <| show ( Units.mk0 x hx ) ^ a = ( Units.mk0 y hy ) ^ a from by simpa [ Units.ext_iff ] using h ) using 1

/-
**Power map bijective on field.** If `gcd(a, |F|−1) = 1` and `a ≥ 1`,
    then `x ↦ x^a` is bijective on `F`.
    Proof: 0 maps to 0, and the restriction to `F*` is bijective.
-/
lemma pow_field_bijective {a : ℕ} (ha : Nat.Coprime (Fintype.card F - 1) a)
    (ha_pos : 0 < a) :
    Function.Bijective (fun x : F => x ^ a) := by
      -- To prove injectivity, assume $x^a = y^a$ for some $x, y \in F$. If $x = 0$, then $y = 0$ because $0^a = 0$ and $y^a = 0$. If $x \neq 0$, then by `pow_injective_of_coprime_ne_zero`, we have $x = y$.
      have h_inj : Function.Injective (fun x : F => x ^ a) := by
        intro x y hxy;
        by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide;
        · rw [ zero_pow ha_pos.ne' ] at hxy; exact absurd hxy.symm ( pow_ne_zero _ hy ) ;
        · cases a <;> aesop;
        · exact pow_injective_of_coprime_ne_zero ha ha_pos hx hy hxy;
      exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-
═══════════════════════════════════════════
F3.3 : Inverse power on units
═══════════════════════════════════════════

**Inverse exponent exists.** If `gcd(a, |F|−1) = 1` and `|F| ≥ 2`,
    there exists `b` with `a·b ≡ 1 (mod |F|−1)`.
-/
omit [Field F] in
lemma exists_pow_mod_inverse {a : ℕ} (ha : Nat.Coprime a (Fintype.card F - 1))
    (_hF : 2 ≤ Fintype.card F) :
    ∃ b, a * b % (Fintype.card F - 1) = 1 % (Fintype.card F - 1) := by
      have := Nat.exists_mul_mod_eq_one_of_coprime ha;
      rcases n : Fintype.card F - 1 with ( _ | _ | n ) <;> simp_all +decide;
      · exact ⟨ 0, by norm_num ⟩;
      · exact ⟨ _, this.choose_spec.2 ⟩

/-
**Round-trip on units.** If `a·b ≡ 1 (mod |F|−1)` and `x ≠ 0`,
    then `(x^a)^b = x`.
-/
lemma pow_pow_eq_self {a b : ℕ}
    (hab : a * b % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ a) ^ b = x := by
      rw [ ← pow_mul, pow_eq_pow_of_mod_eq hx hab, pow_one ]

/-
═══════════════════════════════════════════
F3.4 : Mersenne GCD formula
═══════════════════════════════════════════

**Divisibility of Mersenne numbers.** `a ∣ b ⟹ (p^a − 1) ∣ (p^b − 1)` for `p ≥ 1`.
-/
lemma mersenne_dvd_of_dvd {p' a b : ℕ} (_hp' : 1 ≤ p') (hab : a ∣ b) :
    (p' ^ a - 1) ∣ (p' ^ b - 1) :=
  Nat.pow_sub_one_dvd_pow_sub_one p' hab

/-
**Mersenne modular identity.**
    `(p^b − 1) mod (p^a − 1) = (p^{b mod a} − 1)` for `p ≥ 2`, `a ≥ 1`.
    This is the key step for the Mersenne GCD formula.
-/
lemma mersenne_mod {p' a b : ℕ} (_hp' : 2 ≤ p') (_ha : a ≥ 1) :
    (p' ^ b - 1) % (p' ^ a - 1) = (p' ^ (b % a) - 1) % (p' ^ a - 1) := by
      norm_num [ Nat.cast_sub ( Nat.one_le_pow _ _ ( by linarith : 0 < p' ) ) ]

/-
**Mersenne GCD formula.**
    `gcd(p^a − 1, p^b − 1) = p^{gcd(a,b)} − 1` for `p ≥ 2`.
    Classic number theory result.
-/
lemma mersenne_gcd (p' a b : ℕ) :
    Nat.gcd (p' ^ a - 1) (p' ^ b - 1) = p' ^ Nat.gcd a b - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one p' a b

/-
═══════════════════════════════════════════
F3.5 : Mersenne coprimality corollaries
═══════════════════════════════════════════

**Mersenne coprimality.** If `gcd(a, b) = 1` and `p ≥ 2`, then
    `gcd(p^a − 1, p^b − 1) = p − 1`.
-/
lemma mersenne_coprime {p' a b : ℕ} (_hp' : 2 ≤ p') (hab : Nat.Coprime a b) :
    Nat.gcd (p' ^ a - 1) (p' ^ b - 1) = p' - 1 := by
      rw [mersenne_gcd, hab]; simp

/-
**Mersenne coprimality (char 2 special case).** If `gcd(a, b) = 1`, then
    `gcd(2^a − 1, 2^b − 1) = 1`.
-/
lemma mersenne_coprime_two {a b : ℕ} (hab : Nat.Coprime a b) :
    Nat.Coprime (2 ^ a - 1) (2 ^ b - 1) := by
      show Nat.gcd _ _ = 1
      rw [mersenne_gcd, hab]; simp

/-
**Coprimality with doubled exponent.** If `gcd(a, b) = 1` and `p ≥ 2`, then
    `gcd(p^a − 1, p^{2b} − 1) = p^{gcd(a, 2b)} − 1`.
-/
lemma mersenne_gcd_double (p' a b : ℕ) :
    Nat.gcd (p' ^ a - 1) (p' ^ (2 * b) - 1) = p' ^ Nat.gcd a (2 * b) - 1 :=
  mersenne_gcd p' a (2 * b)

/-
═══════════════════════════════════════════
F3.6 : Modular arithmetic helpers
═══════════════════════════════════════════

**Exponent mod identity.** `p^a mod (p^n − 1) = p^{a mod n} mod (p^n − 1)`
    for `p ≥ 2`, `n ≥ 1`.
-/
lemma pow_mod_mersenne {p' n a : ℕ} (hp' : 2 ≤ p') (_hn : n ≥ 1) :
    p' ^ a % (p' ^ n - 1) = p' ^ (a % n) % (p' ^ n - 1) := by
      -- Since $p^n \equiv 1 \mod (p^n - 1)$, we have $p^a \equiv p^{a \mod n} \mod (p^n - 1)$.
      have h_mod : p' ^ n ≡ 1 [MOD (p' ^ n - 1)] := by
        exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast, Nat.cast_sub <| Nat.one_le_pow _ _ <| zero_lt_two.trans_le hp' ] );
      rw [ ← Nat.mod_add_div a n, pow_add, pow_mul ] ; simpa using Nat.ModEq.mul_left _ ( h_mod.pow _ )

/-
**Mersenne positive.** `p^n − 1 ≥ 1` when `p ≥ 2` and `n ≥ 1`.
-/
lemma mersenne_pos {p' n : ℕ} (hp' : 2 ≤ p') (hn : 1 ≤ n) :
    1 ≤ p' ^ n - 1 := by
      exact Nat.le_sub_one_of_lt ( one_lt_pow₀ ( by linarith ) ( by linarith ) )

/-
**Mersenne at least two.** `p^n − 1 ≥ 2` when `p ≥ 2` and `n ≥ 2`.
-/
lemma mersenne_ge_two {p' n : ℕ} (hp' : 2 ≤ p') (hn : 2 ≤ n) :
    2 ≤ p' ^ n - 1 := by
      exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_left hp' _ ) |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( by linarith ) hn )

-- ═══════════════════════════════════════════
-- F3.7 : Congruent exponents on field elements
-- ═══════════════════════════════════════════

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-
**Congruent exponents give equal powers (unit version).**
    If `a ≡ b (mod |F*|)` then `u^a = u^b` for all `u : F*`.
-/
lemma units_pow_eq_of_mod_eq {a b : ℕ}
    (hab : a % (Fintype.card F - 1) = b % (Fintype.card F - 1))
    (u : Fˣ) : u ^ a = u ^ b := by
      rw [ ← Nat.mod_add_div a ( Fintype.card F - 1 ), ← Nat.mod_add_div b ( Fintype.card F - 1 ), hab ] ; norm_num [ pow_add, pow_mul ] ;
      simp +decide [ DempwolffMueller.units_pow_card_sub_one ]

/-
**Exponent reduction on units (mod |F|−1).**
    `u^a = u^{a mod (|F|−1)}` for `u : F*`.
-/
lemma units_pow_mod (a : ℕ) (u : Fˣ) :
    u ^ a = u ^ (a % (Fintype.card F - 1)) := by
      convert units_pow_eq_of_mod_eq ( show a % ( Fintype.card F - 1 ) = a % ( Fintype.card F - 1 ) from rfl ) u using 1;
      convert units_pow_eq_of_mod_eq ( show a % ( Fintype.card F - 1 ) % ( Fintype.card F - 1 ) = a % ( Fintype.card F - 1 ) from Nat.mod_mod _ _ ) u using 1

/-
**Product of congruences.**
    If `a·b ≡ c (mod n)` and `a·d ≡ e (mod n)`, then `b ≡ d (mod n)`
    when `gcd(a, n) = 1`. This is cancellation in `ℤ/nℤ`.
-/
lemma mul_mod_cancel_left {a b d n : ℕ}
    (ha : Nat.Coprime a n)
    (h1 : a * b % n = a * d % n) :
    b % n = d % n := by
      -- From the given congruence $a*b ≡ a*d (mod n)$, we can deduce that $a*(b-d) ≡ 0 (mod n)$.
      have h2 : a * (b - d) ≡ 0 [ZMOD n] := by
        exact Int.modEq_zero_iff_dvd.mpr ⟨ a * b / n - a * d / n, by linarith [ Int.emod_add_mul_ediv ( a * b ) n, Int.emod_add_mul_ediv ( a * d ) n ] ⟩;
      -- Since $a$ and $n$ are coprime, we can deduce that $b - d ≡ 0 [ZMOD n]$.
      have h3 : (b - d : ℤ) ≡ 0 [ZMOD n] := by
        rw [ Int.modEq_zero_iff_dvd ] at *;
        exact ( Int.dvd_of_dvd_mul_right_of_gcd_one h2 <| by simpa [ Int.gcd_natCast_natCast ] using ha.symm );
      exact Nat.ModEq.symm <| Nat.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using h3.symm.dvd;

/-
**Uniqueness of modular inverse.**
    If `a·b ≡ 1 (mod n)` and `a·c ≡ 1 (mod n)`, then `b ≡ c (mod n)`.
-/
lemma mod_inverse_unique {a b c n : ℕ}
    (ha : Nat.Coprime a n)
    (hb : a * b % n = 1 % n)
    (hc : a * c % n = 1 % n) :
    b % n = c % n := by
      -- From $a * b \equiv 1 \pmod{n}$ and $a * c \equiv 1 \pmod{n}$, we get $a * b \equiv a * c \pmod{n}$.
      have h_cong : a * b ≡ a * c [MOD n] := by
        exact hb.trans hc.symm;
      exact mul_mod_cancel_left ha h_cong

/-
**Modular scaling.**
    If `a·l ≡ 1 (mod n)` and `a·k' ≡ d (mod n)`, then
    `k' ≡ l·d (mod n)`.
-/
lemma mod_inverse_scale {a l k' d n : ℕ}
    (ha : Nat.Coprime a n)
    (hl : a * l % n = 1 % n)
    (hk : a * k' % n = d % n) :
    k' % n = (l * d) % n := by
      -- From $a * l ≡ 1 (mod n)$, multiply both sides by $d$: $a * l * d ≡ d (mod n)$.
      have hld : a * (l * d) ≡ d [MOD n] := by
        convert Nat.ModEq.mul_right d hl using 1 <;> ring;
      exact mul_mod_cancel_left ha ( hk.trans hld.symm )

/-- **Power of 2 addition identity.**
    `2^{m-1} * 2^{n-m+1} = 2^n` when `1 ≤ m ≤ n`. -/
lemma pow_two_mul_eq {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    2 ^ (m - 1) * 2 ^ (n - m + 1) = 2 ^ n := by
  rw [← pow_add]; congr 1; omega

/-- **2^n ≡ 1 mod (2^n - 1)** when n ≥ 1. -/
lemma pow_two_mod_mersenne {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n % (2 ^ n - 1) = 1 % (2 ^ n - 1) := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by ring
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  conv_lhs => rw [← h1]
  simp

end DempwolffMueller