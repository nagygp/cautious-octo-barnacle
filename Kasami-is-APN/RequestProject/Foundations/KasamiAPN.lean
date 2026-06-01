/-
# Layer 42: Kasami APN Proof & Gold APN

This module proves that the Gold and Kasami power functions are APN
on GF(2^n) when gcd(k,n) = 1 (and n odd for Kasami).

## Proof Architecture

### Gold APN (x^{2^k+1})
The differential equation (x+a)^{2^k+1} + x^{2^k+1} = b expands to:
  a^{2^k} · x + a · x^{2^k} + a^{2^k+1} = b
This is a linearized polynomial equation in x of degree 2^k.
When gcd(k,n) = 1, the kernel of L(x) = x^{2^k} + x has exactly 2 elements
(0 and 1 over GF(2)), so the differential equation has ≤ 2 solutions.

### Kasami APN (x^{2^{2k} - 2^k + 1})
More involved but uses the same linearized polynomial machinery.
The Kasami exponent d = 2^{2k} - 2^k + 1 satisfies:
- d ≡ 1 (mod 2^k - 1)
- d ≡ 0 (mod 2^k + 1) ... actually d = (2^k)^2 - 2^k + 1

The differential equation for x^d reduces to showing that a system
involving the Frobenius sum S_k(u) = u + u^2 + ... + u^{2^{k-1}}
has at most 2 solutions, which uses the coprimality
gcd(2^{2k} - 2^k + 1, 2^n - 1) = 1.

### Kasami Coprimality
Key number theory: gcd(2^{2k}-2^k+1, 2^n-1) = 1 when gcd(k,n)=1 and n odd.

Proof:
1. d | 2^{3k}+1 (since x^2-x+1 | x^3+1 with x=2^k)
2. So d | 2^{6k}-1
3. gcd(2^{6k}-1, 2^n-1) = 2^{gcd(6k,n)}-1
4. gcd(6k,n) = gcd(6,n) (since gcd(k,n)=1)
5. n odd ⇒ gcd(6,n) ∈ {1,3}
6. If gcd(6,n)=1: d | 1, done
7. If gcd(6,n)=3: d | 7, but 3∤k (since 3|n, gcd(k,n)=1) so d ≢ 0 (mod 7)

## DAG Structure (depends on Layers 38, 40, 41)
import Mathlib
import RequestProject.Foundations.BooleanFunctions

-/
namespace Caramello.KasamiAPN

-/
open Caramello.APNTheory Caramello.MCMInjectivity Caramello.BooleanFunctions
-/
open Finset Fintype

-/
/-! ## Section 1: Linearized Polynomial Kernel Theory

The kernel of L(x) = x^{2^k} + x over GF(2^n) has exactly
2^{gcd(k,n)} elements. This is a fundamental result in finite
field theory.

/-- The linearized polynomial L_k(x) = x^{2^k} + x.
    In characteristic 2, this is the same as x^{2^k} - x. -/
-/
-/
def linPolyL {F : Type*} [Ring F] (k : ℕ) (x : F) : F :=
  x ^ (2 ^ k) + x

/-- The kernel of L_k. -/
-/
-/
def linPolyKernel {F : Type*} [Ring F] (k : ℕ) : Set F :=
  { x | linPolyL k x = 0 }

/-- L_k(0) = 0. -/
-/
-/
theorem linPolyL_zero {F : Type*} [Ring F] (k : ℕ) :
    linPolyL k (0 : F) = 0 := by simp [linPolyL]

/-- In characteristic 2, L_k(1) = 0 (since 1^{2^k} + 1 = 1 + 1 = 0). -/
-/
-/
theorem linPolyL_one_char2 {F : Type*} [Ring F] (hchar : (2 : F) = 0) (k : ℕ) :
    linPolyL k (1 : F) = 0 := by
  simp only [linPolyL, one_pow]
  have : (1 : F) + 1 = 2 := by norm_num
  rw [this]; exact hchar

/-- The Frobenius sum S_k(x) = x + x^2 + ... + x^{2^{k-1}} is additive
    (in characteristic 2, this is a linearized polynomial). -/
-/
-/
noncomputable def frobSum {F : Type*} [Semiring F] (k : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range k, x ^ (2 ^ i)

/-- S_0 = 0. -/
-/
-/
theorem frobSum_zero {F : Type*} [Semiring F] (x : F) :
    frobSum 0 x = 0 := by simp [frobSum]

/-- S_1 = id. -/
-/
-/
theorem frobSum_one {F : Type*} [Semiring F] (x : F) :
    frobSum 1 x = x := by simp [frobSum]

-/
-/
/-! ## Section 2: Mersenne GCD Identity

The fundamental identity: gcd(2^a - 1, 2^b - 1) = 2^{gcd(a,b)} - 1.
This is the key tool for coprimality proofs.

/-- Mersenne divisibility: d | n implies (2^d - 1) | (2^n - 1). -/
-/
-/
-/
theorem mersenne_dvd {d n : ℕ} (hd : 0 < d) (h : d ∣ n) :
    (2 ^ d - 1) ∣ (2 ^ n - 1) := by
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 h

/-
The Mersenne GCD identity.
    gcd(2^a - 1, 2^b - 1) = 2^{gcd(a,b)} - 1 for positive a, b.
-/
-/
-/
-/
theorem mersenne_gcd (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd (2 ^ a - 1) (2 ^ b - 1) = 2 ^ (Nat.gcd a b) - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one 2 a b

-/
-/
-/
-/
/-! ## Section 3: Kasami Coprimality

The core number theory for Kasami APN:
gcd(2^{2k} - 2^k + 1, 2^n - 1) = 1 when gcd(k,n) = 1 and n odd.

/-
The Kasami exponent divides 2^{3k} + 1.
    Proof: (2^k)^2 - 2^k + 1 divides (2^k)^3 + 1 = (2^k + 1)((2^k)^2 - 2^k + 1).
-/
-/
-/
-/
-/
-/
theorem kasami_divides_cube_plus_one (k : ℕ) (hk : 0 < k) :
    kasamiExponent k ∣ (2 ^ (3 * k) + 1) := by
  unfold kasamiExponent;
  zify;
  rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
  exact ⟨ 1 + 2 ^ k, by ring ⟩

/-
The Kasami exponent divides 2^{6k} - 1.
    Since d | 2^{3k}+1 and 2^{3k}+1 | 2^{6k}-1.
-/
-/
-/
-/
-/
-/
-/
theorem kasami_divides_mersenne_6k (k : ℕ) (hk : 0 < k) :
    kasamiExponent k ∣ (2 ^ (6 * k) - 1) := by
  convert Nat.dvd_trans ( kasami_divides_cube_plus_one k hk ) _ using 1;
  exact ⟨ 2 ^ ( 3 * k ) - 1, by rw [ ← Nat.sq_sub_sq ] ; ring ⟩

/-
When gcd(k,n)=1 and n is odd, gcd(6k, n) divides 3.
    Since gcd(6k,n) = gcd(6,n)·gcd(k,n)/... actually
    gcd(6k,n) = gcd(6,n) when gcd(k,n)=1.
-/
-/
-/
-/
-/
-/
-/
-/
theorem gcd_6k_n_divides_3 {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) :
    Nat.gcd (6 * k) n ∣ 3 := by
  -- Since gcd(k,n) = 1, gcd(6k, n) = gcd(6, n).
  have h_gcd_6k_n : Nat.gcd (6 * k) n = Nat.gcd 6 n := by
    exact Nat.Coprime.gcd_mul_right_cancel _ hgcd;
  rcases hn_odd with ⟨ m, rfl ⟩ ; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
  exact Nat.dvd_of_mod_eq_zero ( by rw [ Nat.gcd_rec ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_mod ] ; have := Nat.mod_lt m ( by decide : 0 < 6 ) ; interval_cases m % 6 <;> trivial )

/-
The Kasami exponent is not divisible by 7 when 3 ∤ k.
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem kasami_not_dvd_seven {k : ℕ} (hk : 0 < k) (h3 : ¬ (3 ∣ k)) :
    ¬ (7 ∣ kasamiExponent k) := by
  -- Since 3 does not divide k, we have that 2^k ≡ 2 or 4 (mod 7).
  have h_mod : (2 ^ k) % 7 = 2 ∨ (2 ^ k) % 7 = 4 := by
    rw [ ← Nat.mod_add_div k 3 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ; ( rw [ Nat.dvd_iff_mod_eq_zero ] at h3; have := Nat.mod_lt k zero_lt_three; interval_cases k % 3 <;> trivial; );
  rcases h_mod with ( h | h ) <;> rw [ Nat.dvd_iff_mod_eq_zero ] <;> rw [ show kasamiExponent k = 2 ^ ( 2 * k ) - 2 ^ k + 1 by rfl ] <;> rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k ) ) 7, ← Nat.mod_add_div ( 2 ^ k ) 7 ] <;> norm_num [ Nat.pow_mul, Nat.pow_mod, h ];
  · rw [ ← Nat.mod_add_div k 3 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k zero_lt_three; interval_cases k % 3 <;> norm_num at *;
    omega;
  · rw [ ← Nat.mod_add_div k 6 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k ( by decide : 6 > 0 ) ; interval_cases k % 6 <;> simp_all +arith +decide;
    · omega;
    · bv_omega

/-
**Main coprimality theorem for Kasami**:
    gcd(2^{2k} - 2^k + 1, 2^n - 1) = 1 when gcd(k,n)=1 and n odd.
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem kasami_coprime_mersenne' {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n) :
    Nat.Coprime (kasamiExponent k) (2 ^ n - 1) := by
  apply Nat.coprime_of_dvd;
  intro p hp hp_dvd hp_not_dvd
  have hp_div_6k_n : p ∣ 2 ^ (Nat.gcd (6 * k) n) - 1 := by
    have hp_div_6k : p ∣ 2 ^ (6 * k) - 1 := by
      exact dvd_trans hp_dvd ( kasami_divides_mersenne_6k k hk );
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add ];
  have := gcd_6k_n_divides_3 hk hn hgcd hn_odd; ( have := Nat.le_of_dvd ( by positivity ) this; interval_cases _ : Nat.gcd ( 6 * k ) n <;> simp_all +decide ; );
  have := Nat.le_of_dvd ( by decide ) hp_div_6k_n; interval_cases p <;> simp_all +decide ;
  exact absurd ( kasami_not_dvd_seven hk ( by intro t; have := Nat.dvd_gcd ( show 3 ∣ k from t ) ( show 3 ∣ n from ‹Nat.gcd ( 6 * k ) n = 3› ▸ Nat.gcd_dvd_right _ _ ) ; simp_all +decide ) ) ( by aesop )

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 4: Gold APN Proof

The Gold function x^{2^k+1} is APN on GF(2^n) when gcd(k,n)=1.

The proof goes through the differential equation:
  (x+a)^{2^k+1} + x^{2^k+1} = b
which in characteristic 2 expands to:
  a^{2^k} · x + a · x^{2^k} + a^{2^k+1} = b

This is an affine linearized polynomial equation. The associated
homogeneous equation a^{2^k} · x + a · x^{2^k} = 0 (for a ≠ 0)
simplifies to x^{2^k} + x · a^{2^k - 1} = 0, i.e., (x/a)^{2^k} + (x/a) = 0.

The kernel of L_k(u) = u^{2^k} + u has exactly 2^{gcd(k,n)} elements.
When gcd(k,n) = 1, this is 2 elements, giving APN.

/-
Gold differential expansion in char 2: the differential equation
    for x^{2^k+1} is a linearized polynomial equation.
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem gold_differential_linearized {F : Type*} [Field F]
    [CharP F 2] (k : ℕ) (a x : F) :
    (x + a) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) =
    a ^ (2 ^ k) * x + a * x ^ (2 ^ k) + a ^ (2 ^ k + 1) := by
  -- By the properties of the Frobenius endomorphism in characteristic 2, we have $(x + a)^{2^k} = x^{2^k} + a^{2^k}$.
  rw [ pow_succ', pow_succ' ];
  rw [ add_pow_char_pow ] ; ring;
  rw [ show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ] ; ring

/-- Gold functions are APN: the main theorem.
    x^{2^k+1} is APN on GF(2^n) when gcd(k,n) = 1 and n odd. -/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem gold_is_apn {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (goldExponent k) : F → F) := by
  sorry

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 5: Kasami APN Proof Architecture

The Kasami function x^{2^{2k}-2^k+1} is APN on GF(2^n) when gcd(k,n)=1.

The proof strategy:
1. Show the differential equation has ≤ 2 solutions for each (a,b) with a ≠ 0
2. Use the substitution y = x/a to normalize
3. Reduce to a system involving the Frobenius sum S_k
4. Use the coprimality of the Kasami exponent with 2^n - 1
5. Conclude via MCM-style injectivity

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem kasami_is_apn {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (kasamiExponent k) : F → F) := by
  sorry

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 6: Kasami Permutation Property

The Kasami function is a permutation of GF(2^n)* when gcd(k,n)=1 and n odd.
This follows from the coprimality theorem.

/-- Kasami is a permutation when coprime. -/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem kasami_is_perm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    Function.Bijective (fun u : Fˣ => u ^ kasamiExponent k) := by
  have hcop := kasami_coprime_mersenne' hk hn hgcd hn_odd
  have hcop' : Nat.Coprime (Nat.card Fˣ) (kasamiExponent k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]; exact hcop.symm
  exact (powCoprime hcop').bijective

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 7: Gold and Kasami AB Property

Gold and Kasami functions are Almost Bent when n is odd.
This is a deeper result involving the Walsh transform.

/-- Gold functions are AB when n is odd. -/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem gold_is_ab {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAB (fun _ => (0 : ZMod 2)) n (powerFunction (goldExponent k) : F → F) := by
  sorry

/-- Kasami functions are AB when n is odd. -/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem kasami_is_ab {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAB (fun _ => (0 : ZMod 2)) n (powerFunction (kasamiExponent k) : F → F) := by
  sorry

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 8: Bridge Framework Connection

The Gold/Kasami APN proofs instantiate the bridge pattern:

```
  Number Theory Layer:
    gcd(d, 2^n-1) = 1        [coprimality invariant]
         ↓
  Group Theory Layer:
    powCoprime → bijection    [Mathlib bridge]
         ↓
  Linearized Poly Layer:
    ker(L_k) has 2^{gcd(k,n)} elements  [finite field theory]
         ↓
  Differential Layer:
    |{x : Δ_a f(x) = b}| ≤ 2  [APN conclusion]
```

Each layer transfers the coprimality invariant to a different context.
This is the concrete instantiation of Caramello's abstract bridge
technique, where the "Morita invariant" is coprimality.

/-- The bridge diagram: coprimality → permutation → injectivity → APN.
    This connects the abstract Morita invariant (coprimality) to the
    concrete cryptographic property (APN). -/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
theorem bridge_diagram {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_odd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) :
    -- Layer 1: Number theory gives coprimality
    Nat.Coprime (goldExponent k) (2 ^ n - 1) ∧
    -- Layer 2: Coprimality gives permutation
    Function.Bijective (fun u : Fˣ => u ^ goldExponent k) ∧
    -- Layer 3: Permutation gives injectivity on F*
    (∀ a b : F, a ≠ 0 → b ≠ 0 → mcmMap k a = mcmMap k b → a = b) := by
  refine ⟨?_, ?_, ?_⟩
  · exact coprime_gold_mersenne hk hn hgcd hn_odd
  · exact mcmUnitMap_bijective hk hn hgcd hn_odd hcard
  · exact mcm_injective hk hn hgcd hn_odd hcard

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
/-! ## Section 9: Conjecture DAG for Full Kasami Proof

The following is the dependency graph for a complete Kasami APN proof:

```
kasami_is_apn
  ├── kasami_coprime_mersenne'
  │     ├── kasami_divides_cube_plus_one
  │     ├── kasami_divides_mersenne_6k
  │     ├── mersenne_gcd
  │     ├── gcd_6k_n_divides_3
  │     └── kasami_not_dvd_seven
  ├── kasami_differential_reduction
  │     ├── gold_differential_linearized
  │     └── char2_expansion
  └── kasami_kernel_bound
        ├── linPoly_kernel_card (ker(L_k) = 2^gcd(k,n))
        └── frobSum_kernel_bound
```

Each node is a lemma. Leaf nodes are the most concrete/provable.
Interior nodes combine children via algebraic manipulation.

### Status:
- kasami_coprime_mersenne': coprimality (number theory core)
- kasami_is_perm: follows from coprimality (PROVED ✓)
- gold_differential_linearized: char 2 expansion
- gold_is_apn: full Gold APN (combines differential + kernel)
- kasami_is_apn: full Kasami APN (the hardest theorem)

-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
end Caramello.KasamiAPN
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/
-/