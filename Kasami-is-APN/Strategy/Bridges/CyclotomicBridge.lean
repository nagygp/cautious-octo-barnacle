/-
# Bridge Pathway: Cyclotomic Polynomial Bridge

## Key Insight

The Kasami exponent d = 2^{2k} - 2^k + 1 is precisely the **third cyclotomic
polynomial** evaluated at 2^k:

  Φ₃(X) = X² - X + 1, so d = Φ₃(2^k).

This connects Kasami APN to the deep theory of cyclotomic polynomials,
which in turn connects to:
- Roots of unity in finite fields
- Galois theory of cyclotomic extensions
- The multiplicative structure of (ℤ/mℤ)*

## Bridge Diagram

```
  Kasami APN
     |
  d = Φ₃(2^k) ─── "Kasami is cyclotomic"
     |
  d | 2^{3k}+1 ─── Φ₃(X) | X³+1 ─── X³ = -1 = 1 (char 2)
     |                                      |
  gcd(d, 2^n-1) = 1 ─── ord(2^k mod d) | n ─── coprimality
     |                                      |
  x^d permutation ─── multiplicative order ─── primitive roots
     |
  "only 2 preimages" ─── APN property
```

## Morita Equivalence

T₁ = "Theory of Kasami differentials over GF(2^n)"
T₂ = "Theory of Φ₃-values in multiplicative groups of prime-power order"

Bridge invariant: "gcd(Φ₃(q), q^n - 1) = 1" ↔ "x^{Φ₃(q)} is a permutation"

## DAG Structure

```
Layer 0: Cyclotomic identities (pure number theory)
Layer 1: Cyclotomic polynomials evaluated at prime powers
Layer 2: Divisibility and GCD via cyclotomic factorization
Layer 3: Multiplicative order and permutation property
Layer 4: Connection to linearized polynomial kernel
Layer 5: Assembly — Kasami coprimality via cyclotomic bridge
```
-/
import Mathlib

set_option maxHeartbeats 800000

namespace CyclotomicBridge

open Finset Fintype Nat

/-! ## Layer 0: Cyclotomic Identities

These are pure number-theoretic identities connecting Φ₃ to the Kasami exponent.
Each lemma is a single algebraic manipulation.
-/

/-- The Kasami exponent. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- **L0.1** The third cyclotomic polynomial Φ₃(X) = X² - X + 1.
    Over ℤ: Φ₃(X) = X² - X + 1.
    Key: d = Φ₃(2^k). -/
theorem kasami_is_cyclotomic3 (k : ℕ) :
    (kasamiExp k : ℤ) = (2 ^ k : ℤ) ^ 2 - 2 ^ k + 1 := by
  simp only [kasamiExp]; zify
  rw [Nat.cast_sub (by gcongr <;> omega)]
  push_cast; ring

/-- **L0.2** Φ₃(X) divides X³ + 1: (X² - X + 1)(X + 1) = X³ + 1.
    Equivalently: d · (2^k + 1) = 2^{3k} + 1. -/
theorem cyclotomic3_divides_cube_plus_one (k : ℕ) :
    kasamiExp k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  unfold kasamiExp; zify
  rw [Nat.cast_sub (by gcongr <;> omega)]
  push_cast; ring

/-- **L0.3** X³ + 1 = (X + 1)(X² - X + 1) over ℤ.
    This is the cyclotomic factorization. -/
theorem cube_plus_one_factor (X : ℤ) :
    X ^ 3 + 1 = (X + 1) * (X ^ 2 - X + 1) := by ring

/-- **L0.4** d divides 2^{3k} + 1. -/
theorem kasami_dvd_cube_plus_one (k : ℕ) :
    kasamiExp k ∣ 2 ^ (3 * k) + 1 :=
  ⟨2 ^ k + 1, (cyclotomic3_divides_cube_plus_one k).symm⟩

/-- **L0.5** Therefore d divides 2^{6k} - 1 (since (2^{3k}+1) | (2^{6k}-1)). -/
theorem kasami_dvd_sixth_power_minus_one (k : ℕ) :
    kasamiExp k ∣ 2 ^ (6 * k) - 1 := by
  have h1 := kasami_dvd_cube_plus_one k
  have h2 : (2 ^ (3 * k) + 1) ∣ (2 ^ (6 * k) - 1) := by
    have : 2 ^ (6 * k) - 1 = (2 ^ (3 * k) + 1) * (2 ^ (3 * k) - 1) := by
      have hle : 1 ≤ 2 ^ (3 * k) := Nat.one_le_two_pow
      zify [hle, Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2)]
      push_cast; ring
    exact ⟨2 ^ (3 * k) - 1, this⟩
  exact dvd_trans h1 h2

/-- **L0.6** Kasami exponent is always odd. -/
theorem kasamiExp_odd (k : ℕ) : Odd (kasamiExp k) := by
  cases k with
  | zero => simp [kasamiExp]
  | succ k =>
    unfold kasamiExp; rw [Nat.odd_iff]
    have : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    have : 2 ∣ 2 ^ (2 * (k + 1)) := dvd_pow_self 2 (by omega)
    omega

/-- **L0.7** Kasami exponent is positive. -/
theorem kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  unfold kasamiExp; omega

/-! ## Layer 1: Mersenne GCD Identity

The fundamental identity gcd(2^a - 1, 2^b - 1) = 2^{gcd(a,b)} - 1
connects GCD computations to GCD of exponents.
-/

/-- **L1.1** Mersenne GCD: gcd(2^a - 1, 2^b - 1) = 2^{gcd(a,b)} - 1. -/
theorem mersenne_gcd (a b : ℕ) :
    Nat.gcd (2 ^ a - 1) (2 ^ b - 1) = 2 ^ Nat.gcd a b - 1 := by
  sorry -- Well-known number theory result; proved in KasamiAPN.lean

/-- **L1.2** Corollary: 2^a - 1 | 2^b - 1 ↔ a | b. -/
theorem mersenne_dvd_iff (a b : ℕ) (ha : a ≥ 1) :
    (2 ^ a - 1) ∣ (2 ^ b - 1) ↔ a ∣ b := by
  sorry -- Follows from mersenne_gcd

/-! ## Layer 2: GCD via Cyclotomic Factorization

The cyclotomic bridge: compute gcd(d, 2^n - 1) using the factorization
d | 2^{6k} - 1 and the Mersenne GCD identity.
-/

/-- **L2.1** gcd(2^{6k} - 1, 2^n - 1) = 2^{gcd(6k,n)} - 1. -/
theorem gcd_sixth_mersenne (k n : ℕ) :
    Nat.gcd (2 ^ (6 * k) - 1) (2 ^ n - 1) = 2 ^ Nat.gcd (6 * k) n - 1 :=
  mersenne_gcd (6 * k) n

/-- **L2.2** When gcd(k,n) = 1: gcd(6k, n) = gcd(6, n).
    Proof: gcd(6k, n) = gcd(6, n) · gcd(k, n/gcd(6,n)) but since gcd(k,n) = 1... -/
theorem gcd_6k_n_eq (k n : ℕ) (hcop : Nat.Coprime k n) :
    Nat.gcd (6 * k) n = Nat.gcd 6 n := by
  sorry -- Number theory

/-- **L2.3** When n is odd: gcd(6, n) ∈ {1, 3}. -/
theorem gcd_6_odd (n : ℕ) (hn : Odd n) (hn0 : n ≥ 1) :
    Nat.gcd 6 n = 1 ∨ Nat.gcd 6 n = 3 := by
  sorry -- Since n is odd, gcd(2,n) = 1, so gcd(6,n) | 3

/-- **L2.4** d divides 2^{gcd(6k,n)} - 1 (since d | 2^{6k}-1 and
    2^{6k}-1 = gcd · cofactor). -/
theorem kasami_dvd_mersenne_gcd (k n : ℕ) :
    Nat.gcd (kasamiExp k) (2 ^ n - 1) ∣ 2 ^ Nat.gcd (6 * k) n - 1 := by
  sorry

/-! ## Layer 3: The Coprimality Theorem via Cyclotomic Bridge

The final step: show gcd(d, 2^n - 1) = 1.
-/

/-- **L3.1** Case gcd(6,n) = 1: d | 2^1 - 1 = 1, so d = 1 (impossible for k ≥ 1)
    or gcd(d, 2^n-1) = 1. -/
theorem coprime_case_gcd1 (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcop : Nat.Coprime k n) (hgcd : Nat.gcd 6 n = 1) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  sorry

/-- **L3.2** Case gcd(6,n) = 3: d | 2^3 - 1 = 7.
    But d = 2^{2k} - 2^k + 1, and d ≡ 0 (mod 7) iff 3 | k.
    Since gcd(k,n) = 1 and 3 | n, we have 3 ∤ k, so d ≢ 0 (mod 7). -/
theorem coprime_case_gcd3 (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcop : Nat.Coprime k n) (hgcd : Nat.gcd 6 n = 3) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  sorry

/-- **L3.3** d not divisible by 7 when 3 ∤ k.
    Key lemma for the gcd(6,n)=3 case. -/
theorem kasami_not_dvd_7 (k : ℕ) (hk : k ≥ 1) (h3 : ¬(3 ∣ k)) :
    ¬(7 ∣ kasamiExp k) := by
  sorry

/-- **L3.4** 3 | n and gcd(k,n) = 1 implies 3 ∤ k. -/
theorem three_not_dvd_k (k n : ℕ) (hcop : Nat.Coprime k n) (h3n : 3 ∣ n) :
    ¬(3 ∣ k) := by
  sorry

/-- **L3.5** The Master Coprimality Theorem (via cyclotomic bridge). -/
theorem kasami_coprime_master (k n : ℕ) (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcop : Nat.Coprime k n) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  rcases gcd_6_odd n hn hn0 with h1 | h3
  · exact coprime_case_gcd1 k n hk hn hn0 hcop h1
  · exact coprime_case_gcd3 k n hk hn hn0 hcop h3

/-! ## Layer 4: From Coprimality to Permutation (Multiplicative Order Bridge)

gcd(d, 2^n - 1) = 1 ↔ x^d is a permutation of GF(2^n)*.
This connects number theory (coprimality) to algebra (permutation).
-/

/-- **L4.1** Coprimality implies x^d is injective on GF(2^n)*. -/
theorem coprime_implies_perm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (hd : Nat.Coprime d (Fintype.card F - 1)) :
    Function.Injective (fun (x : F) => x ^ d) := by
  sorry

/-- **L4.2** On a finite set, injective ↔ surjective ↔ bijective. -/
theorem finite_injective_iff_bijective {F : Type*} [Fintype F]
    (f : F → F) : Function.Injective f ↔ Function.Bijective f :=
  ⟨fun h => ⟨h, h.surjective_of_fintype (Equiv.refl F)⟩, fun h => h.1⟩

/-- **L4.3** x^d permutes GF(2^n) when gcd(d, 2^n-1) = 1. -/
theorem kasami_is_permutation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {k n : ℕ} (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n) :
    Function.Bijective (fun (x : F) => x ^ kasamiExp k) := by
  sorry

/-! ## Layer 5: From Permutation to APN

Being a permutation is necessary but not sufficient for APN.
The extra structure comes from the linearized polynomial kernel.

The bridge: "x^d permutes" + "ker(L_k) = GF(2)" → "x^d is APN"

```
         Kasami is APN
              |
    ┌─────────┴──────────┐
    |                    |
  x^d permutes        ker(L_k) = {0,1}
    |                    |
  gcd(d,2^n-1)=1     gcd(k,n)=1
    |                    |
  cyclotomic          Mersenne GCD
  factorization       identity
```
-/

/-- **L5.1** The linearized polynomial L_k(x) = x^{2^k} + x. -/
def linPolyL (k : ℕ) {F : Type*} [Field F] [CharP F 2] (x : F) : F :=
  x ^ (2 ^ k) + x

/-- **L5.2** L_k is additive (Freshman's dream). -/
theorem linPolyL_add {F : Type*} [Field F] [CharP F 2] (k : ℕ) (x y : F) :
    linPolyL k (x + y) = linPolyL k x + linPolyL k y := by
  simp [linPolyL]; rw [add_pow_expChar_pow]; ring

/-- **L5.3** L_k(0) = 0. -/
theorem linPolyL_zero {F : Type*} [Field F] [CharP F 2] (k : ℕ) :
    linPolyL k (0 : F) = 0 := by simp [linPolyL]

/-- **L5.4** L_k(1) = 0 in char 2. -/
theorem linPolyL_one {F : Type*} [Field F] [CharP F 2] (k : ℕ) :
    linPolyL k (1 : F) = 0 := by
  simp only [linPolyL, one_pow]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : (1 : F) + 1 = 2 := by ring
  rw [this, h2]

/-- **L5.5** Kernel of L_k has size 2^{gcd(k,n)} in GF(2^n). -/
theorem linPolyL_kernel_size {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) :
    Fintype.card {x : F // linPolyL k x = 0} = 2 ^ Nat.gcd k n := by
  sorry

/-- **L5.6** When gcd(k,n) = 1, kernel = {0, 1}. -/
theorem linPolyL_kernel_trivial {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {k n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hcop : Nat.Coprime k n) (x : F) (hx : linPolyL k x = 0) :
    x = 0 ∨ x = 1 := by
  sorry

/-! ## Layer 6: The Differential Equation via Cyclotomic Structure

The APN condition requires: for all a ≠ 0, the equation
  (x+a)^d + x^d = b  has ≤ 2 solutions.

Using d = Φ₃(2^k), the differential expands via:
  (x+a)^d + x^d = a^d + Cross_d(x, a)

where the cross term factors through L_k.
-/

/-- **L6.1** The differential of x^d.
    D_a(x) = (x+a)^d + x^d. -/
def kasamiDiff (k : ℕ) {F : Type*} [CommRing F] (a x : F) : F :=
  (x + a) ^ kasamiExp k + x ^ kasamiExp k

/-- **L6.2** The differential equation has ≤ 2 solutions iff APN. -/
def isAPN {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    Fintype.card {x : F // f (x + a) + f x = b} ≤ 2

/-- **L6.3** The Kasami function is APN when gcd(k,n) = 1 and n odd.
    This is the target theorem, assembled from all layers. -/
theorem kasami_is_apn {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {k n : ℕ} (hk : k ≥ 1) (hn : Odd n) (hn0 : n ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hcop : Nat.Coprime k n) :
    isAPN (fun (x : F) => x ^ kasamiExp k) := by
  sorry

/-! ## Summary: Cyclotomic Bridge Architecture

The cyclotomic bridge gives the cleanest path from number theory to APN:

```
                    kasami_is_apn
                         |
            ┌────────────┼────────────┐
            |            |            |
     permutation    kernel={0,1}   differential
     (Layer 4)      (Layer 5)      expansion
            |            |            |
     gcd(d,2^n-1)=1  gcd(k,n)=1   cyclotomic
     (Layer 3)       (hypothesis)  factorization
            |                         |
     cyclotomic ──────────────────────┘
     bridge
     (Layers 0-2)
```

### What Makes This Bridge Novel

1. **d = Φ₃(2^k)** is not just a coincidence — it explains WHY the
   Kasami exponent has the divisibility properties it does.

2. The cyclotomic factorization X³+1 = (X+1)(X²-X+1) at X = 2^k
   is the NUMBER-THEORETIC analogue of the ALGEBRAIC factorization
   of the differential equation.

3. The bridge connects:
   - **Number theory** (cyclotomic polynomials, Mersenne GCD)
   - **Group theory** (multiplicative orders, permutations)
   - **Field theory** (linearized polynomials, Frobenius)
   
   These are three different "theories" in the Caramello sense,
   connected via their classifying toposes.
-/

end CyclotomicBridge
