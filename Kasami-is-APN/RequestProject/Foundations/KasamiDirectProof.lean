/-
# Layer 44: Direct Proof of Kasami APN — Carlet-Kim-Mesnager Approach

This module formalizes the direct proof of APN-ness of Kasami functions
following the approach of Carlet, Kim, and Mesnager (2020), which resolved
an open question from WAIFI 2014.

## Proof Architecture

### Case 1: n even (simplest direct proof)
Key identity: F(X) + F(X+1) + 1 = f_{k,2^k+1}(X + X²)
where f_{k,2^k+1}(X) = T_k(X)^{2^k+1} / X^{2^k} is the
Müller-Cohen-Matthews (MCM) polynomial.

Since gcd(k,n)=1 and n is even, k must be odd. When k is odd,
f_{k,2^k+1} is a permutation on GF(2^n) (Cohen-Matthews 1994).
Therefore F(X) + F(X+1) is 2-to-1, making Kasami APN.

### Case 2: n odd
Reduces to the MCM equation (v+1)^{q+1} + cv = 0, which by
Kim-Mesnager has 0, 1, or 3 solutions. When 3 exist, the trace
condition eliminates all of them.

## References
- Carlet, Kim, Mesnager: "A direct proof of APN-ness of the Kasami functions"
- Kim, Choe, Mesnager: "Solving X^{q+1}+X+a=0 over Finite Fields"
- Cohen, Matthews: "A class of exceptional polynomials" (1994)

## DAG Structure (depends on Layers 38, 40, 41, 42)
import Mathlib
import RequestProject.Foundations.KasamiAPN

-/
namespace Caramello.KasamiDirectProof

-/
open Caramello.APNTheory Caramello.MCMInjectivity Caramello.KasamiAPN
-/
open Finset Fintype

-/
/-! ## Section 1: MCM Polynomial (Müller-Cohen-Matthews)

f_{k,q+1}(X) = T_k(X)^{q+1} / X^q where
T_k(X) = X + X^2 + ... + X^{2^{k-1}} is the partial trace.

/-- The partial trace T_k(X) = Σ_{i=0}^{k-1} X^{2^i}. -/
-/
-/
noncomputable def partialTrace {F : Type*} [Semiring F] (k : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range k, x ^ (2 ^ i)

/-- T_0(x) = 0. -/
-/
-/
theorem partialTrace_zero {F : Type*} [Semiring F] (x : F) :
    partialTrace 0 x = 0 := by simp [partialTrace]

/-- T_1(x) = x. -/
-/
-/
theorem partialTrace_one {F : Type*} [Semiring F] (x : F) :
    partialTrace 1 x = x := by
  simp [partialTrace, Finset.sum_range_one]

/-- The MCM polynomial: f_{k,q+1}(X) = T_k(X)^{2^k+1} / X^{2^k}. -/
-/
-/
noncomputable def mcmPoly {F : Type*} [Field F] [DecidableEq F] (k : ℕ) (x : F) : F :=
  if x = 0 then 0
  else (partialTrace k x) ^ (2 ^ k + 1) * x⁻¹ ^ (2 ^ k)

/-- MCM(0) = 0. -/
-/
-/
theorem mcmPoly_zero {F : Type*} [Field F] [DecidableEq F] (k : ℕ) :
    mcmPoly k (0 : F) = 0 := by simp [mcmPoly]

-/
-/
/-! ## Section 2: The Key Identity for n Even

F(X) + F(X+1) + 1 = f_{k,2^k+1}(X + X²)

where F(X) = X^{2^{2k}-2^k+1} is the Kasami function.

/-- The Kasami differential: F(X) + F(X+1). -/
-/
-/
-/
noncomputable def kasamiDifferential {F : Type*} [Field F] (k : ℕ) (x : F) : F :=
  x ^ (kasamiExponent k) + (x + 1) ^ (kasamiExponent k)

/-- The Artin-Schreier map X ↦ X + X². -/
-/
-/
-/
def artinSchreier {F : Type*} [Ring F] (x : F) : F := x + x ^ 2

/-- **Key Identity** (Carlet-Kim-Mesnager):
    F(X) + F(X+1) + 1 = f_{k,2^k+1}(X + X²) -/
-/
-/
-/
theorem kasami_mcm_identity {F : Type*} [Field F] [CharP F 2]
    (k : ℕ) (x : F) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    kasamiDifferential k x + 1 = @mcmPoly F _ (Classical.decEq _) k (artinSchreier x) := by
  sorry

-/
-/
-/
/-! ## Section 3: MCM Permutation Theorem -/

/-- MCM is a permutation on GF(2^n)\{0} when k is odd and gcd(k,n)=1.
    (Cohen-Matthews 1994) -/
-/
-/
-/
theorem mcm_poly_bijective {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (_hk : 0 < k) (_hn : 0 < n)
    (_hk_odd : Odd k) (_hgcd : Nat.gcd k n = 1)
    (_hcard : Fintype.card F = 2 ^ n) :
    Function.Bijective (fun x : {x : F // x ≠ 0} =>
      @mcmPoly F _ (Classical.decEq F) k x.val) := by
  sorry

-/
-/
-/
/-! ## Section 4: Kasami APN for n Even -/

/-
When n is even and gcd(k,n)=1, k must be odd.
-/
-/
-/
-/
theorem k_odd_of_n_even {k n : ℕ} (hn_even : Even n) (hgcd : Nat.gcd k n = 1)
    (_hk : 0 < k) :
    Odd k := by
  exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero h ) ( even_iff_two_dvd.mp hn_even ) ; simp +decide [ hgcd ] at this )

/-- **Kasami APN for n even** (simplest direct proof). -/
-/
-/
-/
-/
theorem kasami_apn_even {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1) (hn_even : Even n)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (kasamiExponent k) : F → F) := by
  sorry

-/
-/
-/
-/
/-! ## Section 5: MCM Equation for n Odd -/

/-- The MCM equation: X^{q+1} + X + a = 0. -/
-/
-/
-/
-/
def mcmEquation {F : Type*} [Field F] (q : ℕ) (a x : F) : Prop :=
  x ^ (q + 1) + x + a = 0

/-- Solutions to X^{q+1}+X+a=0 when gcd(k,n)=1 are 0, 1, or 3.
    (Kim-Mesnager Lemma 7) -/
-/
-/
-/
-/
theorem mcm_equation_solutions {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (_hk : 0 < k) (_hn : 0 < n)
    (_hgcd : Nat.gcd k n = 1)
    (_hcard : Fintype.card F = 2 ^ n)
    (a : F) :
    Fintype.card { x : F // x ^ (2^k + 1) + x + a = 0 } = 0 ∨
    Fintype.card { x : F // x ^ (2^k + 1) + x + a = 0 } = 1 ∨
    Fintype.card { x : F // x ^ (2^k + 1) + x + a = 0 } = 3 := by
  sorry

-/
-/
-/
-/
/-! ## Section 6: Three Solutions Parametrization -/

/-- Parametrization of a when three solutions exist. -/
-/
-/
-/
-/
noncomputable def threesolParam {F : Type*} [Field F] (q : ℕ) (u : F) : F :=
  (u + u ^ q) ^ (q ^ 2 + 1) * ((u + u ^ (q ^ 2)) ^ (q + 1))⁻¹

/-- The three solutions when they exist. -/
-/
-/
-/
-/
noncomputable def threeSolutions {F : Type*} [Field F] (q : ℕ) (u : F) :
    Fin 3 → F :=
  fun i => match i with
  | 0 => ((1 : F) + (u + u ^ q) ^ (q - 1))⁻¹
  | 1 => u ^ (q ^ 2 - q) * ((1 : F) + (u + u ^ q) ^ (q - 1))⁻¹
  | 2 => (u + 1) ^ (q ^ 2 - q) * ((1 : F) + (u + u ^ q) ^ (q - 1))⁻¹

-/
-/
-/
-/
/-! ## Section 7: Trace Elimination (Key Step for n Odd) -/

/-
For any w in GF(2^n), Tr(w^q + w^{q²}) = 0 in char 2.
    Because Tr is GF(2)-linear and Tr(x^{2^k}) = Tr(x).
-/
-/
-/
-/
-/
theorem trace_frobenius_sum_zero {F : Type*} [Field F]
    [CharP F 2] (q : ℕ) (w : F)
    (trace : F → ZMod 2)
    (htr_linear : ∀ a b : F, trace (a + b) = trace a + trace b)
    (htr_frob : ∀ a : F, trace (a ^ q) = trace a) :
    trace (w ^ q + w ^ (q ^ 2)) = 0 := by
  simp_all +decide [ sq, pow_add ];
  simp_all +decide [ pow_mul ];
  grind

/-- **Kasami APN for n odd** (Carlet-Kim-Mesnager). -/
-/
-/
-/
-/
-/
theorem kasami_apn_odd {F : Type*} [Field F] [Fintype F] [DecidableEq F]
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
/-! ## Section 8: Combined Kasami APN Theorem -/

/-- **Full Kasami APN Theorem**: x^{2^{2k}-2^k+1} is APN on GF(2^n)
    when gcd(k,n) = 1. -/
-/
-/
-/
-/
-/
theorem kasami_apn_full {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2]
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hgcd : Nat.gcd k n = 1)
    (hcard : Fintype.card F = 2 ^ n) :
    IsAPN (powerFunction (kasamiExponent k) : F → F) := by
  by_cases hn_even : Even n
  · exact kasami_apn_even hk hn hgcd hn_even hcard
  · have hn_odd : Odd n := by
      exact Nat.not_even_iff_odd.mp hn_even
    exact kasami_apn_odd hk hn hgcd hn_odd hcard

-/
-/
-/
-/
-/
/-! ## Section 9: The A_r Polynomial Sequence -/

/-- The A_r polynomial sequence (in char 2, -1 = 1). -/
-/
-/
-/
-/
-/
noncomputable def polySeqA {F : Type*} [Field F] (q : ℕ) :
    ℕ → F → F
  | 0 => fun _ => 0
  | 1 => fun _ => 1
  | 2 => fun _ => 1  -- -1 = 1 in char 2
  | (n+3) => fun x => (polySeqA q (n+2) x) ^ q + x ^ q * (polySeqA q (n+1) x) ^ (q^2)

/-- Alternative recursion: A_{r+2}(X) = A_{r+1}(X) + X^{q^r} · A_r(X)
    (in char 2). -/
-/
-/
-/
-/
-/
theorem polySeqA_alt_recursion {F : Type*} [Field F] [CharP F 2]
    (q : ℕ) (r : ℕ) (hr : 2 ≤ r) (x : F) :
    polySeqA q (r + 2) x = polySeqA q (r + 1) x + x ^ (q ^ r) * polySeqA q r x := by
  sorry

/-- The norm identity. -/
-/
-/
-/
-/
-/
theorem polySeqA_norm_identity {F : Type*} [Field F] [CharP F 2]
    (q : ℕ) (r : ℕ) (hr : 1 ≤ r) (x : F) :
    polySeqA q (r + 1) x ^ (q + 1) + polySeqA q r x ^ q * polySeqA q (r + 2) x =
    x ^ (q * (q ^ r - 1) / (q - 1)) := by
  sorry

-/
-/
-/
-/
-/
/-! ## Section 10: Quadratic Equation for Rational Zeros -/

/-- When A_m(a) ≠ 0, solutions to X^{q+1}+X+a=0 satisfy a quadratic.
    (Kim-Choe-Mesnager, Lemma 3.1) -/
-/
-/
-/
-/
-/
theorem rational_zeros_quadratic {F : Type*} [Field F] [CharP F 2]
    {q m : ℕ} (a x : F) (hx : x ^ (q + 1) + x + a = 0)
    (hF : polySeqA q m a ≠ 0) :
    polySeqA q m a * x ^ 2 +
    (polySeqA q (m + 1) a + a * (polySeqA q (m - 1) a) ^ q) * x +
    a * (polySeqA q m a) ^ q = 0 := by
  sorry

-/
-/
-/
-/
-/
/-! ## Section 11: Proof DAG Summary

```
kasami_apn_full ✓ (from even + odd)
├── kasami_apn_even (sorry)
│     ├── k_odd_of_n_even (sorry)
│     ├── kasami_mcm_identity (sorry)
│     └── mcm_poly_bijective (sorry — Cohen-Matthews)
└── kasami_apn_odd (sorry)
      ├── mcm_equation_solutions (sorry — Kim-Mesnager)
      └── trace_frobenius_sum_zero ✓

Supporting infrastructure:
├── polySeqA (defined ✓)
├── polySeqA_alt_recursion (sorry)
├── polySeqA_norm_identity (sorry)
├── rational_zeros_quadratic (sorry)
├── threesolParam, threeSolutions (defined ✓)
├── partialTrace, mcmPoly (defined ✓)
└── kasami_coprime_mersenne ✓ (Layer 42)
```

### Fully proved in this module:
- trace_frobenius_sum_zero ✓
- kasami_apn_full ✓ (combining even/odd cases)
- partialTrace_zero, partialTrace_one ✓
- mcmPoly_zero ✓

### Key open sorries (deep finite field theory):
- kasami_mcm_identity: Carlet-Kim-Mesnager key identity
- mcm_poly_bijective: Cohen-Matthews permutation theorem
- mcm_equation_solutions: Kim-Mesnager Lemma 7
- kasami_apn_even, kasami_apn_odd: the two main cases

-/
-/
-/
-/
-/
-/
end Caramello.KasamiDirectProof
-/
-/
-/
-/
-/
-/