/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami P₃ — Main Theorem

Assembly of P₃: the triple-intersection equidistribution result for the
Kasami difference set.

## Main theorem
- `kasami_P3`: For `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂`:
  `|{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^{2n-3}`

## Proof chain

  **Layer 1 (Algebra)**: `kasami_is_ab`
    The Kasami function `F(b) = b^{4^k - 2^k + 1}` is almost bent.
    Status: sorry (deep result, see documentation below)

  **Layer 2 (Combinatorics)**: `ab_implies_vanishing_correct`
    AB implies AlmostBentVanishing via the Singer difference set property.
    Status: sorry (depends on `singer_diff_set`)

  **Layer 3 (Counting)**: `tripleCount_from_vanishing`
    AlmostBentVanishing implies the triple count = 2^{2n-3}.
    Status: **FULLY PROVED** (sorry-free)

## IMPORTANT: False lemmas in the project

The following lemmas in other files have been found to be **FALSE**
(counterexample: n=5, k=2, d=13 over GF(2^5)):

1. `kasami_deriv_one_trace` (KasamiWHTSquared.lean):
   Tr((x+1)^d + x^d) ≠ Tr((x+1)^{2^k+1} + x^{2^k+1}) in general.
   20 out of 32 elements of GF(2^5) give different traces.

2. `kasamiDerivAutocorr_vanish` (KasamiWHTSquared.lean):
   C_d(z) ≠ 0 for many z ∉ {0,1}. The autocorrelation of the Kasami
   function is NOT supported on {0,1} (unlike the Gold function).

3. `deltaCharSum_vanish_off_01` (DeltaCharSumSupport.lean):
   S_Δ(c) ≠ 0 for many c ∉ {0,1}.

4. `kasami_wht_sq` (KasamiWHTSquared.lean):
   W_d(a)² ≠ 2^n(1+χ(a+1)). The Walsh support of the Kasami function
   differs from that of the Gold function (they are NOT equal as sets,
   only as multisets of squared values).

5. `kasami_walsh_support` (KasamiWHTSquared.lean):
   The Walsh support of the Kasami function is NOT {a : Tr(a) = 1}.

These false lemmas do NOT affect the truth of kasami_is_ab (which IS true)
or kasami_P3 (which IS true). They only affect the PROOF STRATEGY.
The correct proof goes through spectral equivalence with the Gold function,
not through the autocorrelation vanishing argument.

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000]
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.ABVanishing

namespace Kasami

open scoped BigOperators

/-! ### P₃ from the deep spectral hypothesis -/

/-- **P₃ with explicit spectral hypothesis**: Given `AlmostBentVanishing`,
    the triple-intersection count equals `2^{2n-3}`. -/
theorem kasami_P3_from_constructed_chi (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hn3 : 3 ≤ n) (hgcd : Nat.Coprime k n)
    (hvan : AlmostBentVanishing n k)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) :=
  tripleCount_from_vanishing n k hn hn3 v1 v2 hv1 hv2 hne hvan

/-! ### Full P₃ (using kasami_is_ab) -/

/-- **P₃ (full version)**: For the Kasami function with `gcd(k,n) = 1`, `n` odd, `n ≥ 3`:
    For any nonzero `v₁ ≠ v₂` in F_{2^n},
    `|{(x,y,z) ∈ Δ³ : v₁·x + v₂·y + (v₁+v₂)·z = 0}| = 2^{2n-3}`.

    This combines:
    1. `kasami_is_ab`: The Kasami function is almost bent (sorry)
    2. `ab_implies_vanishing_correct`: AB implies AlmostBentVanishing (sorry)
    3. `tripleCount_from_vanishing`: Vanishing implies the count formula (proved) -/
theorem kasami_P3 (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n) (hn3 : 3 ≤ n)
    (hgcd : Nat.Coprime k n) (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hne : v1 ≠ v2) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  apply kasami_P3_from_constructed_chi n k hk hn hn_odd hn3 hgcd
  · exact ab_implies_vanishing_v2 n k hk hn hn_odd hgcd (kasami_is_ab n k hk hn hn_odd hgcd)
  · exact hv1
  · exact hv2
  · exact hne

end Kasami
