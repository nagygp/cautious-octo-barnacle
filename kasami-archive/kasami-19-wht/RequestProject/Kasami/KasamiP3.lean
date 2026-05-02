/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami P₃ — Main Theorem

Assembly of P₃: the triple-intersection equidistribution result for the
Kasami difference set.

## Main theorem
- `kasami_P3`: For `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂`:
  `|{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^{2n-3}`

- `kasami_P3_from_constructed_chi`: Version that takes `AlmostBentVanishing`
  as an explicit hypothesis, allowing one to plug in different proofs of the
  deep spectral condition.

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
import RequestProject.Kasami.TripleCount

namespace Kasami

open scoped BigOperators

/-! ### P₃ from the deep spectral hypothesis -/

/-- **P₃ with explicit spectral hypothesis**: Given `AlmostBentVanishing`,
    the triple-intersection count equals `2^{2n-3}`.

    This allows one to verify P₃ by supplying any proof of `AlmostBentVanishing`,
    whether from the original Kasami (1971) argument, the Canteaut-Charpin-Dobbertin
    (2000) approach, or any other method. -/
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
    1. `kasami_is_ab`: The Kasami function is almost bent (deep, sorry'd)
    2. `ab_implies_vanishing`: AB implies `AlmostBentVanishing` (deep, sorry'd)
    3. `tripleCount_from_vanishing`: Vanishing implies the count formula -/
theorem kasami_P3 (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n) (hn3 : 3 ≤ n)
    (hgcd : Nat.Coprime k n) (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hne : v1 ≠ v2) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  apply kasami_P3_from_constructed_chi n k hk hn hn_odd hn3 hgcd
  · exact ab_implies_vanishing n k hk hn hn_odd hgcd (kasami_is_ab n k hk hn hn_odd hgcd)
  · exact hv1
  · exact hv2
  · exact hne

/-! ### Summary of the proof structure -/

/-
  The proof of P₃ decomposes into three layers:

  **Layer 1 (Algebra)**: `kasami_is_ab`
    The Kasami function `F(b) = b^{4^k - 2^k + 1}` is almost bent.
    This is the deepest algebraic result, originally proved by Kasami (1971)
    and reproved with modern methods by Canteaut-Charpin-Dobbertin (2000).
    Status: stated, proof left as sorry.

  **Layer 2 (Character sums)**: `ab_implies_vanishing`
    The AB property implies `AlmostBentVanishing`, which states that certain
    triple character sums evaluate to `2^{3n-3}`.
    This uses the fourth moment identity for AB functions and character
    orthogonality.
    Status: stated, proof left as sorry.

  **Layer 3 (Counting)**: `tripleCount_from_vanishing` and `tripleCount_charSum_eq`
    Given `AlmostBentVanishing`, the triple-intersection count equals `2^{2n-3}`.
    This is a relatively straightforward division argument:
    `2^n · T = 2^{3n-3}` implies `T = 2^{2n-3}`.
    Status: **FULLY PROVED** (sorry-free).
-/

end Kasami
