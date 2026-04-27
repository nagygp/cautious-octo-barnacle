/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kasami P₃ — Main Theorem

Assembly of P₃: the triple-intersection equidistribution result.

## Main theorem
- `kasami_P3`: For `gcd(k,n) = 1`, `n` odd, `n ≥ 3`, and nonzero `v₁ ≠ v₂`:
  `|{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}| = 2^{2n-3}`

## References
- [Kasami (1971)][kasami1971], Information and Control 18(4)
- [Canteaut, Charpin, Dobbertin (2000)][canteaut2000]
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

/-- **P₃ with explicit spectral hypothesis** -/
theorem kasami_P3_from_constructed_chi (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hn3 : 3 ≤ n) (hgcd : Nat.Coprime k n)
    (hvan : AlmostBentVanishing n k)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) :=
  tripleCount_from_vanishing n k hn hn3 v1 v2 hv1 hv2 hne hvan

/-! ### Full P₃ (using kasami_is_ab) -/

/-- **P₃ (full version)** -/
theorem kasami_P3 (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n) (hn3 : 3 ≤ n)
    (hgcd : Nat.Coprime k n) (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hne : v1 ≠ v2) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  apply kasami_P3_from_constructed_chi n k hk hn hn_odd hn3 hgcd
  · exact ab_implies_vanishing n k hk hn hn_odd hgcd (kasami_is_ab n k hk hn hn_odd hgcd)
  · exact hv1
  · exact hv2
  · exact hne

end Kasami
