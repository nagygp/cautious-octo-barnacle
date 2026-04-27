/-
# Proof of ab_implies_vanishing via the split approach

This module provides additional infrastructure and uses the results
from VanishingInfra.lean and TripleCount.lean.
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
import RequestProject.Kasami.FourthMoment
import RequestProject.Kasami.TripleCount

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### AB implies APN for the Kasami function -/

theorem ab_implies_kasami_apn (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2 := by
  convert Kasami.ab_implies_apn hn _ hab using 1

/-! ### The main vanishing result -/

theorem ab_implies_vanishing_main (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ) := by
  apply ab_implies_vanishing n k hk hn hn_odd hgcd hab v1 v2 hv1 hv2 hne

end
end Kasami
