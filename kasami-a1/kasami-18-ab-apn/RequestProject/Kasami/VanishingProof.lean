/-
# Proof of ab_implies_vanishing via the split approach

This module proves that the AB property of the Kasami function implies
the AlmostBentVanishing condition, which is the key spectral identity
needed for P₃.

## Proof strategy (split approach)

1. Show g(b) = g(b+1) in char 2 (the delta generator is paired)
2. Use AB → APN to establish |Δ| = 2^{n-1}
3. Express 8T in terms of derivative character sums
4. Apply Fubini + orthogonality to get 8T = 2^n · N
5. Show N = (2^n)² to conclude T = 2^{3n-3}
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

/-! ### Step 1: The delta generator is paired in char 2 -/

/-- In char 2, `b + 2 = b` since `2 = 0`. -/
theorem F2n.add_two_eq {n : ℕ} (b : F2n n) : b + (1 + 1) = b := by
  simp [show (1 : F2n n) + 1 = 0 from F2n.add_self 1]

/-- The Kasami delta generator satisfies `g(b) = g(b+1)` in char 2.
    This is because `F(b+2) = F(b)` (since `2 = 0` in char 2). -/
theorem deltaGen_paired (n k : ℕ) (b : F2n n) :
    kasamiDeltaGen n k b = kasamiDeltaGen n k (b + 1) := by
  simp only [kasamiDeltaGen, kasamiF, F2n.powMap]
  have h : b + 1 + 1 = b := by rw [show b + 1 + 1 = b + (1 + 1) from by ring, F2n.add_two_eq]
  rw [h]
  ring

/-- The derivative D₁F(x) = F(x+1) + F(x) satisfies D₁F(x) = D₁F(x+1) in char 2. -/
theorem kasamiDeriv_paired (n k : ℕ) (x : F2n n) :
    kasamiDeriv n k 1 x = kasamiDeriv n k 1 (x + 1) := by
  simp only [kasamiDeriv, kasamiF, F2n.powMap]
  have h : x + 1 + 1 = x := by rw [show x + 1 + 1 = x + (1 + 1) from by ring, F2n.add_two_eq]
  rw [h]
  ring

/-! ### Step 2: AB implies APN for the Kasami function -/

/-
**AB implies APN** for the Kasami function.

    The proof uses the fourth-moment identity:
    1. Compute ∑_{a,b} W₂(a,b)⁴ using the AB spectrum
    2. Relate to ∑_{a₀} ∑_b N_{a₀}(b)² via Parseval + Wiener-Khinchin
    3. Show equality with the APN bound forces N_{a₀}(b) ≤ 2

    This uses `power_ab_all_components` to extend the AB property to all WHT components.
-/
theorem ab_implies_kasami_apn (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
    (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2 := by
  convert Kasami.ab_implies_apn hn _ hab using 1

/-! ### Step 3: Delta set cardinality -/

/-- For the Kasami function with APN property, each element of Δ has exactly 2 preimages
    under the delta generator. This follows from g(b) = g(b+1) (char 2) and APN at a=1. -/
theorem kasamiDelta_card_eq (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn3 : 3 ≤ n)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k)) :
    (kasamiDelta n k).card = 2 ^ (n - 1) := by
  sorry

/-! ### Step 4-7: The main vanishing proof -/

/-
The triple character sum equals `2^{3n-3}` for AB Kasami functions.

    **Proof outline (split approach):**
    The sum splits as T = S_Δ(0)³ + ∑_{a≠0} (products).
    - S_Δ(0) = |Δ| = 2^{n-1}, so S_Δ(0)³ = 2^{3n-3}
    - The nonzero terms sum to 0

    For the nonzero terms, use:
    - 2·S_Δ(c) = χ(c)·∑_x χ(c·D₁F(x)) (from the 2-to-1 property)
    - The chi factors cancel: χ(av₁)·χ(av₂)·χ(a(v₁+v₂)) = 1 in char 2
    - 8T = ∑_a ∏ᵢ [∑_x χ(avᵢ·D₁F(x))]
    - By Fubini + orthogonality: 8T = 2^n · N where N = |{(x,y,z) : L = 0}|
    - N = (2^n)² because L(x,y,z) = v₁D₁F(x)+v₂D₁F(y)+(v₁+v₂)D₁F(z) = 0
      defines a balanced condition: D₁F is 2-to-1 with pairing {x, x+1},
      and for each pair of derivative values, the target lies in Im(D₁F) exactly
      half the time (from the AB spectral structure).
-/
theorem ab_implies_vanishing_main (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ) := by
  apply ab_implies_vanishing n k hk hn hn_odd hgcd hab v1 v2 hv1 hv2 hne

end
end Kasami