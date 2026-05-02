/-
# Proof of ab_implies_vanishing

This module proves that the AB property of the Kasami function implies
the AlmostBentVanishing condition needed for P₃.

## Proof strategy (split approach)

∑_a S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))
  = S_Δ(0)³ + ∑_{a≠0} S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂))

Since g(b) = g(b+1) and AB→APN gives g 2-to-1, |Δ| = 2^{n-1}.
S_Δ(0) = 2^{n-1}, S_Δ(0)³ = 2^{3n-3}.

The nonzero sum vanishes via the autocorrelation structure of AB functions.

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.4
-/

import Mathlib
import RequestProject.Kasami.TripleCount

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Assembly of ab_implies_vanishing

The full proof of AlmostBentVanishing requires:
1. S_Δ(0) = |Δ| = 2^{n-1} (from APN ← AB)
2. The nonzero sum vanishes (from AB autocorrelation structure)

The key missing step is the vanishing of the nonzero sum, which requires
deeper Fourier-analytic arguments about the autocorrelation structure
of AB functions. This is the content of Canteaut-Charpin-Dobbertin (2000).

We provide the framework with `sorry` for the deepest step. -/

/-- Intermediate: the full ab_implies_vanishing proof using decomposition. -/
theorem ab_implies_vanishing_assembled (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn3 : 3 ≤ n) (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k))
    -- The nonzero sum vanishing (deepest step)
    (hvanish : ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
      ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
        deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
        deltaCharSum n k (a * (v1 + v2)) = 0) :
    AlmostBentVanishing n k := by
  intro v1 v2 hv1 hv2 hne
  rw [show ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
    deltaCharSum n k (a * (v1 + v2)) =
    deltaCharSum n k 0 ^ 3 +
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) from triple_sum_split n k v1 v2]
  rw [hvanish v1 v2 hv1 hv2 hne, add_zero]
  rw [deltaCharSum_zero]
  have h2to1 := deltaGen_two_to_one n k hk hn hn_odd hgcd hab
  rw [kasamiDelta_card n k hn h2to1]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have : (2 ^ (n - 1) : ℕ) ^ 3 = 2 ^ (3 * n - 3) := by
    rw [show 3 * n - 3 = (n - 1) * 3 from by omega, ← pow_mul]
  exact_mod_cast this

end
end Kasami
