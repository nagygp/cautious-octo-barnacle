/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Triple-Intersection Counting via Character Sums

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
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
import RequestProject.Kasami.VanishingInfra

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 16000000

/-! ### The triple-count function -/

noncomputable def tripleSet (n k : ℕ) (v1 v2 : F2n n) : Finset (F2n n × F2n n × F2n n) :=
  ((kasamiDelta n k) ×ˢ (kasamiDelta n k) ×ˢ (kasamiDelta n k)).filter
    fun t => v1 * t.1 + v2 * t.2.1 + (v1 + v2) * t.2.2 = 0

noncomputable def tripleCount (n k : ℕ) (v1 v2 : F2n n) : ℕ :=
  (tripleSet n k v1 v2).card

/-! ### Character-sum representation -/

theorem tripleCount_charSum_eq (n k : ℕ) (hn : n ≠ 0) (v1 v2 : F2n n) :
    (2 ^ n : ℤ) * tripleCount n k v1 v2 =
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) := by
  unfold tripleCount deltaCharSum
  unfold tripleSet; simp +decide [mul_assoc, Finset.sum_mul _ _ _]
  have h_interchange : ∑ a : F2n n, ∑ x ∈ kasamiDelta n k, ∑ y ∈ kasamiDelta n k,
      ∑ z ∈ kasamiDelta n k,
      (chi n (a * (v1 * x)) * chi n (a * (v2 * y)) * chi n (a * ((v1 + v2) * z))) =
    ∑ x ∈ kasamiDelta n k, ∑ y ∈ kasamiDelta n k, ∑ z ∈ kasamiDelta n k,
      ∑ a : F2n n, (chi n (a * (v1 * x + v2 * y + (v1 + v2) * z))) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    intro x _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun z _ => ?_
    simp +decide [mul_add, add_mul, chi_add]
  convert h_interchange.symm using 1
  · have h_card : ∀ x y z : F2n n,
        ∑ a : F2n n, chi n (a * (v1 * x + v2 * y + (v1 + v2) * z)) =
        if v1 * x + v2 * y + (v1 + v2) * z = 0 then (2 ^ n : ℤ) else 0 := by
      intro x y z; convert chi_sum hn (v1 * x + v2 * y + (v1 + v2) * z) using 1; ac_rfl
    simp +decide only [Finset.card_filter, Finset.sum_product, h_card]
    simp +decide [Finset.sum_ite, mul_comm]
    simp +decide only [Finset.mul_sum _ _ _]
  · simp +decide only [Finset.mul_sum _ _ _, mul_assoc]

/-! ### The AlmostBentVanishing condition -/

def AlmostBentVanishing (n k : ℕ) : Prop :=
  ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ)

/-! ### From AB to AlmostBentVanishing -/

/-- The AB property implies AlmostBentVanishing via:
    1. Split sum at a=0: contribution = |Δ|^3 = (2^{n-1})^3 = 2^{3n-3}
    2. For a≠0: use delta_charSum_halving + chi cancellation + character orthogonality
    3. The nonzero terms contribute (2^n·N - 2^{3n})/8 where N = 2^{2n}
    4. So nonzero contribution = 0, total = 2^{3n-3} -/
theorem ab_implies_vanishing_goal (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  intro v1 v2 hv1 hv2 hne
  -- The nonzero terms of the sum vanish (deep spectral identity)
  have h_nonzero_vanish : ∑ a ∈ Finset.univ.erase (0 : F2n n),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = 0 := by
    sorry
  -- The a=0 term gives (2^{n-1})^3
  have h_zero : deltaCharSum n k (0 * v1) * deltaCharSum n k (0 * v2) *
      deltaCharSum n k (0 * (v1 + v2)) = ((2 : ℤ) ^ (n - 1)) ^ 3 := by
    simp [deltaCharSum_zero, kasamiDelta_card_eq n k hk hn hn_odd hgcd hab]; ring
  -- Split the sum and combine
  have h_split := Finset.sum_erase_eq_sub
    (f := fun a => deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)))
    (Finset.mem_univ (0 : F2n n))
  rw [h_split] at h_nonzero_vanish
  have h_total : ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
    deltaCharSum n k (a * (v1 + v2)) = ((2 : ℤ) ^ (n - 1)) ^ 3 := by linarith
  rw [h_total, ← pow_mul]
  congr 1
  obtain ⟨m, hm⟩ := hn_odd; omega

theorem ab_implies_vanishing (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k :=
  ab_implies_vanishing_goal n k hk hn hn_odd hgcd hab

/-! ### Triple count evaluation -/

theorem tripleCount_from_vanishing (n k : ℕ) (hn : n ≠ 0) (hn3 : 3 ≤ n)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2)
    (hvan : AlmostBentVanishing n k) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  have h_eq : (2 ^ n : ℤ) * tripleCount n k v1 v2 = (2 ^ (3 * n - 3) : ℤ) := by
    rw [ ← hvan v1 v2 hv1 hv2 hne, ← tripleCount_charSum_eq n k hn v1 v2 ];
  refine' mul_left_cancel₀ ( pow_ne_zero n two_ne_zero ) _;
  rw [ ← pow_add, show 3 * n - 3 = n + ( 2 * n - 3 ) by omega ] at * ; norm_cast at *

end
end Kasami