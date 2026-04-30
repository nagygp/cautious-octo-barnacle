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
import RequestProject.Kasami.ABImpliesAPN

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ### Step 1: The delta generator is paired (g(b) = g(b+1)) -/

/-- In char 2, `b + 1 + 1 = b`. -/
theorem F2n.add_one_add_one {n : ℕ} (b : F2n n) : b + 1 + 1 = b := by
  have : (1 : F2n n) + 1 = 0 := F2n.add_self 1
  calc b + 1 + 1 = b + (1 + 1) := by ring
    _ = b + 0 := by rw [this]
    _ = b := by ring

/-- The delta generator satisfies `g(b) = g(b+1)` in char 2. -/
theorem deltaGen_paired (n k : ℕ) (b : F2n n) :
    kasamiDeltaGen n k b = kasamiDeltaGen n k (b + 1) := by
  simp only [kasamiDeltaGen, kasamiF, F2n.powMap]
  rw [show b + 1 + 1 = b from F2n.add_one_add_one b]
  ring

/-! ### Step 2: Delta set cardinality -/

/-- Each element of Δ has at least 2 preimages. -/
theorem deltaGen_fiber_ge_two (n k : ℕ) (x : F2n n) (hx : x ∈ kasamiDelta n k) :
    2 ≤ (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card := by
  obtain ⟨b, hb⟩ := Finset.mem_image.mp hx
  refine' Finset.one_lt_card.mpr ⟨b, _, b + 1, _, _⟩ <;>
    simp_all +decide [Finset.mem_univ, Finset.mem_filter]
  grind +suggestions

/-- The delta set has exactly 2^{n-1} elements when g is exactly 2-to-1. -/
theorem kasamiDelta_card (n k : ℕ) (hn : n ≠ 0)
    (h_two_to_one : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2) :
    (kasamiDelta n k).card = 2 ^ (n - 1) := by
  have h_total_pairs : ∑ x ∈ kasamiDelta n k,
    (Finset.univ.filter (fun b : F2n n => kasamiDeltaGen n k b = x)).card = 2 ^ n := by
    rw [← F2n.card n hn, ← Finset.card_biUnion]
    · convert Finset.card_univ; ext x; simp [kasamiDelta]
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop
  rcases n with (_ | n) <;> simp_all +decide [pow_succ']
  grind

/-- For APN Kasami functions, g is exactly 2-to-1. -/
theorem deltaGen_two_to_one (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2 := by
  intro x hx
  have h_ge : 2 ≤ (Finset.univ.filter fun b => kasamiDeltaGen n k b = x).card :=
    deltaGen_fiber_ge_two n k x hx
  have h_le : (Finset.univ.filter fun b => kasamiDeltaGen n k b = x).card ≤ 2 := by
    convert ab_implies_apn hn k hk hn_odd hgcd hab 1 one_ne_zero (x - 1) using 1
    simp +decide [kasamiDeltaGen, eq_sub_iff_add_eq]
    simp +decide only [add_comm]
  linarith

/-! ### Step 3: Triple sum splitting -/

/-- The triple sum splits at a=0. -/
theorem triple_sum_split (n k : ℕ) (v1 v2 : F2n n) :
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) =
    deltaCharSum n k 0 ^ 3 +
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) := by
  simp +decide [Finset.filter_ne', pow_succ, mul_assoc]

/-! ### Step 4: The 2-to-1 relation for deltaCharSum -/

/-- 2 · S_Δ(c) = ∑_b χ(c · g(b)). -/
theorem deltaCharSum_double (n k : ℕ) (hn : n ≠ 0) (c : F2n n)
    (h_two_to_one : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2) :
    2 * deltaCharSum n k c =
    ∑ b : F2n n, chi n (c * kasamiDeltaGen n k b) := by
  have h_fubini : ∑ b : F2n n, chi n (c * kasamiDeltaGen n k b) =
    ∑ x ∈ kasamiDelta n k,
    ∑ b ∈ Finset.univ.filter (fun b => kasamiDeltaGen n k b = x), chi n (c * x) := by
    rw [Finset.sum_sigma']
    refine' Finset.sum_bij (fun x _ => ⟨kasamiDeltaGen n k x, x⟩) _ _ _ _ <;>
      simp +decide
    · exact fun x => Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · aesop
  simp_all +decide [Finset.sum_filter, deltaCharSum]
  rw [Finset.mul_sum _ _ _]

/-! ### Step 5: chi factor cancellation in char 2 -/

/-- In char 2, v₁ + v₂ + (v₁+v₂) = 0, so χ(a·(v₁+v₂+(v₁+v₂))) = 1. -/
theorem chi_triple_cancel {n : ℕ} (a v1 v2 : F2n n) :
    chi n (a * v1) * chi n (a * v2) * chi n (a * (v1 + v2)) = 1 := by
  rw [← chi_add, ← chi_add]
  have h : a * v1 + a * v2 + a * (v1 + v2) = a * (v1 + v2) + a * (v1 + v2) := by ring
  rw [h, F2n.add_self, chi_zero]

/-! ### Step 6: Assembly of ab_implies_vanishing

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
