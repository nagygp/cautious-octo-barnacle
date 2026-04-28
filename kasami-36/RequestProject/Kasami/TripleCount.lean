/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Triple-Intersection Counting via Character Sums
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
import RequestProject.Kasami.ABImpliesAPN
import RequestProject.Kasami.VanishingHelpers

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

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
  unfold tripleCount deltaCharSum;
  unfold tripleSet; simp +decide [ mul_assoc, Finset.sum_mul _ _ _ ] ;
  have h_interchange : ∑ a : F2n n, ∑ x ∈ kasamiDelta n k, ∑ y ∈ kasamiDelta n k, ∑ z ∈ kasamiDelta n k, (chi n (a * (v1 * x)) * chi n (a * (v2 * y)) * chi n (a * ((v1 + v2) * z))) = ∑ x ∈ kasamiDelta n k, ∑ y ∈ kasamiDelta n k, ∑ z ∈ kasamiDelta n k, ∑ a : F2n n, (chi n (a * (v1 * x + v2 * y + (v1 + v2) * z))) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro x hx; rw [ Finset.sum_comm ] ; refine' Finset.sum_congr rfl fun y hy => _ ; rw [ Finset.sum_comm ] ; refine' Finset.sum_congr rfl fun z hz => _ ; simp +decide [ mul_add, add_mul, chi_add ] ;
  convert h_interchange.symm using 1;
  · have h_card : ∀ x y z : F2n n, ∑ a : F2n n, chi n (a * (v1 * x + v2 * y + (v1 + v2) * z)) = if v1 * x + v2 * y + (v1 + v2) * z = 0 then (2 ^ n : ℤ) else 0 := by
      intro x y z;
      convert chi_sum hn ( v1 * x + v2 * y + ( v1 + v2 ) * z ) using 1;
      ac_rfl;
    simp +decide only [Finset.card_filter, Finset.sum_product, h_card];
    simp +decide [ Finset.sum_ite, mul_comm ];
    simp +decide only [Finset.mul_sum _ _ _];
  · simp +decide only [Finset.mul_sum _ _ _, mul_assoc]

/-! ### The AlmostBentVanishing condition -/

def AlmostBentVanishing (n k : ℕ) : Prop :=
  ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ)

/-! ### Helper: sixth moment and cubic identity -/

theorem ab_sixth_moment {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, wht f a ^ 6 = (2 ^ (n + 1) : ℤ) ^ 3 * 2 ^ (n - 1) := by
  have h_sixth_moment : ∀ a, wht f a ^ 6 = if wht f a = 0 then 0 else (2 ^ (n + 1)) ^ 3 := by
    intro a
    by_cases ha : wht f a = 0;
    · simp [ha];
    · have := hf a; norm_cast at *; simp_all +decide [ pow_succ, mul_assoc ] ;
  simp_all +decide [ mul_comm, Finset.sum_ite ];
  rw [ mul_comm, ab_nonzero_count hn f hf ];
  norm_cast

theorem ab_cubic_identity {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : IsAlmostBent f) :
    ∑ a : F2n n, (wht f a ^ 2 - (2 ^ n : ℤ)) ^ 3 = 0 := by
  -- From ab_nonzero_count, |{a:W≠0}| = 2^{n-1} and |F| = 2^n, so |{a:W=0}| = 2^n - 2^{n-1} = 2^{n-1}.
  have h_card_nonzero : (Finset.univ.filter fun a : F2n n => wht f a ≠ 0).card = 2 ^ (n - 1) := by
    exact?;
  have h_card_zero : (Finset.univ.filter fun a : F2n n => wht f a = 0).card = 2 ^ n - 2 ^ (n - 1) := by
    rw [ ← h_card_nonzero, eq_comm, Nat.sub_eq_of_eq_add ];
    rw [ Finset.card_filter_add_card_filter_not, Finset.card_univ, F2n.card n hn ];
  have h_split_sum : ∑ a : F2n n, (wht f a ^ 2 - 2 ^ n) ^ 3 = ∑ a ∈ Finset.univ.filter (fun a : F2n n => wht f a = 0), (-2 ^ n) ^ 3 + ∑ a ∈ Finset.univ.filter (fun a : F2n n => wht f a ≠ 0), (2 ^ (n + 1) - 2 ^ n) ^ 3 := by
    have h_split_sum : ∀ a : F2n n, (wht f a ^ 2 - 2 ^ n) ^ 3 = if wht f a = 0 then (-2 ^ n) ^ 3 else (2 ^ (n + 1) - 2 ^ n) ^ 3 := by
      intro a; specialize hf a; rcases hf with h | h <;> simp_all +decide [ pow_succ' ] ;
      aesop;
    simp +decide only [h_split_sum, Finset.sum_ite];
  simp_all +decide [ Finset.sum_const_zero ];
  rw [ Nat.cast_sub ( Nat.pow_le_pow_right ( by decide ) ( Nat.sub_le _ _ ) ) ] ; cases n <;> norm_num [ pow_succ' ] at * ; ring

/-! ### The nonzero sum vanishing -/

/-- The nonzero sum in the triple product vanishes for AB Kasami functions.
    This is the deepest step, requiring:
    1. The 2-to-1 property of g (from AB → APN)
    2. The relation 2S_Δ(c) = χ(c)·A(c)
    3. The chi_triple_cancel identity
    4. The cubic identity for AB functions -/
theorem nonzero_sum_vanishes (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn3 : 3 ≤ n)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = 0 := by
  sorry

/-! ### From AB to AlmostBentVanishing -/

/-
The AB property of the Kasami function implies AlmostBentVanishing.

    The proof splits into two cases:
    - n = 1: vacuous (F₂ has only one nonzero element)
    - n ≥ 3: uses the split at a=0, the |Δ| = 2^{n-1} identity, and nonzero_sum_vanishes
-/
theorem ab_implies_vanishing (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  intro v1 v2 hv1 hv2 hne
  have h_card : (kasamiDelta n k).card = 2 ^ (n - 1) := by
    exact kasamiDelta_card n k hn ( deltaGen_two_to_one n k hk hn hn_odd hgcd hab );
  by_cases hn3 : 3 ≤ n;
  · rw [ triple_sum_split, deltaCharSum_zero, h_card ];
    rw [ nonzero_sum_vanishes n k hk hn hn3 hn_odd hgcd hab v1 v2 hv1 hv2 hne ] ; norm_num [ Nat.mul_sub_left_distrib, pow_mul' ];
    rw [ ← pow_mul', Nat.mul_sub_left_distrib, mul_one ];
  · interval_cases n <;> simp_all +decide;
    have h_card : Fintype.card (F2n 1) = 2 := by
      convert F2n.card 1 ( by decide );
    have := Finset.card_eq_two.mp h_card;
    obtain ⟨ x, y, hxy, h ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
    cases h 0 <;> cases h 1 <;> cases h v1 <;> cases h v2 <;> aesop

/-! ### Triple count evaluation -/

theorem tripleCount_from_vanishing (n k : ℕ) (hn : n ≠ 0) (hn3 : 3 ≤ n)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2)
    (hvan : AlmostBentVanishing n k) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  convert congr_arg ( fun x : ℤ => Int.toNat ( x / 2 ^ n ) ) ( hvan v1 v2 hv1 hv2 hne ▸ tripleCount_charSum_eq n k hn v1 v2 ) using 1;
  · norm_cast ; norm_num [ hn ];
  · rw [ show 3 * n - 3 = 2 * n - 3 + n by omega, pow_add ] ; norm_num;
    norm_cast

end
end Kasami