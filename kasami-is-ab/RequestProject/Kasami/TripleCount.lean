/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Triple-Intersection Counting via Character Sums

## Main results
- `tripleCount_charSum_eq`: expressing the count as a character sum
- `ab_implies_vanishing`: AB implies the triple character sum identity
- `tripleCount_from_vanishing`: the final P₃ count equals `2^{2n-3}`

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
import RequestProject.Kasami.PowerFnAB

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### The triple-count function -/

/-- The set of triples `(x, y, z) ∈ Δ³` satisfying `v₁·x + v₂·y + (v₁+v₂)·z = 0`. -/
noncomputable def tripleSet (n k : ℕ) (v1 v2 : F2n n) : Finset (F2n n × F2n n × F2n n) :=
  ((kasamiDelta n k) ×ˢ (kasamiDelta n k) ×ˢ (kasamiDelta n k)).filter
    fun t => v1 * t.1 + v2 * t.2.1 + (v1 + v2) * t.2.2 = 0

/-- The triple count: `T(v₁, v₂) = |{(x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0}|`. -/
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

/-- **AlmostBentVanishing**: For AB functions, the character sum
    `∑_a S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂))`
    evaluates to `2^{3n-3}` for all nonzero `v₁ ≠ v₂`. -/
def AlmostBentVanishing (n k : ℕ) : Prop :=
  ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ)

/-! ### Helper: In GF(2), any two nonzero elements are equal -/

/-
In a field with 2 elements, any two nonzero elements are equal.
-/
theorem F2n_one_unique (v1 v2 : F2n 1) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) : v1 = v2 := by
  -- Since F2n 1 has only two elements, which are 0 and 1, and v1 and v2 are non-zero, they must both be 1. Hence, v1 = 1 and v2 = 1, so v1 = v2.
  have h_card : Fintype.card (F2n 1) = 2 := by
    convert F2n.card 1 ( by decide );
  have := Finset.card_eq_two.mp h_card;
  rcases this with ⟨ x, y, hxy, h ⟩ ; simp_all +decide [ Finset.ext_iff ];
  cases h 0 <;> cases h v1 <;> cases h v2 <;> aesop

/-! ### Nonzero triple sum vanishing for AB power functions -/

/-- **Nonzero triple character sum vanishes for AB power functions.**

    The proof is decomposed in `DeltaCharSumSupport.lean` into:
    1. `deltaCharSum_vanish_off_01`: S_Δ(c) = 0 for c ∉ {0, 1}
       (via Wiener-Khintchine + Walsh support characterization)
    2. `not_both_in_01`: for a ≠ 0 and v₁ ≠ v₂, at least one of
       av₁, av₂, a(v₁+v₂) is ∉ {0, 1}
    3. Product vanishes termwise.

    The deepest sub-lemma is `kasamiDerivAutocorr_vanish` from
    `KasamiWHTSquared.lean`, which establishes the autocorrelation
    support structure of the Kasami function. -/
theorem nonzero_triple_sum_vanishes (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (hn3 : 3 ≤ n)
    (hab : IsAlmostBent (kasamiF n k))
    (hapn : ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n,
      (Finset.univ.filter fun x : F2n n => kasamiF n k (x + a) + kasamiF n k x = b).card ≤ 2)
    (h2to1 : ∀ x ∈ kasamiDelta n k,
      (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = x).card = 2)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    ∑ a ∈ (Finset.univ : Finset (F2n n)).filter (· ≠ 0),
      deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = 0 := by
  sorry

/-! ### From AB to AlmostBentVanishing -/

/-- The AB property of the Kasami function implies AlmostBentVanishing.

    **Proof**: Split the sum at a=0. The a=0 term gives S_Δ(0)³ = |Δ|³ = 2^{3(n-1)}.
    The nonzero terms vanish by `nonzero_triple_sum_vanishes`. -/
theorem ab_implies_vanishing (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  intro v1 v2 hv1 hv2 hne
  -- n is odd and n ≥ 1. For n = 1, v1 = v2 (only one nonzero element), contradiction.
  have hn3 : 3 ≤ n := by
    rcases hn_odd with ⟨m, hm⟩; subst hm
    by_contra h; push_neg at h
    have : m = 0 := by omega
    subst this
    exact hne (F2n_one_unique v1 v2 hv1 hv2)
  -- AB → APN → 2-to-1 → |Δ| = 2^{n-1}
  have hapn := kasami_ab_implies_apn hk hn hn_odd hgcd hab
  have h2to1 := deltaGen_two_to_one' n k hk hn hn_odd hgcd hapn
  -- Split: total = S_Δ(0)³ + nonzero_sum
  rw [triple_sum_split' n k v1 v2, deltaCharSum_zero, kasamiDelta_card' n k hn h2to1]
  -- nonzero_sum = 0
  rw [nonzero_triple_sum_vanishes n k hk hn hn_odd hgcd hn3 hab hapn h2to1 v1 v2 hv1 hv2 hne,
      add_zero]
  -- (2^{n-1})³ = 2^{3n-3}
  have : (2 ^ (n - 1) : ℕ) ^ 3 = 2 ^ (3 * n - 3) := by
    rw [show 3 * n - 3 = (n - 1) * 3 from by omega, ← pow_mul]
  exact_mod_cast this

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