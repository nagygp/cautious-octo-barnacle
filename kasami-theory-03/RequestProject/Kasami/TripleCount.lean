/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Triple-Intersection Counting via Character Sums

Reduces the triple-intersection count from P₃ to a character-sum expression,
then evaluates it using the AB property.

## Main results
- `tripleCount_charSum_eq`: character-sum representation
- `tripleCount_from_vanishing`: evaluation for AB functions
- `AlmostBentVanishing`: the deep spectral condition

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

/-
Character-sum representation of the triple count:
    `2^n · T(v₁,v₂) = ∑_a S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂))`
-/
theorem tripleCount_charSum_eq (n k : ℕ) (hn : n ≠ 0) (v1 v2 : F2n n) :
    (2 ^ n : ℤ) * tripleCount n k v1 v2 =
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) := by
  -- Apply the character orthogonality identity to each term in the sum.
  have h_char_ortho : ∀ x y z : F2n n, (if v1 * x + v2 * y + (v1 + v2) * z = 0 then (2 ^ n : ℤ) else 0) = ∑ a : F2n n, chi n (a * (v1 * x + v2 * y + (v1 + v2) * z)) := by
    intro x y z;
    convert chi_sum hn ( v1 * x + v2 * y + ( v1 + v2 ) * z ) |> Eq.symm using 1;
  -- Apply the character orthogonality identity to each term in the sum to rewrite the left-hand side.
  have h_rewrite : ∑ x ∈ kasamiDelta n k, ∑ y ∈ kasamiDelta n k, ∑ z ∈ kasamiDelta n k, (if v1 * x + v2 * y + (v1 + v2) * z = 0 then (2 ^ n : ℤ) else 0) = ∑ a : F2n n, (∑ x ∈ kasamiDelta n k, chi n (a * v1 * x)) * (∑ y ∈ kasamiDelta n k, chi n (a * v2 * y)) * (∑ z ∈ kasamiDelta n k, chi n (a * (v1 + v2) * z)) := by
    simp +decide only [h_char_ortho, Finset.sum_mul _ _ _, Finset.mul_sum];
    simp +decide only [Finset.sum_sigma'];
    refine' Finset.sum_bij ( fun x hx => ⟨ x.snd.snd.snd, x.fst, x.snd.fst, x.snd.snd.fst ⟩ ) _ _ _ _ <;> simp +decide [ mul_assoc, mul_add, add_mul, chi_add ];
    · bound;
    · exact fun b hb₁ hb₂ hb₃ => ⟨ _, _, _, ⟨ hb₁, hb₂, hb₃ ⟩, _, rfl ⟩;
  convert h_rewrite using 1;
  unfold tripleCount;
  unfold tripleSet; simp +decide [ Finset.sum_ite ] ; ring;
  simp +decide only [Finset.card_filter];
  simp +decide only [Finset.sum_product, Nat.cast_sum, Finset.sum_mul]

/-! ### The AlmostBentVanishing condition -/

/-- **AlmostBentVanishing**: the deep spectral condition.
    For any nonzero `v₁ ≠ v₂`, the triple character sum evaluates to `2^{3n-3}`. -/
def AlmostBentVanishing (n k : ℕ) : Prop :=
  ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ)

/-! ### From AB to AlmostBentVanishing -/

/-- The AB property of the Kasami function implies AlmostBentVanishing. -/
theorem ab_implies_vanishing (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  sorry

/-! ### Triple count evaluation -/

/-
Given `AlmostBentVanishing`, the triple count is `2^{2n-3}`.
-/
theorem tripleCount_from_vanishing (n k : ℕ) (hn : n ≠ 0) (hn3 : 3 ≤ n)
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2)
    (hvan : AlmostBentVanishing n k) :
    tripleCount n k v1 v2 = 2 ^ (2 * n - 3) := by
  convert congr_arg ( fun x : ℤ => x / 2 ^ n ) ( tripleCount_charSum_eq n k hn v1 v2 ) using 1;
  rw [ hvan v1 v2 hv1 hv2 hne ] ; norm_cast;
  rw [ Nat.mul_div_cancel_left _ ( by positivity ), show 3 * n - 3 = n + ( 2 * n - 3 ) by omega, pow_add ] ; norm_num [ Nat.mul_div_assoc, pow_pos ]

end
end Kasami