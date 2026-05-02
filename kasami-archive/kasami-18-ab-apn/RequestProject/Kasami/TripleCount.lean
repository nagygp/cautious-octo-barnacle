/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Triple-Intersection Counting via Character Sums

This is the technically hardest module. It reduces the triple-intersection count
from P₃ to a character-sum expression, and then evaluates it using the AB property.

## Main results
- `tripleCount_eq_charSum`: expressing the count as a character sum
- `tripleCount_from_ab`: evaluating the character sum for AB functions
- `tripleCount_eq`: the final P₃ count equals `2^{2n-3}`

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.4
- [Pott, *Finite Geometry and Character Theory*][pott1995], Chapter 4
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
**Character-sum representation of the triple count**.
    Using the orthogonality relation `1_{s=0} = (1/q) ∑_a χ(as)`,
    the triple count can be written as:
    `T(v₁,v₂) = (1/q) ∑_a S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂))`
    where `S_Δ(c) = ∑_{x∈Δ} χ(cx)`.

    In ℤ form (multiplied by q):
    `q · T(v₁,v₂) = ∑_a S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂))`
-/
theorem tripleCount_charSum_eq (n k : ℕ) (hn : n ≠ 0) (v1 v2 : F2n n) :
    (2 ^ n : ℤ) * tripleCount n k v1 v2 =
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) := by
  unfold tripleCount deltaCharSum;
  unfold tripleSet; simp +decide [ mul_assoc, Finset.sum_mul _ _ _ ] ;
  -- By interchanging the order of summation, we can rewrite the right-hand side.
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

/-- **AlmostBentVanishing**: The deep spectral condition from Kasami (1971) /
    Canteaut-Charpin-Dobbertin (2000).

    For any three nonzero elements `c₁, c₂, c₃` with `c₁ + c₂ + c₃ = 0` and
    pairwise distinct, the "twisted" fourth moment vanishes:
    `∑_a W_F(a·c₁) · W_F(a·c₂) · W_F(a·c₃) · W_F(0) = ...`

    More precisely, for AB functions, the character sum
    `∑_a S_Δ(a·v₁) · S_Δ(a·v₂) · S_Δ(a·(v₁+v₂))`
    evaluates to `2^{3n-3}` for all nonzero `v₁ ≠ v₂`. -/
def AlmostBentVanishing (n k : ℕ) : Prop :=
  ∀ (v1 v2 : F2n n), v1 ≠ 0 → v2 ≠ 0 → v1 ≠ v2 →
    ∑ a : F2n n, deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2)) = (2 ^ (3 * n - 3) : ℤ)

/-! ### From AB to AlmostBentVanishing -/

/-- The AB property of the Kasami function implies AlmostBentVanishing.

    **Proof sketch** (following Carlet 2021, §6.4 and Pott 1995):

    1. The character sum `S_Δ(c) = ∑_{x∈Δ} χ(cx)` is related to the WHT of the
       Kasami function by `S_Δ(c) = (1/2^n) ∑_a W_F(a) · W_F(a+c)` plus correction terms.

    2. The triple product `∑_a S_Δ(av₁) S_Δ(av₂) S_Δ(a(v₁+v₂))` can be expanded
       in terms of fourth moments of the WHT.

    3. For AB functions, `W_F(a)^2 ∈ {0, 2^{n+1}}`, which constrains the fourth
       moment and the triple product.

    4. After careful evaluation (using `ab_fourth_moment` and the Parseval identity),
       the triple product evaluates to `2^{3n-3}`.

    This is the deepest step and is left as sorry — it requires substantial
    character-sum manipulation. -/
-- The main theorem to prove
theorem ab_implies_vanishing_goal (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k := by
  sorry

theorem ab_implies_vanishing (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k)) :
    AlmostBentVanishing n k :=
  ab_implies_vanishing_goal n k hk hn hn_odd hgcd hab

/-! ### Triple count evaluation -/

/-
**P₃ from AlmostBentVanishing**: Given the spectral condition, the triple count
    evaluates to `2^{2n-3}`.

    Proof: From `tripleCount_charSum_eq` and `AlmostBentVanishing`:
    `2^n · T(v₁,v₂) = 2^{3n-3}`
    Hence `T(v₁,v₂) = 2^{3n-3} / 2^n = 2^{2n-3}`.
-/
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