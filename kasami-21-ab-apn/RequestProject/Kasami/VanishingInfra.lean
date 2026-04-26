/-
# Infrastructure for ab_implies_vanishing_goal

Helper lemmas connecting the delta character sum to derivative character sums
and establishing the vanishing of the triple character sum for AB Kasami functions.
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

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 16000000

/-! ### Delta generator pairing -/

/-- In char 2, `b + 2 = b` since `2 = 0`. -/
theorem F2n.add_two_eq {n : ℕ} (b : F2n n) : b + (1 + 1) = b := by
  simp [show (1 : F2n n) + 1 = 0 from F2n.add_self 1]

/-- The Kasami delta generator satisfies `g(b) = g(b+1)` in char 2. -/
theorem deltaGen_paired (n k : ℕ) (b : F2n n) :
    kasamiDeltaGen n k b = kasamiDeltaGen n k (b + 1) := by
  simp only [kasamiDeltaGen, kasamiF, F2n.powMap]
  have h : b + 1 + 1 = b := by
    rw [show b + 1 + 1 = b + (1 + 1) from by ring, F2n.add_two_eq]
  rw [h]; ring

/-! ### Kasami delta set cardinality -/

/-
The delta generator is 2-to-1 when the Kasami function is APN.
    Specifically: if g(b₁) = g(b₂) then b₂ ∈ {b₁, b₁+1}.
-/
theorem deltaGen_two_to_one (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (b₁ b₂ : F2n n) (heq : kasamiDeltaGen n k b₁ = kasamiDeltaGen n k b₂) :
    b₂ = b₁ ∨ b₂ = b₁ + 1 := by
  -- By the APN property, the equation F(x+1)+F(x) = c has at most 2 solutions for any c.
  have apn_property : ∀ c : F2n n, (Finset.univ.filter (fun x : F2n n => kasamiF n k (x + 1) + kasamiF n k x = c)).card ≤ 2 := by
    have := @ab_implies_apn n hn ( kasamiF n k ) hab 1;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Fin.ext_iff, ZMod ];
  contrapose! apn_property;
  refine' ⟨ _, Finset.two_lt_card.mpr ⟨ b₁, _, b₁ + 1, _, b₂, _, _ ⟩ ⟩ <;> simp_all +decide [ kasamiDeltaGen ];
  exact kasamiF n k ( b₁ + 1 ) + kasamiF n k b₁;
  · rfl;
  · grind +locals;
  · unfold kasamiDeltaGen at heq; linear_combination heq.symm;
  · tauto

/-
|Δ| = 2^{n-1} for AB Kasami functions.
-/
theorem kasamiDelta_card_eq (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hab : IsAlmostBent (kasamiF n k)) :
    (kasamiDelta n k).card = 2 ^ (n - 1) := by
  -- Since $g$ is 2-to-1, the cardinality of its image is half the cardinality of its domain.
  have h_card_image : (Finset.univ.image (fun b : F2n n => kasamiDeltaGen n k b)).card * 2 = Fintype.card (F2n n) := by
    have h_card_image : ∀ y ∈ Finset.image (fun b : F2n n => kasamiDeltaGen n k b) Finset.univ, Finset.card (Finset.filter (fun x => kasamiDeltaGen n k x = y) Finset.univ) = 2 := by
      intro y hy
      have h_two_to_one : ∀ x, kasamiDeltaGen n k x = y → kasamiDeltaGen n k (x + 1) = y := by
        exact fun x hx => hx ▸ deltaGen_paired n k x ▸ rfl;
      have h_two_to_one : ∀ x₁ x₂, kasamiDeltaGen n k x₁ = y → kasamiDeltaGen n k x₂ = y → x₂ = x₁ ∨ x₂ = x₁ + 1 := by
        intros x₁ x₂ hx₁ hx₂
        apply deltaGen_two_to_one n k hk hn hn_odd hgcd hab x₁ x₂ (by
        rw [hx₁, hx₂]);
      obtain ⟨ x, hx ⟩ := Finset.mem_image.mp hy;
      rw [ show Finset.filter ( fun z => kasamiDeltaGen n k z = y ) Finset.univ = { x, x + 1 } from ?_ ];
      · rw [ Finset.card_pair ] ; norm_num;
      · grind +locals;
    have h_card_image : ∑ y ∈ Finset.image (fun b : F2n n => kasamiDeltaGen n k b) Finset.univ, Finset.card (Finset.filter (fun x => kasamiDeltaGen n k x = y) Finset.univ) = Fintype.card (F2n n) := by
      rw [ ← Finset.card_biUnion ];
      · convert Finset.card_univ using 2 ; ext x ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    rw [ ← h_card_image, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
  rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
  exact Eq.symm ( by rw [ F2n.card _ ( Nat.succ_ne_zero _ ) ] at h_card_image; norm_num [ pow_succ' ] at *; linarith! )

/-! ### Delta character sum halving -/

/-
For c ≠ 0 and AB Kasami functions:
    `2 · S_Δ(c) = χ(c) · ∑_b χ(c · D₁F(b))`.

    This follows from the 2-to-1 property of the delta generator:
    `∑_b χ(c·g(b)) = 2 · S_Δ(c)` (since each element of Δ has exactly 2 preimages).
    And `g(b) = F(b) + F(b+1) + 1 = D₁F(b) + 1`, so
    `χ(c·g(b)) = χ(c·D₁F(b) + c) = χ(c) · χ(c·D₁F(b))`.
    Therefore `2·S_Δ(c) = χ(c) · ∑_b χ(c·D₁F(b))`.
-/
theorem delta_charSum_halving (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (c : F2n n) (hc : c ≠ 0) :
    2 * deltaCharSum n k c = chi n c * derivCharSum (kasamiF n k) 1 c := by
  unfold deltaCharSum derivCharSum;
  -- By definition of `kasamiDeltaGen`, we know that each element in `kasamiDelta n k` has exactly two preimages.
  have h_preimage : ∀ x ∈ kasamiDelta n k, (Finset.filter (fun b => kasamiDeltaGen n k b = x) Finset.univ).card = 2 := by
    intro x hx
    have h_two_to_one : ∀ b₁ b₂ : F2n n, (kasamiDeltaGen n k b₁ = x ∧ kasamiDeltaGen n k b₂ = x) → b₂ = b₁ ∨ b₂ = b₁ + 1 := by
      exact fun b₁ b₂ h => deltaGen_two_to_one n k hk hn hn_odd hgcd hab b₁ b₂ <| h.1.trans h.2.symm
    generalize_proofs at *; (
    obtain ⟨ b, hb ⟩ := Finset.mem_image.mp hx; use Finset.card_eq_two.mpr ⟨ b, b + 1, ?_, ?_ ⟩ <;> simp_all +decide [ Finset.ext_iff ] ;
    grind +suggestions);
  have h_sum_preimage : ∑ x ∈ kasamiDelta n k, (Finset.filter (fun b => kasamiDeltaGen n k b = x) Finset.univ).sum (fun b => chi n (c * (kasamiDeltaGen n k b))) = ∑ b : F2n n, chi n (c * (kasamiDeltaGen n k b)) := by
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x hx => x.snd ) _ _ _ _ <;> simp +decide;
    · aesop;
    · exact fun x => Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
  convert h_sum_preimage using 1;
  · rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_filter.mp hy |>.2 ] ] ; aesop;
  · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring;
    rw [ ← chi_add ] ; ring;
    unfold kasamiDeltaGen; ring;

/-! ### Chi triple product -/

/-- χ(av₁) · χ(av₂) · χ(a(v₁+v₂)) = 1 in characteristic 2. -/
theorem chi_triple_cancel {n : ℕ} (a v1 v2 : F2n n) :
    chi n (a * v1) * chi n (a * v2) * chi n (a * (v1 + v2)) = 1 := by
  rw [show chi n (a * v1) * chi n (a * v2) * chi n (a * (v1 + v2)) =
    chi n (a * v1 + a * v2 + a * (v1 + v2)) from by rw [← chi_add, ← chi_add]]
  have : a * v1 + a * v2 + a * (v1 + v2) = 0 := by
    rw [show a * v1 + a * v2 + a * (v1 + v2) = a * (v1 + v2) + a * (v1 + v2) from by ring]
    exact F2n.add_self _
  rw [this, chi_zero]

/-! ### Triple sum decomposition -/

/-
The nonzero part of the triple character sum.
    For a ≠ 0: S_Δ(av₁)·S_Δ(av₂)·S_Δ(a(v₁+v₂)) = (1/8)·A(av₁)·A(av₂)·A(a(v₁+v₂))
    where A(c) = derivCharSum F 1 c.
-/
theorem triple_sum_nonzero_term (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (a v1 v2 : F2n n) (ha : a ≠ 0) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    8 * (deltaCharSum n k (a * v1) * deltaCharSum n k (a * v2) *
      deltaCharSum n k (a * (v1 + v2))) =
    derivCharSum (kasamiF n k) 1 (a * v1) *
    derivCharSum (kasamiF n k) 1 (a * v2) *
    derivCharSum (kasamiF n k) 1 (a * (v1 + v2)) := by
  have h_delta_charSum_halving : ∀ c : F2n n, c ≠ 0 → 2 * deltaCharSum n k c = chi n c * derivCharSum (kasamiF n k) 1 c := by
    exact?;
  have h_chi_triple_cancel : chi n (a * v1) * chi n (a * v2) * chi n (a * (v1 + v2)) = 1 := by
    exact?;
  grind +splitImp

/-
The sum ∑_a A(av₁)·A(av₂)·A(a(v₁+v₂)) equals 2^n · N
    where N = |{(b₁,b₂,b₃) : v₁D₁F(b₁)+v₂D₁F(b₂)+(v₁+v₂)D₁F(b₃)=0}|.
    By character orthogonality.
-/
theorem deriv_triple_sum_eq_count (n k : ℕ) (hn : n ≠ 0) (v1 v2 : F2n n) :
    ∑ a : F2n n,
      derivCharSum (kasamiF n k) 1 (a * v1) *
      derivCharSum (kasamiF n k) 1 (a * v2) *
      derivCharSum (kasamiF n k) 1 (a * (v1 + v2)) =
    (2 ^ n : ℤ) * ((Finset.univ.filter fun t : F2n n × F2n n × F2n n =>
      v1 * (kasamiF n k (t.1 + 1) + kasamiF n k t.1) +
      v2 * (kasamiF n k (t.2.1 + 1) + kasamiF n k t.2.1) +
      (v1 + v2) * (kasamiF n k (t.2.2 + 1) + kasamiF n k t.2.2) = 0).card : ℤ) := by
  -- Let's expand the product of sums.
  have h_expand : ∀ a : F2n n, derivCharSum (kasamiF n k) 1 (a * v1) * derivCharSum (kasamiF n k) 1 (a * v2) * derivCharSum (kasamiF n k) 1 (a * (v1 + v2)) = ∑ t : F2n n × F2n n × F2n n, chi n (a * (v1 * (kasamiF n k (t.1 + 1) + kasamiF n k t.1) + v2 * (kasamiF n k (t.2.1 + 1) + kasamiF n k t.2.1) + (v1 + v2) * (kasamiF n k (t.2.2 + 1) + kasamiF n k t.2.2))) := by
    intro a; rw [ derivCharSum, derivCharSum, derivCharSum ] ; simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum, mul_assoc, mul_left_comm, Finset.sum_add_distrib, chi_add ] ; ring;
    simp +decide only [← Finset.sum_product'];
    refine' Finset.sum_congr rfl fun x hx => _ ; rw [ ← chi_add, ← chi_add ] ; ring;
  -- By character orthogonality, we know that $\sum_{a \in \mathbb{F}_{2^n}} \chi(a \cdot s) = 2^n$ if $s = 0$ and $0$ otherwise.
  have h_orthogonality : ∀ s : F2n n, ∑ a : F2n n, chi n (a * s) = if s = 0 then (2 ^ n : ℤ) else 0 := by
    intro s; specialize h_expand 0; simp_all +decide [ Finset.sum_ite ] ;
    convert Kasami.chi_sum hn s using 1;
    ac_rfl;
  simp_all +decide [ Finset.sum_ite ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => h_orthogonality _ ] ; simp +decide [ Finset.sum_ite ] ; ring;

/-- The triple count N = |{(b₁,b₂,b₃) : v₁D₁F(b₁)+v₂D₁F(b₂)+(v₁+v₂)D₁F(b₃)=0}|
    equals 2^{2n} for AB Kasami functions with v₁, v₂ nonzero and distinct. -/
theorem kasami_triple_count_eq (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) (hab : IsAlmostBent (kasamiF n k))
    (v1 v2 : F2n n) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hne : v1 ≠ v2) :
    (Finset.univ.filter fun t : F2n n × F2n n × F2n n =>
      v1 * (kasamiF n k (t.1 + 1) + kasamiF n k t.1) +
      v2 * (kasamiF n k (t.2.1 + 1) + kasamiF n k t.2.1) +
      (v1 + v2) * (kasamiF n k (t.2.2 + 1) + kasamiF n k t.2.2) = 0).card = 2 ^ (2 * n) := by
  sorry

end
end Kasami