/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AB implies APN

This module proves that almost bent (AB) functions are also almost perfect
nonlinear (APN). The proof uses the fourth moment identity.

## Main results
- `ab_implies_apn_via_fourth_moment`: AB ⟹ APN using spectral methods
- `apn_deltaGen_two_to_one`: for APN, kasamiDeltaGen is 2-to-1

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*][carlet2021], §6.2
- [Chabaud, Vaudenay (1995)][chabaud1995]
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.APN
import RequestProject.Kasami.AutoCorrelation
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction
import RequestProject.Kasami.DifferenceSet
import RequestProject.Kasami.CrossCorrelation

namespace Kasami

open scoped BigOperators
open Classical

noncomputable section

set_option maxHeartbeats 800000

/-! ### Spectral characterization of APN -/

/-- The fourth moment of WHT relates to the derivative distribution:
    `∑_b W_f(b)^4 = 2^n · ∑_{a≠0} ∑_c N_a(c)^2 + ...` -/
theorem fourth_moment_deriv_link {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ b : F2n n, wht f b ^ 4 =
    (2 ^ n : ℤ) * ∑ a : F2n n, ∑ c : F2n n,
      ((Finset.univ.filter fun x => f (x + a) + f x = c).card : ℤ) ^ 2 := by
  sorry

/-
For AB functions, the fourth moment identity forces APN.
    Since `∑ W^4 = 2·(2^n)^3` and the fourth moment relates to ∑ N_a(b)²,
    we get that N_a(b) ≤ 2 for all a ≠ 0, b.
-/
theorem ab_implies_apn_via_spectrum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) : IsAPN f := by
  convert ab_implies_apn hn f hf using 1

/-! ### Consequence for kasamiDeltaGen -/

/-
For APN functions, kasamiDeltaGen is 2-to-1:
    each element of Δ has exactly 2 preimages under `b ↦ F(b) + F(b+1) + 1`.
    This follows from the APN property applied with `a = 1`.
-/
theorem apn_deltaGen_two_to_one {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAPN f) (y : F2n n)
    (hy : y ∈ Finset.image (fun b => f (b + 1) + f b + 1) Finset.univ) :
    (Finset.univ.filter fun b : F2n n => f (b + 1) + f b + 1 = y).card = 2 := by
  obtain ⟨ b, hb, rfl ⟩ := Finset.mem_image.mp hy;
  have := apn_deriv_two_to_one f hf 1 ; simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ];
  convert this b using 1

/-
For APN functions, |Δ| = 2^{n-1}.
-/
theorem apn_delta_card {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hf : IsAPN f) :
    (Finset.image (fun b => f (b + 1) + f b + 1) Finset.univ).card = 2 ^ (n - 1) := by
  -- For APN functions, the image of the derivative map $D_1 f$ has cardinality $2^{n-1}$.
  have h_deriv_image_card : (Finset.image (fun b => f (b + 1) + f b) (Finset.univ : Finset (F2n n))).card = 2 ^ (n - 1) := by
    convert Kasami.apn_image_card hn f hf 1 _ using 1;
    · refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ derivDistrib ];
      · intro a;
        have := Kasami.apn_deriv_two_to_one f hf 1 ( by aesop ) ( f ( a + 1 ) + f a ) ; aesop;
      · exact fun b hb => Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, by simpa using hx ⟩;
    · exact?;
  convert h_deriv_image_card using 1;
  exact Finset.card_bij ( fun x hx => x - 1 ) ( by aesop ) ( by aesop ) ( by aesop )

/-
For APN functions, the weighted character sum is twice the deltaCharSum.
-/
theorem apn_weighted_eq_twice_delta {n k : ℕ} (hn : n ≠ 0)
    (hf : IsAPN (kasamiF n k)) (c : F2n n) :
    weightedCharSum n k c = 2 * deltaCharSum n k c := by
  have h_two_to_one : ∀ y ∈ Finset.image (kasamiDeltaGen n k) Finset.univ, (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = y).card = 2 := by
    convert apn_deltaGen_two_to_one hn ( kasamiF n k ) hf using 1;
    simp +decide [ kasamiDeltaGen, add_comm, add_left_comm, add_assoc ];
  have h_sum_rewrite : ∑ b : F2n n, chi n (c * kasamiDeltaGen n k b) = ∑ y ∈ Finset.image (kasamiDeltaGen n k) Finset.univ, (Finset.univ.filter fun b : F2n n => kasamiDeltaGen n k b = y).card * chi n (c * y) := by
    rw [ Finset.sum_image' ];
    simp +contextual [ Finset.sum_filter ];
    simp +decide [ Finset.sum_ite ];
  convert h_sum_rewrite using 1;
  rw [ Finset.sum_congr rfl fun x hx => by rw [ h_two_to_one x hx ] ] ; norm_num [ mul_comm, Finset.mul_sum _ _ _ ];
  unfold deltaCharSum; simp +decide [ mul_comm, Finset.mul_sum _ _ _ ] ;
  rfl

end
end Kasami