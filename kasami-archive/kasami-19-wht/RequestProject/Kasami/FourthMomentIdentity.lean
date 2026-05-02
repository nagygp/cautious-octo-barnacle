/-
# Fourth Moment Identity

The key identity: ∑_a W_f(a)^4 = 2^n · ∑_z (∑_x χ(D_z f(x)))^2

This connects the Walsh-Hadamard transform to the derivative distribution.
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FourthMoment

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-- The derivative sum: S_z = ∑_x χ(D_z f(x)) = ∑_x χ(f(x+z) + f(x)). -/
def derivSum {n : ℕ} (f : F2n n → F2n n) (z : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (f (x + z) + f x)

/-- S_0 = 2^n (the derivative at 0 is always 0). -/
theorem derivSum_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    derivSum f 0 = 2 ^ n := by
  simp [derivSum, chi_zero, F2n.card n hn]

/-- W_f(a)^2 = ∑_z χ(az) · S_z. -/
theorem wht_sq_eq_sum_derivSum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (a : F2n n) :
    wht f a ^ 2 = ∑ z : F2n n, chi n (a * z) * derivSum f z := by
  unfold wht derivSum
  rw [sq, Finset.sum_mul_sum]
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [← chi_add]
    rw [show a * x + f x + (a * y + f y) = a * (x + y) + (f x + f y) from by ring]
  conv_lhs =>
    arg 2; ext x
    rw [show ∑ y : F2n n, chi n (a * (x + y) + (f x + f y)) =
        ∑ z : F2n n, chi n (a * (x + (x + z)) + (f x + f (x + z))) from
      (Equiv.sum_comp (Equiv.addLeft x) _).symm]
  have hxx : ∀ (x z : F2n n), x + (x + z) = z := by
    intro x z; rw [← add_assoc, F2n.add_self, zero_add]
  simp_rw [hxx]
  conv_lhs =>
    arg 2; ext x; arg 2; ext z
    rw [show a * z + (f x + f (x + z)) = a * z + (f (x + z) + f x) from by abel]
    rw [chi_add]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-
The fourth-moment identity: ∑_a W_f(a)^4 = 2^n · ∑_z S_z^2.
-/
theorem fourth_moment_identity {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) :
    ∑ a : F2n n, wht f a ^ 4 = (2 ^ n : ℤ) * ∑ z : F2n n, derivSum f z ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F2n n, ∑ z1 : F2n n, ∑ z2 : F2n n, chi n (a * (z1 + z2)) * derivSum f z1 * derivSum f z2 = ∑ z1 : F2n n, ∑ z2 : F2n n, (∑ a : F2n n, chi n (a * (z1 + z2))) * derivSum f z1 * derivSum f z2 := by
    simp +decide only [Finset.sum_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  convert h_fubini using 1;
  · refine' Finset.sum_congr rfl fun a ha => _;
    have h_expand : wht f a ^ 2 = ∑ z : F2n n, chi n (a * z) * derivSum f z := by
      exact?;
    convert congr_arg ( · ^ 2 ) h_expand using 1;
    · ring;
    · simp +decide only [mul_add, chi_add, mul_comm, mul_left_comm, sq, Finset.mul_sum _ _ _, mul_assoc];
  · rw [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Finset.sum_eq_single i ] <;> simp +contextual [ *, Finset.sum_ite ];
    · rw [ show ( Fintype.card ( F2n n ) : ℤ ) = 2 ^ n by exact_mod_cast F2n.card n hn ] ; norm_num [ chi_zero ] ; ring;
    · intro j hj; specialize hj; have := chi_sum hn ( i + j ) ; simp_all +decide [ add_comm i ] ;
      simp_all +decide [ mul_comm, add_eq_zero_iff_eq_neg ]

/-
For AB functions, ∑_z S_z^2 = 2^{2n+1}.
-/
theorem ab_derivSum_sq_sum {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n)
    (hf : IsAlmostBent f) :
    ∑ z : F2n n, derivSum f z ^ 2 = (2 ^ (2 * n + 1) : ℤ) := by
  convert congr_arg ( fun x : ℤ => x / 2 ^ n ) ( ab_fourth_moment hn f hf ) using 1;
  · rw [ fourth_moment_identity, Int.ediv_eq_of_eq_mul_left ] <;> first | positivity | ring;
  · exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by positivity ) ( by ring ) )

/-
The derivative count is always even for z ≠ 0.
-/
theorem derivSum_even {n : ℕ} (f : F2n n → F2n n) (z : F2n n) (hz : z ≠ 0) :
    Even (derivSum f z) := by
  -- Let $g(x) = D_z f(x)$. Then $derivSum = \sum_{x} \chi(g(x))$.
  set g : F2n n → F2n n := fun x => f (x + z) + f x;
  -- Since $g(x) = g(x+z)$, the map $x \mapsto x + z$ is a fixed-point-free involution on the set of solutions to $g(x) = b$.
  have h_involution : ∀ b : F2n n, Even (Finset.card (Finset.filter (fun x => g x = b) Finset.univ)) := by
    intro b;
    -- Since $g(x) = g(x+z)$, the set of solutions to $g(x) = b$ is partitioned into pairs $\{x, x+z\}$.
    have h_partition : ∃ S : Finset (Finset (F2n n)), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, g x = b) ∧ (∀ x, g x = b → ∃ s ∈ S, x ∈ s) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) := by
      use Finset.image (fun x => {x, x + z}) (Finset.filter (fun x => g x = b) Finset.univ);
      simp_all +decide [ Finset.disjoint_left ];
      grind +extAll;
    obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_partition;
    have h_partition_card : Finset.card (Finset.filter (fun x => g x = b) Finset.univ) = Finset.sum S (fun s => s.card) := by
      rw [ ← Finset.card_biUnion ];
      · congr with x ; aesop;
      · exact fun s hs t ht hst => hS₄ s hs t ht hst;
    exact h_partition_card.symm ▸ even_iff_two_dvd.mpr ( Finset.dvd_sum fun s hs => hS₁ s hs ▸ dvd_rfl );
  -- Since $g(x) = g(x+z)$, the sum $\sum_{x} \chi(g(x))$ can be rewritten as $\sum_{b} \chi(b) \cdot |g^{-1}(b)|$.
  have h_sum_rewrite : derivSum f z = ∑ b : F2n n, chi n b * (Finset.card (Finset.filter (fun x => g x = b) Finset.univ)) := by
    simp +decide only [derivSum, Finset.card_filter];
    simp +decide only [Nat.cast_sum, Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ] ; aesop;
  exact h_sum_rewrite.symm ▸ even_iff_two_dvd.mpr ( Finset.dvd_sum fun b _ => dvd_mul_of_dvd_right ( mod_cast even_iff_two_dvd.mp ( h_involution b ) ) _ )

end
end Kasami