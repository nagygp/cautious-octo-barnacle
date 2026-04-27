/-
# Fourth Moment Identity and AB implies APN

This module builds infrastructure for the fourth-moment identity connecting
Walsh–Hadamard transform values to derivative distributions.

## References
- [Carlet, *Boolean Functions for Cryptography and Coding Theory*], §6.2
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

/-! ### Extended Walsh–Hadamard transform -/

/-- The extended (two-argument) WHT: `W_f(a, b) = ∑_x χ(a·x + b·f(x))`. -/
def wht2 {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (a * x + b * f x)

/-- `wht2 f a 1 = wht f a`. -/
theorem wht2_one {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    wht2 f a 1 = wht f a := by
  simp [wht2, wht, mul_one]

/-! ### Derivative distribution -/

/-- The derivative distribution: `N_f(a,b) = |{x : f(x+a) + f(x) = b}|`. -/
noncomputable def derivCount {n : ℕ} (f : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter fun x : F2n n => f (x + a) + f x = b).card

/-- The sum ∑_b N_f(a,b) = |F|. -/
theorem derivCount_sum {n : ℕ} (f : F2n n → F2n n) (a : F2n n) :
    ∑ b : F2n n, derivCount f a b = Fintype.card (F2n n) := by
  unfold derivCount
  simp only [Finset.card_filter]
  rw [← Finset.card_univ]
  rw [Finset.sum_comm]
  simp

/-
Solutions come in pairs: x ↦ x + a is an involution on solution sets.
-/
theorem derivCount_even {n : ℕ} (f : F2n n → F2n n) (a : F2n n) (ha : a ≠ 0)
    (b : F2n n) : Even (derivCount f a b) := by
  have h_partition : ∃ S : Finset (Finset (F2n n)), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, f (x + a) + f x = b) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) ∧ (Finset.univ.filter (fun x => f (x + a) + f x = b)) = Finset.biUnion S id := by
    refine' ⟨ Finset.image ( fun x => { x, x + a } ) ( Finset.filter ( fun x => f ( x + a ) + f x = b ) Finset.univ ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
    · grind;
    · grind +revert;
    · ext x; simp +decide [ Finset.mem_biUnion ] ;
      grind;
  obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_partition;
  unfold derivCount;
  rw [ hS₄, Finset.card_biUnion ] <;> aesop

/-! ### Scaling for power functions -/

/-
For a power function x ↦ x^d with bijective power map, the extended WHT at (a,b)
    for b ≠ 0 equals the standard WHT at a shifted argument.
-/
theorem wht2_power_scaling {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d))
    (a b : F2n n) (hb : b ≠ 0) :
    ∃ c : F2n n, c ≠ 0 ∧ c ^ d = b ∧
      wht2 (fun x => x ^ d) a b = wht (fun x => x ^ d) (a * c⁻¹) := by
  obtain ⟨c, hc⟩ : ∃ c : F2n n, c^d = b := by
    exact hbij.surjective b;
  use c;
  unfold wht2 wht;
  by_cases hc0 : c = 0 <;> simp_all +decide [ mul_assoc, mul_left_comm ];
  conv_lhs => rw [ ← Equiv.sum_comp ( Equiv.mulLeft₀ c⁻¹ ( inv_ne_zero hc0 ) ) ] ;
  simp +decide [ ← mul_assoc, ← hc, mul_pow, hc0 ]

/-- For power functions, identity-component AB implies full AB on all components. -/
theorem power_ab_all_components {n : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (hbij : Function.Bijective (F2n.powMap n d))
    (hab : IsAlmostBent (fun x : F2n n => x ^ d)) :
    ∀ a b : F2n n, b ≠ 0 →
      wht2 (fun x => x ^ d) a b ^ 2 = 0 ∨
      wht2 (fun x => x ^ d) a b ^ 2 = (2 ^ (n + 1) : ℤ) := by
  intro a b hb
  obtain ⟨c, _, _, heq⟩ := wht2_power_scaling hn d hd hbij a b hb
  rw [heq]
  exact hab (a * c⁻¹)

end
end Kasami