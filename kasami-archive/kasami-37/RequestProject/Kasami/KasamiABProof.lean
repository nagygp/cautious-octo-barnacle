/-
# Decomposed Proof Architecture for kasami_is_ab

This file decomposes the proof of `kasami_is_ab` into modular sub-lemmas.
Each sorry'd lemma represents a single, well-defined mathematical step.

## Proof Route (Quadratic Form / CCD)

1. **wht f 0 = 0**: Since x^d is a permutation, ∑_x χ(x^d) = ∑_y χ(y) = 0.  ✅
2. **Q(x) = Tr(x^d) is an F₂-quadratic form**: bilinearity of polar form.    ⚠️
3. **Polar form B(x,y) = Tr(y · L(x))**: via Frobenius and trace invariance.  ⚠️
4. **|rad(B)| ∈ {1, 2}**: from linPolyL kernel classification.               ⚠️
5. **Q vanishes on rad**: algebraic constraint from Kasami exponent.           ⚠️
6. **Gauss sum S(Q)² = 2^n · |rad|**: from QuadFormGF2/GaussSum.              ⚠️
7. **Parity: S² = 2^n impossible for odd n**: 2^n not a perfect square.       ⚠️
8. **Shifted Gauss sum**: wht f a = ±S(Q) or 0 depending on linear term.      ⚠️
9. **Assembly**: combine 1-8 to get IsAlmostBent.                              ⚠️

## References
- Canteaut, Charpin, Dobbertin (2000), SIAM J. Discrete Math.
- Carlet (2021), §6.4
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.KasamiExponent
import RequestProject.Kasami.KasamiFunction

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 8000000

/-! ## Step 1: WHT at a = 0 vanishes (PROVED) -/

/-- The WHT of a permutation at 0 vanishes: if x ↦ f(x) is bijective,
    then ∑_x χ(f(x)) = 0. -/
theorem wht_perm_zero {n : ℕ} (hn : n ≠ 0)
    (f : F2n n → F2n n) (hperm : Function.Bijective f) :
    ∑ x : F2n n, chi n (f x) = 0 := by
  exact (Equiv.sum_comp (Equiv.ofBijective _ hperm) (chi n)).trans (chi_sum_all_zero hn)

/-- For the Kasami function: wht f 0 = 0. -/
theorem kasami_wht_at_zero (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n) :
    wht (kasamiF n k) 0 = 0 := by
  simp only [wht, zero_mul, zero_add, kasamiF, F2n.powMap]
  exact wht_perm_zero hn _ (kasamiExp_permutation k n hk hn hn_odd hgcd)

/-! ## Step 2: The wht as a shifted quadratic form sum -/

/-- The wht of the Kasami function at parameter a equals the
    "shifted" exponential sum ∑_x (-1)^{Tr(x^d) + Tr(a·x)}.
    This is the exponential sum of Q(x) + L_a(x) where
    Q(x) = Tr(x^d) and L_a(x) = Tr(a·x). -/
theorem kasami_wht_as_shifted_sum (n k : ℕ) (a : F2n n) :
    wht (kasamiF n k) a =
    ∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k) + tr2 n (a * x))) := by
  simp only [wht, kasamiF, F2n.powMap, chi]
  congr 1; ext x
  congr 1
  rw [← tr2_add]; congr 1; ring

/-! ## Steps 3-8: Deep sub-lemmas (each is a single mathematical step) -/

/-- **Step 3**: Tr(x^d) is an F₂-quadratic form.
    The polar form B(x,y) = Tr((x+y)^d + x^d + y^d) is F₂-biadditive.
    For the Kasami exponent d = 2^{2k} - 2^k + 1, this follows from
    the specific structure of (x+y)^d + x^d + y^d as a sum of
    Frobenius cross-terms. -/
theorem kasami_trace_power_is_quadratic (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    ∀ x₁ x₂ y : F2n n,
      tr2 n ((x₁ + x₂ + y) ^ kasamiExp k) + tr2 n ((x₁ + x₂) ^ kasamiExp k) +
        tr2 n (y ^ kasamiExp k) =
      tr2 n ((x₁ + y) ^ kasamiExp k) + tr2 n (x₁ ^ kasamiExp k) +
        (tr2 n ((x₂ + y) ^ kasamiExp k) + tr2 n (x₂ ^ kasamiExp k)) := by
  sorry

/-- **Step 4**: The radical of the Kasami quadratic form has size 1 or 2.
    This follows from the linearized polynomial kernel analysis:
    - The polar form B(x,y) = Tr(y · L(x)) where L is related to linPolyL k
    - ker(L) has size 1 or 4 (from linPolyL_ker_card_classification)
    - rad(B) = ker(L) intersected with ker(Tr), giving size 1 or 2 -/
theorem kasami_radical_card (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    (Finset.univ.filter fun y : F2n n =>
      ∀ x : F2n n, tr2 n ((x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k) = 0).card
    ∈ ({1, 2} : Set ℕ) := by
  sorry

/-- **Step 5**: The Gauss sum squared of Tr(x^d) equals 2^n · |radical|.
    This uses the expSum_sq_eq_card_mul_radical_card from QuadFormGF2/GaussSum.lean
    combined with the fact that Tr(x^d) vanishes on the radical. -/
theorem kasami_gauss_sum_sq_eq (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k)))) ^ 2 =
    (2 : ℤ) ^ n *
    (Finset.univ.filter fun y : F2n n =>
      ∀ x : F2n n, tr2 n ((x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k) = 0).card := by
  sorry

/-- **Step 6**: For odd n, the Gauss sum squared is 2^{n+1} (not 2^n).
    Since S = ∑_x (-1)^{Q(x)} is an integer, S² must be a perfect square.
    2^n is not a perfect square when n is odd, so |rad| ≠ 1.
    Combined with |rad| ∈ {1, 2}, we get |rad| = 2 and S² = 2^{n+1}. -/
theorem kasami_gauss_sum_sq_value (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k)))) ^ 2 =
    (2 : ℤ) ^ (n + 1) := by
  sorry

/-- **Step 7**: The shifted Gauss sum squared is 0 or S².
    For Q : F → ZMod 2 quadratic and L : F → ZMod 2 linear:
    (∑_x (-1)^{Q(x)+L(x)})² ∈ {0, (∑_x (-1)^{Q(x)})²}
    This is the "completing the square" argument for F₂-quadratic forms. -/
theorem shifted_gauss_sq_dichotomy (n : ℕ) (hn : n ≠ 0)
    (Q : F2n n → ZMod 2) (hQ0 : Q 0 = 0)
    (hQbil : ∀ x₁ x₂ y : F2n n,
      Q (x₁ + x₂ + y) + Q (x₁ + x₂) + Q y =
      Q (x₁ + y) + Q x₁ + (Q (x₂ + y) + Q x₂))
    (hQrad : ∀ y : F2n n,
      (∀ x : F2n n, Q (x + y) + Q x + Q y = 0) → Q y = 0)
    (L : F2n n → ZMod 2) (hL : ∀ x y : F2n n, L (x + y) = L x + L y) :
    (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x + L x))) ^ 2 = 0 ∨
    (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x + L x))) ^ 2 =
    (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (Q x))) ^ 2 := by
  sorry

/-! ## Step 9: Assembly -/

/-- Assembly: kasami_is_ab follows from the decomposed steps above. -/
theorem kasami_is_ab_from_steps (n k : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) (hn_odd : Odd n)
    (hgcd : Nat.Coprime k n)
    -- Step 6: Gauss sum value
    (h_gauss : (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k)))) ^ 2 =
      (2 : ℤ) ^ (n + 1))
    -- Step 7: Shifted dichotomy
    (h_shifted : ∀ a : F2n n,
      (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k) + tr2 n (a * x)))) ^ 2 = 0 ∨
      (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k) + tr2 n (a * x)))) ^ 2 =
      (∑ x : F2n n, (-1 : ℤ) ^ (ZMod.val (tr2 n (x ^ kasamiExp k)))) ^ 2) :
    IsAlmostBent (kasamiF n k) := by
  intro a
  have hwht := kasami_wht_as_shifted_sum n k a
  rcases h_shifted a with h | h
  · left; rw [hwht]; exact h
  · right; rw [hwht, h, h_gauss]

end
end Kasami
