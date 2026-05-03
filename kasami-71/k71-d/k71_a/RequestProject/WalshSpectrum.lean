/-
  WalshSpectrum.lean

  Task 3: Spectral Link and Triple Count.

  Connects the kernel bound (APN / AB property) to the Walsh spectrum
  and the combinatorial triple count.

  For an AB function on F_{2^n} (n odd):
  - The number of nonzero Walsh coefficients is exactly 2^{2n-1} + 2^{n-1}
  - The triple count is 2^{2n-3} - 2^{n-2}
-/
import Mathlib
import k71_a.RequestProject.BinomialKernel

set_option maxHeartbeats 4000000

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

noncomputable instance : Algebra (ZMod 2) F := ZMod.algebra _ _

/-! ### Walsh Transform definitions -/

/-- The canonical additive character of F_{2^n}.
    For x ∈ F_{2^n}, χ(x) = (-1)^{Tr(x)} where Tr is the absolute trace
    from F_{2^n} to F_2. -/
noncomputable def walshChar (x : F) : ℤ :=
  if (Algebra.trace (ZMod 2) F x) = 0 then 1 else -1

/-- The Walsh coefficient of f at (a, b):
    W_f(a, b) = Σ_{x ∈ F} χ(ax + bf(x)) -/
noncomputable def walshCoeff (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, walshChar (a * x + b * f x)

/-! ### Almost Bent (AB) property -/

/-- A function f: F_{2^n} → F_{2^n} is Almost Bent (AB) if
    W_f(a, b)² ∈ {0, 2^{n+1}} for all a, b with b ≠ 0. -/
def isAB (n : ℕ) (f : F → F) : Prop :=
  ∀ a b : F, b ≠ 0 → walshCoeff f a b ^ 2 ∈
    ({0, 2 ^ (n + 1)} : Set ℤ)

/-- The kernel dimension bound implies the AB property.
    If for every nonzero u, the derivative kernel has at most 2 elements,
    then the function is AB (when n is odd). -/
theorem kernel_dim_le_one_implies_AB (n : ℕ) (hn_odd : n % 2 = 1) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F)
    (hkernel : ∀ u : F, u ≠ 0 →
      Fintype.card {x : F | f (x + u) + f x + f u = 0} ≤ 2) :
    isAB n f := by
  sorry

/-! ### Walsh spectrum counting -/

/-- For an AB function on F_{2^n} (n odd), the number of nonzero
    Walsh coefficients W_f(a, b) (over all a ∈ F and nonzero b ∈ F)
    is exactly 2^{2n-1} + 2^{n-1}. -/
theorem ab_nonzero_walsh_count (n : ℕ) (hn_odd : n % 2 = 1) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hAB : isAB n f) :
    Fintype.card {p : F × F | p.2 ≠ 0 ∧ walshCoeff f p.1 p.2 ≠ 0} =
    2 ^ (2 * n - 1) + 2 ^ (n - 1) := by
  sorry

/-! ### Triple Count

A "triple" for f is a pair (a, b) ∈ F × F* such that W_f(a,b) = 0.
The triple count captures the combinatorial structure of the Walsh spectrum.
For an AB function on F_{2^n} (n odd), this count is 2^{2n-3} - 2^{n-2}. -/

/-- For an AB function on F_{2^n} (n odd), the number of zero Walsh
    coefficients (over nonzero b) is 2^{2n-1} - 2^{n-1}. -/
theorem ab_zero_walsh_count (n : ℕ) (hn_odd : n % 2 = 1) (hn : 1 < n)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hAB : isAB n f) :
    Fintype.card {p : F × F | p.2 ≠ 0 ∧ walshCoeff f p.1 p.2 = 0} =
    2 ^ (2 * n - 1) - 2 ^ (n - 1) := by
  sorry

/-
The total number of (a, b) pairs with b ≠ 0 is 2^n · (2^n - 1).
    Together with the nonzero count, this gives the zero count.
-/
theorem ab_walsh_partition (n : ℕ) (hn : 0 < n) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hAB : isAB n f) (hn_odd : n % 2 = 1) :
    Fintype.card {p : F × F | p.2 ≠ 0 ∧ walshCoeff f p.1 p.2 ≠ 0} +
    Fintype.card {p : F × F | p.2 ≠ 0 ∧ walshCoeff f p.1 p.2 = 0} =
    2 ^ n * (2 ^ n - 1) := by
  have h_total : Fintype.card {p : F × F | p.2 ≠ 0} = 2 ^ n * (2 ^ n - 1) := by
    simp +decide [ ← hcard, Fintype.card_subtype_compl ];
    rw [ Nat.mul_sub_left_distrib, mul_one, Fintype.card_subtype ];
    rw [ Finset.card_filter ];
    erw [ Finset.sum_product ] ; aesop;
  rw [ ← h_total, Fintype.card_subtype, Fintype.card_subtype ];
  rw [ Fintype.card_subtype ] ; rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext ; by_cases h : walshCoeff f ‹F × F›.1 ‹F × F›.2 = 0 <;> simp +decide [ h ] ;
  exact Finset.disjoint_filter.mpr ( by aesop )

end