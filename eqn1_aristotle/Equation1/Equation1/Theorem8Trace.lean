import Mathlib
import Dobbertin1999MVP.Equation1.FiniteFieldPrereqs

/-!
# Equation (1) MVP — trace lemmas from Theorem 8

The two `Dobbertin.Thm8` trace facts on the dependency path of equation (1):
Frobenius invariance of the absolute trace (`trace_frob_shift`) and the
Artin–Schreier vanishing `Tr(t^{2^k} + t) = 0` (`trace_artin_schreier_zero`).
Copied verbatim from `Theorem8.lean`; nothing else from that file is needed.
-/

namespace Dobbertin.Thm8

open scoped BigOperators

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]


/-
Frobenius invariance of the full trace: `Tr(x^{2^k}) = Tr(x)`.
-/
theorem trace_frob_shift {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ) (x : F) :
    DempwolffMueller.truncTrace n (x ^ (2 ^ k)) = DempwolffMueller.truncTrace n x := by
  -- By definition of exponentiation in a finite field, we can rewrite the right-hand side.
  have h_exp : ∑ i ∈ Finset.range n, (x ^ (2 ^ k)) ^ (2 ^ i) = ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
    -- Since $x^{2^n} = x$, we can rewrite the sum as $\sum_{i=k}^{n+k-1} x^{2^i}$.
    have h_sum_shift : ∑ i ∈ Finset.range n, x ^ (2 ^ (i + k)) = ∑ i ∈ Finset.range n, x ^ (2 ^ ((i + k) % n)) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ ← Nat.mod_add_div ( i + k ) n ] ; simp_all +decide [ pow_add, pow_mul ] ;
      induction' ( i + k ) / n with m ih <;> simp_all +decide [ pow_succ, pow_mul ];
      rw [ ← pow_mul, mul_comm, pow_mul, ← hn, FiniteField.pow_card ];
    -- Since $(i + k) \mod n$ is a permutation of $\{0, 1, ..., n-1\}$, the sums are equal.
    have h_perm : Finset.image (fun i => (i + k) % n) (Finset.range n) = Finset.range n := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by rintro rfl; simp_all +decide [ pow_succ' ] ) _;
      rw [ Finset.card_image_of_injOn ];
      intros i hi j hj hij; have := Nat.modEq_iff_dvd.mp hij.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith ] ;
    have h_perm_sum : ∑ i ∈ Finset.range n, x ^ (2 ^ ((i + k) % n)) = ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
      conv_rhs => rw [ ← h_perm, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
    convert h_sum_shift.trans h_perm_sum using 2 ; ring;
  exact h_exp

/-
`Tr(t^{2^k} + t) = 0` for all `t`.
-/
theorem trace_artin_schreier_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (t : F) : DempwolffMueller.truncTrace n (t ^ (2 ^ k) + t) = 0 := by
  rw [ DempwolffMueller.truncTrace_add ];
  rw [ trace_frob_shift hn k t, ← two_mul, CharTwo.two_eq_zero, MulZeroClass.zero_mul ]

end Field

end Dobbertin.Thm8
