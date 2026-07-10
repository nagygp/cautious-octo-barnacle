import Mathlib

/-!
# The additive (absolute) trace of a characteristic-2 finite field

The `𝔽₂`-linear trace map `L(x) = ∑_{i<m} x^{2^i}` on a field of characteristic
`2`, and the identities that make it behave like a trace:

* `truncTrace`             — the length-`m` (truncated) trace `∑_{i<m} x^{2^i}`;
* `truncTrace_add`         — additivity (`𝔽₂`-linearity), the "freshman's dream";
* `truncTrace_sq_add_self` — the telescoping identity `L(x)² + L(x) = x^{2^m} + x`;
* `trace_frob_shift`       — Frobenius invariance of the *full* trace
                             `Tr(x^{2^k}) = Tr(x)` on `𝔽_{2ⁿ}`;
* `trace_artin_schreier_zero` — Artin–Schreier vanishing `Tr(t^{2^k} + t) = 0`;
* `trace_sq` / `trace_bit` — the full trace is idempotent, hence lands in `{0,1}`.

Taking `m = n` (where `|F| = 2ⁿ`) yields the absolute trace `𝔽_{2ⁿ} → 𝔽₂`.

(These facts were previously spread across the `DempwolffMueller` prerequisites
and the `Dobbertin.Thm8` / `Dobbertin.Thm8C1` files.)
-/

namespace Kasami.FiniteField

open Finset BigOperators

/-- The truncated trace map `L(x) = ∑_{i=0}^{m-1} x^{2^i}`. -/
def truncTrace {F : Type*} [CommSemiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

/-- Additivity of the truncated trace (`𝔽₂`-linearity via the freshman's dream). -/
lemma truncTrace_add {F : Type*} [CommSemiring F] [CharP F 2] (m : ℕ) (x y : F) :
    truncTrace m (x + y) = truncTrace m x + truncTrace m y := by
  simp only [truncTrace, ← Finset.sum_add_distrib]
  congr 1; ext i; exact add_pow_char_pow (p := 2) (n := i) x y

/-- The telescoping identity `L(x)² + L(x) = x^{2^m} + x`. -/
lemma truncTrace_sq_add_self {F : Type*} [CommSemiring F] [CharP F 2]
    (m : ℕ) (x : F) :
    truncTrace m x ^ 2 + truncTrace m x = x ^ (2 ^ m) + x := by
  unfold truncTrace; induction m <;> simp_all +decide [ Finset.sum_range_succ, pow_succ ] ; ring;
  · rw [ mul_two, CharTwo.add_self_eq_zero ];
  · simp_all +decide [ add_mul, mul_add, pow_mul ] ; ring;
    simp_all +decide [ CharTwo.two_eq_zero ];
    simp_all +decide [ add_comm, add_left_comm, add_assoc, sq ];
    simp_all +decide [ ← add_assoc, ← two_mul, CharTwo.two_eq_zero ]

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Frobenius invariance of the full trace: `Tr(x^{2^k}) = Tr(x)` on `𝔽_{2ⁿ}`. -/
theorem trace_frob_shift {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ) (x : F) :
    truncTrace n (x ^ (2 ^ k)) = truncTrace n x := by
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

/-- Artin–Schreier vanishing: `Tr(t^{2^k} + t) = 0` for all `t`. -/
theorem trace_artin_schreier_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (t : F) : truncTrace n (t ^ (2 ^ k) + t) = 0 := by
  rw [ truncTrace_add ];
  rw [ trace_frob_shift hn k t, ← two_mul, CharTwo.two_eq_zero, MulZeroClass.zero_mul ]

/-- On `𝔽_{2ⁿ}` the absolute trace is idempotent under squaring: `Tr(x)² = Tr(x)`. -/
theorem trace_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    (truncTrace n x) ^ 2 = truncTrace n x := by
  have := @truncTrace_sq_add_self F _ _ n x;
  simp_all +decide [ ← hn, FiniteField.pow_card ];
  grind

/-- On `𝔽_{2ⁿ}` the absolute trace is a bit: `Tr(x) ∈ {0,1}`. -/
theorem trace_bit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    truncTrace n x = 0 ∨ truncTrace n x = 1 := by
  have := trace_sq hn x; simp_all +decide [ pow_succ' ] ;
  grind

end Field

end Kasami.FiniteField
