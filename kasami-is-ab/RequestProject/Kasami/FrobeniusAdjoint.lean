/-
# Frobenius Adjoint and Trace Nondegeneracy

Helper lemmas for the radical characterization of the Gold bilinear form.

## Main results

* `trace_nondegenerate_F2n` : Tr(c·y) = 0 for all y ⟹ c = 0
* `tr_Mk_eq_zero` : Tr(x^{2^k} + x) = 0
* `frob_adj_exponent` : Definition of the adjoint exponent j = (n - k%n)%n
* `pow_frob_adj_eq` : y^{2^{k+j}} = y (so the Frobenius adjoint works)
* `tr_frobenius_adjoint` : Tr(c · y^{2^k}) = Tr(c^{2^j} · y)

## References

* Lidl, Niederreiter, *Finite Fields*, Theorem 2.24
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace

namespace Kasami

open scoped BigOperators
noncomputable section

/-! ### Trace Nondegeneracy -/

/-
Trace nondegeneracy: Tr(c·y) = 0 for all y implies c = 0.
-/
theorem trace_nondegenerate_F2n (n : ℕ) (c : F2n n)
    (h : ∀ y : F2n n, tr2 n (c * y) = 0) : c = 0 := by
  nontriviality;
  have := traceForm_nondegenerate ( ZMod 2 ) ( F2n n );
  exact this.1 c fun y => by simpa [ Algebra.traceForm_apply ] using h y;

/-! ### Trace of M_k -/

/-
Tr(x^{2^k} + x) = 0 for all x.
-/
theorem tr_Mk_eq_zero (n : ℕ) (hn : n ≠ 0) (x : F2n n) (k : ℕ) :
    tr2 n (x ^ (2 ^ k) + x) = 0 := by
  -- Use the fact that Tr(x^{2^k}) = Tr(x) (proved as tr2_pow2 in Trace.lean).
  have h_trace_pow : tr2 n (x ^ 2 ^ k) = tr2 n x := by
    exact?;
  grind +qlia

/-! ### Frobenius Adjoint -/

/-- The adjoint exponent: j = (n - k % n) % n.
    Satisfies: n ∣ (k + j) when n > 0. -/
def frobAdjExp (k n : ℕ) : ℕ := (n - k % n) % n

/-
k + frobAdjExp k n is a multiple of n when n > 0.
-/
theorem frobAdjExp_dvd (k n : ℕ) (hn : 0 < n) : n ∣ (k + frobAdjExp k n) := by
  unfold frobAdjExp;
  simp +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( Nat.mod_lt k hn |> Nat.le_of_lt ) ]

/-
y^{2^(k + frobAdjExp k n)} = y in F_{2^n}.
-/
theorem pow_frob_adj_eq (n : ℕ) (hn : n ≠ 0) (y : F2n n) (k : ℕ) :
    y ^ (2 ^ (k + frobAdjExp k n)) = y := by
  -- Since n | (k + frobAdjExp k n) by frobAdjExp_dvd, write k + frobAdjExp k n = n * q for some q.
  obtain ⟨q, hq⟩ : ∃ q : ℕ, k + frobAdjExp k n = n * q := by
    exact frobAdjExp_dvd k n ( Nat.pos_of_ne_zero hn );
  have h_exp : ∀ q : ℕ, y ^ (2 ^ (n * q)) = y := by
    intro q; induction q <;> simp_all +decide [ pow_mul, pow_succ, pow_add ] ;
    have h_exp : y ^ (2 ^ n) = y := by
      have h_card : Fintype.card (F2n n) = 2 ^ n := by
        exact?
      rw [ ← h_card, FiniteField.pow_card ];
    exact h_exp;
  rw [ hq, h_exp ]

/-
Frobenius adjoint of trace: Tr(c · y^{2^k}) = Tr(c^{2^j} · y)
    where j = frobAdjExp k n.
-/
theorem tr_frobenius_adjoint (n : ℕ) (hn : n ≠ 0) (c y : F2n n) (k : ℕ) :
    tr2 n (c * y ^ (2 ^ k)) = tr2 n (c ^ (2 ^ frobAdjExp k n) * y) := by
  -- Use the Frobenius invariance of trace: Tr(x^{2^m}) = Tr(x) for all m (this is tr2_pow2 from Trace.lean).
  have h_frob : ∀ m : ℕ, tr2 n (c * y ^ (2 ^ k)) = tr2 n ((c * y ^ (2 ^ k)) ^ (2 ^ m)) := by
    grind +suggestions;
  convert h_frob ( frobAdjExp k n ) using 2 ; ring;
  rw [ ← pow_add, add_comm, pow_frob_adj_eq n hn y k ]

end
end Kasami