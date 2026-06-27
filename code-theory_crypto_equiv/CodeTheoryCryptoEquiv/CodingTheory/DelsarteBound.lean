import Mathlib
import CodeTheoryCryptoEquiv.CodingTheory.DelsarteLP

/-!
# The Delsarte linear-programming bound

This module completes roadmap item 9 of `CODING_THEORY_DIRECTIONS.md`
(MacWilliams–Sloane, Ch. 17): the **Delsarte linear-programming (LP) bound** on
the size of a code, obtained from the Delsarte inequalities
(`CodingTheory.delsarte_transform_eq`) by exhibiting a *feasible dual function*.

The previous layer (`CodeTheoryCryptoEquiv/CodingTheory/DelsarteLP.lean`) established the
linear constraints — the Krawtchouk transform of the weight distribution is
nonnegative.  Here we run the optimisation argument in its standard, witness-based
form: any polynomial `f(x) = Σ_k f_k K_k(x)` with nonnegative Krawtchouk
coefficients `f_k ≥ 0` (`k ≥ 1`), positive leading constant `f_0 > 0`, and which
is *nonpositive* on the achievable nonzero weights `d ≤ i ≤ n`, yields the bound

  `|C| ≤ f(0) / f_0`.

This is the dual (feasibility) form of the LP bound: every feasible `f` certifies
an upper bound on `|C|`, and the LP optimum is the best such certificate.

## Proof outline

Write `A_i = weightDistribution C i`, `B_k = weightDistribution Cᗮ k`,
`g(x) = Σ_k f_k K_k(x)`, summing `k` over `0 … n`.  Consider `S = Σ_i A_i g(i)`.

* Swapping the order of summation and using the Delsarte transform identity
  `Σ_i A_i K_k(i) = |C| · B_k` gives `S = |C| · Σ_k f_k B_k`.  Since `B_0 = 1`,
  `f_k ≥ 0` for `k ≥ 1`, and `B_k ≥ 0`, this is `≥ |C| · f_0`.
* Splitting the `i`-sum at the minimum distance: `A_0 = 1`, the terms with
  `0 < i < d` vanish (minimum distance `≥ d`), and the terms with `d ≤ i ≤ n`
  have `g(i) ≤ 0` and `A_i ≥ 0`, so `S ≤ g(0)`.

Combining, `|C| · f_0 ≤ g(0)`, i.e. `|C| ≤ g(0)/f_0`.

## Main result

* `delsarte_lp_bound` — the Delsarte LP bound `|C| ≤ f(0)/f_0` for a feasible `f`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- The value at `x` of the candidate dual polynomial
`f(x) = Σ_{k=0}^{n} f_k K_k(x)` built from coefficients `f : ℕ → ℝ`, where
`q` is the field size and `n` the length. -/
noncomputable def lpDual (q n : ℕ) (f : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f k * (krawtchouk q n k x : ℝ)

/--
**The Delsarte transform identity, real form.**  The Krawtchouk transform of the
primal weight distribution equals `|C|` times the dual weight distribution:
`Σ_{i=0}^{n} A_i K_k(i) = |C| · B_k`.
-/
theorem delsarte_transform_eq_real (C : Submodule F (ι → F)) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1),
        (weightDistribution C i : ℝ)
          * (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℝ)
      = (Fintype.card C : ℝ) * (weightDistribution (dualCode C) k : ℝ) := by
  have h := delsarte_transform_eq C k hk
  have := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at this ⊢
  linarith [this]

/-
**The Delsarte linear-programming bound** (MacWilliams–Sloane, Ch. 17).

Let `C` be a linear code of length `n = #ι` over a field with `q = #F` elements,
with minimum distance at least `d` (no nonzero codeword of weight `< d`, encoded
by `hd`).  Suppose `f : ℕ → ℝ` satisfies

* `hf0 : 0 < f 0`,
* `hfk : ∀ k, 1 ≤ k → k ≤ n → 0 ≤ f k`  (nonnegative Krawtchouk coefficients),
* `hfneg : ∀ i, d ≤ i → i ≤ n → lpDual f i ≤ 0`  (nonpositive on the achievable
  nonzero weights).

Then `|C| ≤ f(0)/f_0`, where `f(0) = lpDual f 0 = Σ_k f_k K_k(0)`.
-/
theorem delsarte_lp_bound (C : Submodule F (ι → F)) (d : ℕ)
    (f : ℕ → ℝ) (hf0 : 0 < f 0)
    (hfk : ∀ k, 1 ≤ k → k ≤ Fintype.card ι → 0 ≤ f k)
    (hfneg : ∀ i, d ≤ i → i ≤ Fintype.card ι →
      lpDual (Fintype.card F) (Fintype.card ι) f i ≤ 0)
    (hd : ∀ i, 0 < i → i < d → weightDistribution C i = 0) :
    (Fintype.card C : ℝ) ≤ lpDual (Fintype.card F) (Fintype.card ι) f 0 / f 0 := by
  rw [ le_div_iff₀ hf0 ];
  -- Lower bound: $f(0) \cdot |C| \leq \sum_{i=0}^n A_i g(i)$.
  have h_lower_bound : (Fintype.card C : ℝ) * f 0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℝ) * (lpDual (Fintype.card F) (Fintype.card ι) f i) := by
    -- By definition of $lpDual$, we can rewrite the right-hand side of the inequality.
    have h_lpDual : ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℝ) * (lpDual (Fintype.card F) (Fintype.card ι) f i) = ∑ k ∈ Finset.range (Fintype.card ι + 1), (f k : ℝ) * (Fintype.card C : ℝ) * (weightDistribution (dualCode C) k : ℝ) := by
      have h_lower_bound : ∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℝ) * (lpDual (Fintype.card F) (Fintype.card ι) f i) = ∑ k ∈ Finset.range (Fintype.card ι + 1), (f k : ℝ) * (∑ i ∈ Finset.range (Fintype.card ι + 1), (weightDistribution C i : ℝ) * (krawtchouk (Fintype.card F) (Fintype.card ι) k i : ℝ)) := by
        simp +decide only [lpDual, Finset.mul_sum _ _ _, mul_left_comm];
        exact Finset.sum_comm;
      convert h_lower_bound using 2;
      rw [ mul_assoc, delsarte_transform_eq_real C _ ( Finset.mem_range_succ_iff.mp ‹_› ) ];
    rw [ h_lpDual, Finset.sum_range_succ' ];
    rw [ weightDistribution_zero ] ; norm_num ; ring_nf;
    exact le_add_of_nonneg_right ( Finset.sum_nonneg fun i hi => mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( hfk _ ( by linarith ) ( by linarith [ Finset.mem_range.mp hi ] ) ) ) ( Nat.cast_nonneg _ ) );
  refine' le_trans h_lower_bound ( le_trans ( Finset.sum_le_sum fun i hi => _ ) _ );
  use fun i => if i = 0 then ( weightDistribution C 0 : ℝ ) * lpDual ( Fintype.card F ) ( Fintype.card ι ) f 0 else 0;
  · by_cases hi0 : i = 0 <;> simp_all +decide;
    by_cases hi1 : i < d;
    · rw [ hd i ( Nat.pos_of_ne_zero hi0 ) hi1, Nat.cast_zero, MulZeroClass.zero_mul ];
    · exact mul_nonpos_of_nonneg_of_nonpos ( Nat.cast_nonneg _ ) ( hfneg i ( le_of_not_gt hi1 ) hi );
  · simp +decide [ weightDistribution_zero ]

end CodingTheory