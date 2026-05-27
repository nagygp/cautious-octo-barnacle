import Mathlib
import RequestProject.FrobAlg

/-!
# Foundational Layer F2: Trace and Norm Theory

A systematic theory of trace maps over finite fields, their bilinear-form
properties, and adjoint computations for linearized polynomials.

**Motivation.** Many `sorry`s in the Dempwolff–Müller formalization reduce to
the identity `Tr(L(w)·z) = Tr(w·L*(z))` and its prerequisites: Frobenius
invariance of the trace, product-Frobenius identities, trace nondegeneracy.
This layer provides a reusable DAG of tiny lemmas that collapse all such goals.

## Main results

1. **Frobenius sum** (`frobSum`): `∑_{i=0}^{m-1} x^{p^i}` — a general version
   of the truncated trace, parametric in the characteristic.
2. **Additivity** (F2.1): `frobSum` is additive, distributes over finite sums.
3. **Frobenius invariance** (F2.2): The full trace `frobSum n` satisfies
   `Tr(x^{p^j}) = Tr(x)` via cyclic-sum reindexing.
4. **Product-Frobenius** (F2.3): `Tr(x^{p^j}·y) = Tr(x·y^{p^{n-j}})`.
5. **Nontriviality** (F2.4): `∃ x, Tr(x) ≠ 0`.
6. **Nondegeneracy** (F2.5): `x ≠ 0 ⟹ ∃ y, Tr(x·y) ≠ 0`.
7. **Sum reindexing** (F2.6): `∑_{i<m} z^{p^{n-i}} = ∑_{j ∈ Ico(n-m+1,n+1)} z^{p^j}`.
8. **Adjoint property** (F2.7): `Tr(frobSum_m(w)·z) = Tr(w·L*(z))`.

## DAG structure

```
  F2.1 (additivity)
    │
    ├──► F2.2 (Frobenius invariance)
    │      │
    │      └──► F2.3 (product-Frobenius)
    │             │
    │             └──► F2.7 (adjoint) ◄── F2.6 (reindexing)
    │
    ├──► F2.4 (nontriviality)
    │      │
    │      └──► F2.5 (nondegeneracy)
    │
    └──► F2.7 (adjoint — uses additivity + product-Frobenius)
```

**Dependencies:** Layer F1 (`FrobAlg.lean`), Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- F2.0 : Definition
-- ═══════════════════════════════════════════

/-- The Frobenius sum `∑_{i=0}^{m-1} x^{p^i}`.
    When `|F| = p^n` and `m = n`, this is the field trace `Tr_{F/GF(p)}`.
    When `m < n`, this is a truncated (partial) trace.

    This generalizes `truncTrace` (which is `frobSum 2 m`) to arbitrary
    characteristic `p`. -/
def frobSum (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (p ^ i)

/-
═══════════════════════════════════════════
F2.1 : Additivity of frobSum
═══════════════════════════════════════════

**Additivity.** `frobSum m (x + y) = frobSum m x + frobSum m y`.
    Proof: each summand `(x + y)^{p^i} = x^{p^i} + y^{p^i}` by Frobenius,
    then split the sum.
-/
lemma frobSum_add (m : ℕ) (x y : F) :
    frobSum p m (x + y) = frobSum p m x + frobSum p m y := by
      unfold frobSum;
      simp +decide [ ← Finset.sum_add_distrib, add_pow_char_pow ]

/-
**Zero.** `frobSum m 0 = 0`.
-/
lemma frobSum_zero (m : ℕ) : frobSum p m (0 : F) = 0 := by
  exact Finset.sum_eq_zero fun i hi => zero_pow ( pow_ne_zero _ hp.1.ne_zero )

/-
**Negation.** `frobSum m (-x) = -(frobSum m x)`.
-/
lemma frobSum_neg (m : ℕ) (x : F) :
    frobSum p m (-x) = -(frobSum p m x) := by
      -- Apply the fact that $(-x)^{p^i} = -x^{p^i}$ for any integer $i$.
      have h_neg_pow : ∀ i : ℕ, (-x) ^ (p ^ i) = -x ^ (p ^ i) := fun i =>
        show (iterateFrobenius F p i) (-x) = -(iterateFrobenius F p i x) from map_neg _ x
      simp +decide [ frobSum, h_neg_pow, Finset.sum_neg_distrib ]

/-
**Scalar (GF(p)).** `frobSum m (c · x) = c · frobSum m x`
    when `c^p = c` (i.e., `c ∈ GF(p)`).
-/
lemma frobSum_gfp_smul (m : ℕ) {c : F} (hc : c ^ p = c) (x : F) :
    frobSum p m (c * x) = c * frobSum p m x := by
      convert additivePolyEval_smul p m ( fun _ => 1 ) c hc x using 1 ; simp +decide [ frobSum ] ; ring;
      · simp +decide [ additivePolyEval, mul_pow ];
        rw [ Finset.sum_range ];
      · simp +decide [ frobSum, additivePolyEval ];
        exact Or.inl ( by rw [ Finset.sum_range ] )

/-
═══════════════════════════════════════════
F2.1b : Distribution over finite sums
═══════════════════════════════════════════

**Finite sum distribution.** `frobSum m (∑ fᵢ) = ∑ frobSum m (fᵢ)`.
    Follows from additivity by induction.
-/
lemma frobSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → F) (m : ℕ) :
    frobSum p m (∑ i ∈ s, f i) = ∑ i ∈ s, frobSum p m (f i) := by
      induction s using Finset.induction <;> simp_all +decide [ frobSum_add ];
      exact Finset.sum_eq_zero fun _ _ => zero_pow ( pow_ne_zero _ hp.1.ne_zero )

/-
═══════════════════════════════════════════
F2.2 : Frobenius invariance of full trace
═══════════════════════════════════════════

**Frobenius on frobSum (expansion).** `frobSum n (x^{p^j}) = ∑_{i<n} x^{p^{j+i}}`.
    This is just the definition expanded.
-/
lemma frobSum_frob_expand {n : ℕ} (x : F) (j : ℕ) :
    frobSum p n (x ^ (p ^ j)) = ∑ i ∈ Finset.range n, x ^ (p ^ (j + i)) := by
      simp +decide [ frobSum, pow_add, pow_mul ]

/-
**Idempotence.** `frobSum n (x)^p = frobSum n (x)` on `GF(p^n)`.
    The full trace lands in `GF(p)`, i.e., is a fixed point of Frobenius.
    Proof: `Tr(x)^p = ∑ x^{p^{i+1}} = ∑ x^{p^i}` by cycling with `x^{p^n} = x`.
-/
lemma frobSum_pow_p {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) :
    (frobSum p n x) ^ p = frobSum p n x := by
      have h_frob_sum : (∑ i ∈ Finset.range n, x ^ (p ^ i)) ^ p = ∑ i ∈ Finset.range n, x ^ (p ^ (i + 1)) := by
        have h_frob_sum : ∀ (s : Finset ℕ) (f : ℕ → F), (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p :=
          fun s f => by simp_rw [← show ∀ x : F, (frobenius F p) x = x ^ p from fun x => rfl]; rw [← map_sum]
        exact h_frob_sum _ _ ▸ Finset.sum_congr rfl fun _ _ => by ring;
      have h_frob_sum : ∑ i ∈ Finset.range n, x ^ (p ^ (i + 1)) = ∑ i ∈ Finset.range (n + 1), x ^ (p ^ i) - x := by
        simp +decide [ Finset.sum_range_succ' ];
      simp_all +decide [ Finset.sum_range_succ, frobSum ];
      rw [ ← hn, DempwolffMueller.frob_cycle ] ; ring

/-
**Full trace is Frobenius-stable.**
    `Tr(x)^{p^j} = Tr(x)` for all `j`. Follows from `Tr(x)^p = Tr(x)` by induction.
-/
lemma frobSum_frob_stable {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (j : ℕ) :
    (frobSum p n x) ^ (p ^ j) = frobSum p n x := by
      induction j <;> simp_all +decide [ pow_succ, pow_mul ];
      convert frobSum_pow_p p hn x using 1

/-
**Full trace is Frobenius-invariant.**
    `Tr(x^{p^j}) = Tr(x)`. Proof: `Tr(x^{p^j})^p = Tr(x^{p^j})` (idempotent),
    and `Tr(x^{p^j}) = ∑ x^{p^{j+i}}`, which is a cyclic shift of `∑ x^{p^i}`.
-/
lemma frobSum_frob_invariant {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (j : ℕ) :
    frobSum p n (x ^ (p ^ j)) = frobSum p n x := by
      -- By Lemma 4.2's support property, applying Frobenius to x^{p^j} stabilizes the trace.
      have h_trace_stabilize : frobSum p n (x ^ (p ^ j)) = ∑ i ∈ Finset.range n, x ^ (p ^ (j + i)) :=
        frobSum_frob_expand p x j
      -- By Lemma 4.2's support property, applying Frobenius to x^{p^j} stabilizes the trace. Hence, we have:
      have h_trace_stabilize' : (∑ i ∈ Finset.range n, x ^ (p ^ (j + i))) = (∑ i ∈ Finset.range n, x ^ (p ^ i)) ^ (p ^ j) := by
        rw [ finset_sum_frob_eq ];
        exact Finset.sum_congr rfl fun _ _ => by ring;
      rw [ h_trace_stabilize, h_trace_stabilize' ];
      convert frobSum_frob_stable p hn x j using 1

/-
═══════════════════════════════════════════
F2.3 : Product-Frobenius identity
═══════════════════════════════════════════

**Product-Frobenius factorization.**
    `(x · y^{p^{n-j}})^{p^j} = x^{p^j} · y` when `|F| = p^n` and `j ≤ n`.
    Proof: `(x · y^{p^{n-j}})^{p^j} = x^{p^j} · y^{p^n} = x^{p^j} · y`.
-/
lemma frob_prod_factor {n : ℕ} (hn : Fintype.card F = p ^ n) (x y : F) (j : ℕ) (hj : j ≤ n) :
    (x * y ^ (p ^ (n - j))) ^ (p ^ j) = x ^ (p ^ j) * y := by
      rw [ mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hj ];
      rw [ ← hn, FiniteField.pow_card ]

/-
**Product-Frobenius trace identity.**
    `Tr(x^{p^j} · y) = Tr(x · y^{p^{n-j}})`.
    Proof: `x^{p^j} · y = (x · y^{p^{n-j}})^{p^j}` by `frob_prod_factor`,
    so `Tr(x^{p^j} · y) = Tr((x · y^{p^{n-j}})^{p^j}) = Tr(x · y^{p^{n-j}})`.
-/
lemma trace_prod_frob {n : ℕ} (hn : Fintype.card F = p ^ n) (x y : F) (j : ℕ) (hj : j ≤ n) :
    frobSum p n (x ^ (p ^ j) * y) =
    frobSum p n (x * y ^ (p ^ (n - j))) := by
      convert frobSum_frob_invariant p hn ( x * y ^ p ^ ( n - j ) ) j using 1;
      grind +suggestions

/-
═══════════════════════════════════════════
F2.4 : Trace nontriviality
═══════════════════════════════════════════

**Nontriviality of the full trace.** There exists `x ∈ F` with `Tr(x) ≠ 0`.
    Proof: the polynomial `∑_{i<n} X^{p^i}` has degree `p^{n-1} < p^n = |F|`,
    so it cannot vanish on all of `F`.
-/
lemma frobSum_ne_zero {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n) :
    ∃ x : F, frobSum p n x ≠ 0 := by
      by_contra! h_contra;
      -- Consider the polynomial $P(X) = \sum_{i=0}^{n-1} X^{p^i}$.
      set P : Polynomial F := Finset.sum (Finset.range n) (fun i => Polynomial.X ^ (p ^ i)) with hP_def;
      have hP_deg : P.degree < Fintype.card F := by
        erw [ Polynomial.degree_lt_iff_coeff_zero ];
        simp +zetaDelta at *;
        intro m hm; rw [ Finset.card_eq_zero.mpr ] ; aesop;
        exact Finset.eq_empty_of_forall_notMem fun x hx => by linarith [ Finset.mem_filter.mp hx, Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ), pow_lt_pow_right₀ hp.1.one_lt ( show x < n from Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) ] ;;
      have hP_zero : P = 0 := by
        refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
        exact Finset.univ;
        · simpa using hP_deg;
        · simp_all +decide [ Polynomial.eval_finset_sum, frobSum ];
      simp_all +decide [ Polynomial.ext_iff ];
      specialize hP_def ( p ^ 0 ) ; simp +decide [ Finset.filter_eq ] at hP_def;
      exact absurd hP_def ( by rw [ eq_comm ] ; exact ne_of_apply_ne ( fun x : F => x ) ( by simp +decide [ show ( Finset.filter ( fun x => 1 = p ^ x ) ( Finset.range n ) ) = { 0 } from Finset.eq_singleton_iff_unique_mem.2 ⟨ Finset.mem_filter.2 ⟨ Finset.mem_range.2 hn1, by simp +decide ⟩, fun x hx => Nat.pow_right_injective hp.1.one_lt <| by linarith [ Finset.mem_filter.mp hx ] ⟩ ] ) )

/-
═══════════════════════════════════════════
F2.5 : Nondegeneracy of trace bilinear form
═══════════════════════════════════════════

**Nondegeneracy.** For `x ≠ 0`, there exists `y` with `Tr(x·y) ≠ 0`.
    Proof: take `z` with `Tr(z) ≠ 0` (nontriviality) and set `y = z · x⁻¹`.
    Then `Tr(x · y) = Tr(x · z · x⁻¹) = Tr(z) ≠ 0`.
-/
lemma trace_nondegenerate {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    {x : F} (hx : x ≠ 0) :
    ∃ y : F, frobSum p n (x * y) ≠ 0 := by
      -- By frobSum_ne_zero, get z with frobSum n z ≠ 0.
      obtain ⟨z, hz⟩ : ∃ z : F, frobSum p n z ≠ 0 :=
        frobSum_ne_zero p hn hn1
      exact ⟨ z / x, by simpa [ mul_div_cancel₀ _ hx ] using hz ⟩

/-
═══════════════════════════════════════════
F2.6 : Sum reindexing
═══════════════════════════════════════════

**Reindexing (range to Ico).**
    `∑_{i=0}^{m-1} z^{p^{n-i}} = ∑_{j ∈ Ico(n-m+1, n+1)} z^{p^j}`
    via the substitution `j = n - i`.
-/
omit [Fintype F] hp [CharP F p] in
lemma sum_frob_reverse {n m : ℕ} (hm : m ≤ n) (z : F) :
    ∑ i ∈ Finset.range m, z ^ (p ^ (n - i)) =
    ∑ j ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (p ^ j) := by
      refine' Finset.sum_bij ( fun i hi => n - i ) _ _ _ _ <;> simp_all +arith +decide;
      · exact fun a ha => by omega;
      · intros; omega;
      · exact fun b hb₁ hb₂ => ⟨ n - b, by omega, by omega ⟩

/-
═══════════════════════════════════════════
F2.7 : Adjoint of the truncated trace
═══════════════════════════════════════════

**Adjoint step 1: expansion.**
    `Tr(frobSum_m(w) · z) = ∑_{i<m} Tr(w^{p^i} · z)`.
    Proof: expand `frobSum m w = ∑ w^{p^i}`, distribute multiplication,
    then use additivity of the trace.
-/
lemma frobSum_adj_expand {n : ℕ} (m : ℕ) (w z : F) :
    frobSum p n (frobSum p m w * z) =
    ∑ i ∈ Finset.range m, frobSum p n (w ^ (p ^ i) * z) := by
      convert frobSum_finset_sum p ( Finset.range m ) ( fun i => w ^ p ^ i * z ) n using 1;
      simp +decide only [frobSum, sum_mul]

/-
**Adjoint step 2: Frobenius swap.**
    `∑_{i<m} Tr(w^{p^i} · z) = ∑_{i<m} Tr(w · z^{p^{n-i}})`.
    Proof: apply `trace_prod_frob` to each summand.
-/
lemma frobSum_adj_frob_swap {n : ℕ} (hn : Fintype.card F = p ^ n) (m : ℕ) (hm : m ≤ n) (w z : F) :
    ∑ i ∈ Finset.range m, frobSum p n (w ^ (p ^ i) * z) =
    ∑ i ∈ Finset.range m, frobSum p n (w * z ^ (p ^ (n - i))) := by
      apply Finset.sum_congr rfl;
      exact fun i hi => trace_prod_frob p hn w z i ( by linarith [ Finset.mem_range.mp hi ] )

/-
**Adjoint step 3: reassembly.**
    `∑_{i<m} Tr(w · z^{p^{n-i}}) = Tr(w · ∑_{i<m} z^{p^{n-i}})`.
    Proof: factor out `w`, recombine using trace additivity.
-/
lemma frobSum_adj_reassemble {n : ℕ} (m : ℕ) (w z : F) :
    ∑ i ∈ Finset.range m, frobSum p n (w * z ^ (p ^ (n - i))) =
    frobSum p n (w * ∑ i ∈ Finset.range m, z ^ (p ^ (n - i))) := by
      simp +decide only [mul_sum, frobSum_finset_sum]

/-
**The adjoint property (range form).**
    `Tr(frobSum_m(w) · z) = Tr(w · ∑_{i<m} z^{p^{n-i}})`.
    Chains steps 1–3 of the adjoint computation.
-/
lemma frobSum_adjoint {n : ℕ} (hn : Fintype.card F = p ^ n) (m : ℕ) (hm : m ≤ n)
    (w z : F) :
    frobSum p n (frobSum p m w * z) =
    frobSum p n (w * ∑ i ∈ Finset.range m, z ^ (p ^ (n - i))) := by
      rw [ frobSum_adj_expand, frobSum_adj_frob_swap, frobSum_adj_reassemble ];
      · exact hn;
      · exact hm

/-
**The adjoint property (Ico form).**
    `Tr(frobSum_m(w) · z) = Tr(w · ∑_{j ∈ Ico(n-m+1,n+1)} z^{p^j})`.
    Combines `frobSum_adjoint` with `sum_frob_reverse`.
-/
lemma frobSum_adjoint_Ico {n : ℕ} (hn : Fintype.card F = p ^ n) (m : ℕ) (hm : m ≤ n)
    (w z : F) :
    frobSum p n (frobSum p m w * z) =
    frobSum p n (w * ∑ j ∈ Finset.Ico (n - m + 1) (n + 1), z ^ (p ^ j)) := by
      -- Apply the adjoint property to rewrite the left-hand side.
      rw [DempwolffMueller.frobSum_adjoint p hn m hm w z];
      rw [ DempwolffMueller.sum_frob_reverse p hm z ]

end DempwolffMueller