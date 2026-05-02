/-
Formalization of the weight restriction theorems from Kasami (1971):
  Theorem 1 (generalization of BCH bound) and Theorem 2.
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.Lemma1

open Polynomial Finset BigOperators

noncomputable section

/-!
## Theorem 1: Generalized BCH Bound

This is a generalization of the BCH bound and Berlekamp's theorem.

**Setup**: Let `v(X) = ∑ c_i X^{u_i}` over GF(q) with `c_i ≠ 0`, and
`R = {e | v(α^e) = 0}` as before. The polynomial `v` has `t` nonzero terms.

**Statement**: Suppose that `A₀ + ∑ A_{i,t_i} ∉ R`, and that for all other
choices `(j₀, j₁, …, j_l)` with `0 ≤ j_i ≤ t_i`, we have
`∑ A_{i,j_i} ∈ R`. Then `t > ∑ t_i`.

This gives a lower bound on the weight of codewords.
-/

/-- **Theorem 1** (Kasami, 1971).
    A generalized BCH bound: under the hypotheses about the root set `R`,
    the number of terms `t` exceeds the sum `∑ t_i`.

    We state this in terms of a finite field element `α` and abstract root set. -/
theorem kasami_theorem1
    {K : Type*} [Field K] [Fintype K]
    {t : ℕ} (α : K) (c : Fin t → K) (u : Fin t → ℤ)
    (hc : ∀ i, c i ≠ 0)
    {l : ℕ} (t_param : Fin (l + 1) → ℕ)
    (A : (i : Fin (l + 1)) → Fin (t_param i + 1) → ℤ)
    -- The "exceptional" index
    (j_bar₀ : Fin (t_param 0 + 1))
    -- Hypothesis: the "exceptional" sum is NOT in R
    (hNotInR : evalV α c u
      (A 0 j_bar₀ +
       ∑ i : Fin l, A i.castSucc (Fin.last (t_param i.castSucc))) ≠ 0)
    -- Hypothesis: all other sums ARE in R
    (hInR : ∀ (j : (i : Fin (l + 1)) → Fin (t_param i + 1)),
      (j 0 ≠ j_bar₀ ∨
       ∃ i : Fin l, j i.castSucc ≠ Fin.last (t_param i.castSucc)) →
      evalV α c u (∑ i : Fin (l + 1), A i (j i)) = 0) :
    t > ∑ i : Fin (l + 1), t_param i := by
  sorry

/-!
### Remark 1: Recovery of the BCH Bound

Setting `t₀ = 0`, `t_i = 1`, `A_{00} = 1`, `A_{i0} = 0`, `A_{i1} = 1`
for `1 ≤ i ≤ l` in Theorem 1 recovers the classical BCH bound.
-/

/-
**Remark 1**: The classical BCH bound is a special case of Theorem 1.
    If a cyclic code has consecutive roots `α, α², …, α^{d-1}` (where `α` is a
    primitive `n`-th root of unity), then its minimum distance is at least `d`.

    Here `t` is the number of nonzero terms (weight of the codeword polynomial),
    and we show `t ≥ d` given that `d - 1` consecutive powers are roots but `α^d` is not.
-/
theorem bch_bound_from_theorem1
    {K : Type*} [Field K] [Fintype K]
    {t : ℕ} (α : K) (c : Fin t → K) (u : Fin t → ℤ)
    (hc : ∀ i, c i ≠ 0)
    {d : ℕ} (hd : 1 ≤ d)
    -- Consecutive roots: v(α^e) = 0 for e = 1, 2, …, d-1
    (hRoots : ∀ e : ℕ, 1 ≤ e → e ≤ d - 1 → evalV α c u (e : ℤ) = 0)
    -- But v(α^d) ≠ 0 (i.e., the d-th power is not a root)
    (hNotRoot : evalV α c u (d : ℤ) ≠ 0) :
    t ≥ d := by
  by_contra! ht_lt_d;
  -- Let's assume that $v(X) = \sum_{i=1}^d c_i X^{u_i}$ is a polynomial with $d$ nonzero terms and that $v(\alpha^e) = 0$ for $e = 1, 2, \ldots, d-1$, but $v(\alpha^d) \neq 0$.
  set l := d - 1;
  -- Let's choose $t_param$ such that $t_param 0 = 0$ and $t_param i = 1$ for $1 \leq i \leq l$.
  set t_param : Fin (l + 1) → ℕ := fun i => if i = 0 then 0 else 1;
  -- Let's choose $A$ such that $A 0 0 = 1$ and $A i 0 = 0$, $A i 1 = 1$ for $1 \leq i \leq l$.
  set A : (i : Fin (l + 1)) → Fin (t_param i + 1) → ℤ := fun i j => if i = 0 then 1 else if j = 0 then 0 else 1;
  refine' kasami_theorem1 α c u hc t_param A _ _ _ |> fun h => _;
  any_goals exact Fin.last _;
  · rcases d with ( _ | _ | d ) <;> simp_all +decide [ Fin.sum_univ_succ ];
    simp +zetaDelta at *;
    linarith;
  · convert hNotRoot using 2;
    simp +zetaDelta at *;
    rcases d with ( _ | _ | d ) <;> simp_all +decide [ Fin.sum_univ_succ ];
    ring;
  · intro j hj;
    convert hRoots ( ∑ i : Fin ( l + 1 ), if i = 0 then 1 else if j i = 0 then 0 else 1 ) _ _ using 1;
    · simp +zetaDelta at *;
    · exact le_trans ( by simp +decide ) ( Finset.single_le_sum ( fun i _ => by positivity ) ( Finset.mem_univ 0 ) );
    · rcases d with ( _ | _ | d ) <;> simp_all +decide [ Fin.sum_univ_succ ];
      · grind +splitImp;
      · simp +zetaDelta at *;
        rw [ Finset.sum_ite ];
        simp +arith +decide [ Finset.filter_not, Finset.card_sdiff ];
        by_cases h : j 0 = 0 <;> simp_all +decide [ Fin.exists_fin_succ ];
        · obtain ⟨ i, hi ⟩ := hj;
          use Fin.castSucc i;
          grind;
        · exact False.elim ( h ( Fin.ext ( by simp +decide [ t_param ] ) ) )

/-!
## Theorem 2: Restrictions on Codeword Weights

Theorem 2 gives restrictions on which weights can occur in certain subcodes
of the 2nd-order Reed-Muller codes.

If the roots of the generator polynomial include all `α^i` for
`1 ≤ i ≤ 2w` with `i ∉ K(m-r, j)`, then the extended code has no
codewords of weight `w` unless `w = 2^{m-r+1} - 2^{lj-1}` for some `l`.
-/

/-- **Theorem 2** (Kasami, 1971).
    Weight restriction for subcodes of 2nd-order Reed-Muller codes.
    The possible nonzero weights of codewords in the extended code
    are restricted to specific values of the form `2^{m-r+1} - 2^{lj-1}`. -/
theorem kasami_theorem2
    (m r j : ℕ)
    (_hr : 2 ≤ r) (_hr' : r ≤ m - 2)
    (_hj : j ∣ m - r + 2)
    (w : ℕ) (_hw : w < 2 ^ (m - r + 1) - 2)
    -- (Code and root conditions would be formalized with the code families)
    -- The conclusion: w must be of the specified form
    (_hweight : ∃ (C : Submodule (ZMod 2) (Codeword (2 ^ m)))
               (v : Codeword (2 ^ m)), v ∈ C ∧ hammingWt v = w) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ (m - r + 2) / j ∧ w = 2 ^ (m - r + 1) - 2 ^ (l * j - 1) := by
  sorry

end