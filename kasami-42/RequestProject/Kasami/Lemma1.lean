/-
Formalization of Lemma 1 from Kasami (1971).

Lemma 1 states: Let `v(X) = c₁X^{u₁} + ⋯ + c_tX^{u_t}` be a polynomial over GF(q)
with `c_i ≠ 0`, and let `R = {e | v(α^e) = 0}` where `α` has order `n` in GF(q^m).
Let `f(X) = ∏(X - α^{u_i})`. Let `R̄` be the subspace spanned by `{X^e | e ∈ R}`
in the residue classes modulo `f(X)` over GF(q^m).
Then, for any `e ∉ R`, `X^e ∉ R̄`.

The key idea: if `X^e ≡ ∑_{j∈R} b_j X^j (mod f(X))`, then evaluating at each root
`α^{u_i}` gives `α^{eu_i} = ∑_{j∈R} b_j α^{ju_i}`, so
`v(α^e) = ∑_i c_i α^{eu_i} = ∑_{j∈R} b_j v(α^j) = 0`, contradicting `e ∉ R`.
-/
import Mathlib
import RequestProject.Kasami.Defs

open Polynomial Finset BigOperators

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [Fintype K]

/-!
## Lemma 1: Linear Independence in Residue Classes

We formalize this as a statement about linear independence over the evaluation map.
Given elements `u₁, …, u_t` in a field extension, and coefficients `c₁, …, c_t`,
the "root set" `R` consists of those `e` where `∑_i c_i α^{e·u_i} = 0`.
The lemma says that elements outside `R` cannot be in the span of elements in `R`
when viewed through the Vandermonde-like evaluation map.
-/

/-- The evaluation function `v` applied to `α^e`:
    `v(α^e) = ∑_{i} c_i · α^{e · u_i}`. -/
def evalV {t : ℕ} (α : K) (c : Fin t → K) (u : Fin t → ℤ) (e : ℤ) : K :=
  ∑ i : Fin t, c i * α ^ (e * u i)

/-- The root set `R = {e | v(α^e) = 0}` with respect to a fixed modulus `n`. -/
def rootSet {t : ℕ} (α : K) (c : Fin t → K) (u : Fin t → ℤ) (n : ℕ) : Set (ZMod n) :=
  {e | evalV α c u (ZMod.val e : ℤ) = 0}

/-
**Lemma 1** (Kasami, 1971).
    Let `v(X) = ∑ c_i X^{u_i}` with all `c_i ≠ 0`.
    Let `f(X) = ∏ (X - α^{u_i})`.
    If `X^e` can be written as a linear combination of `{X^j | j ∈ R}` modulo `f(X)`,
    then `e ∈ R`.

    Equivalently: for `e ∉ R`, `X^e` is not in the span of `{X^j | j ∈ R}`
    in the quotient ring `K[X]/(f(X))`.

    We state a more algebraic version: if `α^{e·u_i} = ∑_{j∈S} b_j · α^{j·u_i}`
    for all `i` (where `S ⊆ R`), then `v(α^e) = 0`, i.e., `e ∈ R`.

    The contrapositive gives the original lemma.
-/
theorem kasami_lemma1 {t : ℕ} (α : K) (c : Fin t → K) (u : Fin t → ℤ)
    (_hc : ∀ i, c i ≠ 0) {S : Finset ℤ} (b : ℤ → K)
    (hS : ∀ j, j ∈ S → evalV α c u j = 0)
    {e : ℤ}
    (hspan : ∀ i : Fin t, α ^ (e * u i) = ∑ j ∈ S, b j * α ^ (j * u i)) :
    evalV α c u e = 0 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ i : Fin t, c i * α ^ (e * u i) = ∑ j ∈ S, b j * ∑ i : Fin t, c i * α ^ (j * u i) := by
    simp +decide only [Finset.mul_sum _ _ _]
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    intros; rw [hspan]; simp +decide [mul_left_comm, Finset.mul_sum _ _ _]
  exact h_fubini.trans ( Finset.sum_eq_zero fun j hj => mul_eq_zero_of_right _ ( hS j hj ) )

end